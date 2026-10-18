//! A minimal HTTP/1.1 server for `http.serve(listener, handler)`.
//!
//! The serving task waits for connections. When no task is ready, the scheduler
//! accepts one connection, reads one request and runs `handler(request)` as a
//! task. When that task finishes, the server writes its response and closes the
//! connection. `RunOptions::max_requests` stops the server after that many
//! requests.

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::rc::Rc;
use std::time::{Duration, Instant};

use super::{Flow, TState, TaskResult, Wait, R};
use crate::error::ErrorKind;
use crate::trace::{SuspendReason, TraceEvent};
use crate::value::{Cap, HEnv, HttpRequest, HttpResponse, TaskId, Value};

/// The state of a running server.
#[derive(Debug)]
pub struct HttpState {
    listener: TcpListener,
    handler: Value,
    henv: HEnv,
    server: TaskId,
    served: usize,
    max: Option<usize>,
    in_flight: Vec<(TaskId, TcpStream)>,
}

/// How long the server waits for one connection.
const ACCEPT_LIMIT: Duration = Duration::from_secs(30);

fn bind_addr(addr: &str) -> String {
    if addr.starts_with(':') {
        format!("127.0.0.1{addr}")
    } else {
        addr.to_string()
    }
}

fn decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => out.push(b' '),
            b'%' if i + 2 < bytes.len() => {
                let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).unwrap_or("");
                if let Ok(b) = u8::from_str_radix(hex, 16) {
                    out.push(b);
                    i += 2;
                } else {
                    out.push(b'%');
                }
            }
            b => out.push(b),
        }
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Parses the request line and the query of an HTTP request.
pub fn parse_request(text: &str) -> HttpRequest {
    let line = text.lines().next().unwrap_or("");
    let mut parts = line.split_whitespace();
    let method = parts.next().unwrap_or("GET").to_string();
    let target = parts.next().unwrap_or("/");
    let (path, query) = target.split_once('?').unwrap_or((target, ""));
    let mut params = BTreeMap::new();
    for pair in query.split('&').filter(|p| !p.is_empty()) {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        params.insert(decode(k), decode(v));
    }
    HttpRequest {
        method,
        path: path.to_string(),
        params,
    }
}

/// Formats an HTTP response.
pub fn format_response(r: &HttpResponse) -> String {
    let reason = match r.status {
        200 => "OK",
        404 => "Not Found",
        _ => "Internal Server Error",
    };
    format!(
        "HTTP/1.1 {} {reason}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
        r.status,
        r.content_type,
        r.body.len(),
        r.body
    )
}

fn read_request(stream: &mut TcpStream) -> String {
    let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
    let mut buf = Vec::new();
    let mut chunk = [0u8; 1024];
    loop {
        match stream.read(&mut chunk) {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                buf.extend_from_slice(&chunk[..n]);
                if buf.windows(4).any(|w| w == b"\r\n\r\n") || buf.len() > 64 * 1024 {
                    break;
                }
            }
        }
    }
    String::from_utf8_lossy(&buf).into_owned()
}

impl super::Machine<'_, '_> {
    /// `http.serve(listener, handler)`.
    pub(crate) fn http_serve(&mut self, l: &Value, handler: Value, henv: &HEnv) -> R<Flow> {
        let max = self.opts.max_requests;
        if max == Some(0) {
            self.heap.drop_value(handler);
            return self.deliver(Value::Unit);
        }
        let Value::Cap(Cap::Listener(i)) = *l else {
            return Err(self.fault("`serve` needs a listener"));
        };
        let addr = bind_addr(self.listeners.get(i).map_or(":0", String::as_str));
        let listener = TcpListener::bind(&addr)
            .map_err(|e| self.fault(format!("cannot listen on {addr}: {e}")))?;
        let _ = listener.set_nonblocking(true);
        let server = self.cur;
        self.http = Some(HttpState {
            listener,
            handler,
            henv: henv.clone(),
            server,
            served: 0,
            max,
            in_flight: Vec::new(),
        });
        Ok(self.block(Wait::Accept, SuspendReason::Accept))
    }

    /// Returns true if the server waits for work.
    pub(crate) const fn http_pending(&self) -> bool {
        self.http.is_some()
    }

    /// Finishes requests whose handler task is done, then accepts a connection.
    pub(crate) fn http_poll(&mut self) -> R<()> {
        let Some(mut st) = self.http.take() else {
            return Ok(());
        };
        let mut still = Vec::new();
        for (t, mut stream) in std::mem::take(&mut st.in_flight) {
            if self.tasks[t].state != TState::Done {
                still.push((t, stream));
                continue;
            }
            let resp = match self.tasks[t].result.take() {
                Some(TaskResult::Ok(Value::Response(r))) => (*r).clone(),
                Some(TaskResult::Ok(v)) => HttpResponse {
                    status: 200,
                    content_type: "text/plain".into(),
                    body: self.show(&v),
                },
                _ => HttpResponse {
                    status: 500,
                    content_type: "text/plain".into(),
                    body: "internal error".into(),
                },
            };
            let _ = stream.write_all(format_response(&resp).as_bytes());
            let _ = stream.flush();
            st.served += 1;
        }
        st.in_flight = still;
        let started = st.served + st.in_flight.len();
        if st.max.is_some_and(|m| started >= m) {
            if st.in_flight.is_empty() {
                let server = st.server;
                self.heap.drop_value(st.handler);
                self.wake(server, Some(Value::Unit));
                return Ok(());
            }
            self.http = Some(st);
            return Ok(());
        }
        if !st.in_flight.is_empty() {
            self.http = Some(st);
            return Ok(());
        }
        let begin = Instant::now();
        let stream = loop {
            match st.listener.accept() {
                Ok((s, _)) => break s,
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    if begin.elapsed() > ACCEPT_LIMIT {
                        self.http = Some(st);
                        return Err(
                            self.err(ErrorKind::Deadlock, "the server got no connection in time")
                        );
                    }
                    std::thread::sleep(Duration::from_millis(2));
                }
                Err(e) => {
                    self.http = Some(st);
                    return Err(self.fault(format!("accept failed: {e}")));
                }
            }
        };
        let mut stream = stream;
        let _ = stream.set_nonblocking(false);
        let req = parse_request(&read_request(&mut stream));
        let handler = st.handler.clone();
        let server = st.server;
        let worker = self.tasks[server].worker;
        let frame = self.task_frame_args(handler, vec![Value::Request(Rc::new(req))], &st.henv)?;
        let t = self.add_task(frame, worker, true, None);
        let _ = self.tasks[t].handle.consume();
        self.trace.push(TraceEvent::Spawn {
            task: t,
            parent: server,
            worker,
            stealable: true,
        });
        st.in_flight.push((t, stream));
        self.http = Some(st);
        Ok(())
    }

    /// Makes the first frame of a task that calls `f` with arguments.
    pub(crate) fn task_frame_args(
        &mut self,
        f: Value,
        args: Vec<Value>,
        henv: &HEnv,
    ) -> R<super::CodeFrame> {
        match f {
            Value::Closure(c) => {
                self.code_frame(c.code, args, Rc::from(c.cells.as_slice()), c.henv.clone())
            }
            Value::FnItem(f) => {
                let Some(code) = self.rt.compiled.fn_code.get(f).copied().flatten() else {
                    return Err(self.fault("a handler needs a function with a body"));
                };
                self.code_frame(code, args, Rc::from(Vec::new()), henv.clone())
            }
            _ => Err(self.fault("a handler must be a function")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_query_parameters() {
        let r = parse_request("GET /user?id=7&name=a+b%21 HTTP/1.1\r\nHost: x\r\n\r\n");
        assert_eq!(r.method, "GET");
        assert_eq!(r.path, "/user");
        assert_eq!(r.params.get("id").map(String::as_str), Some("7"));
        assert_eq!(r.params.get("name").map(String::as_str), Some("a b!"));
        let r = parse_request("");
        assert_eq!(r.path, "/");
        assert_eq!(decode("%zz"), "%zz");
    }

    #[test]
    fn formats_responses() {
        let r = HttpResponse {
            status: 200,
            content_type: "text/plain".into(),
            body: "hi".into(),
        };
        let s = format_response(&r);
        assert!(s.starts_with("HTTP/1.1 200 OK\r\n"));
        assert!(s.ends_with("\r\n\r\nhi"));
        let r = HttpResponse { status: 500, ..r };
        assert!(format_response(&r).contains("500 Internal Server Error"));
        assert_eq!(bind_addr(":80"), "127.0.0.1:80");
        assert_eq!(bind_addr("0.0.0.0:80"), "0.0.0.0:80");
    }
}
