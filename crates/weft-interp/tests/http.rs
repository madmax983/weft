//! The HTTP stretch: `http.serve` answers one request on a real socket.

#![allow(clippy::unwrap_used, clippy::expect_used, missing_docs)]

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::{Duration, Instant};

use weft_interp::{run_main, RunOptions};
use weft_sema::Options;

const SRC: &str = r#"
struct User { id: u64, name: String }

mod db {
    pub fn user(id: String) -> User / net { User { id: 1, name: id } }
}

fn handle(req: Request) -> Response / net, log {
    let user = db.user(req.param("id"))
    log.info("served {user.id}")
    Response.json(user)
}

fn main(env: Env) / io {
    http.serve(env.net.listen("ADDR"), handle)
    print("stopped")
}
"#;

#[test]
fn http_serve_answers_one_request() {
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let addr = format!("127.0.0.1:{port}");
    let src = SRC.replace("ADDR", &addr);
    let server = std::thread::spawn(move || {
        let c = weft_check::check_source("http.wf", &src, Options::default());
        assert!(c.ok(), "{:?}", c.codes());
        let opts = RunOptions {
            max_requests: Some(1),
            ..RunOptions::default()
        };
        run_main(&c, &opts).map_err(|e| e.to_string())
    });
    let start = Instant::now();
    let mut stream = loop {
        match TcpStream::connect(&addr) {
            Ok(s) => break s,
            Err(_) if start.elapsed() < Duration::from_secs(20) => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("cannot connect: {e}"),
        }
    };
    stream
        .write_all(b"GET /user?id=7 HTTP/1.1\r\nHost: localhost\r\n\r\n")
        .unwrap();
    let mut resp = String::new();
    stream.read_to_string(&mut resp).unwrap();
    assert!(resp.starts_with("HTTP/1.1 200 OK\r\n"), "{resp}");
    assert!(resp.contains("Content-Type: application/json"));
    assert!(resp.ends_with(r#"{"id":1,"name":"7"}"#), "{resp}");
    let outcome = server.join().unwrap().unwrap();
    assert_eq!(outcome.stdout, "stopped\n");
    assert_eq!(outcome.stderr, "info: served 1\n");
}

#[test]
fn http_serve_with_no_requests_returns() {
    let src = SRC.replace("ADDR", "127.0.0.1:1");
    let c = weft_check::check_source("http.wf", &src, Options::default());
    let opts = RunOptions {
        max_requests: Some(0),
        ..RunOptions::default()
    };
    assert_eq!(run_main(&c, &opts).unwrap().stdout, "stopped\n");
}

/// Serves one request with the handler `handler` and returns, for each
/// request task, true if the scheduler may move it to another worker.
fn request_tasks_stealable(handler: &str) -> Vec<bool> {
    request_tasks_stealable_with("", handler)
}

/// As `request_tasks_stealable`, with the items `items` before `main`. The
/// result has each task that the run spawns, in order.
fn request_tasks_stealable_with(items: &str, handler: &str) -> Vec<bool> {
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let addr = format!("127.0.0.1:{port}");
    let src = format!(
        "{items}\nfn main(env: Env) / io {{\n    let hits = Rc.new(0)\n    let n = 1\n    http.serve(env.net.listen(\"{addr}\"), {handler})\n}}\n"
    );
    let server = std::thread::spawn(move || {
        let c = weft_check::check_source("http.wf", &src, Options::default());
        assert!(c.ok(), "{:?}", c.codes());
        let opts = RunOptions {
            max_requests: Some(1),
            workers: 4,
            ..RunOptions::default()
        };
        run_main(&c, &opts).map_err(|e| e.to_string())
    });
    let start = Instant::now();
    let mut stream = loop {
        match TcpStream::connect(&addr) {
            Ok(s) => break s,
            Err(_) if start.elapsed() < Duration::from_secs(20) => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("cannot connect: {e}"),
        }
    };
    stream.write_all(b"GET / HTTP/1.1\r\n\r\n").unwrap();
    let mut resp = String::new();
    stream.read_to_string(&mut resp).unwrap();
    let outcome = server.join().unwrap().unwrap();
    outcome
        .trace
        .iter()
        .filter_map(|e| match e {
            weft_interp::TraceEvent::Spawn { stealable, .. } => Some(*stealable),
            _ => None,
        })
        .collect()
}

#[test]
fn request_task_of_a_nonportable_handler_is_pinned() {
    // The handler captures an `Rc`: its request task stays on the worker of
    // the server (ADR 0006).
    let pinned =
        request_tasks_stealable("|req| {\n let h = hits.clone()\n Response.text(\"hit\") }");
    assert_eq!(pinned, vec![false]);
    // A handler with portable captures can move.
    let plain = request_tasks_stealable("|req| Response.text(\"n = {n}\")");
    assert_eq!(plain, vec![true]);
}

#[test]
fn request_task_of_a_function_item_is_stealable() {
    // A function item captures nothing: its request task can move, unless the
    // item can start a pinned task (`EffectSig::pins`, ADR 0010).
    let item = "fn reply(req: Request) -> Response { Response.text(\"hi\") }";
    assert_eq!(request_tasks_stealable_with(item, "reply"), vec![true]);
    let pins = "fn reply(req: Request) -> Response / async {\n    let r = Rc.new(0)\n    scope { s => s.spawn(|| { let y = r.clone() }) }\n    Response.text(\"hi\")\n}";
    assert_eq!(
        request_tasks_stealable_with(pins, "reply"),
        vec![false, false]
    );
}
