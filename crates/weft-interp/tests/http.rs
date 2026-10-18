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
