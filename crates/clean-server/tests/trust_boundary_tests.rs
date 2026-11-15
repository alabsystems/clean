// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The server's trust boundary (plan item `devsurface-server-trust-boundary`,
//! `docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`).
//!
//! The threat these tests need: a process on the server's machine that did not
//! start it, and a web page in a browser there, can both open a connection to
//! the port. Neither knows the launch token, and a web page's WebSocket
//! handshake carries the page's `Origin`. Four refusals, each red before the
//! boundary existed:
//!
//! 1. a WebSocket handshake from an origin not on the allow-list (empty by
//!    default) is refused;
//! 2. `saveEnvironment` to a path that does not resolve under the workspace
//!    root writes nothing and answers a named error, and so do
//!    `loadEnvironment` and `importModule`;
//! 3. a TCP connection that has not presented the launch token is refused, and
//!    so is a WebSocket connection;
//! 4. `loadEnvironment` with `replace_unchecked` is refused without the token
//!    in its own params.
//!
//! A fifth, from review of the boundary, red before its fix:
//!
//! 5. `importModule`, which installs what it imports with no kernel check, is
//!    refused without the token in its own params.
//!
//! The controls at the end show the same boundary admitting what it should:
//! a named origin, a connection that presents the token, `replace_unchecked`
//! and `importModule` with the token. What a peer without the token can make
//! the server hold is `trust_boundary_bounds_tests.rs`'s.

use std::fs;
use std::io::{Read, Write};
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::time::Duration;

use clean_kernel::Environment;
use clean_server::handlers::{
    handle_get_environment, handle_load_environment, handle_save_environment, GetEnvironmentResult,
    ServerState,
};
use clean_server::{RequestId, Response, ServerConfig, WebSocketConfig};
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::TcpStream;

/// The code a request answers when its connection, or its own params, lack
/// the server's launch token.
const UNAUTHORIZED: i32 = -32006;
/// The code a file method answers for a path that does not resolve under the
/// workspace root.
const OUTSIDE_WORKSPACE: i32 = -32007;

const UNAUTHORIZED_MISSING: &str = "unauthorized: a connection's first message must be the \
request {\"jsonrpc\":\"2.0\",\"method\":\"authenticate\",\"params\":{\"token\":\"<launch token>\"},\
\"id\":0}; `clean server` prints its launch token on standard error and writes it to its \
token file";
const UNAUTHORIZED_MISMATCH: &str =
    "unauthorized: the token presented is not this server's launch token";
const REPLACE_UNCHECKED_MISSING: &str = "loadEnvironment refuses replace_unchecked without the \
server's launch token: pass it as params.token";
const REPLACE_UNCHECKED_MISMATCH: &str =
    "loadEnvironment refuses replace_unchecked: params.token is not this server's launch token";

const IMPORT_MODULE_MISSING: &str =
    "importModule refuses without the server's launch token: pass it as params.token";
const IMPORT_MODULE_MISMATCH: &str =
    "importModule refuses: params.token is not this server's launch token";

/// A token of the launch token's shape that no server generates by chance.
const WRONG_TOKEN: &str = "0000000000000000000000000000000000000000000000000000000000000000";
/// RFC 6455's sample handshake nonce (section 1.3), the value every WebSocket
/// example carries. It is named apart from the header line so a secret scanner
/// does not read `Sec-WebSocket-Key: <base64>` as a credential.
const SAMPLE_WEBSOCKET_NONCE: &str = "dGhlIHNhbXBsZSBub25jZQ==";

fn canonical(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|e| panic!("canonicalize {}: {e}", path.display()))
}

fn outside_message(
    method: &str,
    what: &str,
    requested: &str,
    resolved: &Path,
    root: &Path,
) -> String {
    format!(
        "{method} refuses {what} `{requested}`: it resolves to `{}`, which is not under the \
         workspace root `{}`",
        resolved.display(),
        root.display()
    )
}

fn params<T: serde::de::DeserializeOwned>(value: Value) -> T {
    serde_json::from_value(value).expect("params deserialize")
}

async fn save(state: &ServerState, path: &str) -> Response {
    handle_save_environment(
        state,
        RequestId::Number(1),
        params(json!({ "path": path, "timeout_ms": 60_000 })),
    )
    .await
}

async fn constants(state: &ServerState) -> usize {
    let response = handle_get_environment(
        state,
        RequestId::Number(9),
        params(json!({ "include_json": false })),
    )
    .await;
    let result = response
        .result
        .unwrap_or_else(|| panic!("getEnvironment failed: {:?}", response.error));
    let result: GetEnvironmentResult = serde_json::from_value(result).expect("result shape");
    result.num_constants
}

fn entries(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .expect("read dir")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    names
}

/// The status line and the rest of an HTTP response to a WebSocket upgrade
/// sent over a raw socket, `origin` as its `Origin` header (none when `None`).
/// The socket blocks, so it is driven off the runtime the server runs on.
async fn websocket_handshake(addr: SocketAddr, origin: Option<&str>) -> (String, String) {
    let origin = origin.map(str::to_string);
    tokio::task::spawn_blocking(move || blocking_handshake(addr, origin.as_deref()))
        .await
        .expect("the handshake thread")
}

fn blocking_handshake(addr: SocketAddr, origin: Option<&str>) -> (String, String) {
    let mut stream = std::net::TcpStream::connect(addr).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_secs(20)))
        .expect("read timeout");
    let origin_header = origin.map_or(String::new(), |o| format!("Origin: {o}\r\n"));
    write!(
        stream,
        "GET / HTTP/1.1\r\nHost: {addr}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\
         Sec-WebSocket-Key: {SAMPLE_WEBSOCKET_NONCE}\r\nSec-WebSocket-Version: 13\r\n\
         {origin_header}\r\n"
    )
    .expect("write handshake");
    // Read the head; for a refusal also the body, until the server closes.
    let mut received = Vec::new();
    let mut buf = [0u8; 4096];
    loop {
        match stream.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => {
                received.extend_from_slice(&buf[..n]);
                let text = String::from_utf8_lossy(&received);
                if text.starts_with("HTTP/1.1 101") && text.contains("\r\n\r\n") {
                    break;
                }
            }
            Err(e) => panic!("reading the handshake answer: {e}"),
        }
    }
    let text = String::from_utf8_lossy(&received).into_owned();
    let (status, rest) = text.split_once("\r\n").unwrap_or((text.as_str(), ""));
    (status.to_string(), rest.to_string())
}

/// Send `line` as a connection's first message; the answer, and whether the
/// server then closed the connection.
async fn first_message(addr: SocketAddr, line: &str) -> (Value, bool) {
    let mut stream = TcpStream::connect(addr).await.expect("connect");
    stream.write_all(line.as_bytes()).await.expect("write");
    stream.write_all(b"\n").await.expect("write");
    let mut reader = BufReader::new(stream);
    let mut answer = String::new();
    tokio::time::timeout(Duration::from_secs(20), reader.read_line(&mut answer))
        .await
        .expect("an answer within 20s")
        .expect("read");
    let value: Value = serde_json::from_str(&answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    let mut next = String::new();
    let closed = matches!(
        tokio::time::timeout(Duration::from_secs(5), reader.read_line(&mut next)).await,
        Ok(Ok(0))
    );
    (value, closed)
}

// ── 1. a hostile WebSocket Origin ────────────────────────────────────────────

#[tokio::test]
async fn test_trust_boundary_hostile_websocket_origin_is_refused() {
    let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().expect("addr"));
    let handle = clean_server::serve_websocket(config)
        .await
        .expect("serve websocket");
    let addr = handle.local_addr();

    // Control: a client that is not a browser sends no Origin, and its
    // handshake is accepted (the token is asked for after it).
    let (status, _) = websocket_handshake(addr, None).await;
    assert_eq!(
        status, "HTTP/1.1 101 Switching Protocols",
        "a handshake without an Origin must be accepted"
    );

    let origin = "https://attacker.example";
    let (status, rest) = websocket_handshake(addr, Some(origin)).await;
    assert_eq!(
        status, "HTTP/1.1 403 Forbidden",
        "a web page at {origin} opened a WebSocket to the server: {status} {rest}"
    );
    assert!(
        rest.ends_with(&format!(
            "clean-server refuses a WebSocket connection from origin `{origin}`: the origin is \
             not on the server's allow-list, which is empty unless `clean server --allow-origin` \
             names it"
        )),
        "the refusal names the origin and how to allow one: {rest:?}"
    );
    handle.shutdown();
}

// ── 2. file methods outside the workspace root ───────────────────────────────

#[tokio::test]
async fn test_trust_boundary_save_environment_outside_the_root_writes_nothing() {
    let root = tempfile::tempdir().expect("root");
    let outside = tempfile::tempdir().expect("outside");
    let state = ServerState::from_root(root.path());
    let canonical_root = canonical(root.path());
    let canonical_outside = canonical(outside.path());

    // Control: a save inside the root is written.
    let inside = root.path().join("inside.env");
    let response = save(&state, &inside.to_string_lossy()).await;
    assert!(
        response.error.is_none(),
        "a save inside the root must succeed: {:?}",
        response.error
    );
    assert!(inside.is_file(), "the save inside the root wrote its file");

    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(outside.path(), root.path().join("out_dir"))
            .expect("directory link");
        std::os::unix::fs::symlink(
            outside.path().join("dangling.env"),
            root.path().join("dangling.env"),
        )
        .expect("file link");
    }
    let outside_name = outside
        .path()
        .file_name()
        .expect("named")
        .to_string_lossy()
        .into_owned();
    let mut cases: Vec<(&str, String, PathBuf)> = vec![
        (
            "an absolute path",
            outside
                .path()
                .join("absolute.env")
                .to_string_lossy()
                .into_owned(),
            canonical_outside.join("absolute.env"),
        ),
        (
            "a relative path that climbs out",
            format!("../{outside_name}/relative.env"),
            canonical_outside.join("relative.env"),
        ),
    ];
    if cfg!(unix) {
        cases.push((
            "a path through a link to a directory outside",
            root.path()
                .join("out_dir")
                .join("linked.env")
                .to_string_lossy()
                .into_owned(),
            canonical_outside.join("linked.env"),
        ));
        cases.push((
            "a link to a file outside that does not exist yet",
            root.path()
                .join("dangling.env")
                .to_string_lossy()
                .into_owned(),
            canonical_outside.join("dangling.env"),
        ));
    }
    for (label, requested, resolved) in &cases {
        let response = save(&state, requested).await;
        let error = response.error.unwrap_or_else(|| {
            panic!(
                "{label}: saveEnvironment wrote outside the workspace root ({}): {:?}",
                entries(outside.path()).join(", "),
                response.result
            )
        });
        assert_eq!(error.code, OUTSIDE_WORKSPACE, "{label}: {}", error.message);
        assert_eq!(
            error.message,
            outside_message(
                "saveEnvironment",
                "path",
                requested,
                resolved,
                &canonical_root
            ),
            "{label}"
        );
    }
    assert_eq!(
        entries(outside.path()),
        Vec::<String>::new(),
        "nothing was written outside the root, not even a temporary file"
    );
}

#[tokio::test]
async fn test_trust_boundary_load_and_import_outside_the_root_are_refused() {
    let root = tempfile::tempdir().expect("root");
    // No `.` in the name: the module-name probe below spells this path as
    // `.`-separated components.
    let outside = tempfile::Builder::new()
        .prefix("tb")
        .rand_bytes(8)
        .tempdir()
        .expect("outside");
    let canonical_root = canonical(root.path());
    let canonical_outside = canonical(outside.path());

    // A saved environment outside the root, written by a server rooted there.
    let source = ServerState::from_root(outside.path()).with_env(Environment::with_prelude());
    let saved = outside.path().join("saved.env");
    let response = save(&source, &saved.to_string_lossy()).await;
    assert!(
        response.error.is_none(),
        "set-up save: {:?}",
        response.error
    );

    let state = ServerState::from_root(root.path());
    let before = constants(&state).await;

    let requested = saved.to_string_lossy().into_owned();
    let response = handle_load_environment(
        &state,
        RequestId::Number(2),
        params(json!({ "path": requested, "timeout_ms": 120_000 })),
    )
    .await;
    let error = response.error.unwrap_or_else(|| {
        panic!(
            "loadEnvironment merged a file outside the workspace root: {:?}",
            response.result
        )
    });
    assert_eq!(error.code, OUTSIDE_WORKSPACE, "{}", error.message);
    assert_eq!(
        error.message,
        outside_message(
            "loadEnvironment",
            "path",
            &requested,
            &canonical_outside.join("saved.env"),
            &canonical_root
        )
    );
    assert_eq!(constants(&state).await, before, "nothing was loaded");

    // importModule asks for the launch token in its own params (what it
    // imports is installed without a kernel check), so it is asked over the
    // wire, with the token, as a client that holds it asks: only the
    // confinement refuses these.
    fs::write(
        outside.path().join("TrustBoundaryProbe.olean"),
        b"not an olean",
    )
    .expect("probe file");
    let handle = serve_rooted(root.path()).await;
    let token = handle.launch_token().as_str().to_string();
    // A search path outside the root.
    let search_path = outside.path().to_string_lossy().into_owned();
    // A module name whose component is an absolute path read the file it
    // named, wherever it was.
    let module = format!(
        "Probe.{}",
        canonical_outside.join("TrustBoundaryProbe").display()
    );
    let answers = exchange(
        handle.local_addr(),
        &[
            authenticate_request(&token),
            get_environment_request(1),
            request(
                "importModule",
                json!({
                    "module": "TrustBoundaryProbe",
                    "search_paths": [search_path],
                    "token": token,
                    "timeout_ms": 60_000,
                }),
                3,
            ),
            request(
                "importModule",
                json!({ "module": module, "token": token, "timeout_ms": 60_000 }),
                4,
            ),
            get_environment_request(5),
        ],
    )
    .await;
    assert_authenticated(&answers[0]);
    let before = wire_constants(&answers[1]);
    assert_eq!(
        error_of(&answers[2]),
        Some((
            i64::from(OUTSIDE_WORKSPACE),
            outside_message(
                "importModule",
                "search path",
                &search_path,
                &canonical_outside,
                &canonical_root
            )
        )),
        "importModule must refuse a search path outside the root before it reads from it: {}",
        answers[2]
    );
    assert_eq!(
        error_of(&answers[3]),
        Some((
            -32602,
            format!(
                "importModule refuses module `{module}`: a module name's components cannot \
                 contain a path separator"
            )
        )),
        "a module name must not name a file by its path: {}",
        answers[3]
    );
    assert_eq!(wire_constants(&answers[4]), before, "nothing was imported");
    handle.shutdown();
}

// ── 3. a TCP connection without the launch token ─────────────────────────────

#[tokio::test]
async fn test_trust_boundary_tcp_connection_without_the_token_is_refused() {
    // The workspace root is the scratch directory, so the root admits the save
    // below: the token is the only thing between the request and the write.
    let scratch = tempfile::tempdir().expect("scratch");
    let config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(scratch.path().to_path_buf());
    let handle = clean_server::serve(config).await.expect("serve");
    let addr = handle.local_addr();

    // A save sent as a connection's first message writes nothing.
    let target = scratch.path().join("over_the_wire.env");
    let request = json!({
        "jsonrpc": "2.0",
        "method": "saveEnvironment",
        "params": { "path": target.to_string_lossy() },
        "id": 5,
    })
    .to_string();
    let (answer, closed) = first_message(addr, &request).await;
    assert!(
        !target.exists(),
        "a connection that presented no token saved {}: {answer}",
        target.display()
    );
    assert_eq!(
        (answer["error"]["code"].as_i64(), &answer["id"]),
        (Some(i64::from(UNAUTHORIZED)), &json!(5)),
        "{answer}"
    );
    assert_eq!(answer["error"]["message"], UNAUTHORIZED_MISSING, "{answer}");
    assert!(closed, "the server closes a connection it refused");

    // A read-only request is refused the same way.
    let (answer, closed) =
        first_message(addr, r#"{"jsonrpc":"2.0","method":"serverInfo","id":7}"#).await;
    assert_eq!(
        (answer["error"]["code"].as_i64(), &answer["id"]),
        (Some(i64::from(UNAUTHORIZED)), &json!(7)),
        "{answer}"
    );
    assert_eq!(answer["error"]["message"], UNAUTHORIZED_MISSING, "{answer}");
    assert!(closed, "the server closes a connection it refused");

    // A wrong token is refused, and named as wrong.
    let request = json!({
        "jsonrpc": "2.0",
        "method": "authenticate",
        "params": { "token": WRONG_TOKEN },
        "id": 0,
    })
    .to_string();
    let (answer, closed) = first_message(addr, &request).await;
    assert_eq!(
        (answer["error"]["code"].as_i64(), &answer["id"]),
        (Some(i64::from(UNAUTHORIZED)), &json!(0)),
        "{answer}"
    );
    assert_eq!(
        answer["error"]["message"], UNAUTHORIZED_MISMATCH,
        "{answer}"
    );
    assert!(closed, "the server closes a connection it refused");

    // An HTTP request (a web page's POST to the port) is refused at its first
    // line, before the JSON body it carries is read as a request.
    let (answer, closed) = first_message(addr, "POST / HTTP/1.1").await;
    assert_eq!(
        answer["error"]["code"].as_i64(),
        Some(i64::from(UNAUTHORIZED)),
        "{answer}"
    );
    assert!(closed, "the server closes a connection it refused");
    handle.shutdown();
}

#[tokio::test]
async fn test_trust_boundary_websocket_connection_without_the_token_is_refused() {
    use futures_util::{SinkExt, StreamExt};
    use tokio_tungstenite::tungstenite::Message;

    // As on TCP, the root admits the save: only the token refuses it.
    let scratch = tempfile::tempdir().expect("scratch");
    let mut config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().expect("addr"));
    config.workspace_root = Some(scratch.path().to_path_buf());
    let handle = clean_server::serve_websocket(config)
        .await
        .expect("serve websocket");
    let target = scratch.path().join("over_the_websocket.env");

    let (mut ws, _) = tokio_tungstenite::connect_async(format!("ws://{}", handle.local_addr()))
        .await
        .expect("a client that is not a browser completes the handshake");
    let request = json!({
        "jsonrpc": "2.0",
        "method": "saveEnvironment",
        "params": { "path": target.to_string_lossy() },
        "id": 3,
    })
    .to_string();
    ws.send(Message::Text(request.into())).await.expect("send");
    let answer = tokio::time::timeout(Duration::from_secs(20), ws.next())
        .await
        .expect("an answer within 20s");
    let answer = match answer {
        Some(Ok(Message::Text(text))) => text.to_string(),
        other => panic!("the server answered no text: {other:?}"),
    };
    assert!(
        !target.exists(),
        "a WebSocket connection that presented no token saved {}: {answer}",
        target.display()
    );
    let answer: Value = serde_json::from_str(&answer).expect("JSON");
    assert_eq!(
        (answer["error"]["code"].as_i64(), &answer["id"]),
        (Some(i64::from(UNAUTHORIZED)), &json!(3)),
        "{answer}"
    );
    assert_eq!(answer["error"]["message"], UNAUTHORIZED_MISSING, "{answer}");
    let after = tokio::time::timeout(Duration::from_secs(5), ws.next())
        .await
        .expect("the server closes the connection within 5s");
    assert!(
        !matches!(after, Some(Ok(Message::Text(_)))),
        "the server kept serving a connection it refused: {after:?}"
    );
    handle.shutdown();
}

// ── 4. replace_unchecked without the launch token ────────────────────────────

#[tokio::test]
async fn test_trust_boundary_replace_unchecked_without_the_token_is_refused() {
    let root = tempfile::tempdir().expect("root");
    let source = ServerState::from_root(root.path()).with_env(Environment::with_prelude());
    let saved = root.path().join("prelude.env");
    let response = save(&source, &saved.to_string_lossy()).await;
    assert!(
        response.error.is_none(),
        "set-up save: {:?}",
        response.error
    );
    let prelude_constants = constants(&source).await;

    let state = ServerState::from_root(root.path());
    let before = constants(&state).await;
    assert_ne!(
        before, prelude_constants,
        "the install below would be visible in the constant count"
    );

    let path = saved.to_string_lossy().into_owned();
    let cases = [
        (
            "no token",
            json!({ "path": path, "replace": true, "replace_unchecked": true }),
            REPLACE_UNCHECKED_MISSING,
        ),
        (
            "a wrong token",
            json!({
                "path": path,
                "replace": true,
                "replace_unchecked": true,
                "token": WRONG_TOKEN,
            }),
            REPLACE_UNCHECKED_MISMATCH,
        ),
    ];
    for (label, request, message) in cases {
        let response = handle_load_environment(&state, RequestId::Number(2), params(request)).await;
        let error = response.error.unwrap_or_else(|| {
            panic!(
                "{label}: loadEnvironment installed an unchecked environment without the \
                 launch token: {:?}",
                response.result
            )
        });
        assert_eq!(
            (error.code, error.message.as_str()),
            (UNAUTHORIZED, message),
            "{label}"
        );
        assert_eq!(
            constants(&state).await,
            before,
            "{label}: the environment was not replaced"
        );
    }
}

// ── 5. importModule without the launch token ─────────────────────────────────

/// A TCP server whose workspace root is `root`.
async fn serve_rooted(root: &Path) -> clean_server::ServerHandle {
    let config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(root.to_path_buf());
    clean_server::serve(config).await.expect("serve")
}

/// A request line.
fn request(method: &str, params: Value, id: i64) -> String {
    json!({ "jsonrpc": "2.0", "method": method, "params": params, "id": id }).to_string()
}

fn get_environment_request(id: i64) -> String {
    request("getEnvironment", json!({ "include_json": false }), id)
}

/// The constant count a `getEnvironment` answer reports.
fn wire_constants(answer: &str) -> u64 {
    let value: Value = serde_json::from_str(answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    value["result"]["num_constants"]
        .as_u64()
        .unwrap_or_else(|| panic!("getEnvironment failed: {answer}"))
}

/// The code and message of an error answer; `None` for anything else.
fn error_of(answer: &str) -> Option<(i64, String)> {
    let value: Value = serde_json::from_str(answer).ok()?;
    let error = value.get("error")?;
    Some((
        error["code"].as_i64()?,
        error["message"].as_str()?.to_string(),
    ))
}

/// A module `ServerFixture` that declares one axiom, exported as an `.olean`
/// into `dir`.
fn write_fixture_module(dir: &Path) {
    use clean_kernel::{Declaration, Expr, Name};
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ServerFixture.imported"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("an axiom whose type is Prop is admitted");
    let bytes = clean_olean::OleanExporter::export_with_env(
        &env,
        &[],
        &[],
        "c0de000000000000000000000000000000000002",
    )
    .expect("export the fixture module");
    fs::write(dir.join("ServerFixture.olean"), bytes).expect("write the fixture module");
}

#[tokio::test]
async fn test_trust_boundary_import_module_without_the_token_is_refused() {
    let root = tempfile::tempdir().expect("root");
    fs::create_dir(root.path().join("oleans")).expect("oleans");
    write_fixture_module(&root.path().join("oleans"));
    let handle = serve_rooted(root.path()).await;
    let token = handle.launch_token().as_str().to_string();
    let import = |token: Option<&str>, id: i64| {
        let mut params = json!({
            "module": "ServerFixture",
            "search_paths": ["oleans"],
            "timeout_ms": 60_000,
        });
        if let Some(token) = token {
            params["token"] = json!(token);
        }
        request("importModule", params, id)
    };
    let answers = exchange(
        handle.local_addr(),
        &[
            authenticate_request(&token),
            get_environment_request(1),
            import(None, 2),
            import(Some(WRONG_TOKEN), 3),
            get_environment_request(4),
            // Control: the token in params admits the import.
            import(Some(&token), 5),
            get_environment_request(6),
        ],
    )
    .await;
    assert_authenticated(&answers[0]);
    let before = wire_constants(&answers[1]);
    for (label, answer, message) in [
        ("no token", &answers[2], IMPORT_MODULE_MISSING),
        ("a wrong token", &answers[3], IMPORT_MODULE_MISMATCH),
    ] {
        assert_eq!(
            error_of(answer),
            Some((i64::from(UNAUTHORIZED), message.to_string())),
            "{label}: importModule installed declarations no kernel checked without the launch \
             token: {answer}"
        );
    }
    assert_eq!(
        wire_constants(&answers[4]),
        before,
        "nothing was imported without the token"
    );
    let imported: Value = serde_json::from_str(&answers[5]).expect("JSON");
    assert_eq!(
        (
            &imported["result"]["success"],
            &imported["result"]["modules_loaded"],
            &imported["result"]["constants_added"],
        ),
        (&json!(true), &json!(["ServerFixture"]), &json!(1)),
        "the token in params admits importModule: {imported}"
    );
    assert_eq!(
        wire_constants(&answers[6]),
        before + 1,
        "the control imported its one axiom"
    );
    handle.shutdown();
}

// ── Controls: what the boundary admits ───────────────────────────────────────
//
// A boundary that refused everything would pass every test above. These need
// the boundary's own API (the launch token, the allow-list), so they were
// written with it.

fn authenticate_request(token: &str) -> String {
    json!({
        "jsonrpc": "2.0",
        "method": "authenticate",
        "params": { "token": token },
        "id": 0,
    })
    .to_string()
}

/// The answer to `authenticate` with the server's launch token.
fn assert_authenticated(answer: &str) {
    let value: Value = serde_json::from_str(answer)
        .unwrap_or_else(|e| panic!("answer is not JSON ({e}): {answer:?}"));
    assert_eq!(
        value,
        json!({ "jsonrpc": "2.0", "result": { "authenticated": true }, "id": 0 }),
        "the launch token admits the connection"
    );
}

#[tokio::test]
async fn test_trust_boundary_control_an_allowed_origin_is_admitted() {
    let allowed = "https://ide.example";
    let mut config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().expect("addr"));
    config.allowed_origins = vec![allowed.to_string()];
    let handle = clean_server::serve_websocket(config)
        .await
        .expect("serve websocket");
    let addr = handle.local_addr();
    let (status, _) = websocket_handshake(addr, Some(allowed)).await;
    assert_eq!(
        status, "HTTP/1.1 101 Switching Protocols",
        "an origin the operator named is admitted to the token check"
    );
    // The list admits what it names, not what resembles it.
    let (status, _) = websocket_handshake(addr, Some("https://ide.example.attacker.example")).await;
    assert_eq!(status, "HTTP/1.1 403 Forbidden");
    handle.shutdown();
}

#[tokio::test]
async fn test_trust_boundary_control_the_launch_token_admits_a_tcp_connection() {
    let root = tempfile::tempdir().expect("root");
    let config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(root.path().to_path_buf());
    let handle = clean_server::serve(config).await.expect("serve");
    let token = handle.launch_token().as_str().to_string();
    assert_eq!(token.len(), 64, "a launch token is 64 hex digits");

    let save = json!({
        "jsonrpc": "2.0",
        "method": "saveEnvironment",
        "params": { "path": "admitted.env" },
        "id": 8,
    })
    .to_string();
    let answers = exchange(handle.local_addr(), &[authenticate_request(&token), save]).await;
    assert_authenticated(&answers[0]);
    let saved: Value = serde_json::from_str(&answers[1]).expect("JSON");
    assert_eq!(saved["result"]["success"], json!(true), "{saved}");
    assert!(
        root.path().join("admitted.env").is_file(),
        "an admitted connection's relative save lands under the root"
    );
    handle.shutdown();
}

/// Send `requests` in order on one TCP connection; the line answering each.
async fn exchange(addr: SocketAddr, requests: &[String]) -> Vec<String> {
    let stream = TcpStream::connect(addr).await.expect("connect");
    let (read, mut write) = stream.into_split();
    let mut lines = BufReader::new(read).lines();
    let mut answers = Vec::new();
    for request in requests {
        write
            .write_all(format!("{request}\n").as_bytes())
            .await
            .expect("write");
        answers.push(
            tokio::time::timeout(Duration::from_secs(120), lines.next_line())
                .await
                .expect("an answer within 120s")
                .expect("read")
                .expect("an answer line before the server closed"),
        );
    }
    answers
}

#[tokio::test]
async fn test_trust_boundary_control_the_launch_token_admits_a_websocket_connection() {
    use futures_util::{SinkExt, StreamExt};
    use tokio_tungstenite::tungstenite::Message;

    let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().expect("addr"));
    let handle = clean_server::serve_websocket(config)
        .await
        .expect("serve websocket");
    let (mut ws, _) = tokio_tungstenite::connect_async(format!("ws://{}", handle.local_addr()))
        .await
        .expect("handshake");
    let mut answers = Vec::new();
    for request in [
        authenticate_request(handle.launch_token().as_str()),
        r#"{"jsonrpc":"2.0","method":"serverInfo","id":1}"#.to_string(),
    ] {
        ws.send(Message::Text(request.into())).await.expect("send");
        match tokio::time::timeout(Duration::from_secs(20), ws.next())
            .await
            .expect("an answer within 20s")
        {
            Some(Ok(Message::Text(text))) => answers.push(text.to_string()),
            other => panic!("the server answered no text: {other:?}"),
        }
    }
    assert_authenticated(&answers[0]);
    let info: Value = serde_json::from_str(&answers[1]).expect("JSON");
    assert_eq!(
        info["result"]["destructive_methods"],
        json!(["saveEnvironment", "loadEnvironment", "importModule"]),
        "{info}"
    );
    handle.shutdown();
}

#[tokio::test]
async fn test_trust_boundary_control_replace_unchecked_with_the_token_installs() {
    let root = tempfile::tempdir().expect("root");
    let source = ServerState::from_root(root.path()).with_env(Environment::with_prelude());
    let saved = root.path().join("prelude.env");
    let response = save(&source, &saved.to_string_lossy()).await;
    assert!(
        response.error.is_none(),
        "set-up save: {:?}",
        response.error
    );
    let prelude_constants = constants(&source).await;

    let config = ServerConfig::default()
        .with_addr("127.0.0.1:0".parse().expect("addr"))
        .with_workspace_root(root.path().to_path_buf());
    let handle = clean_server::serve(config).await.expect("serve");
    let token = handle.launch_token().as_str().to_string();
    let load = json!({
        "jsonrpc": "2.0",
        "method": "loadEnvironment",
        "params": {
            "path": "prelude.env",
            "replace": true,
            "replace_unchecked": true,
            "token": token,
            "timeout_ms": 120_000,
        },
        "id": 2,
    })
    .to_string();
    let answers = exchange(handle.local_addr(), &[authenticate_request(&token), load]).await;
    assert_authenticated(&answers[0]);
    let loaded: Value = serde_json::from_str(&answers[1]).expect("JSON");
    assert_eq!(
        loaded["result"]["num_constants"].as_u64(),
        Some(prelude_constants as u64),
        "the token in params admits replace_unchecked: {loaded}"
    );
    handle.shutdown();
}
