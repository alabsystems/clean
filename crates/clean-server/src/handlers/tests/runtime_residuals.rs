// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What R36 (`docs/DECISIONS.md`) left on the runtime, each test pinned by the
//! defect it names (R87 in `docs/DECISIONS.md`, 2026-10-17):
//!
//! * `verifyFile`, `fillSorries` and `composeProof` parsed the file they were
//!   sent on the runtime, with no deadline (and `composeProof` the proof it
//!   reports a failed set-up of the environment with).
//! * A proof state the cache let go while a request held it, and a session
//!   closed while an `addDecl` held it, were freed where that request let them
//!   go: on the runtime.
//!
//! (`runtime_frees.rs` pins where sessions are copied, and `save_file.rs` the
//! saves; `tests/corpus_scans.rs`, a process of its own with a Mathverse
//! corpus installed, pins the lifecycle refusal's scan.)
//!
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use super::concurrent_writers::{answered, prelude_state_with, spawned};
use super::free_gate::gated_source;
use crate::dispatch::dispatch_request;
use crate::handlers::work::WorkPool;
use crate::handlers::*;
use crate::rpc::Response;
use crate::session_env::SessionId;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use serde_json::{json, Value};
use std::sync::{Arc, Weak};
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
const TIMEOUT: i32 = -32004;

/// Send `method` through the dispatcher; it must answer within the hang
/// detector.
async fn sent(state: &ServerState, method: &str, params: Value) -> Response {
    tokio::time::timeout(
        HANG,
        dispatch_request(method, Some(params), RequestId::Number(1), state, None),
    )
    .await
    .unwrap_or_else(|_| panic!("{method} was not answered within the hang detector"))
}

/// Send `method` and return its result; it must succeed.
async fn result_of(state: &ServerState, method: &str, params: Value) -> Value {
    let response = sent(state, method, params).await;
    assert!(response.error.is_none(), "{method}: {:?}", response.error);
    response.result.expect("a result")
}

async fn open_session(state: &ServerState) -> SessionId {
    state.create_session().await.expect("open a session")
}

/// A file each method parses to "no theorem": the base answered that from the
/// runtime, without a work slot.
const NO_THEOREM: &str = "-- nothing to prove here\ndef x := 1\n";

/// `verifyFile`, `fillSorries` and `composeProof` parsed their file on the
/// runtime, with no deadline, before any of their work took a slot: a file
/// with no theorem was answered from the runtime. The parse is pool work under
/// the request's deadline now. Here the pool's only slot is held: each waits
/// for it inside its timeout and answers the timeout error at it (the base
/// answered each at once, "no theorem found" or "no proof provided"). With the
/// slot free, each answers again.
#[tokio::test]
async fn file_methods_parse_on_the_pool_inside_their_timeout() {
    let state = prelude_state_with(Some(WorkPool::new(1)));
    let requests = [
        ("verifyFile", json!({ "content": NO_THEOREM })),
        ("fillSorries", json!({ "content": NO_THEOREM })),
        (
            "composeProof",
            json!({ "content": NO_THEOREM, "replacements": [] }),
        ),
    ];

    let slot = state.work.slot().await.expect("the pool's only slot");
    let mut parsed_without_a_slot = Vec::new();
    for (method, params) in &requests {
        let mut params = params.clone();
        params["timeout_ms"] = json!(300);
        let response = sent(&state, method, params).await;
        if response.error.as_ref().map(|e| e.code) != Some(TIMEOUT) {
            parsed_without_a_slot.push((*method, response.result));
        }
    }
    drop(slot);
    assert!(
        parsed_without_a_slot.is_empty(),
        "answered without a work slot: {parsed_without_a_slot:?}"
    );

    for (method, params) in requests {
        let answer = result_of(&state, method, params).await;
        assert_eq!(answer["verified"], json!(false), "{method}: {answer}");
    }
}

/// `composeProof` answers a failed set-up of the environment with the holes
/// left in the proof it was sent, which parses the proof: it did so on the
/// runtime after its file's parse had moved to the pool. Here the shared
/// environment already declares `Prime`, which the set-up adds, so the set-up
/// fails; the parse asserts in debug builds that it runs on no runtime thread
/// (`parse_lean.rs`), so the answer built on this test's runtime panicked.
#[tokio::test]
async fn compose_proof_answers_a_failed_set_up_from_the_pool() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Prime"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("declare `Prime` before the set-up does");
    let state = ServerState::new().with_env(env);
    let answer = result_of(
        &state,
        "composeProof",
        json!({
            "content": "theorem t : True := by\n  sorry\n",
            "replacements": [],
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert!(
        answer["error"]["message"]
            .as_str()
            .is_some_and(|message| message.starts_with("failed to initialize")),
        "the set-up failed: this test's premise; {answer}"
    );
    assert_eq!(
        answer["remaining_sorries"].as_array().map(Vec::len),
        Some(1),
        "{answer}"
    );
}

/// The parse read no deadline: a file of many `theorem` lines (each of which
/// searches the rest of the file) ran to its end past the request's deadline.
/// The hole scan polls the deadline before each line, and the declaration scan
/// reads the clock before each `theorem` or `lemma` line; past the deadline
/// each stops. Fails when either read is removed: that scan then runs to its
/// end and finds the hole, or the theorem.
#[test]
fn the_file_parse_stops_at_its_deadline() {
    let content = "theorem t : True := by\n  sorry\n";
    let found = |deadline: Option<Instant>| {
        let mut found = None;
        let _ = clean_kernel::tc::run_until(deadline, || {
            let holes = explicit_holes(content);
            let declaration = first_declaration(content, &mut []);
            found = Some((holes, declaration));
        });
        found.expect("the scans ran")
    };

    let (holes, declaration) = found(None);
    assert_eq!(
        (
            holes.map(|holes| holes.len()),
            declaration.map(|theorem| theorem.map(|theorem| theorem.name))
        ),
        (Ok(1), Ok(Some("t".to_string()))),
        "a theorem and its hole, without a deadline: this test's premise"
    );
    let (holes, declaration) = found(Some(Instant::now()));
    assert!(
        holes.is_err() && declaration.is_err(),
        "past their deadline the scans found (holes, declaration) = ({holes:?}, {declaration:?})"
    );
}

/// The hole scan, as it was before it stripped each line once and searched
/// each token once: re-stripping the line for every candidate, and searching
/// every token to the line's end for every candidate (quadratic in a line's
/// candidates). The oracle for the rewrite.
fn holes_as_before(line: &str) -> Vec<usize> {
    const TOKENS: &[&str] = &["sorry", "admit"];
    let comment_free = match line.find("--") {
        Some(pos) => &line[..pos],
        None => line,
    };
    let mut columns = Vec::new();
    let mut search_start = 0usize;
    while search_start < comment_free.len() {
        let next_match = TOKENS
            .iter()
            .filter_map(|&token| {
                comment_free[search_start..]
                    .find(token)
                    .map(|offset| (search_start + offset, token))
            })
            .min_by_key(|(column, _)| *column);
        let Some((column, token)) = next_match else {
            break;
        };
        if explicit_hole_token_at(line, column).is_some() {
            columns.push(column);
        }
        search_start = column + token.len();
    }
    columns
}

/// The rewritten hole scan finds exactly the holes the old one found, on
/// every line built from the pieces that decide a hole: the two tokens,
/// identifier characters on either side, line and block comments, string
/// literals, quoted identifiers and multibyte characters.
#[test]
fn the_hole_scan_finds_what_it_found_before() {
    const PIECES: &[&str] = &[
        "sorry", "admit", "x", "_", "'", " ", "--", "/-", "-/", "\"", "\u{ab}", "\u{bb}",
        "\u{3bb}", ";", "(", ")", "sorr", "dmit", "\\",
    ];
    // Every line of up to four pieces: 19^4 + 19^3 + 19^2 + 19 of them.
    let mut lines = vec![String::new()];
    let mut frontier = vec![String::new()];
    for _ in 0..4 {
        let mut next = Vec::new();
        for prefix in &frontier {
            for piece in PIECES {
                next.push(format!("{prefix}{piece}"));
            }
        }
        lines.extend(next.iter().cloned());
        frontier = next;
    }
    let mut differ = Vec::new();
    for line in &lines {
        let now: Vec<usize> = explicit_holes(line)
            .expect("no deadline")
            .into_iter()
            .map(|hole| hole.col - 1)
            .collect();
        // `explicit_holes` reads lines (`str::lines`): one line here, unless
        // it holds none.
        let before = if line.is_empty() {
            Vec::new()
        } else {
            holes_as_before(line)
        };
        if now != before {
            differ.push((line.clone(), before, now));
        }
    }
    assert!(
        differ.is_empty(),
        "{} lines' holes differ (line, before, now), first: {:?}",
        differ.len(),
        differ.first()
    );
}

/// Wait until `holders` is down to `count` holders: a free off the runtime
/// runs on its own.
async fn until_held_by(holders: &Weak<dyn clean_kernel::env::ConstantSource>, count: usize) {
    let give_up = Instant::now() + HANG;
    while holders.strong_count() != count {
        assert!(
            Instant::now() < give_up,
            "the source kept {} holders, never {count}",
            holders.strong_count()
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

/// A request that read a cached proof state held a share of it, and when the
/// cache let the state go meanwhile (closed, expired, evicted), the request's
/// share was the last: it freed the state, a whole environment, where the
/// request let it go, on the runtime. Here the state's environment holds the
/// last shares of a gated source (`free_gate.rs`), and a `getProofState` whose
/// `llm` snapshot waits for the pool's only slot (the test holds it) reads the
/// state, then the state is closed, then the request answers its timeout
/// error. On this one-thread runtime a free on the runtime's thread can never
/// be released, and the base waited for it to the hang detector.
#[tokio::test]
async fn a_proof_state_closed_while_a_request_holds_it_is_freed_off_the_runtime() {
    let (source, gate) = gated_source();
    let holders = Arc::downgrade(&source);
    let mut env = Environment::with_prelude();
    env.set_constant_source(source);
    let state = Arc::new({
        let mut state = ServerState::new().with_env(env);
        state.work = WorkPool::new(1);
        state
    });
    let opened = result_of(
        &state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    // The shared environment lets its share go (off the runtime, on its own):
    // the cached state's are then the last.
    let with_shared = holders.strong_count();
    state.env.replace(Environment::with_prelude()).await;
    until_held_by(&holders, with_shared - 1).await;

    let slot = state.work.slot().await.expect("the pool's only slot");
    let s = Arc::clone(&state);
    let id = opened["state_id"].clone();
    let reading = spawned(async move {
        sent(
            &s,
            "getProofState",
            json!({ "state_id": id, "format": "llm", "timeout_ms": 300 }),
        )
        .await
    });
    // The request runs until it waits for the slot, holding the state.
    tokio::task::yield_now().await;
    let closed = result_of(
        &state,
        "proofState.close",
        json!({ "state_id": opened["state_id"] }),
    )
    .await;
    assert_eq!(closed["closed"], json!(true), "{closed}");
    let runtime = std::thread::current().id();
    let (response, _) = answered("the getProofState", reading).await;
    assert_eq!(
        response.error.map(|e| e.code),
        Some(TIMEOUT),
        "the request read the state before it was closed, and waited for the slot: this \
         test's premise"
    );
    gate.freeing().await;
    drop(slot);
    let check = result_of(
        &state,
        "check",
        json!({ "code": "Type", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    assert_eq!(check["valid"], json!(true), "{check}");
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the state was freed on the runtime's thread: the test could not release it"
    );
    assert_ne!(freed.on, runtime);
}

/// An `addDecl` holds a share of its session from its look-up to its end, and
/// a session closed meanwhile was freed where that `addDecl` let its share go,
/// on the runtime (`drop_session` freed only the map's share off it). Here the
/// session holds the last shares of a gated source, an `addDecl` waits for
/// the pool's only slot (the test holds it) holding its session, the session
/// is closed, and the `addDecl` answers its timeout error. On this one-thread
/// runtime the base waited for the free to the hang detector.
#[tokio::test]
async fn a_session_closed_while_an_add_decl_holds_it_is_freed_off_the_runtime() {
    let (source, gate) = gated_source();
    let holders = Arc::downgrade(&source);
    let mut env = Environment::with_prelude();
    env.set_constant_source(source);
    let state = Arc::new({
        let mut state = ServerState::new().with_env(env);
        state.work = WorkPool::new(1);
        state
    });
    let session = open_session(&state).await;
    let with_shared = holders.strong_count();
    state.env.replace(Environment::with_prelude()).await;
    until_held_by(&holders, with_shared - 1).await;

    let slot = state.work.slot().await.expect("the pool's only slot");
    let s = Arc::clone(&state);
    let params: AddDeclParams = serde_json::from_value(json!({
        "session_id": session.to_string(),
        "decl": Declaration::Axiom {
            name: Name::from_string("residual_axiom"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        "require_foundational": false,
        "timeout_ms": 300,
    }))
    .expect("addDecl params");
    let adding = spawned(async move { handle_add_decl(&s, RequestId::Number(1), params).await });
    // The addDecl runs until it waits for the slot, holding its session.
    tokio::task::yield_now().await;
    assert!(state.drop_session(&session).await, "the session was open");
    let runtime = std::thread::current().id();
    let (response, _) = answered("the addDecl", adding).await;
    assert_eq!(
        response.error.map(|e| e.code),
        Some(TIMEOUT),
        "the addDecl held its session before it was closed, and waited for the slot: this \
         test's premise"
    );
    gate.freeing().await;
    drop(slot);
    let check = result_of(
        &state,
        "check",
        json!({ "code": "Type", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    assert_eq!(check["valid"], json!(true), "{check}");
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the session was freed on the runtime's thread: the test could not release it"
    );
    assert_ne!(freed.on, runtime);
}
