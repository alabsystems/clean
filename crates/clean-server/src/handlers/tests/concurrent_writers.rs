// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The writers' concurrency (R34 in `docs/DECISIONS.md`), each test pinned by
//! a defect R32 left open:
//!
//! * `addDecl` held the whole session map's write lock across its check, so
//!   `addDecl`s to different sessions waited for each other, and one queued for
//!   the lock held a work slot while it waited.
//! * `loadEnvironment`'s merge held the environment's write lock while it
//!   re-checked every loaded declaration: nothing could read the environment
//!   until it had finished.
//! * `importModule` loaded with no timeout, and installed a copy of the
//!   environment made before its load, overwriting a change that landed
//!   meanwhile.
//!
//! The tests drive real requests and use only what the server had before the
//! fix as well, so each runs against the old code too (where it fails). Every
//! wait for something that must happen is a one-minute hang detector, never a
//! latency budget.

use crate::handlers::work::WorkPool;
use crate::handlers::*;
use crate::rpc::Response;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use serde_json::json;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
#[cfg(unix)]
const TIMEOUT: i32 = -32004;

/// A state over the kernel prelude, its file methods confined to the system's
/// temporary directory (`super::temp_rooted_state`).
pub(super) fn prelude_state_with(work: Option<WorkPool>) -> Arc<ServerState> {
    let env = Environment::try_with_prelude().expect("try_with_prelude should succeed");
    let mut state = super::temp_rooted_state().with_env(env);
    if let Some(work) = work {
        state.work = work;
    }
    Arc::new(state)
}

/// A state over `Environment::new()`, which has no logical prelude, its file
/// methods confined to the system's temporary directory.
pub(super) fn bare_state_with(work: WorkPool) -> Arc<ServerState> {
    let mut state = super::temp_rooted_state();
    state.work = work;
    Arc::new(state)
}

/// `code` elaborated against the state's environment, before any request runs.
fn elaborated(state: &ServerState, code: &str) -> Expr {
    let env = state
        .env
        .try_read()
        .expect("no request holds the environment yet");
    let surface = clean_parser::parse_expr_with_tactics_exact(code, &state.tactic_patterns)
        .unwrap_or_else(|e| panic!("{code} parses: {e}"));
    clean_elab::elaborate(&env, &surface).unwrap_or_else(|e| panic!("{code} elaborates: {e}"))
}

/// `Nat.rec` unfolded 60,000 times with the step `n + c + ih`: a term the
/// kernel can only compute (about three seconds in a debug build), and the
/// number it computes. Distinct for each `c`, so no check shares another's.
fn big(c: u64) -> (String, u64) {
    let n: u64 = 60_000;
    (
        format!("@Nat.rec (fun _ => Nat) 0 (fun n ih => n + {c} + ih) {n}"),
        n * (n - 1) / 2 + c * n,
    )
}

/// `slow_c : big(c) = its value`, proved by `Eq.refl`: stating it computes
/// nothing, and the kernel accepts the proof only by computing.
pub(super) fn slow_theorem(state: &ServerState, c: u64) -> Declaration {
    let (term, value) = big(c);
    Declaration::Theorem {
        name: Name::from_string(&format!("slow_{c}")),
        level_params: vec![],
        type_: elaborated(state, &format!("{term} = {value}")),
        value: elaborated(state, &format!("@Eq.refl Nat ({term})")),
    }
}

fn quick_axiom(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    }
}

/// An `addDecl` with no heartbeat limit and the hang detector for its
/// timeout: it must be answered with a verdict.
fn add_decl(session: impl ToString, decl: &Declaration) -> AddDeclParams {
    serde_json::from_value(json!({
        "session_id": session.to_string(),
        "decl": decl,
        "require_foundational": false,
        "heartbeat_limit": 0,
        "timeout_ms": HANG.as_millis() as u64,
    }))
    .expect("addDecl params")
}

fn accepted(what: &str, response: &Response) {
    assert!(response.error.is_none(), "{what}: {:?}", response.error);
    let result = response.result.as_ref().expect("a result");
    assert_eq!(result["accepted"], json!(true), "{what}: {result}");
}

pub(super) async fn until(what: &str, limit: Duration, mut cond: impl FnMut() -> bool) {
    let give_up = Instant::now() + limit;
    while !cond() {
        assert!(Instant::now() < give_up, "{what} never happened");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

/// Spawn a request; its task answers with the response and when it came.
pub(super) fn spawned<F>(request: F) -> tokio::task::JoinHandle<(Response, Instant)>
where
    F: std::future::Future<Output = Response> + Send + 'static,
{
    tokio::spawn(async move {
        let response = request.await;
        (response, Instant::now())
    })
}

pub(super) async fn answered(
    what: &str,
    request: tokio::task::JoinHandle<(Response, Instant)>,
) -> (Response, Instant) {
    tokio::time::timeout(HANG, request)
        .await
        .unwrap_or_else(|_| panic!("{what} was not answered within the hang detector"))
        .unwrap_or_else(|e| panic!("{what}'s task failed: {e}"))
}

#[cfg(unix)]
pub(super) async fn wait_until_idle(state: &ServerState) {
    until("the abandoned work's end", HANG, || {
        state.work.in_use() == 0
    })
    .await;
}

/// `addDecl` held the session map's write lock across its check, so an
/// `addDecl` to another session waited for the whole check, and with a short
/// `timeout_ms` answered the timeout error. The map is held only to look a
/// session up now: the quick one is answered while the slow one checks.
#[tokio::test]
async fn add_decls_to_different_sessions_do_not_wait_for_each_other() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let (busy, other) = (
        state.create_session().await.expect("open a session"),
        state.create_session().await.expect("open a session"),
    );
    let decl = slow_theorem(&state, 1);
    let s = Arc::clone(&state);
    let slow =
        spawned(
            async move { handle_add_decl(&s, RequestId::Number(1), add_decl(busy, &decl)).await },
        );
    until("the slow addDecl takes its work slot", HANG, || {
        state.work.in_use() >= 1
    })
    .await;

    let quick = handle_add_decl(
        &state,
        RequestId::Number(2),
        add_decl(other, &quick_axiom("quick")),
    )
    .await;
    let quick_answered = Instant::now();
    let (slow, slow_answered) = answered("the slow addDecl", slow).await;
    accepted("the quick addDecl", &quick);
    accepted("the slow addDecl", &slow);
    assert!(
        quick_answered < slow_answered,
        "the addDecl to another session waited for the slow one's check"
    );
}

/// An `addDecl` queued behind another of its session took its work slot and
/// then waited, holding it, for the session map: a burst of them filled the
/// pool, and an unrelated request waited for a slot behind them. It waits for
/// its session holding no slot now, so here, with the first `addDecl` checking
/// in one of two slots and the second queued, a `check` takes the other slot
/// at once. The second `addDecl` cites the first's declaration: same-session
/// `addDecl`s are checked in the order they came.
#[tokio::test]
async fn add_decls_queued_on_their_session_hold_no_work_slot() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let session = state.create_session().await.expect("open a session");
    let first_decl = slow_theorem(&state, 2);
    let Declaration::Theorem { type_, .. } = &first_decl else {
        unreachable!("slow_theorem is a theorem")
    };
    let second_decl = Declaration::Theorem {
        name: Name::from_string("slow_2_again"),
        level_params: vec![],
        type_: type_.clone(),
        value: Expr::const_(Name::from_string("slow_2"), vec![]),
    };

    // Both slots taken, so both addDecls reach their first wait.
    let held = (
        state.work.slot().await.expect("a slot"),
        state.work.slot().await.expect("a slot"),
    );
    let s = Arc::clone(&state);
    let first = spawned(async move {
        handle_add_decl(&s, RequestId::Number(1), add_decl(session, &first_decl)).await
    });
    let s = Arc::clone(&state);
    let second = spawned(async move {
        handle_add_decl(&s, RequestId::Number(2), add_decl(session, &second_decl)).await
    });
    // On this one-thread runtime a yield runs every task already woken, so
    // both addDecls reach their wait before a slot is let go.
    for _ in 0..8 {
        tokio::task::yield_now().await;
    }
    drop(held.0);
    until("the first addDecl takes the slot let go", HANG, || {
        state.work.in_use() == 2
    })
    .await;
    drop(held.1);

    let check = handle_check(
        &state,
        RequestId::Number(3),
        CheckParams {
            code: "Type".to_string(),
            timeout_ms: Some(HANG.as_millis() as u64),
        },
    )
    .await;
    let check_answered = Instant::now();
    let (first, first_answered) = answered("the first addDecl", first).await;
    let (second, _) = answered("the second addDecl", second).await;
    assert!(check.error.is_none(), "{:?}", check.error);
    accepted("the first addDecl", &first);
    accepted(
        "the second addDecl, which cites the first's declaration",
        &second,
    );
    assert!(
        check_answered < first_answered,
        "the check waited for a slot held by an addDecl queued on its session"
    );
}

/// `loadEnvironment`'s merge held the environment's write lock while it
/// re-checked the loaded declarations, so it could not even start while a
/// request read the environment, and nothing read the environment until it
/// had finished. It works on a copy now, and waits for the write lock only to
/// publish. Here the test reads the environment throughout: the merge checks
/// its declaration meanwhile, gives its slot back, and then waits only to
/// publish; once the read ends it publishes. The old merge waited for the
/// write lock holding its slot, before checking anything, until its timeout.
#[tokio::test]
async fn load_environment_merge_checks_while_the_environment_is_read() {
    let state = prelude_state_with(None);
    let mut saved = Environment::try_with_prelude().expect("try_with_prelude should succeed");
    saved.add_decl_unchecked(slow_theorem(&state, 3));
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("merge.bincode");
    saved.save_to_file(&path).expect("save the environment");

    let reading = state.env.read().await;
    let s = Arc::clone(&state);
    let params: LoadEnvironmentParams = serde_json::from_value(json!({
        "path": path.to_string_lossy(),
        "timeout_ms": HANG.as_millis() as u64,
    }))
    .expect("loadEnvironment params");
    let merge =
        spawned(async move { handle_load_environment(&s, RequestId::Number(1), params).await });
    // Past the hang detector: the old merge answers at its timeout, the hang
    // detector, and the loop ends there.
    until(
        "the merge waits only to publish (or answers)",
        HANG + HANG,
        || merge.is_finished() || (state.env.try_read().is_err() && state.work.in_use() == 0),
    )
    .await;
    drop(reading);

    let (response, _) = answered("the merge", merge).await;
    assert!(
        response.error.is_none(),
        "the merge could not check while the environment was read: {:?}",
        response.error
    );
    assert!(state
        .env
        .read()
        .await
        .get_const(&Name::from_string("slow_3"))
        .is_some());
}

/// A module `ServerFixture` with one axiom, `ServerFixture.imported : Prop`:
/// its `.olean` bytes.
pub(super) fn fixture_module() -> Vec<u8> {
    let mut fixture = Environment::default();
    fixture.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("ServerFixture.imported"),
        level_params: vec![],
        type_: Expr::prop(),
    });
    clean_olean::OleanExporter::export_with_env(
        &fixture,
        &[],
        &[],
        "c0de000000000000000000000000000000000001",
    )
    .expect("export the fixture module")
}

/// A named pipe at `path`: whoever reads it waits for the test to write it.
#[cfg(unix)]
pub(super) fn named_pipe(path: &std::path::Path) {
    let made = std::process::Command::new("mkfifo")
        .arg(path)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo {}", path.display());
}

/// Open the pipe for writing: it opens once its reader has opened it.
#[cfg(unix)]
pub(super) async fn pipe_writer(path: std::path::PathBuf) -> std::fs::File {
    let opening =
        tokio::task::spawn_blocking(move || std::fs::OpenOptions::new().write(true).open(path));
    tokio::time::timeout(HANG, opening)
        .await
        .expect("the import opens the module within the hang detector")
        .expect("the opening thread")
        .expect("open the pipe")
}

#[cfg(unix)]
fn import_params(
    state: &ServerState,
    dir: &std::path::Path,
    timeout_ms: u64,
) -> ImportModuleParams {
    serde_json::from_value(json!({
        "module": "ServerFixture",
        "search_paths": [dir.to_string_lossy()],
        "timeout_ms": timeout_ms,
        "token": super::launch_token_of(state),
    }))
    .expect("importModule params")
}

/// `importModule` loaded into a copy of the environment made before its load
/// and installed the copy: a change that landed meanwhile was lost. Here the
/// module is a named pipe, so the load waits in the middle (its copy made)
/// until the test writes it, and meanwhile `verifyFile` sets up the logical
/// prelude in the shared environment. The old import overwrote it; now the
/// load runs again on a copy of the changed environment (a plain file by
/// then), and both are kept.
#[cfg(unix)]
#[tokio::test]
async fn import_module_keeps_a_change_made_during_its_load() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let module = dir.path().join("ServerFixture.olean");
    named_pipe(&module);
    let bytes = fixture_module();
    let state = bare_state_with(WorkPool::new(2));
    let truth = Name::from_string("True");
    assert!(state.env.read().await.get_const(&truth).is_none());

    let s = Arc::clone(&state);
    let params = import_params(&state, dir.path(), HANG.as_millis() as u64);
    let import =
        spawned(async move { handle_import_module(&s, RequestId::Number(1), params).await });
    let mut pipe = pipe_writer(module.clone()).await;

    // The change: verifyFile seeds `True` (its own answer does not matter).
    let _ = handle_verify_file(
        &state,
        RequestId::Number(2),
        VerifyFileParams {
            content: "theorem t : True := trivial\n".to_string(),
            proof: None,
            timeout_ms: Some(HANG.as_millis() as u64),
        },
    )
    .await;
    assert!(
        state.env.read().await.get_const(&truth).is_some(),
        "verifyFile sets up the logical prelude"
    );

    // A load that runs again reads a plain file; this one reads the pipe.
    let plain = dir.path().join("ServerFixture.plain");
    std::fs::write(&plain, &bytes).expect("write the module");
    std::fs::rename(&plain, &module).expect("put the plain module in place");
    tokio::task::spawn_blocking(move || {
        use std::io::Write;
        pipe.write_all(&bytes)
            .expect("write the module down the pipe");
    })
    .await
    .expect("the writing thread");

    let (response, _) = answered("the import", import).await;
    assert!(response.error.is_none(), "{:?}", response.error);
    let env = state.env.read().await;
    assert!(env
        .get_const(&Name::from_string("ServerFixture.imported"))
        .is_some());
    assert!(
        env.get_const(&truth).is_some(),
        "the change made while the module loaded was overwritten"
    );
}

/// `importModule` took no timeout and loaded on a blocking thread with no
/// deadline: a load that never ended was never answered. Its load is pool work
/// under the request's deadline now: at `timeout_ms` it answers the timeout
/// error, and nothing it loads is imported. Here the module is a named pipe
/// the test writes only after the answer; the load then ends (an empty module)
/// and gives its slot back.
#[cfg(unix)]
#[tokio::test]
async fn import_module_answers_its_timeout_and_imports_nothing() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let module = dir.path().join("ServerFixture.olean");
    named_pipe(&module);
    let state = bare_state_with(WorkPool::new(2));
    let before = state.env.read().await.num_constants();

    let s = Arc::clone(&state);
    let params = import_params(&state, dir.path(), 300);
    let import =
        spawned(async move { handle_import_module(&s, RequestId::Number(1), params).await });
    let answer = tokio::time::timeout(HANG, import).await;
    // End the load: the pipe opens and closes empty.
    drop(pipe_writer(module).await);
    let (response, _) = answer
        .expect("the import answers within the hang detector")
        .expect("the import's task");
    assert_eq!(response.error.map(|e| e.code), Some(TIMEOUT));
    wait_until_idle(&state).await;
    assert_eq!(state.env.read().await.num_constants(), before);
}
