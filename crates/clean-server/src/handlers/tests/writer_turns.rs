// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The writers' turns, the set-up they share the environment with, and
//! writers whose requests are cancelled (R34 in `docs/DECISIONS.md`): the
//! probes of the concurrency review of 2026-10-16 that pin a rule, adapted.
//!
//! Each test names the change that makes it fail: the rule it pins, undone.
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use super::concurrent_writers::{answered, bare_state_with, prelude_state_with, spawned, until};
use crate::handlers::work::WorkPool;
use crate::handlers::*;
use crate::rpc::Response;
use crate::session_env::SessionId;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use serde_json::json;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
const TIMEOUT: i32 = -32004;

fn axiom(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    }
}

fn true_axiom(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    }
}

/// `name : True := from`.
fn true_theorem(name: &str, from: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
        value: Expr::const_(Name::from_string(from), vec![]),
    }
}

fn has(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

fn save(dir: &Path, file: &str, env: &Environment) -> PathBuf {
    let path = dir.join(file);
    env.save_to_file(&path).expect("save the environment");
    path
}

fn add_decl(session: SessionId, decl: &Declaration, timeout_ms: u64) -> AddDeclParams {
    serde_json::from_value(json!({
        "session_id": session.to_string(),
        "decl": decl,
        "require_foundational": false,
        "heartbeat_limit": 0,
        "timeout_ms": timeout_ms,
    }))
    .expect("addDecl params")
}

fn merge(path: &Path, timeout_ms: u64) -> LoadEnvironmentParams {
    serde_json::from_value(json!({
        "path": path.to_string_lossy(),
        "timeout_ms": timeout_ms,
    }))
    .expect("loadEnvironment params")
}

/// `loadEnvironment` replacing `state`'s environment with `path`'s, with the
/// launch token `replace_unchecked` needs.
fn replace(state: &ServerState, path: &Path, timeout_ms: u64) -> LoadEnvironmentParams {
    serde_json::from_value(json!({
        "path": path.to_string_lossy(),
        "replace": true,
        "replace_unchecked": true,
        "token": super::launch_token_of(state),
        "timeout_ms": timeout_ms,
    }))
    .expect("loadEnvironment params")
}

fn import(state: &ServerState, dir: &Path, module: &str, timeout_ms: u64) -> ImportModuleParams {
    serde_json::from_value(json!({
        "module": module,
        "search_paths": [dir.to_string_lossy()],
        "timeout_ms": timeout_ms,
        "token": super::launch_token_of(state),
    }))
    .expect("importModule params")
}

/// `verifyFile` of a one-line theorem: its set-up seeds the logical prelude.
fn verify_file() -> VerifyFileParams {
    VerifyFileParams {
        content: "theorem t : True := trivial\n".to_string(),
        proof: None,
        timeout_ms: Some(HANG.as_millis() as u64),
    }
}

/// The `.olean` bytes of a module `module` with one axiom `<module>.imported`.
fn module_bytes(module: &str) -> Vec<u8> {
    let mut fixture = Environment::default();
    fixture.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string(&format!("{module}.imported")),
        level_params: vec![],
        type_: Expr::prop(),
    });
    clean_olean::OleanExporter::export_with_env(
        &fixture,
        &[],
        &[],
        "c0de000000000000000000000000000000000002",
    )
    .expect("export the fixture module")
}

fn accepted(what: &str, response: &Response) {
    assert!(response.error.is_none(), "{what}: {:?}", response.error);
    let result = response.result.as_ref().expect("a result");
    assert_eq!(result["accepted"], json!(true), "{what}: {result}");
}

fn timed_out(what: &str, response: &Response) {
    assert_eq!(
        response.error.as_ref().map(|e| e.code),
        Some(TIMEOUT),
        "{what}: {:?}",
        response.error
    );
}

/// Is the writers' turn held now? Takes it for an instant when it is free.
async fn turn_held(state: &ServerState) -> bool {
    tokio::time::timeout(Duration::ZERO, state.env.writer_turn())
        .await
        .is_err()
}

/// Every slot, the writers' turn, the environment and the sessions' locks are
/// free again, and no work panicked.
async fn quiescent(state: &ServerState, sessions: &[SessionId]) {
    until("every slot is given back", HANG, || {
        state.work.in_use() == 0
    })
    .await;
    drop(
        tokio::time::timeout(HANG, state.env.writer_turn())
            .await
            .expect("the writers' turn is free"),
    );
    drop(
        tokio::time::timeout(HANG, state.env.write())
            .await
            .expect("the environment's write lock is free"),
    );
    for id in sessions {
        if let Some(session) = state.session(id).await {
            drop(
                tokio::time::timeout(HANG, session.lock())
                    .await
                    .expect("the session's lock is free"),
            );
        }
    }
    assert_eq!(state.work.panics(), 0, "no work panicked");
}

// ---------------------------------------------------------------------------
// The verify family's set-up, the one writer that takes no turn.
// ---------------------------------------------------------------------------

/// The verify family's set-up seeds the logical prelude on every call; a
/// seed that added nothing must count no change, or every writer computing
/// meanwhile works again (a stream of `verifyFile`s would keep a merge working
/// until its timeout). Here on a bare environment and on a full prelude, whose
/// set-up still adds declarations the first time. Fails when a seed counts a
/// change whatever it adds (`EnvWriteGuard::seed` setting `changed`
/// unconditionally).
#[tokio::test]
async fn repeated_verify_file_set_up_counts_one_change() {
    for (what, state) in [
        ("bare", bare_state_with(WorkPool::new(2))),
        ("full prelude", prelude_state_with(Some(WorkPool::new(2)))),
    ] {
        let before = state.env.revision().await;
        let _ = handle_verify_file(&state, RequestId::Number(1), verify_file()).await;
        let seeded = state.env.revision().await;
        assert_ne!(seeded, before, "{what}: the first set-up added nothing");
        for n in 2..4 {
            let _ = handle_verify_file(&state, RequestId::Number(n), verify_file()).await;
            assert_eq!(
                state.env.revision().await,
                seeded,
                "{what}: verifyFile {n} counted a change it did not make"
            );
        }
    }
}

/// A constant source serving one proposition, `merge_gate : Prop`, whose
/// first look-up says so (`reached`) and waits for the test (`go`); later
/// look-ups go straight through. A merge that admits a declaration naming
/// `merge_gate` looks it up while it checks its copy, so the test knows the
/// merge has made its copy and is computing on it, and holds it there.
#[derive(Debug)]
struct MergeGate {
    info: clean_kernel::env::ConstantInfo,
    reached: std::sync::Mutex<Option<std::sync::mpsc::Sender<()>>>,
    go: std::sync::Mutex<Option<std::sync::mpsc::Receiver<()>>>,
}

impl clean_kernel::env::ConstantSource for MergeGate {
    fn get(&self, name: &Name) -> Option<&clean_kernel::env::ConstantInfo> {
        if *name != self.info.name {
            return None;
        }
        let first = self
            .reached
            .lock()
            .ok()
            .and_then(|mut reached| reached.take());
        if let Some(reached) = first {
            let _ = reached.send(());
            let go = self.go.lock().ok().and_then(|mut go| go.take());
            if let Some(go) = go {
                let _ = go.recv_timeout(HANG);
            }
        }
        Some(&self.info)
    }

    fn contains(&self, name: &Name) -> bool {
        *name == self.info.name
    }
}

/// A [`MergeGate`], its `reached` signal and its `go` sender.
fn merge_gate() -> (
    Arc<MergeGate>,
    std::sync::mpsc::Receiver<()>,
    std::sync::mpsc::Sender<()>,
) {
    let mut defined = Environment::new();
    defined.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("merge_gate"),
        level_params: vec![],
        type_: Expr::prop(),
    });
    let info = defined
        .get_const(&Name::from_string("merge_gate"))
        .cloned()
        .expect("merge_gate is defined");
    let (reached_tx, reached) = std::sync::mpsc::channel();
    let (go, go_rx) = std::sync::mpsc::channel();
    let gate = Arc::new(MergeGate {
        info,
        reached: std::sync::Mutex::new(Some(reached_tx)),
        go: std::sync::Mutex::new(Some(go_rx)),
    });
    (gate, reached, go)
}

/// A seed made while a merge computes on its copy is kept: the merge's copy
/// is stale by then, so it is merged again into the seeded environment rather
/// than published over it. The merge admits `uses_gate : merge_gate`, and the
/// environment serves `merge_gate` from a [`MergeGate`]: the merge's first
/// check of its copy waits there until the test has seeded. Fails when a
/// publish ignores the revision (the stale copy is installed and the seed is
/// lost).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_merge_keeps_a_seed_made_while_it_merges() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let (gate, reached, go) = merge_gate();
    state.env.write().await.set_constant_source(gate);
    let dir = tempfile::tempdir().expect("a scratch directory");
    let mut saved = Environment::new();
    saved.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("uses_gate"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("merge_gate"), vec![]),
    });
    let path = save(dir.path(), "gated.bincode", &saved);
    let s = Arc::clone(&state);
    let merging = spawned(async move {
        handle_load_environment(
            &s,
            RequestId::Number(1),
            merge(&path, HANG.as_millis() as u64),
        )
        .await
    });
    // The merge has its copy and is checking `uses_gate` in it.
    let give_up = Instant::now() + HANG;
    while reached.try_recv().is_err() {
        assert!(Instant::now() < give_up, "the merge never checked its copy");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    let before = state.env.revision().await;
    let _ = handle_verify_file(&state, RequestId::Number(2), verify_file()).await;
    assert_ne!(
        state.env.revision().await,
        before,
        "the seed added nothing: this test's premise"
    );
    let seeded = state.env.read().await.num_constants();
    let _ = go.send(());

    let (response, _) = answered("the merge", merging).await;
    assert!(response.error.is_none(), "{:?}", response.error);
    let env = state.env.read().await;
    assert!(has(&env, "uses_gate"));
    assert!(
        env.num_constants() > seeded,
        "the merge's publish dropped the seed: {} constants, {seeded} after the seed",
        env.num_constants()
    );
    drop(env);
    let revision = state.env.revision().await;
    let _ = handle_verify_file(&state, RequestId::Number(3), verify_file()).await;
    assert_eq!(
        state.env.revision().await,
        revision,
        "the seed had to add its declarations again: the merge overwrote them"
    );
    quiescent(&state, &[]).await;
}

// ---------------------------------------------------------------------------
// The writers' turn is waited for inside the request's timeout.
// ---------------------------------------------------------------------------

/// A writer that waits for the writers' turn waits inside its timeout: while
/// the turn is held, `importModule`, a merge and a replace each answer the
/// timeout error at theirs, hold no work slot, and publish nothing. Fails
/// when `importModule` waits outside its timeout (it is then never answered).
#[tokio::test]
async fn writers_waiting_for_their_turn_answer_their_timeout() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let dir = tempfile::tempdir().expect("a scratch directory");
    std::fs::write(
        dir.path().join("TurnFixture.olean"),
        module_bytes("TurnFixture"),
    )
    .expect("write the module");
    let mut merged = Environment::new();
    merged.add_decl_unchecked(axiom("turn_merged"));
    let merged = save(dir.path(), "merged.bincode", &merged);
    let mut replaced = Environment::new();
    replaced.add_decl_unchecked(axiom("turn_replaced"));
    let replaced = save(dir.path(), "replaced.bincode", &replaced);
    let before = state.env.revision().await;

    let turn = state.env.writer_turn().await;
    let imported = tokio::time::timeout(
        HANG,
        handle_import_module(
            &state,
            RequestId::Number(1),
            import(&state, dir.path(), "TurnFixture", 300),
        ),
    )
    .await
    .expect("importModule answers while the turn is held");
    timed_out("importModule waiting for the turn", &imported);
    let merge_answer = tokio::time::timeout(
        HANG,
        handle_load_environment(&state, RequestId::Number(2), merge(&merged, 300)),
    )
    .await
    .expect("the merge answers while the turn is held");
    timed_out("the merge waiting for the turn", &merge_answer);
    let replace_answer = tokio::time::timeout(
        HANG,
        handle_load_environment(
            &state,
            RequestId::Number(3),
            replace(&state, &replaced, 300),
        ),
    )
    .await
    .expect("the replace answers while the turn is held");
    timed_out("the replace waiting for the turn", &replace_answer);
    assert_eq!(
        state.work.in_use(),
        0,
        "a writer waiting for the turn holds a work slot"
    );
    drop(turn);

    assert_eq!(
        state.env.revision().await,
        before,
        "a timed-out writer published"
    );
    let env = state.env.read().await;
    assert!(!has(&env, "TurnFixture.imported"));
    assert!(!has(&env, "turn_merged"));
    assert!(!has(&env, "turn_replaced"));
    drop(env);
    quiescent(&state, &[]).await;
}

// ---------------------------------------------------------------------------
// Cancellation: a request's future dropped while it waits.
// ---------------------------------------------------------------------------

/// An import whose request is cancelled while its load runs lets the turn go
/// at once (the turn is the request's, never its work's), keeps its slot until
/// the load ends, and publishes nothing. The module is a named pipe, so the
/// load waits in the middle until the test writes it. Fails when the load
/// holds the turn itself (the turn then waits for the load).
#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_cancelled_import_lets_the_turn_go_and_publishes_nothing() {
    use super::concurrent_writers::{named_pipe, pipe_writer};

    let dir = tempfile::tempdir().expect("a scratch directory");
    let module = dir.path().join("PipeFixture.olean");
    named_pipe(&module);
    let state = bare_state_with(WorkPool::new(2));
    let before = state.env.revision().await;
    let s = Arc::clone(&state);
    let d = dir.path().to_path_buf();
    let importing = spawned(async move {
        handle_import_module(
            &s,
            RequestId::Number(1),
            import(&s, &d, "PipeFixture", HANG.as_millis() as u64),
        )
        .await
    });
    let mut pipe = pipe_writer(module.clone()).await;
    assert!(
        turn_held(&state).await,
        "the import holds the turn while it loads"
    );
    importing.abort();
    assert!(importing.await.is_err(), "the import was cancelled");
    drop(
        tokio::time::timeout(HANG, state.env.writer_turn())
            .await
            .expect("a cancelled import lets the turn go while its load still runs"),
    );
    assert_eq!(state.work.in_use(), 1, "the load still holds its slot");
    let bytes = module_bytes("PipeFixture");
    tokio::task::spawn_blocking(move || {
        use std::io::Write;
        pipe.write_all(&bytes)
            .expect("write the module down the pipe");
    })
    .await
    .expect("the writing thread");
    until("the cancelled load's end", HANG, || {
        state.work.in_use() == 0
    })
    .await;
    assert_eq!(
        state.env.revision().await,
        before,
        "a cancelled import published"
    );
    assert!(!has(&*state.env.read().await, "PipeFixture.imported"));
    quiescent(&state, &[]).await;
}

/// A merge cancelled while it waits to publish (a reader holds the
/// environment) takes its write waiter away, lets the turn go and publishes
/// nothing. Fails when the merge holds the write lock while it works (it then
/// waits for the reader before it computes, holding its slot).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_merge_cancelled_while_it_waits_to_publish_publishes_nothing() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let dir = tempfile::tempdir().expect("a scratch directory");
    let mut saved = Environment::new();
    saved.add_decl_unchecked(axiom("cancelled_merge"));
    let path = save(dir.path(), "merge.bincode", &saved);
    let before = state.env.revision().await;
    let reading = state.env.read().await;
    let s = Arc::clone(&state);
    let merging = spawned(async move {
        handle_load_environment(
            &s,
            RequestId::Number(1),
            merge(&path, HANG.as_millis() as u64),
        )
        .await
    });
    // The environment is write-preferring: a queued publish keeps new reads
    // out. The merge's work is done when its slot is back.
    until("the merge waits only to publish", HANG, || {
        state.env.try_read().is_err() && state.work.in_use() == 0
    })
    .await;
    assert!(
        turn_held(&state).await,
        "the merge holds the turn while it waits to publish"
    );
    merging.abort();
    assert!(merging.await.is_err(), "the merge was cancelled");
    until("the merge's write waiter is gone", HANG, || {
        state.env.try_read().is_ok()
    })
    .await;
    assert!(
        !turn_held(&state).await,
        "the cancelled merge let the turn go"
    );
    drop(reading);
    assert_eq!(
        state.env.revision().await,
        before,
        "a cancelled merge published"
    );
    assert!(!has(&*state.env.read().await, "cancelled_merge"));
    quiescent(&state, &[]).await;
}

/// `addDecl`s cancelled while they wait for their session, and for a slot
/// holding their session, leave every lock and slot free and the session as
/// it was. On this one-thread runtime a yield runs every task already woken,
/// so the first `addDecl` reaches its wait before it is cancelled. Fails when
/// an `addDecl` takes its slot before its session (the second then never
/// holds its session while it waits).
#[tokio::test]
async fn cancelled_add_decls_leave_nothing_held() {
    let state = prelude_state_with(Some(WorkPool::new(1)));
    let session = state.create_session().await.expect("open a session");
    let handle = state.session(&session).await.expect("the session is open");

    let held = handle.lock().await;
    let s = Arc::clone(&state);
    let waiting_for_session = spawned(async move {
        handle_add_decl(
            &s,
            RequestId::Number(1),
            add_decl(session, &true_axiom("cancelled_a"), HANG.as_millis() as u64),
        )
        .await
    });
    for _ in 0..8 {
        tokio::task::yield_now().await;
    }
    waiting_for_session.abort();
    assert!(
        waiting_for_session.await.is_err(),
        "the addDecl was cancelled"
    );
    drop(held);

    let slot = state.work.slot().await.expect("the pool's one slot");
    let s = Arc::clone(&state);
    let waiting_for_slot = spawned(async move {
        handle_add_decl(
            &s,
            RequestId::Number(2),
            add_decl(session, &true_axiom("cancelled_b"), HANG.as_millis() as u64),
        )
        .await
    });
    until(
        "the addDecl holds its session, waiting for the slot",
        HANG,
        || handle.try_lock().is_err(),
    )
    .await;
    waiting_for_slot.abort();
    assert!(waiting_for_slot.await.is_err(), "the addDecl was cancelled");
    assert!(
        handle.try_lock().is_ok(),
        "the cancelled addDecl let its session go"
    );
    drop(slot);

    let after = handle_add_decl(
        &state,
        RequestId::Number(3),
        add_decl(session, &true_axiom("after"), HANG.as_millis() as u64),
    )
    .await;
    accepted("an addDecl after the cancellations", &after);
    let checked = handle.lock().await;
    assert!(!checked.contains(&Name::from_string("cancelled_a")));
    assert!(!checked.contains(&Name::from_string("cancelled_b")));
    drop(checked);
    quiescent(&state, &[session]).await;
}

// ---------------------------------------------------------------------------
// One session's addDecls, in the order they came.
// ---------------------------------------------------------------------------

/// `addDecl`s queued on one session are checked one at a time in the order
/// they reached its lock, each against every declaration accepted before it:
/// each here cites the one queued before it, so each is accepted only if the
/// one before it was checked first and kept. Fails when an `addDecl` lets its
/// session go while it checks (the next one then checks against a session
/// without its predecessor).
#[tokio::test]
async fn same_session_add_decls_are_checked_in_arrival_order() {
    let state = prelude_state_with(Some(WorkPool::new(2)));
    let session = state.create_session().await.expect("open a session");
    let handle = state.session(&session).await.expect("the session is open");
    let held = handle.lock().await;
    let decls = [
        true_axiom("fifo_0"),
        true_theorem("fifo_1", "fifo_0"),
        true_theorem("fifo_2", "fifo_1"),
        true_theorem("fifo_3", "fifo_2"),
    ];
    let mut queued = Vec::new();
    for (i, decl) in decls.into_iter().enumerate() {
        let s = Arc::clone(&state);
        queued.push(spawned(async move {
            handle_add_decl(
                &s,
                RequestId::Number(i as i64),
                add_decl(session, &decl, HANG.as_millis() as u64),
            )
            .await
        }));
        // Each reaches the session's lock before the next is sent.
        for _ in 0..8 {
            tokio::task::yield_now().await;
        }
    }
    drop(held);
    for (i, request) in queued.into_iter().enumerate() {
        let (response, _) = answered("an addDecl", request).await;
        accepted(
            &format!("addDecl {i}, which cites the one before it"),
            &response,
        );
    }
    quiescent(&state, &[session]).await;
}
