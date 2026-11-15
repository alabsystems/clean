// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the reviews of R36 (`docs/DECISIONS.md`, 2026-10-16) found still
//! freed on the runtime, or held past a request's timeout:
//!
//! * A failed `applyTactic` dropped the copy of the proof state its tactic ran
//!   on (a whole environment) on the runtime, and a state refused at the
//!   lifecycle limit was dropped there too, under the proof-state cache's
//!   lock.
//! * Closing a session, and the session copy an `addDecl` replaced or left,
//!   were freed on the runtime.
//! * A save past its timeout held the environment for reading while it wrote
//!   its file: a writer queued behind the hold, and every reader queued behind
//!   that writer, waited for the write.
//! * The searches' scans of every constant did not stop at their deadline.
//! * `ServerState::create_session` and `addDecl` copied a session's
//!   environment on the runtime (R87, 2026-10-17).
//!
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use super::free_gate::gated_source;
use crate::dispatch::dispatch_request;
use crate::handlers::*;
use crate::rpc::Response;
use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, ExtensionIdx,
    PersistentExtEntry, PersistentExtState, TrustedEnvExt,
};
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use serde_json::{json, Value};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

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

// ---------------------------------------------------------------------------
// Where copies of an environment are freed.
//
// `DropSites` is the state of a persistent environment extension. Every
// `Environment::clone` clones the extension states (`clone_box`), so with the
// state set in an environment, each copy of it, and each copy of a copy,
// carries one instance with an id of its own, and freeing a copy records the
// thread it was freed on. The extension is registered once per test process
// under a name no module carries: an environment without the state set holds
// none, and `materialize_extension_states` creates one only for an extension
// its imports name, so no other test's environment ever holds one.
// ---------------------------------------------------------------------------

/// What every copy of an environment holding a recording `DropSites` shares.
#[derive(Default)]
struct Recorder {
    /// Ids handed out so far.
    next: AtomicU64,
    /// Each freed copy: its id and the thread it was freed on.
    freed: Mutex<Vec<(u64, ThreadId)>>,
    /// Each copy: its id and the thread that made it.
    made: Mutex<Vec<(u64, ThreadId)>>,
}

#[derive(Default)]
struct DropSites {
    /// `None` in an environment that is not recording (the default state).
    recorder: Option<Arc<Recorder>>,
    id: u64,
}

impl DropSites {
    fn recording(recorder: &Arc<Recorder>) -> Self {
        Self {
            recorder: Some(Arc::clone(recorder)),
            id: recorder.next.fetch_add(1, Ordering::SeqCst),
        }
    }
}

impl Clone for DropSites {
    fn clone(&self) -> Self {
        match &self.recorder {
            Some(recorder) => {
                let copy = Self::recording(recorder);
                if let Ok(mut made) = recorder.made.lock() {
                    made.push((copy.id, std::thread::current().id()));
                }
                copy
            }
            None => Self::default(),
        }
    }
}

impl Drop for DropSites {
    fn drop(&mut self) {
        if let Some(recorder) = &self.recorder {
            if let Ok(mut freed) = recorder.freed.lock() {
                freed.push((self.id, std::thread::current().id()));
            }
        }
    }
}

#[derive(Clone)]
struct NoEntry;

impl PersistentExtEntry for NoEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: Name::from_string("CleanServerTest.dropSites"),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for DropSites {
    type Entry = NoEntry;

    fn add_entry(&mut self, _entry: &NoEntry) {}

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

fn drop_sites_ext() -> ExtensionIdx {
    static IDX: OnceLock<ExtensionIdx> = OnceLock::new();
    *IDX.get_or_init(|| {
        register_persistent_ext::<DropSites>(Name::from_string("CleanServerTest.dropSites"))
    })
}

/// The test's side of a recording environment.
struct Sites(Arc<Recorder>);

impl Sites {
    /// `env`, recording where each of its copies is freed.
    fn record(mut env: Environment) -> (Environment, Self) {
        let recorder = Arc::new(Recorder::default());
        *env.get_ext_state_mut::<DropSites>(drop_sites_ext()) = DropSites::recording(&recorder);
        (env, Self(recorder))
    }

    /// A mark: the copies made after it are the ones `freed_since` reads.
    fn mark(&self) -> u64 {
        self.0.next.load(Ordering::SeqCst)
    }

    /// Wait until every copy made since `mark` has been freed, and return the
    /// threads they were freed on. The copies a request makes and keeps none
    /// of are all freed by the time it has answered or soon after (a free off
    /// the runtime runs on its own).
    async fn freed_since(&self, mark: u64) -> Vec<ThreadId> {
        let give_up = Instant::now() + HANG;
        loop {
            let made = self.mark();
            let freed: Vec<ThreadId> = self
                .0
                .freed
                .lock()
                .expect("the recorder")
                .iter()
                .filter(|(id, _)| *id >= mark && *id < made)
                .map(|(_, on)| *on)
                .collect();
            if freed.len() as u64 == made - mark {
                return freed;
            }
            assert!(
                Instant::now() < give_up,
                "{} of the {} copies made since the mark were never freed",
                (made - mark) - freed.len() as u64,
                made - mark
            );
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }
}

/// The copies made since `mark` were made, at least one, none on this
/// runtime's thread (the test's: these tests run on a one-thread runtime).
fn made_off_the_runtime(sites: &Sites, mark: u64, what: &str) {
    let runtime = std::thread::current().id();
    let made: Vec<ThreadId> = sites
        .0
        .made
        .lock()
        .expect("the recorder")
        .iter()
        .filter(|(id, _)| *id >= mark)
        .map(|(_, on)| *on)
        .collect();
    assert!(
        !made.is_empty(),
        "{what} made no copy of the environment: this test's premise"
    );
    let on_runtime = made.iter().filter(|on| **on == runtime).count();
    assert_eq!(
        on_runtime,
        0,
        "{what} made {on_runtime} of its {} copies on the runtime's thread",
        made.len()
    );
}

/// The copies made since `mark` were freed, at least one, none on this
/// runtime's thread (the test's: these tests run on a one-thread runtime).
async fn freed_off_the_runtime(sites: &Sites, mark: u64, what: &str) {
    let runtime = std::thread::current().id();
    let freed = sites.freed_since(mark).await;
    assert!(
        !freed.is_empty(),
        "{what} made no copy of the environment: this test's premise"
    );
    let on_runtime = freed.iter().filter(|on| **on == runtime).count();
    assert_eq!(
        on_runtime,
        0,
        "{what} freed {on_runtime} of its {} copies on the runtime's thread",
        freed.len()
    );
}

/// A failed `applyTactic` dropped the copy of the proof state its tactic ran
/// on (a whole environment) where the handler returned, on the runtime: a
/// failed tactic is the common case for an agent. It is freed off the runtime
/// now. Fails when the failure arm drops the copy (no `free_off_runtime`).
#[tokio::test]
async fn a_failed_tactic_frees_its_copy_off_the_runtime() {
    let (env, sites) = Sites::record(Environment::with_prelude());
    let state = ServerState::new().with_env(env);
    let opened = result_of(
        &state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;

    let mark = sites.mark();
    let failed = result_of(
        &state,
        "applyTactic",
        json!({
            "state_id": opened["state_id"],
            "goal_id": opened["goals"][0]["goal_id"],
            "tactic": "exact runtime_frees_no_such_lemma",
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert_eq!(failed["success"], json!(false), "{failed}");
    freed_off_the_runtime(&sites, mark, "a failed applyTactic").await;
}

/// A tactic that succeeded at the lifecycle limit had its new state refused
/// inside `ProofStateCache::insert_child`, which dropped it under the cache's
/// write lock, on the runtime. The refused state is freed off the runtime
/// now, after the lock is let go. Fails when `insert_child` drops it.
#[tokio::test]
async fn a_state_refused_at_the_lifecycle_limit_is_freed_off_the_runtime() {
    let (env, sites) = Sites::record(Environment::with_prelude());
    let state = ServerState::new().with_env(env);
    let opened = result_of(
        &state,
        "proofState.openObligation",
        json!({
            "schema_version": crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION,
            "environment_id": "runtime-frees",
            "domain_profile": "general",
            "goal": {
                "pretty": "True",
                "expr": serde_json::to_value(Expr::const_(Name::from_string("True"), vec![]))
                    .expect("the goal's JSON"),
            },
            "trust_policy": "constructive-only",
            "ttl_sec": 600,
            "max_states": 1,
            "min_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
            "max_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;

    let mark = sites.mark();
    let refused = result_of(
        &state,
        "applyTactic",
        json!({
            "state_id": opened["state_id"],
            "goal_id": opened["initial_snapshot"]["goals"][0]["goal_id"],
            "tactic": "trivial",
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert_eq!(refused["success"], json!(false), "{refused}");
    assert_eq!(
        refused["error"]["code"],
        json!("LIFECYCLE_LIMIT_EXCEEDED"),
        "{refused}"
    );
    freed_off_the_runtime(&sites, mark, "a refusal at the lifecycle limit").await;
}

/// `addDecl` dropped the session it replaced (an accepted declaration) and
/// the candidate a rejection left on the runtime: each holds a whole overlay
/// environment. Both are freed off the runtime now. (The candidate is copied
/// on the pool since R87: `sessions_are_copied_off_the_runtime`.)
#[tokio::test]
async fn add_decl_frees_what_it_lets_go_off_the_runtime() {
    let (env, sites) = Sites::record(Environment::with_prelude());
    let state = ServerState::new().with_env(env);
    let session = state.create_session().await.expect("open a session");
    let params = |decl: Declaration| -> AddDeclParams {
        serde_json::from_value(json!({
            "session_id": session.to_string(),
            "decl": decl,
            "require_foundational": false,
            "timeout_ms": HANG.as_millis() as u64,
        }))
        .expect("addDecl params")
    };

    let mark = sites.mark();
    let accepted = handle_add_decl(
        &state,
        RequestId::Number(1),
        params(Declaration::Axiom {
            name: Name::from_string("runtime_frees_accepted"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        }),
    )
    .await;
    let accepted = accepted.result.expect("an addDecl result");
    assert_eq!(accepted["accepted"], json!(true), "{accepted}");
    // The session's new overlay is the candidate: every copy but that one is
    // freed. Read the frees once the session is closed.
    let mark_after_accept = sites.mark();

    let rejected = handle_add_decl(
        &state,
        RequestId::Number(2),
        params(Declaration::Theorem {
            name: Name::from_string("runtime_frees_rejected"),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::prop(),
        }),
    )
    .await;
    let rejected = rejected.result.expect("an addDecl result");
    assert_eq!(rejected["accepted"], json!(false), "{rejected}");
    freed_off_the_runtime(&sites, mark_after_accept, "a rejected addDecl").await;

    assert!(state.drop_session(&session).await, "the session was open");
    freed_off_the_runtime(&sites, mark, "addDecl and closing its session").await;
}

/// Opening a session copied the shared environment twice (its base, then its
/// overlay from the base) on the runtime, under a read hold, and `addDecl`
/// copied the session (its overlay) on the runtime, holding the session's
/// lock: each a whole environment. Both copies are made on the work pool now,
/// in its lock order. Fails when either copy moves back to the runtime.
#[tokio::test]
async fn sessions_are_copied_off_the_runtime() {
    let (env, sites) = Sites::record(Environment::with_prelude());
    let state = ServerState::new().with_env(env);

    let mark = sites.mark();
    let session = state.create_session().await.expect("open a session");
    made_off_the_runtime(&sites, mark, "opening a session");

    let mark = sites.mark();
    let accepted = handle_add_decl(
        &state,
        RequestId::Number(1),
        serde_json::from_value(json!({
            "session_id": session.to_string(),
            "decl": Declaration::Axiom {
                name: Name::from_string("runtime_frees_copied"),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            "require_foundational": false,
            "timeout_ms": HANG.as_millis() as u64,
        }))
        .expect("addDecl params"),
    )
    .await;
    let accepted = accepted.result.expect("an addDecl result");
    assert_eq!(accepted["accepted"], json!(true), "{accepted}");
    made_off_the_runtime(&sites, mark, "an addDecl");
}

/// `verifyFile`, `fillSorries` and `composeProof` set the shared environment
/// up (the logical prelude a file's replay needs, added where it is missing)
/// on the runtime, holding its write lock, and the kernel adds each inductive
/// transactionally: it copies the whole environment, then frees the copy
/// (review of 2026-10-19: four of each for an environment without that
/// prelude, 0.8 to 1.5 s in a debug build, and every environment a
/// `loadEnvironment` replace installs lacks it again). The set-up seeds on the
/// work pool now. Fails when it seeds on the runtime again.
#[tokio::test]
async fn the_file_methods_set_the_environment_up_off_the_runtime() {
    let (env, sites) = Sites::record(Environment::with_prelude());
    let state = ServerState::new().with_env(env);

    let mark = sites.mark();
    let answered = result_of(
        &state,
        "verifyFile",
        json!({
            "content": "theorem runtime_frees_seeded : True := by\n  sorry\n",
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert_eq!(answered["verified"], json!(false), "{answered}");
    made_off_the_runtime(&sites, mark, "verifyFile's set-up");
    freed_off_the_runtime(&sites, mark, "verifyFile's set-up").await;
}

/// Closing a session dropped it under the session map's write lock, on the
/// runtime, and a session holds a whole environment. Here the closed session
/// holds the last shares of a gated source (`free_gate.rs`), so its free lasts
/// until the test releases it; on this one-thread runtime, a free on the
/// runtime's thread can never be released.
#[tokio::test]
async fn closing_a_session_frees_it_off_the_runtime() {
    let (source, gate) = gated_source();
    let holders = Arc::downgrade(&source);
    let mut env = Environment::with_prelude();
    env.set_constant_source(source);
    let state = ServerState::new().with_env(env);
    let session = state.create_session().await.expect("open a session");
    // The shared environment lets its share go (freed off the runtime, on its
    // own): the session's two (its base and its overlay) are then the last.
    state.env.replace(Environment::with_prelude()).await;
    let give_up = Instant::now() + HANG;
    while holders.strong_count() != 2 {
        assert!(
            Instant::now() < give_up,
            "the replaced environment was never freed"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    assert!(state.drop_session(&session).await, "the session was open");
    let runtime = std::thread::current().id();
    gate.freeing().await;
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
        "the closed session was freed on the runtime's thread: the test could not release it"
    );
    assert_ne!(freed.on, runtime);
}

/// A save held the environment for reading while it wrote its file, past its
/// timeout. A writer queued behind the hold waited for the write, and, the
/// lock being write-preferring, so did every reader queued behind the writer:
/// a save to a pipe nobody reads made `check` and `getEnvironment` answer
/// their timeout errors. The hold now covers the encoding only. Here the save
/// writes to a named pipe the test reads only at the end: past its timeout it
/// waits on the pipe, and a replace and the readers after it are served
/// meanwhile. With the old hold the replace waited to the hang detector.
#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_save_past_its_timeout_keeps_no_writer_or_reader_waiting() {
    use super::concurrent_writers::{named_pipe, prelude_state_with, wait_until_idle};
    use crate::handlers::work::WorkPool;

    let state = prelude_state_with(Some(WorkPool::new(3)));
    let dir = tempfile::tempdir().expect("a scratch directory");
    let pipe = dir.path().join("save.fifo");
    named_pipe(&pipe);
    let mut replacement = Environment::new();
    replacement.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("runtime_frees_replaced"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    });
    let replacement_path = dir.path().join("replacement.bincode");
    replacement
        .save_to_file(&replacement_path)
        .expect("save the replacement");

    let save = sent(
        &state,
        "saveEnvironment",
        json!({ "path": pipe.to_string_lossy(), "timeout_ms": 300 }),
    )
    .await;
    assert_eq!(
        save.error.map(|e| e.code),
        Some(-32004),
        "the save waits on its pipe"
    );

    let replaced = result_of(
        &state,
        "loadEnvironment",
        json!({
            "path": replacement_path.to_string_lossy(),
            "replace": true,
            "replace_unchecked": true,
            "token": super::launch_token_of(&state),
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert_eq!(replaced["success"], json!(true), "{replaced}");
    let check = result_of(
        &state,
        "check",
        json!({ "code": "Type", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    assert_eq!(check["valid"], json!(true), "{check}");
    result_of(
        &state,
        "getEnvironment",
        json!({ "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;

    // End the save: read the pipe to its end.
    let read = tokio::task::spawn_blocking(move || std::fs::read(pipe).map(|bytes| bytes.len()));
    let written = tokio::time::timeout(HANG, read)
        .await
        .expect("the save writes its pipe within the hang detector")
        .expect("the reading thread")
        .expect("read the pipe");
    assert!(written > 0, "the save wrote nothing");
    wait_until_idle(&state).await;
}

// ---------------------------------------------------------------------------
// The searches stop at their deadline.
// ---------------------------------------------------------------------------

/// An environment where each scan of the searches finds one lemma: a
/// predicate premise selection relates to the goal `RfNat → Prop`, and a
/// proposition the `sat-pb` profile's keywords match. (The goal names only
/// constants some premise's statement names: MePo weighs a constant by how
/// rarely the premises name it, and one they never name outweighs the rest.)
fn searched_env() -> Environment {
    let mut env = Environment::new();
    for (name, type_) in [
        ("RfNat", Expr::sort(Level::succ(Level::zero()))),
        ("RfPred", Expr::arrow(rf_nat(), Expr::prop())),
        ("Sat.PB.runtime_frees_sound", Expr::prop()),
    ] {
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        });
    }
    env
}

fn rf_nat() -> Expr {
    Expr::const_(Name::from_string("RfNat"), vec![])
}

/// The names the searches return for `goal` under `profile`, under
/// `deadline`. What the search returned is read even when the deadline fired
/// (the work's answer is dropped then, but the scan's length is the point).
fn searched(
    goal: Expr,
    profile: crate::proof_state::ObligationDomainProfile,
    deadline: Option<Instant>,
) -> Vec<String> {
    let env = searched_env();
    let state = clean_elab::tactic::ProofState::new(env.clone(), goal);
    let mut found = Vec::new();
    let _ = clean_kernel::tc::run_until(deadline, || {
        let guidance = crate::proof_state::llm_guidance_for_goal_and_profile(
            &state,
            state.goals().front(),
            &env,
            profile,
        );
        found = guidance
            .relevant_lemmas
            .into_iter()
            .map(|lemma| lemma.name)
            .collect();
    });
    found
}

/// The searches' scans of every constant (premise selection, and a domain
/// profile's keyword scan) ran to their end past the request's deadline,
/// holding the work slot. Each stops at its first constant once the deadline
/// has passed. Premise selection is read through the general profile, which
/// scans nothing else; the `sat-pb` scan through a goal of `Prop`, which names
/// no constant, so premise selection finds nothing for it. Fails when either
/// scan's `poll_deadline` break is removed: that scan then finds its lemma.
#[test]
fn the_searches_stop_at_their_deadline() {
    use crate::proof_state::ObligationDomainProfile::{General, SatPb};
    let premises = || Expr::arrow(rf_nat(), Expr::prop());

    let premise = searched(premises(), General, None);
    assert_eq!(
        premise,
        vec!["RfPred".to_string()],
        "premise selection finds the predicate: this test's premise"
    );
    let profiled = searched(Expr::prop(), SatPb, None);
    assert_eq!(
        profiled,
        vec!["Sat.PB.runtime_frees_sound".to_string()],
        "the sat-pb scan finds its proposition, and premise selection nothing: this \
         test's premise"
    );

    let passed = Some(Instant::now());
    assert_eq!(
        (
            searched(premises(), General, passed),
            searched(Expr::prop(), SatPb, passed)
        ),
        (Vec::new(), Vec::new()),
        "(premise selection, the sat-pb scan) past their deadline"
    );
}
