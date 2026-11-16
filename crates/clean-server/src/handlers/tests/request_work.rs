// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The work pool's other promises (`handlers/work.rs`), each pinned by the
//! review of 2026-10-15 that found it broken: no request waits for a work slot
//! while it holds the environment, a request that makes no kernel check takes
//! no slot, a request renders from the environment its work checked in (one
//! read, never two), every wait is inside the request's timeout, a batch gives
//! its slot back at its deadline whatever it has left, nothing the deadline cut
//! short is reported as a verdict, and no request's work panics because its
//! deadline passed (the release profile aborts on a panic, so a caught one is a
//! server killed).
//!
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use crate::handlers::work::WorkPool;
use crate::handlers::*;
use crate::progress::ProgressSender;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::Environment;
use serde_json::json;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
const TIMEOUT: i32 = -32004;

fn prelude_state_with(work: Option<WorkPool>) -> Arc<ServerState> {
    let env = Environment::try_with_prelude().expect("try_with_prelude should succeed");
    let mut state = super::temp_rooted_state().with_env(env);
    if let Some(work) = work {
        state.work = work;
    }
    Arc::new(state)
}

/// `rfl` at a type whose two sides the kernel must compute: `Nat.rec`
/// unfolded `n` times.
fn slow_rfl(n: u64) -> String {
    format!(
        "(rfl : @Nat.rec (fun _ => Nat) 0 (fun n ih => n + 1 + ih) {n} = {})",
        n * (n + 1) / 2
    )
}

/// Wait until no work holds a slot: the abandoned work has ended.
async fn wait_until_idle(state: &ServerState) {
    let give_up = Instant::now() + HANG;
    while state.work.in_use() > 0 {
        assert!(Instant::now() < give_up, "the abandoned work never ended");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

/// Await a spawned request within the hang detector.
async fn answered(
    what: &str,
    request: tokio::task::JoinHandle<crate::rpc::Response>,
) -> crate::rpc::Response {
    tokio::time::timeout(HANG, request)
        .await
        .unwrap_or_else(|_| panic!("{what} was not answered within the hang detector"))
        .unwrap_or_else(|e| panic!("{what}'s task failed: {e}"))
}

/// `applyTactic` took the environment's read guard and then waited for a
/// work slot; every other pool request takes the slot first. The guard's lock
/// is write-preferring, so with a writer queued the two orders closed a cycle:
/// the request holding the slot waited for the guard behind the writer, the
/// writer for `applyTactic`'s guard, and `applyTactic` for the slot. Nothing on
/// the pool was answered until `applyTactic`'s own `timeout_ms` passed, and with
/// an hour's timeout the test below hung. With the slot taken first there is
/// no cycle: everything is answered once the slow check's deadline passes.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn apply_tactic_never_waits_for_a_slot_holding_the_environment() {
    let state = prelude_state_with(Some(WorkPool::new(1)));

    // A cached proof state whose goal `rfl` closes at once.
    let init: InitProofStateParams =
        serde_json::from_value(json!({"theorem": "Nat = Nat"})).expect("init params");
    let initialized = handle_init_proof_state(&state, RequestId::Number(0), init)
        .await
        .result
        .expect("the goal is stated");
    let state_id = initialized["state_id"]
        .as_str()
        .expect("a state id")
        .to_string();
    let goal_id = initialized["goals"][0]["goal_id"]
        .as_str()
        .expect("a goal id")
        .to_string();

    // The one slot runs work until its 3 s deadline, holding the guard.
    let s = Arc::clone(&state);
    let slow = tokio::spawn(async move {
        handle_check(
            &s,
            RequestId::Number(1),
            CheckParams {
                code: slow_rfl(60_000),
                timeout_ms: Some(3_000),
            },
        )
        .await
    });
    let give_up = Instant::now() + HANG;
    while state.work.in_use() < 1 {
        assert!(
            Instant::now() < give_up,
            "the slow check never took its slot"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }

    // A request queued for the slot (with the hang detector for its timeout:
    // it waits behind the slow check and the writer).
    let s = Arc::clone(&state);
    let queued = tokio::spawn(async move {
        handle_get_type(
            &s,
            RequestId::Number(2),
            GetTypeParams {
                expr: "Nat".to_string(),
                timeout_ms: Some(HANG.as_millis() as u64),
            },
        )
        .await
    });
    tokio::time::sleep(Duration::from_millis(100)).await;

    // applyTactic, with a timeout far past the hang detector.
    let s = Arc::clone(&state);
    let apply: ApplyTacticParams = serde_json::from_value(json!({
        "state_id": state_id,
        "goal_id": goal_id,
        "tactic": "rfl",
        "timeout_ms": 3_600_000u64,
    }))
    .expect("apply params");
    let tactic =
        tokio::spawn(async move { handle_apply_tactic(&s, RequestId::Number(3), apply).await });
    tokio::time::sleep(Duration::from_millis(100)).await;

    // A writer queued on the environment's lock (verifyFile initializes the
    // shared environment under the write lock).
    let s = Arc::clone(&state);
    let writer = tokio::spawn(async move {
        handle_verify_file(
            &s,
            RequestId::Number(4),
            VerifyFileParams {
                content: "theorem t : True := by\n  trivial\n".to_string(),
                proof: None,
                timeout_ms: Some(60_000),
            },
        )
        .await
    });

    let _ = answered("the slow check", slow).await;
    let tactic = answered("applyTactic", tactic).await;
    assert!(
        tactic.error.is_none(),
        "rfl closes `Nat = Nat`: {:?}",
        tactic.error
    );
    let queued = answered("the queued getType", queued).await;
    assert!(queued.error.is_none(), "{:?}", queued.error);
    let writer = answered("the writer", writer).await;
    assert!(writer.error.is_none(), "{:?}", writer.error);
    wait_until_idle(&state).await;
}

/// `getType` took no timeout and ran its work without a deadline, so a slow one
/// held its work slot until the work ended and then answered its type, late
/// (9 s for one of these in a debug build). A few of them filled every slot,
/// and a request that carried a timeout answered the timeout error while it
/// waited for one. Now each `getType` answers the timeout error at its own
/// deadline and its work stops there, so the slots come back and the queued
/// request is served. The queued check's one-minute timeout is the hang
/// detector.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn slow_get_types_give_their_slots_back_at_their_deadline() {
    let ids = [1i64, 2];
    let slots = ids.len();
    let state = prelude_state_with(Some(WorkPool::new(slots)));
    let slow: Vec<_> = ids
        .into_iter()
        .map(|i| {
            let s = Arc::clone(&state);
            let params: GetTypeParams =
                serde_json::from_value(json!({"expr": slow_rfl(60_000), "timeout_ms": 300}))
                    .expect("getType params");
            tokio::spawn(async move { handle_get_type(&s, RequestId::Number(i), params).await })
        })
        .collect();
    let give_up = Instant::now() + HANG;
    while state.work.in_use() < slots {
        assert!(
            Instant::now() < give_up,
            "the slow getTypes never took their slots"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }

    let queued = handle_check(
        &state,
        RequestId::Number(99),
        CheckParams {
            code: "Type".to_string(),
            timeout_ms: Some(HANG.as_millis() as u64),
        },
    )
    .await;
    assert!(
        queued.error.is_none(),
        "the queued check must be served once the slow getTypes' deadlines pass: {:?}",
        queued.error
    );
    for (i, request) in slow.into_iter().enumerate() {
        let response = answered(&format!("slow getType {i}"), request).await;
        assert_eq!(
            response.error.map(|e| e.code),
            Some(TIMEOUT),
            "a getType past its deadline answers the timeout error"
        );
    }
    wait_until_idle(&state).await;
}

/// `getProofState` of an unsolved state makes no kernel check: its trust
/// summary is its ledger's. It took a work slot all the same, so on a busy
/// pool it answered the timeout error where it had answered at once (review of
/// 2026-10-15: after 1.0 s, against 4 ms on the base). But its default `llm`
/// snapshot selects premises from the whole environment, which ran on the
/// runtime's thread from then on (R36). It takes a slot when its work checks a
/// proof (a solved state) or searches (an unsolved state's `llm` snapshot, or
/// any snapshot with a Mathverse corpus installed), and only then. Here the
/// test holds the pool's only slot: the unsolved state's `compact` snapshot,
/// rendering only, is answered (its one-minute timeout is the hang detector),
/// and its `llm` snapshot and the solved state, which must wait for the slot,
/// answer the timeout error at theirs.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn get_proof_state_takes_a_work_slot_only_to_check_or_search() {
    let state = prelude_state_with(Some(WorkPool::new(1)));
    let stated = |theorem: &str| -> InitProofStateParams {
        serde_json::from_value(json!({ "theorem": theorem })).expect("init params")
    };
    let unsolved = handle_init_proof_state(&state, RequestId::Number(0), stated("Nat = Nat"))
        .await
        .result
        .expect("the goal is stated");
    assert_eq!(unsolved["is_solved"], json!(false));
    let solved = handle_apply_tactic(
        &state,
        RequestId::Number(0),
        serde_json::from_value(json!({
            "state_id": unsolved["state_id"],
            "goal_id": unsolved["goals"][0]["goal_id"],
            "tactic": "rfl",
        }))
        .expect("apply params"),
    )
    .await
    .result
    .expect("rfl closes `Nat = Nat`");
    assert_eq!(solved["is_solved"], json!(true));

    let slot = state.work.slot().await.expect("the pool's only slot");
    let viewed =
        |state_id: &serde_json::Value, format: &str, timeout_ms: u64| -> GetProofStateParams {
            serde_json::from_value(json!({
                "state_id": state_id,
                "format": format,
                "timeout_ms": timeout_ms,
            }))
            .expect("getProofState params")
        };
    let open = handle_get_proof_state(
        &state,
        RequestId::Number(1),
        viewed(&unsolved["state_id"], "compact", HANG.as_millis() as u64),
    )
    .await;
    let guided = handle_get_proof_state(
        &state,
        RequestId::Number(2),
        viewed(&unsolved["state_id"], "llm", 300),
    )
    .await;
    let closed = handle_get_proof_state(
        &state,
        RequestId::Number(3),
        viewed(&solved["new_state_id"], "llm", 300),
    )
    .await;
    drop(slot);
    assert!(
        open.error.is_none(),
        "an unsolved state's compact getProofState waited for a work slot: {:?}",
        open.error
    );
    assert_eq!(
        guided.error.map(|e| e.code),
        Some(TIMEOUT),
        "an unsolved state's llm snapshot selects premises from the environment on the pool, \
         so it waits for a slot"
    );
    assert_eq!(
        closed.error.map(|e| e.code),
        Some(TIMEOUT),
        "a solved state's getProofState re-checks its proof on the pool, so it waits for a slot"
    );
}

/// `proofState.openObligation` checked its goal on the pool holding the
/// environment, let it go, and read it again to render the new state. A writer
/// that queued for the environment during the check ran in between, so the
/// request answered at the writer's pace, past its own timeout (review of
/// 2026-10-15: after 14.9 s with `timeout_ms: 12000`, behind a
/// `loadEnvironment` merge), and rendered against an environment other than
/// the one it checked in. One read is held across the check and the rendering
/// now. Here a writer queued during the check keeps the environment until the
/// request has answered: a second read would never be granted.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn open_obligation_renders_in_the_environment_it_checked() {
    let state = prelude_state_with(None);
    let goal = super::request_deadline::slow_kernel_goal(&state);
    let params: OpenObligationParams = serde_json::from_value(json!({
        "schema_version": crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION,
        "environment_id": "one-read",
        "domain_profile": "general",
        "goal": {"pretty": "slow", "expr": goal},
        "trust_policy": "constructive-only",
        "ttl_sec": 60,
        "max_states": 4,
        "min_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
        "max_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
        "timeout_ms": HANG.as_millis() as u64,
    }))
    .expect("openObligation params");
    let s = Arc::clone(&state);
    let request =
        tokio::spawn(async move { handle_open_obligation(&s, RequestId::Number(1), params).await });

    // The goal's check holds the environment (about 3 s in a debug build).
    let give_up = Instant::now() + HANG;
    while state.env.try_write().is_ok() {
        assert!(
            Instant::now() < give_up,
            "the goal's check never held the environment"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    let (release, released) = tokio::sync::oneshot::channel::<()>();
    let env = state.env.clone();
    let writer = tokio::spawn(async move {
        let _written = env.write().await;
        let _ = released.await;
    });

    let response = answered("openObligation behind a queued writer", request).await;
    let _ = release.send(());
    tokio::time::timeout(HANG, writer)
        .await
        .expect("the writer ends once released")
        .expect("the writer's task");
    assert!(
        response.error.is_none(),
        "the goal is a proposition: {:?}",
        response.error
    );
    let opened = response.result.expect("an opened obligation");
    assert!(
        opened["initial_snapshot"].is_object(),
        "the answer carries the new state's snapshot: {opened}"
    );
}

/// `addDecl` looked its session up before its timeout started, so behind
/// another session's `addDecl`, which held the session map's write lock
/// across its check, it waited past its own `timeout_ms` (review of
/// 2026-10-15: 2.9 s with `timeout_ms: 300`). Every wait is inside the timeout
/// now: for the session map (held only to look a session up since R34) and
/// for the session's own lock (held across another `addDecl`'s check). Here
/// the test holds each in turn.
#[tokio::test]
async fn add_decl_waits_for_its_session_inside_its_timeout() {
    let state = prelude_state_with(None);
    let session = state.create_session().await.expect("open a session");
    let name = clean_kernel::Name::from_string("map_held_axiom");
    let params: AddDeclParams = serde_json::from_value(json!({
        "session_id": session.to_string(),
        "decl": clean_kernel::Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        },
        "require_foundational": false,
        "timeout_ms": 300,
    }))
    .expect("addDecl params");
    let handle = state.session(&session).await.expect("the session is open");

    let map = state.sessions.write().await;
    let response = tokio::time::timeout(
        HANG,
        handle_add_decl(&state, RequestId::Number(1), params.clone()),
    )
    .await
    .expect("addDecl answers while the session map is held");
    drop(map);
    assert_eq!(response.error.map(|e| e.code), Some(TIMEOUT));

    let held = handle.lock().await;
    let response =
        tokio::time::timeout(HANG, handle_add_decl(&state, RequestId::Number(2), params))
            .await
            .expect("addDecl answers while its session is held");
    drop(held);
    assert_eq!(response.error.map(|e| e.code), Some(TIMEOUT));
    assert!(
        !handle.lock().await.contains(&name),
        "a request that timed out adds nothing to the session"
    );
}

/// A `batchCheck` read neither the latch nor the clock between items, so past
/// its deadline it went on through every item left, each failing fast in
/// degraded mode, holding its slot and the environment's read guard all the
/// while (about a millisecond an item in a debug build: 200,000 items run
/// minutes past the hang detector). No item starts past the deadline now.
#[tokio::test]
async fn batch_check_gives_its_slot_back_at_its_deadline_whatever_is_left() {
    let state = prelude_state_with(None);
    let params = BatchCheckParams {
        items: (0..200_000)
            .map(|i| BatchCheckItem {
                id: i.to_string(),
                code: slow_rfl(20_000),
            })
            .collect(),
        use_gpu: false,
        timeout_ms: Some(300),
    };
    let response = handle_batch_check(&state, RequestId::Number(1), params, None).await;
    assert_eq!(response.error.map(|e| e.code), Some(TIMEOUT));
    wait_until_idle(&state).await;
}

/// Between the work's latch firing and the request's timer, `batchCheck`
/// forwarded the result of an item the deadline had cut short: a valid item
/// reported `valid: false` ("type checking interrupted") on the progress
/// stream. Every item here is valid, so any `valid: false` is a wrong verdict.
/// The window is a race; the sweep of deadlines crosses it (the review saw it
/// once in 21 runs) and can only fail when a wrong verdict is reported.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn batch_check_reports_no_verdict_its_deadline_cut_short() {
    let state = prelude_state_with(None);
    let mut wrong = Vec::new();
    for timeout_ms in (60..=400).step_by(17) {
        let params = BatchCheckParams {
            items: (0..100)
                .map(|i| BatchCheckItem {
                    id: i.to_string(),
                    code: slow_rfl(3_000),
                })
                .collect(),
            use_gpu: false,
            timeout_ms: Some(timeout_ms),
        };
        let (tx, mut rx) = tokio::sync::mpsc::channel(100_000);
        let progress = ProgressSender::new(RequestId::Number(1), tx);
        let _ = handle_batch_check(&state, RequestId::Number(1), params, Some(progress)).await;
        while let Ok(update) = rx.try_recv() {
            if let Some(details) = update.details {
                if details["valid"] == json!(false) {
                    wrong.push((timeout_ms, details));
                }
            }
        }
        wait_until_idle(&state).await;
    }
    assert!(wrong.is_empty(), "wrong per-item verdicts: {wrong:?}");
}

/// `proveTLA` built its engine under the request's deadline, and a deadline
/// that had passed refused the engine's fixed theories and failed their
/// `expect`s: a panic in the work at every timeout tried, which a release
/// build (`panic = "abort"`) turned into a killed server. The engine's seeding
/// runs with the deadline suspended now.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn prove_tla_work_never_panics_at_a_short_deadline() {
    let state = prelude_state_with(None);
    for timeout_ms in [0u64, 1, 2, 3, 5, 8, 13, 21] {
        let params = ProveTlaParams {
            obligation: clean_tla::TlaObligation::new(clean_tla::encoding::TlaFormula::True),
            timeout_ms: Some(timeout_ms),
        };
        let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
        wait_until_idle(&state).await;
        assert_eq!(
            state.work.panics(),
            0,
            "proveTLA at timeout_ms {timeout_ms}: its work panicked (answer {:?})",
            response.error
        );
        if let Some(error) = response.error {
            assert_eq!(error.code, TIMEOUT, "{error:?}");
        }
    }
}

/// The class `proveTLA` belonged to: every pool request at deadlines that land
/// at different points of its work. A caught panic is a release server
/// aborted, so the pool's count must stay zero.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn no_request_work_panics_at_a_short_deadline() {
    let state = prelude_state_with(None);
    let init: InitProofStateParams =
        serde_json::from_value(json!({"theorem": "forall (n : Nat), n + 0 = n"}))
            .expect("init params");
    let initialized = handle_init_proof_state(&state, RequestId::Number(0), init)
        .await
        .result
        .expect("the goal is stated");
    let sid = initialized["state_id"]
        .as_str()
        .expect("a state id")
        .to_string();
    let gid = initialized["goals"][0]["goal_id"]
        .as_str()
        .expect("a goal id")
        .to_string();
    let file = "theorem t (n : Nat) : n + 0 = n := by\n  sorry\n".to_string();
    let goal = "forall (n : Nat), n + 0 = n";
    // The goal as a kernel term, for the requests that take one.
    let target = initialized["goals"][0]["target"].clone();
    // A solved state, for the requests that re-check a closed proof.
    let init: InitProofStateParams =
        serde_json::from_value(json!({"theorem": "Nat = Nat"})).expect("init params");
    let solving = handle_init_proof_state(&state, RequestId::Number(0), init)
        .await
        .result
        .expect("the goal is stated");
    let solved = handle_apply_tactic(
        &state,
        RequestId::Number(0),
        serde_json::from_value(json!({
            "state_id": solving["state_id"],
            "goal_id": solving["goals"][0]["goal_id"],
            "tactic": "rfl",
        }))
        .expect("apply params"),
    )
    .await
    .result
    .expect("rfl closes `Nat = Nat`")["new_state_id"]
        .clone();
    let session = state
        .create_session()
        .await
        .expect("open a session")
        .to_string();
    let axiom = clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("sweep_axiom"),
        level_params: vec![],
        type_: serde_json::from_value(target.clone()).expect("a kernel term"),
    };
    let saved = std::env::temp_dir().join(format!(
        "clean_test_sweep_merge_{}.bincode",
        std::process::id()
    ));
    let mut merged = Environment::new();
    merged.add_decl_unchecked(axiom.clone());
    merged.save_to_file(&saved).expect("save the environment");
    let modules = tempfile::tempdir().expect("a module directory");
    std::fs::write(
        modules.path().join("ServerFixture.olean"),
        super::concurrent_writers::fixture_module(),
    )
    .expect("write the module");
    let mut panicked = Vec::new();
    for t in [0u64, 1, 3, 8, 21] {
        macro_rules! probe {
            ($name:expr, $call:expr) => {{
                let before = state.work.panics();
                let _ = $call.await;
                wait_until_idle(&state).await;
                if state.work.panics() > before {
                    panicked.push(format!("{} at timeout_ms {t}", $name));
                }
            }};
        }
        probe!(
            "check",
            handle_check(
                &state,
                RequestId::Number(1),
                CheckParams {
                    code: "theorem t (n : Nat) : n + 0 = n := rfl".into(),
                    timeout_ms: Some(t),
                },
            )
        );
        probe!(
            "getType",
            handle_get_type(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"expr": "fun (n : Nat) => n + 0", "timeout_ms": t}))
                    .expect("params"),
            )
        );
        probe!(
            "proofState.openObligation",
            handle_open_obligation(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "schema_version": crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION,
                    "environment_id": "sweep",
                    "domain_profile": "general",
                    "goal": {"pretty": goal, "expr": target},
                    "trust_policy": "constructive-only",
                    "ttl_sec": 60,
                    "max_states": 4,
                    "min_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
                    "max_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "getProofState",
            handle_get_proof_state(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"state_id": solved, "timeout_ms": t}))
                    .expect("params"),
            )
        );
        probe!(
            "extractProof",
            handle_extract_proof(
                &state,
                RequestId::Number(1),
                serde_json::from_value(
                    json!({"state_id": solved, "format": "all", "timeout_ms": t})
                )
                .expect("params"),
            )
        );
        probe!(
            "applyTactic on a solved state",
            handle_apply_tactic(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "state_id": solved,
                    "goal_id": "g0",
                    "tactic": "rfl",
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "addDecl",
            handle_add_decl(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "session_id": session,
                    "decl": axiom,
                    "require_foundational": false,
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "loadEnvironment",
            handle_load_environment(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "path": saved.to_string_lossy(),
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "importModule",
            handle_import_module(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "module": "ServerFixture",
                    "search_paths": [modules.path().to_string_lossy()],
                    "timeout_ms": t,
                    // Without it the request is refused before it loads.
                    "token": super::launch_token_of(&state),
                }))
                .expect("params"),
            )
        );
        probe!(
            "batchCheck",
            handle_batch_check(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "items": [{"id": "a", "code": "fun (n : Nat) => n + 0"}],
                    "timeout_ms": t,
                }))
                .expect("params"),
                None,
            )
        );
        probe!(
            "prove",
            handle_prove(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"goal": goal, "timeout_ms": t})).expect("params"),
            )
        );
        probe!(
            "getPremises",
            handle_get_premises(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"goal": goal, "timeout_ms": t})).expect("params"),
            )
        );
        probe!(
            "searchProof",
            handle_search_proof(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "theorem": goal,
                    "strategy": "auto_only",
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "verifyProof",
            handle_verify_proof(
                &state,
                RequestId::Number(1),
                VerifyProofParams {
                    goal: goal.into(),
                    proof: "intro n\nsimp".into(),
                    context: None,
                    timeout_ms: Some(t),
                },
            )
        );
        probe!(
            "verifyFile",
            handle_verify_file(
                &state,
                RequestId::Number(1),
                VerifyFileParams {
                    content: file.clone(),
                    proof: Some("simp".into()),
                    timeout_ms: Some(t),
                },
            )
        );
        probe!(
            "fillSorries",
            handle_fill_sorries(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"content": file, "timeout_ms": t})).expect("params"),
            )
        );
        probe!(
            "composeProof",
            handle_compose_proof(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "content": file,
                    "replacements": [],
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "initProofState",
            handle_init_proof_state(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({"theorem": goal, "timeout_ms": t})).expect("params"),
            )
        );
        for tactic in ["intro n", "simp", "omega", "decide", "rfl", "aesop"] {
            probe!(
                format!("applyTactic {tactic}"),
                handle_apply_tactic(
                    &state,
                    RequestId::Number(1),
                    serde_json::from_value(json!({
                        "state_id": sid,
                        "goal_id": gid,
                        "tactic": tactic,
                        "timeout_ms": t,
                    }))
                    .expect("params"),
                )
            );
        }
        probe!(
            "batchApplyTactic",
            handle_batch_apply_tactic(
                &state,
                RequestId::Number(1),
                serde_json::from_value(json!({
                    "items": [{"id": "a", "state_id": sid, "goal_id": gid, "tactic": "simp"}],
                    "timeout_ms": t,
                }))
                .expect("params"),
            )
        );
        probe!(
            "verifyC",
            handle_verify_c(
                &state,
                RequestId::Number(1),
                VerifyCParams {
                    code: "//@ requires n >= 0;\n//@ ensures \\result >= 0;\nint f(int n) { return n; }\n"
                        .into(),
                    fail_unknown: false,
                    include_details: false,
                    timeout_ms: Some(t),
                },
                None,
            )
        );
        probe!(
            "proveTLA",
            handle_prove_tla(
                &state,
                RequestId::Number(1),
                ProveTlaParams {
                    obligation: clean_tla::TlaObligation::new(
                        clean_tla::encoding::TlaFormula::True
                    ),
                    timeout_ms: Some(t),
                },
            )
        );
        probe!(
            "batchProveTLA",
            handle_batch_prove_tla(
                &state,
                RequestId::Number(1),
                BatchProveTlaParams {
                    items: vec![BatchProveTlaItem {
                        id: "a".into(),
                        obligation: clean_tla::TlaObligation::new(
                            clean_tla::encoding::TlaFormula::True
                        ),
                    }],
                    threads: 1,
                    timeout_ms: Some(t),
                },
                None,
            )
        );
    }
    let _ = std::fs::remove_file(&saved);
    assert!(
        panicked.is_empty(),
        "request work panicked past its deadline (a release server aborts): {panicked:?}"
    );
}
