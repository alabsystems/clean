// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A request whose work outlasts its `timeout_ms` answers the timeout error,
//! other requests are served while it runs, and its abandoned work ends
//! (`handlers/work.rs`).
//!
//! Each test sends the slow request first and a fast `check` 50 ms later, on
//! the test's single-threaded runtime. Before the work pool, the slow request's
//! synchronous work held that thread until it returned: the fast request
//! waited for it, and the slow one answered its result, late, instead of the
//! timeout error. Every wait for something that must happen is a one-minute
//! hang detector, never a latency budget.

use crate::handlers::*;
use crate::rpc::Response;
use clean_kernel::cert::{archive_cert_with_algorithm_stats, CompressionAlgorithm, ProofCert};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use serde_json::json;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
const TIMEOUT: i32 = -32004;

/// The slow requests' timeout.
const TIMEOUT_MS: u64 = 300;

fn prelude_state() -> Arc<ServerState> {
    let env = Environment::try_with_prelude().expect("try_with_prelude should succeed");
    Arc::new(super::temp_rooted_state().with_env(env))
}

/// `rfl` at a type whose two sides the kernel must compute: `Nat.rec`
/// unfolded `n` times. Elaborating it takes about a second at 20,000 in a
/// release build, and its time grows with `n`.
fn slow_rfl(n: u64) -> String {
    format!(
        "(rfl : @Nat.rec (fun _ => Nat) 0 (fun n ih => n + 1 + ih) {n} = {})",
        n * (n + 1) / 2
    )
}

/// A goal whose elaboration is `slow_rfl`'s.
fn slow_goal() -> String {
    let r = slow_rfl(20_000);
    format!("{r} = {r}")
}

/// A Lean file whose one theorem's statement is `slow_goal`.
fn slow_file() -> String {
    format!("theorem slow : {} := by\n  rfl\n", slow_goal())
}

/// `Nat.rec` unfolded 60,000 times, and the number it computes.
const BIG: &str = "@Nat.rec (fun _ => Nat) 0 (fun n ih => n + 1 + ih) 60000";
const BIG_VALUE: u64 = 1_800_030_000;

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

/// A theorem `slow : BIG = BIG_VALUE` proved by `Eq.refl BIG`: stating it
/// computes nothing, and the kernel accepts the proof only by computing `BIG`.
fn slow_theorem(state: &ServerState) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string("slow"),
        level_params: vec![],
        type_: elaborated(state, &format!("{BIG} = {BIG_VALUE}")),
        value: elaborated(state, &format!("@Eq.refl Nat ({BIG})")),
    }
}

/// `Prop`, reached through `Nat.rec` unfolded 60,000 times twice over.
const SLOW_PROP: &str = "@Nat.rec (fun _ => Type) \
    (@Nat.rec (fun _ => Type) Prop (fun _ ih => ih) 60000) (fun _ ih => ih) 60000";

/// `(fun (T : Type) (x : T) => x) SLOW_PROP (Nat = Nat)`: a goal that is a
/// proposition only once the kernel has reduced its type 120,000 steps (one
/// 60,000-step level took 1.65 s in a debug build). Building it computes
/// nothing.
pub(super) fn slow_kernel_goal(state: &ServerState) -> Expr {
    Expr::app(
        Expr::app(
            elaborated(state, "fun (T : Type) (x : T) => x"),
            elaborated(state, SLOW_PROP),
        ),
        elaborated(state, "Nat = Nat"),
    )
}

/// `(fun x : Prop => x x) (fun x : Prop => x x)`: reduces to itself forever.
fn omega() -> Expr {
    let prop = Expr::sort(Level::zero());
    let self_app = Expr::lam(
        BinderInfo::Default,
        prop,
        Expr::app(Expr::bvar(0), Expr::bvar(0)),
    );
    Expr::app(self_app.clone(), self_app)
}

/// A certificate for `Prop` whose `DefEq` step asks the verifier to reduce
/// `omega`: its check never ends on its own.
fn endless_cert() -> (ProofCert, Expr) {
    let cert = ProofCert::DefEq {
        inner: Arc::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(omega()),
        actual_type: Box::new(Expr::sort(Level::succ(Level::zero()))),
        eq_steps: vec![],
    };
    (cert, Expr::sort(Level::zero()))
}

/// A fast request, answered: when it was.
async fn fast_check(state: &ServerState) -> Instant {
    let response = handle_check(
        state,
        RequestId::Number(99),
        CheckParams {
            code: "Type".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        response.error.is_none(),
        "the fast request failed: {:?}",
        response.error
    );
    Instant::now()
}

/// Send the slow request, and the fast one once the slow one has the
/// runtime. Returns the slow response and whether the fast one was answered
/// first.
macro_rules! race {
    ($state:expr, |$s:ident| $slow:expr) => {{
        let state: Arc<ServerState> = $state;
        let slow_state = Arc::clone(&state);
        let slow = tokio::spawn(async move {
            let $s: &ServerState = &slow_state;
            let response: Response = $slow.await;
            (response, Instant::now())
        });
        tokio::time::sleep(Duration::from_millis(50)).await;
        let fast_answered = fast_check(&state).await;
        let (response, slow_answered) = tokio::time::timeout(HANG, slow)
            .await
            .expect("the slow request answers within the hang detector")
            .expect("the slow request's task");
        (state, response, fast_answered < slow_answered)
    }};
}

fn assert_timed_out(response: &Response, fast_first: bool) {
    let code = response.error.as_ref().map(|error| error.code);
    assert_eq!(
        code,
        Some(TIMEOUT),
        "the request must answer the timeout error, not {response:?}"
    );
    assert!(
        fast_first,
        "the fast request must be served while the slow one runs"
    );
}

/// The abandoned work has ended: its pool slot is free again.
async fn wait_until_idle(state: &ServerState) {
    let give_up = Instant::now() + HANG;
    while state.work.in_use() > 0 {
        assert!(Instant::now() < give_up, "the abandoned work never ended");
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}

#[tokio::test]
async fn check_answers_its_timeout_and_its_work_ends() {
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_check(
        s,
        RequestId::Number(1),
        CheckParams {
            code: slow_rfl(60_000),
            timeout_ms: Some(TIMEOUT_MS),
        },
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn check_without_a_deadline_problem_is_unchanged() {
    // The same kind of term, small: the answer is the answer it always was.
    let state = prelude_state();
    let response = handle_check(
        &state,
        RequestId::Number(1),
        CheckParams {
            code: slow_rfl(100),
            timeout_ms: None,
        },
    )
    .await;
    let result: CheckResult =
        serde_json::from_value(response.result.expect("a result")).expect("a check result");
    assert!(result.valid, "{:?}", result.errors);
}

#[tokio::test]
async fn get_type_answers_its_timeout_and_its_work_ends() {
    // Until 2026-10-15 getType took no timeout and ran without a deadline: it
    // answered the type minutes later, and held its slot until then.
    let params: GetTypeParams =
        serde_json::from_value(json!({"expr": slow_rfl(60_000), "timeout_ms": TIMEOUT_MS}))
            .expect("getType params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_get_type(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn open_obligation_answers_its_timeout_and_opens_nothing() {
    // Inferring the goal's type ran on the runtime worker with no deadline.
    let state = prelude_state();
    let goal = slow_kernel_goal(&state);
    let params: OpenObligationParams = serde_json::from_value(json!({
        "schema_version": crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION,
        "environment_id": "slow",
        "domain_profile": "general",
        "goal": {"pretty": "slow", "expr": goal},
        "trust_policy": "constructive-only",
        "ttl_sec": 60,
        "max_states": 4,
        "min_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
        "max_schema_version": crate::proof_state::PROOF_STATE_SCHEMA_VERSION,
        "timeout_ms": TIMEOUT_MS,
    }))
    .expect("openObligation params");
    let (state, response, fast_first) = race!(state, |s| handle_open_obligation(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    assert_eq!(
        state.proof_cache.len(),
        0,
        "an interrupted open caches no state"
    );
}

/// The cached state `rfl` leaves on `BIG = BIG_VALUE`: solved, and its closed
/// proof re-checks only by computing `BIG` (about 3 s in a debug build). Its id.
async fn solved_slow_state(state: &ServerState) -> String {
    let (state_id, goal_id) = slow_rfl_goal(state).await;
    // Setting up is work, not a wait for an answer: ten minutes of it.
    let params: ApplyTacticParams = serde_json::from_value(json!({
        "state_id": state_id, "goal_id": goal_id, "tactic": "rfl", "timeout_ms": 600_000u64
    }))
    .expect("apply params");
    let applied = handle_apply_tactic(state, RequestId::Number(0), params).await;
    let applied = applied.result.expect("rfl answers");
    assert_eq!(
        applied["is_solved"],
        json!(true),
        "rfl solves the goal: {applied}"
    );
    applied["new_state_id"]
        .as_str()
        .expect("a new state id")
        .to_string()
}

#[tokio::test]
async fn get_proof_state_answers_its_timeout_and_its_work_ends() {
    // A solved state's trust summary re-checks its closed proof in the kernel;
    // that ran on the runtime worker with no deadline.
    let state = prelude_state();
    let solved = solved_slow_state(&state).await;
    let params: GetProofStateParams =
        serde_json::from_value(json!({"state_id": solved, "timeout_ms": TIMEOUT_MS}))
            .expect("getProofState params");
    let (state, response, fast_first) = race!(state, |s| handle_get_proof_state(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn extract_proof_answers_its_timeout_and_its_work_ends() {
    // The kernel's re-check of the closed proof (and its certificate) ran on
    // the runtime worker with no deadline; one cut short would have read
    // `verified: false`.
    let state = prelude_state();
    let solved = solved_slow_state(&state).await;
    let params: ExtractProofParams = serde_json::from_value(
        json!({"state_id": solved, "format": "certificate", "timeout_ms": TIMEOUT_MS}),
    )
    .expect("extractProof params");
    let (state, response, fast_first) = race!(state, |s| handle_extract_proof(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn apply_tactic_on_a_solved_state_answers_its_timeout() {
    // A goal id the solved state no longer has: the answer carries the state's
    // trust summary, which re-checks its closed proof. That ran on the runtime
    // worker after the slot was taken, with no deadline.
    let state = prelude_state();
    let solved = solved_slow_state(&state).await;
    let params: ApplyTacticParams = serde_json::from_value(json!({
        "state_id": solved, "goal_id": "g0", "tactic": "rfl", "timeout_ms": TIMEOUT_MS
    }))
    .expect("apply params");
    let (state, response, fast_first) = race!(state, |s| handle_apply_tactic(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn add_decl_answers_its_timeout_and_keeps_nothing() {
    // The kernel's check ran on the runtime worker, holding the session map's
    // write lock, bounded only by `heartbeat_limit` (none at 0).
    let state = prelude_state();
    let session = state.create_session().await.expect("open a session");
    let params: AddDeclParams = serde_json::from_value(json!({
        "session_id": session.to_string(),
        "decl": slow_theorem(&state),
        "heartbeat_limit": 0,
        "timeout_ms": TIMEOUT_MS,
    }))
    .expect("addDecl params");
    let (state, response, fast_first) =
        race!(state, |s| handle_add_decl(s, RequestId::Number(1), params));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    let session = state
        .session(&session)
        .await
        .expect("the session is still open");
    let kept = session.lock().await.contains(&Name::from_string("slow"));
    assert!(!kept, "an interrupted check adds nothing to the session");
}

#[tokio::test]
async fn load_environment_merge_answers_its_timeout_and_merges_nothing() {
    // A merge re-checks every declaration it loads. It ran on the runtime
    // worker holding the environment's write lock, with no deadline. (It works
    // on a copy now and takes the write lock only to publish:
    // `concurrent_writers.rs` pins that a reader is served meanwhile.)
    let state = prelude_state();
    let mut saved = Environment::try_with_prelude().expect("try_with_prelude should succeed");
    saved.add_decl_unchecked(slow_theorem(&state));
    let path = std::env::temp_dir().join(format!(
        "clean_test_slow_merge_{}.bincode",
        std::process::id()
    ));
    saved.save_to_file(&path).expect("save the environment");
    let params: LoadEnvironmentParams = serde_json::from_value(json!({
        "path": path.to_string_lossy(),
        "timeout_ms": TIMEOUT_MS,
    }))
    .expect("loadEnvironment params");

    let slow_state = Arc::clone(&state);
    let slow = tokio::spawn(async move {
        let response = handle_load_environment(&slow_state, RequestId::Number(1), params).await;
        (response, Instant::now())
    });
    tokio::time::sleep(Duration::from_millis(50)).await;
    let metrics = handle_get_metrics(&state, RequestId::Number(99)).await;
    assert!(metrics.error.is_none(), "{:?}", metrics.error);
    let fast_answered = Instant::now();
    let (response, slow_answered) = tokio::time::timeout(HANG, slow)
        .await
        .expect("the merge answers within the hang detector")
        .expect("the merge's task");
    let _ = std::fs::remove_file(&path);
    assert_timed_out(&response, fast_answered < slow_answered);
    wait_until_idle(&state).await;
    assert!(
        state
            .env
            .read()
            .await
            .get_const(&Name::from_string("slow"))
            .is_none(),
        "an interrupted merge merges nothing"
    );
}

#[tokio::test]
async fn batch_check_stops_at_its_deadline() {
    // Unbounded, 200 such items run far past the hang detector in a debug
    // build; the batch must stop at its deadline for its slot to come back.
    let items: Vec<_> = (0..200)
        .map(|i| json!({"id": i.to_string(), "code": slow_rfl(20_000)}))
        .collect();
    let params: BatchCheckParams =
        serde_json::from_value(json!({"items": items, "timeout_ms": TIMEOUT_MS}))
            .expect("batch params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_batch_check(
        s,
        RequestId::Number(1),
        params,
        None
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn prove_answers_its_timeout_and_its_work_ends() {
    let params: ProveParams =
        serde_json::from_value(json!({"goal": slow_goal(), "timeout_ms": TIMEOUT_MS}))
            .expect("prove params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_prove(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn verify_cert_stops_at_its_deadline() {
    // The check never ends on its own: the slot coming back is the deadline's.
    let (cert, expr) = endless_cert();
    let params = VerifyCertParams {
        cert,
        expr,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_cert(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn verify_cert_archive_stops_at_its_deadline() {
    let (cert, expr) = endless_cert();
    let (archive, _) =
        archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4).expect("archive");
    let params = VerifyCertArchiveParams {
        archive,
        expr,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_cert_archive(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn batch_verify_cert_stops_at_its_deadline() {
    let items = (0..4)
        .map(|i| {
            let (cert, expr) = endless_cert();
            BatchVerifyCertItem {
                id: i.to_string(),
                cert,
                expr,
            }
        })
        .collect();
    let params = BatchVerifyCertParams {
        items,
        threads: 2,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_batch_verify_cert(
        s,
        RequestId::Number(1),
        params,
        None
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn batch_verify_cert_archive_stops_at_its_deadline() {
    let items = (0..4)
        .map(|i| {
            let (cert, expr) = endless_cert();
            let (archive, _) = archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4)
                .expect("archive");
            BatchVerifyCertArchiveItem {
                id: i.to_string(),
                archive,
                expr,
            }
        })
        .collect();
    let params = BatchVerifyCertArchiveParams {
        items,
        threads: 2,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) =
        race!(prelude_state(), |s| handle_batch_verify_cert_archive(
            s,
            RequestId::Number(1),
            params,
            None
        ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn get_premises_answers_its_timeout_and_its_work_ends() {
    let params: GetPremisesParams =
        serde_json::from_value(json!({"goal": slow_goal(), "timeout_ms": TIMEOUT_MS}))
            .expect("premise params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_get_premises(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn batch_get_premises_stops_at_its_deadline() {
    let items: Vec<_> = (0..200)
        .map(|i| json!({"id": i.to_string(), "goal": slow_goal()}))
        .collect();
    let params: BatchGetPremisesParams =
        serde_json::from_value(json!({"items": items, "timeout_ms": TIMEOUT_MS}))
            .expect("batch premise params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_batch_get_premises(
        s,
        RequestId::Number(1),
        params,
        None
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn search_proof_answers_its_timeout_and_its_work_ends() {
    let params: SearchProofParams = serde_json::from_value(
        json!({"theorem": slow_goal(), "strategy": "auto_only", "timeout_ms": TIMEOUT_MS}),
    )
    .expect("search params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_search_proof(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn verify_proof_answers_its_timeout_and_its_work_ends() {
    let params = VerifyProofParams {
        goal: slow_goal(),
        proof: "rfl".to_string(),
        context: None,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_proof(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn verify_proof_batch_stops_at_its_deadline() {
    let proofs: Vec<_> = (0..200)
        .map(|i| json!({"id": i.to_string(), "goal": slow_goal(), "proof": "rfl"}))
        .collect();
    let params: VerifyProofBatchParams =
        serde_json::from_value(json!({"proofs": proofs, "threads": 2, "timeout_ms": TIMEOUT_MS}))
            .expect("batch params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_proof_batch(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn verify_file_answers_its_timeout_and_its_work_ends() {
    let params = VerifyFileParams {
        content: slow_file(),
        proof: Some("rfl".to_string()),
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_file(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn fill_sorries_answers_its_timeout_and_caches_nothing() {
    let content = format!("theorem slow : {} := by\n  sorry\n", slow_goal());
    let params: FillSorriesParams =
        serde_json::from_value(json!({"content": content, "timeout_ms": TIMEOUT_MS}))
            .expect("fill params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_fill_sorries(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    assert_eq!(
        state.proof_cache.len(),
        0,
        "an interrupted replay caches no proof state"
    );
}

#[tokio::test]
async fn compose_proof_answers_its_timeout_and_its_work_ends() {
    let params: ComposeProofParams = serde_json::from_value(
        json!({"content": slow_file(), "replacements": [], "timeout_ms": TIMEOUT_MS}),
    )
    .expect("compose params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_compose_proof(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

#[tokio::test]
async fn init_proof_state_answers_its_timeout_and_caches_nothing() {
    let params: InitProofStateParams =
        serde_json::from_value(json!({"theorem": slow_goal(), "timeout_ms": TIMEOUT_MS}))
            .expect("init params");
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_init_proof_state(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    assert_eq!(
        state.proof_cache.len(),
        0,
        "an interrupted init caches no state"
    );
}

/// A cached proof state whose goal `rfl` closes only by computing `Nat.rec`
/// unfolded 60,000 times (stating the goal computes nothing), and its goal id.
async fn slow_rfl_goal(state: &ServerState) -> (String, String) {
    let theorem = "@Nat.rec (fun _ => Nat) 0 (fun n ih => n + 1 + ih) 60000 = 1800030000";
    let params: InitProofStateParams =
        serde_json::from_value(json!({"theorem": theorem})).expect("init params");
    let response = handle_init_proof_state(state, RequestId::Number(0), params).await;
    let result = response.result.expect("the goal is stated");
    let state_id = result["state_id"].as_str().expect("a state id").to_string();
    let goal_id = result["goals"][0]["goal_id"]
        .as_str()
        .expect("a goal id")
        .to_string();
    (state_id, goal_id)
}

#[tokio::test]
async fn apply_tactic_answers_its_timeout_and_caches_nothing() {
    let state = prelude_state();
    let (state_id, goal_id) = slow_rfl_goal(&state).await;
    let cached_before = state.proof_cache.len();
    let params: ApplyTacticParams = serde_json::from_value(json!({
        "state_id": state_id, "goal_id": goal_id, "tactic": "rfl", "timeout_ms": TIMEOUT_MS
    }))
    .expect("apply params");
    let (state, response, fast_first) = race!(state, |s| handle_apply_tactic(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    assert_eq!(
        state.proof_cache.len(),
        cached_before,
        "an interrupted tactic caches no state"
    );
}

#[tokio::test]
async fn batch_apply_tactic_stops_at_its_deadline() {
    let state = prelude_state();
    let (state_id, goal_id) = slow_rfl_goal(&state).await;
    let cached_before = state.proof_cache.len();
    let items: Vec<_> = (0..200)
        .map(|i| {
            json!({"id": i.to_string(), "state_id": state_id, "goal_id": goal_id, "tactic": "rfl"})
        })
        .collect();
    let params: BatchApplyTacticParams =
        serde_json::from_value(json!({"items": items, "threads": 2, "timeout_ms": TIMEOUT_MS}))
            .expect("batch apply params");
    let (state, response, fast_first) = race!(state, |s| handle_batch_apply_tactic(
        s,
        RequestId::Number(1),
        params
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
    assert_eq!(
        state.proof_cache.len(),
        cached_before,
        "an interrupted batch caches no state"
    );
}

#[tokio::test]
async fn verify_c_stops_at_its_deadline() {
    // 20,000 functions: their verification runs far past the timeout; the
    // work reads the clock between functions.
    let code: String = (0..20_000)
        .map(|i| format!("//@ requires n >= 0;\n//@ ensures \\result >= 0;\nint f{i}(int n) {{ return n; }}\n"))
        .collect();
    let params = VerifyCParams {
        code,
        fail_unknown: false,
        include_details: false,
        timeout_ms: Some(TIMEOUT_MS),
    };
    let (state, response, fast_first) = race!(prelude_state(), |s| handle_verify_c(
        s,
        RequestId::Number(1),
        params,
        None
    ));
    assert_timed_out(&response, fast_first);
    wait_until_idle(&state).await;
}

