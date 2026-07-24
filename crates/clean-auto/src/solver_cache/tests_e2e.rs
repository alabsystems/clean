// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end telemetry tests: drive the real `auto_prove` dispatch with the
//! telemetry sink enabled and assert well-formed `solver-attempt-record-v1`
//! rows are emitted with the right result/timing.
//!
//! These tests mutate process-global telemetry/cache environment variables.
//! Their bodies therefore run in fresh, single-threaded libtest subprocesses:
//! `#[serial]` alone only coordinates other annotated tests and cannot protect
//! unannotated solver tests that read those variables concurrently.

use crate::engine::AutomationEngine;
use crate::engine_api::{AutomationOutcome, AutomationRequest};
use crate::solver_cache::record::{CacheOutcome, SolverAttemptRecord};
use crate::solver_cache::store::{self, CacheMeta};
use crate::solver_cache::telemetry::TELEMETRY_DIR_ENV;
use crate::solver_cache::{obligation_digest, store::CACHE_DIR_ENV};
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};
use serial_test::serial;
use std::time::Duration;

/// Minimal `Eq` + `Eq.refl` + base type environment, mirroring the crate's
/// reflexivity-proving setup so `auto_prove` produces a real `Proved` outcome.
fn setup_env_with_eq() -> Environment {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .expect("add Eq");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .expect("add Eq.refl");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");

    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .expect("add const");
    }

    env
}

/// `Eq A lhs rhs`.
fn make_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Read every record from `<dir>/attempts.jsonl`, asserting each line parses as
/// the pinned schema.
fn read_records(dir: &std::path::Path) -> Vec<SolverAttemptRecord> {
    let path = dir.join("attempts.jsonl");
    let contents = std::fs::read_to_string(&path).expect("attempts.jsonl should exist");
    contents
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| serde_json::from_str(line).expect("each line is a schema-valid record"))
        .collect()
}

/// RAII guard: set `CLEAN_SOLVER_TELEMETRY_DIR` for the test body and restore
/// the previous value on drop (via the crate env choke point) so a panicking
/// test cannot leak the env var. The calling test body runs in an isolated,
/// single-threaded subprocess, so there are no concurrent environment readers.
struct TelemetryEnvGuard {
    _var: crate::test_env::ScopedEnvVar,
}

impl TelemetryEnvGuard {
    fn set(dir: &std::path::Path) -> Self {
        Self {
            _var: crate::test_env::ScopedEnvVar::set(TELEMETRY_DIR_ENV, &dir.to_string_lossy()),
        }
    }
}

/// RAII guard: set `CLEAN_SOLVER_CACHE_DIR` for the test body and restore the
/// previous value on drop (via the crate env choke point), so a panicking test
/// cannot leak the cache env var. The calling test body runs in an isolated,
/// single-threaded subprocess, so there are no concurrent environment readers.
struct CacheEnvGuard {
    _var: crate::test_env::ScopedEnvVar,
}

impl CacheEnvGuard {
    fn set(dir: &std::path::Path) -> Self {
        Self {
            _var: crate::test_env::ScopedEnvVar::set(CACHE_DIR_ENV, &dir.to_string_lossy()),
        }
    }
}

/// The downstream kernel re-check the *caller* performs on any proof term —
/// freshly found or cache-served. This mirrors `recheck_and_classify`: infer the
/// proof term's type and check it is definitionally equal to the goal. Returns
/// `true` iff the kernel accepts the term as a proof of `goal`.
///
/// This is the soundness arbiter. The cache only changes *what search produced*
/// a term; this function is what decides whether the term is honored, and it runs
/// identically for cached and freshly-found proofs.
fn kernel_rechecks_proof(env: &Environment, goal: &Expr, outcome: &AutomationOutcome) -> bool {
    let AutomationOutcome::Verified(result) = outcome else {
        return false;
    };
    let tc = match result.proof_context() {
        Some(ctx) => TypeChecker::with_context(env, ctx.clone()),
        None => TypeChecker::new(env),
    };
    match tc.infer_type(result.proof_term()) {
        Ok(inferred) => tc.is_def_eq(&inferred, goal),
        Err(_) => false,
    }
}

#[test]
#[serial]
fn test_auto_prove_emits_proved_record() {
    crate::test_env::in_isolated_test_process(test_auto_prove_emits_proved_record_body);
}

fn test_auto_prove_emits_proved_record_body() {
    let dir = tempfile::tempdir().expect("tempdir");
    let _guard = TelemetryEnvGuard::set(dir.path());

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(
        outcome.verified().is_some(),
        "reflexive equality must be proved"
    );

    let records = read_records(dir.path());
    assert!(
        !records.is_empty(),
        "a proving run must emit at least one attempt record"
    );

    // The first attempt is the SMT engine. The proving run must contain exactly
    // one `Proved` record carrying a proof-term digest.
    let proved: Vec<_> = records.iter().filter(|r| r.success).collect();
    assert_eq!(proved.len(), 1, "exactly one Proved record: {records:?}");
    let proved = proved[0];
    assert_eq!(proved.schema, "solver-attempt-record-v1");
    assert_eq!(
        proved.result,
        crate::solver_cache::record::AttemptResult::Proved
    );
    assert!(
        proved.obligation_digest.starts_with("blake3:"),
        "obligation digest is blake3-tagged: {}",
        proved.obligation_digest
    );
    assert_eq!(proved.obligation_digest.len(), "blake3:".len() + 64);
    assert!(
        proved.proof_term_digest.is_some(),
        "Proved record must carry a proof-term digest (re-checkable proof)"
    );
    assert!(
        proved.solver.version.starts_with(env!("CARGO_PKG_VERSION")),
        "solver version starts with crate version: {}",
        proved.solver.version
    );
}

#[test]
#[serial]
fn test_auto_prove_emits_advisory_record_on_failure() {
    crate::test_env::in_isolated_test_process(
        test_auto_prove_emits_advisory_record_on_failure_body,
    );
}

fn test_auto_prove_emits_advisory_record_on_failure_body() {
    let dir = tempfile::tempdir().expect("tempdir");
    let _guard = TelemetryEnvGuard::set(dir.path());

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    // `a = b` for distinct constants is not provable by reflexivity.
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = make_eq(a_ty, a, b);

    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(2)));
    assert!(
        outcome.verified().is_none(),
        "a = b must not be proved by reflexivity"
    );

    let records = read_records(dir.path());
    assert!(
        !records.is_empty(),
        "even a failing run emits advisory attempt records"
    );
    assert!(
        records.iter().all(|r| !r.success),
        "no record may report success when the goal is unproved: {records:?}"
    );
    // No advisory record may claim a proof-term digest.
    assert!(
        records.iter().all(|r| r.proof_term_digest.is_none()),
        "advisory records carry no proof-term digest"
    );
    // The obligation key is stable across all attempts on the same goal.
    let first = &records[0].obligation_digest;
    assert!(
        records.iter().all(|r| &r.obligation_digest == first),
        "all attempts on one goal share the obligation key"
    );
}

#[test]
#[serial]
fn test_disabled_telemetry_writes_nothing() {
    crate::test_env::in_isolated_test_process(test_disabled_telemetry_writes_nothing_body);
}

fn test_disabled_telemetry_writes_nothing_body() {
    // With the env var unset, the sink is a no-op: no file is created.
    let _guard = crate::test_env::ScopedEnvVar::unset(TELEMETRY_DIR_ENV);
    let dir = tempfile::tempdir().expect("tempdir");

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(outcome.verified().is_some(), "still proves with sink off");

    assert!(
        !dir.path().join("attempts.jsonl").exists(),
        "disabled telemetry must not write any file"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// Cache-hit hook (Phase 0 §4): MISS→solve→cache, then HIT→serve→kernel-recheck.
// ───────────────────────────────────────────────────────────────────────────

/// DEMO + soundness: a two-pass run. Pass 1 MISSES (the cache is empty), so the
/// solver runs and the proof term is cached. Pass 2 HITS (the cached term is
/// returned without re-searching). BOTH passes' proof terms are re-checked
/// through the kernel and must verify — the cache hit is sound precisely because
/// it flows through the same kernel re-check as a freshly-found proof.
#[test]
#[serial]
fn test_cache_two_pass_miss_then_hit_both_kernel_verify() {
    crate::test_env::in_isolated_test_process(
        test_cache_two_pass_miss_then_hit_both_kernel_verify_body,
    );
}

fn test_cache_two_pass_miss_then_hit_both_kernel_verify_body() {
    let cache_dir = tempfile::tempdir().expect("cache tempdir");
    let telem_dir = tempfile::tempdir().expect("telemetry tempdir");
    let _cache_guard = CacheEnvGuard::set(cache_dir.path());
    let _telem_guard = TelemetryEnvGuard::set(telem_dir.path());

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);
    let digest = obligation_digest(&goal).expect("obligation digest");

    // Pre-condition: empty cache.
    assert!(
        store::get(&digest).is_none(),
        "cache must start empty for this obligation"
    );

    // ── Pass 1: MISS — solve and cache. ──
    let outcome1 =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(
        kernel_rechecks_proof(&env, &goal, &outcome1),
        "pass-1 (freshly solved) proof term must kernel-verify"
    );
    // The solve must have populated the cache.
    assert!(
        store::get(&digest).is_some(),
        "pass 1 must cache the proof term"
    );

    // The telemetry log must show NO cache_hit yet (the first solves are misses).
    let records1 = read_records(telem_dir.path());
    assert!(
        records1
            .iter()
            .all(|r| r.cache_outcome == CacheOutcome::Miss),
        "pass-1 records must all be Miss: {records1:?}"
    );

    // ── Pass 2: HIT — served from cache, still kernel-verified. ──
    let outcome2 =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(
        kernel_rechecks_proof(&env, &goal, &outcome2),
        "pass-2 (cache-served) proof term must STILL kernel-verify"
    );

    // A cache_hit telemetry record must now exist, and it must be marked Proved
    // (the served term is proof-bearing) and tagged CacheHit.
    let records2 = read_records(telem_dir.path());
    let hits: Vec<_> = records2
        .iter()
        .filter(|r| r.cache_outcome == CacheOutcome::CacheHit)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "exactly one cache_hit record after the second pass: {records2:?}"
    );
    assert!(hits[0].success, "a cache hit serves a proof-bearing result");
    assert_eq!(
        hits[0].obligation_digest, digest,
        "the cache hit is keyed on the goal's obligation digest"
    );
}

/// SOUNDNESS: a deliberately-corrupted cache entry is REJECTED by the kernel
/// re-check. We seed the cache with a *wrong* proof term filed under the goal's
/// correct obligation key (a stale/colliding/malicious entry). The cache HITS and
/// returns the wrong term, but the caller's kernel re-check (`infer_type` +
/// `is_def_eq`) refuses it — proving the cache is NOT trusted and a bad entry can
/// never be silently honored.
#[test]
#[serial]
fn test_corrupted_cache_entry_is_rejected_by_kernel_recheck() {
    crate::test_env::in_isolated_test_process(
        test_corrupted_cache_entry_is_rejected_by_kernel_recheck_body,
    );
}

fn test_corrupted_cache_entry_is_rejected_by_kernel_recheck_body() {
    let cache_dir = tempfile::tempdir().expect("cache tempdir");
    let _cache_guard = CacheEnvGuard::set(cache_dir.path());

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    // Goal: `a = a` (provable by reflexivity).
    let goal = make_eq(a_ty, a.clone(), a);
    let digest = obligation_digest(&goal).expect("obligation digest");

    // Poison the cache: file a WRONG, well-typed proof term under the goal's key.
    // `Eq.refl` (the bare constant) type-checks but is NOT a proof of `a = a`
    // (its inferred type is the polymorphic ∀-statement, not the goal). This is
    // the worst case: a kernel-acceptable term that does not prove THIS goal.
    let wrong_term = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    store::put(&digest, &wrong_term, CacheMeta::new("malicious", "poison"))
        .expect("seed corrupt cache entry");

    // The cache HITS (same obligation key) and returns the wrong term.
    let cached = store::get(&digest).expect("corrupt entry must be a hit");
    assert_eq!(
        cached.proof_term, wrong_term,
        "the cache returns exactly the stored (wrong) term"
    );

    // The engine surfaces the cached term as its (untrusted) outcome — it does
    // not itself re-check; that is the caller's job, by design. The CALLER's
    // kernel re-check is what arbitrates, and it REJECTS the poisoned hit: the
    // served term's inferred type is not def-eq to the goal.
    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    let served = match &outcome {
        AutomationOutcome::Verified(result) => result.proof_term().clone(),
        other => panic!("cache hit must surface a Verified outcome, got {other:?}"),
    };
    assert_eq!(
        served, wrong_term,
        "the surfaced term is exactly the poisoned cache entry (cache is consulted before solving)"
    );
    assert!(
        !kernel_rechecks_proof(&env, &goal, &outcome),
        "the caller's kernel re-check must REJECT the corrupted cache entry — \
         the cache is a search-result store, never trusted"
    );

    // Direct statement of the soundness property: the poisoned term does NOT
    // kernel-verify as a proof of the goal. The kernel is the arbiter.
    let tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(&wrong_term).expect("Eq.refl type-checks");
    assert!(
        !tc.is_def_eq(&inferred, &goal),
        "the poisoned term must not be def-eq to the goal: the kernel is the arbiter"
    );
}

/// The cache hook is a no-op when `CLEAN_SOLVER_CACHE_DIR` is unset: solving is
/// unchanged and nothing is written. (Behaviour-preservation guard.)
#[test]
#[serial]
fn test_cache_disabled_does_not_serve_or_store() {
    crate::test_env::in_isolated_test_process(test_cache_disabled_does_not_serve_or_store_body);
}

fn test_cache_disabled_does_not_serve_or_store_body() {
    let _guard = crate::test_env::ScopedEnvVar::unset(CACHE_DIR_ENV);
    let cache_dir = tempfile::tempdir().expect("cache tempdir");

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(
        kernel_rechecks_proof(&env, &goal, &outcome),
        "still proves with the cache off"
    );
    // No record files: a disabled cache writes nothing into the would-be dir.
    let entries: Vec<_> = std::fs::read_dir(cache_dir.path())
        .expect("read cache dir")
        .collect();
    assert!(
        entries.is_empty(),
        "disabled cache must not write any record"
    );
}
