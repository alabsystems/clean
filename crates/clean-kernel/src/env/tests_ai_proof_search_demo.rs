// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Demo and throughput tests for the AI proof search kernel verification loop.
//!
//! These tests exercise `ai_search_proof` end-to-end with a `MockBackend`
//! acting as a deterministic stand-in for an LLM. The goal is to document and
//! demonstrate the contract required by issue #3386:
//!
//! 1. **Kernel is the judge.** The backend can return anything; the loop only
//!    accepts candidates that `try_verify_proof` (which invokes
//!    `TypeChecker::infer_type` + `is_def_eq`) accepts.
//! 2. **Bogus candidates are rejected.** If the backend returns type-incorrect
//!    or unknown terms, the loop never returns them as proofs and never
//!    registers them with `add_decl`.
//! 3. **Throughput is measurable.** Candidates tried per second and hit rate
//!    are tracked in `AiSearchStats`.
//!
//! The "gamma-crown demo" here uses an `Eq.refl`-shaped proposition that is
//! structurally analogous to the base cases of the (now axiom-free) gamma-crown
//! conjectures. The real gamma-crown library reached 0 domain axioms via the
//! C001-C030 effort (see `data/axiom_audit.json`), so this demo targets the
//! generate-and-test mechanism itself rather than an outstanding axiom.

use crate::env::ai_proof_search::{
    ai_search_proof, register_ai_proved_theorem, AiProofSearchResult, AiSearchBudget, MockBackend,
};
use crate::env::proof_search::try_verify_proof;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Environment + goal helpers
// ---------------------------------------------------------------------------

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}

fn nat_succ(arg: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), arg)
}

fn eq_level() -> Level {
    Level::succ(Level::zero())
}

fn eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![eq_level()]),
        [nat(), lhs, rhs],
    )
}

fn eq_refl_proof(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![eq_level()]),
        [nat(), value],
    )
}

// ---------------------------------------------------------------------------
// Demo: AI proof search finds a proof after a wrong candidate
// ---------------------------------------------------------------------------

/// Demo: an LLM-like backend returns a wrong candidate first, then a correct
/// one. The kernel verification loop rejects the wrong candidate, feeds back
/// diagnostic information, and accepts the second candidate.
///
/// This mirrors the expected real-world interaction pattern: the LLM guesses,
/// the kernel rejects, and the LLM refines based on feedback until a proof
/// type-checks. The kernel remains the single source of trust.
#[test]
fn demo_ai_proof_search_gamma_crown_refl_shape() {
    let env = make_env();
    // A gamma-crown-style proposition: `Eq Nat (succ zero) (succ zero)`.
    // Structurally identical to base cases in C002/C006/C008 IBP proofs.
    let succ_zero = nat_succ(nat_zero());
    let goal = eq_goal(succ_zero.clone(), succ_zero.clone());

    // Round 1: backend returns a type-incorrect candidate (bogus "True.intro"
    // for an Eq goal).
    // Round 2: backend returns the correct Eq.refl term.
    let wrong = Expr::const_str("True.intro");
    let correct = eq_refl_proof(succ_zero.clone());
    let mut backend = MockBackend::new(vec![vec![wrong], vec![correct.clone()]]);

    let result = ai_search_proof(
        &env,
        &goal,
        &mut backend,
        AiSearchBudget {
            max_rounds: 4,
            max_candidates: 8,
        },
    )
    .expect("ai_search_proof runs without I/O errors");

    match result {
        AiProofSearchResult::Found {
            proof,
            stats,
            feedback,
        } => {
            // Kernel accepted the candidate.
            assert_eq!(proof, correct);
            assert!(try_verify_proof(&env, &goal, &proof));

            // Exactly two unique candidates tried: wrong, then correct.
            assert_eq!(stats.candidates_tried, 2);
            assert_eq!(stats.rounds, 2);
            assert!(stats.hit_rate > 0.0 && stats.hit_rate <= 1.0);
            assert!(
                stats.verification_time.as_nanos() > 0,
                "verification_time must be measured"
            );

            // The feedback from round 1 describes the type mismatch, so round 2's
            // prompt contains actionable information for the LLM.
            assert_eq!(feedback.len(), 1);
            assert!(backend.prompts().len() == 2);
            let second_prompt = &backend.prompts()[1];
            assert!(
                second_prompt.contains("has type") || second_prompt.contains("failed"),
                "round 2 prompt must carry kernel feedback from round 1, got: {second_prompt}"
            );
        }
        other => panic!("expected Found after kernel-guided refinement, got {other:?}"),
    }
}

/// Demo: after AI search succeeds, the resulting proof can be registered as a
/// `Declaration::Theorem` via the kernel's `add_decl` path. This closes the
/// loop: AI proposes, kernel verifies, kernel registers.
#[test]
fn demo_ai_proof_register_as_theorem() {
    let mut env = make_env();
    let goal = eq_goal(nat_zero(), nat_zero());
    let name = Name::from_string("AiDemo.refl_zero");
    let proof = eq_refl_proof(nat_zero());

    register_ai_proved_theorem(&mut env, name.clone(), vec![], goal, proof)
        .expect("registration through add_decl must succeed");

    let info = env
        .get_const(&name)
        .expect("registered theorem must be looked up by name");
    assert_eq!(info.kind, ConstantKind::Theorem);
    // The registered theorem must carry a proof term (not an axiom stub).
    // Per design doc soundness rule, Theorem wrapping Axiom is not a proof —
    // here we confirm the value is present and non-trivial.
    let value = info.value.as_ref().expect("theorem must have a proof term");
    // The proof term should not be a bare reference to an `Axiom`-style stub.
    assert!(
        !matches!(value, v if v.to_string() == "sorry"),
        "proof term must not be a sorry/axiom stub, got {value}"
    );
}

// ---------------------------------------------------------------------------
// Soundness: kernel rejects bogus candidates
// ---------------------------------------------------------------------------

/// Soundness: an LLM backend that returns ONLY type-incorrect candidates must
/// never cause the loop to succeed, and must never register anything with the
/// kernel. This is the critical invariant: AI creativity cannot bypass the
/// kernel trust boundary.
#[test]
fn soundness_ai_search_rejects_only_bogus_candidates() {
    let env = make_env();
    let goal = eq_goal(nat_zero(), nat_succ(nat_zero()));
    // Backend keeps offering wrong candidates.
    let mut backend = MockBackend::new(vec![
        vec![Expr::const_str("True.intro")],
        vec![Expr::const_str("Nat.zero")],
        vec![eq_refl_proof(nat_zero())], // well-typed but wrong goal (0=0 not 0=1)
    ]);

    let result = ai_search_proof(
        &env,
        &goal,
        &mut backend,
        AiSearchBudget {
            max_rounds: 3,
            max_candidates: 6,
        },
    )
    .expect("ai_search_proof runs without I/O errors");

    match result {
        AiProofSearchResult::Found { proof, .. } => panic!(
            "kernel must reject all bogus candidates, but ai_search_proof returned Found with proof {proof}"
        ),
        AiProofSearchResult::Exhausted { stats, feedback }
        | AiProofSearchResult::BudgetExceeded { stats, feedback, .. } => {
            assert!(stats.candidates_tried >= 1);
            assert!(
                !feedback.is_empty(),
                "kernel rejection must surface diagnostic feedback"
            );
        }
    }
}

/// Soundness: `register_ai_proved_theorem` refuses to register an
/// unverified proof, even if the caller bypassed the search loop entirely.
/// This double-checks the trust boundary at the registration seam.
#[test]
fn soundness_register_refuses_unverified_proof() {
    let mut env = make_env();
    let goal = eq_goal(nat_zero(), nat_succ(nat_zero()));
    let bogus = Expr::const_str("True.intro");
    let name = Name::from_string("AiDemo.bogus");

    let result = register_ai_proved_theorem(&mut env, name.clone(), vec![], goal, bogus);
    assert!(
        result.is_err(),
        "register_ai_proved_theorem must refuse an unverified proof term"
    );
    assert!(
        env.get_const(&name).is_none(),
        "bogus theorem must not be registered in the environment"
    );
}

// ---------------------------------------------------------------------------
// Throughput measurement
// ---------------------------------------------------------------------------

/// Throughput measurement: run AI search across several distinct goals,
/// collect candidates-tried / total verification time, and sanity-check the
/// reported hit rate. Emits a human-readable summary via `println!` so the
/// value is visible with `cargo test -- --nocapture`.
///
/// This test satisfies acceptance criterion 5 ("Throughput measurement:
/// candidates/sec, hit rate") for issue #3386. The numbers depend on the host
/// machine; the test only asserts that the metrics are positive and
/// internally consistent, so it remains stable in CI.
#[test]
fn throughput_ai_search_metrics_are_positive_and_consistent() {
    let env = make_env();

    // Suite of equality goals. Each one is solvable by a single Eq.refl
    // candidate, but the backend emits one decoy before the correct answer —
    // so the loop exercises both the verification and feedback paths.
    let goals: Vec<Expr> = (0..4)
        .map(|i| {
            let term = (0..i).fold(nat_zero(), |acc, _| nat_succ(acc));
            eq_goal(term.clone(), term)
        })
        .collect();

    let mut total_candidates = 0usize;
    let mut total_found = 0usize;
    let mut total_verify_nanos: u128 = 0;

    for goal in &goals {
        let lhs_rhs = match goal.get_app_args().as_slice() {
            [_, lhs, _] => (*lhs).clone(),
            _ => unreachable!("eq_goal has three args"),
        };
        let decoy = Expr::const_str("True.intro");
        let correct = eq_refl_proof(lhs_rhs);
        let mut backend = MockBackend::new(vec![vec![decoy], vec![correct]]);

        let result = ai_search_proof(
            &env,
            goal,
            &mut backend,
            AiSearchBudget {
                max_rounds: 3,
                max_candidates: 4,
            },
        )
        .expect("search succeeds without I/O error");

        match result {
            AiProofSearchResult::Found { stats, proof, .. } => {
                assert!(try_verify_proof(&env, goal, &proof));
                total_candidates += stats.candidates_tried;
                total_found += 1;
                total_verify_nanos += stats.verification_time.as_nanos();
            }
            other => panic!("expected Found for refl goal, got {other:?}"),
        }
    }

    assert_eq!(total_found, goals.len(), "all refl goals must be solved");
    assert!(
        total_candidates >= goals.len(),
        "each goal tries >=1 candidate"
    );
    assert!(
        total_verify_nanos > 0,
        "aggregate verification time must be measured"
    );

    // candidates/sec and hit rate are purely informational; print them so
    // `cargo test -- --nocapture` surfaces the numbers for operators without
    // introducing host-dependent assertions.
    let verify_secs = (total_verify_nanos as f64) / 1e9;
    let candidates_per_sec = if verify_secs > 0.0 {
        (total_candidates as f64) / verify_secs
    } else {
        f64::INFINITY
    };
    let hit_rate = (total_found as f64) / (total_candidates as f64);
    println!(
        "ai_proof_search throughput: goals={} candidates_tried={} verify_time_ns={} candidates_per_sec≈{:.0} hit_rate={:.2}",
        goals.len(),
        total_candidates,
        total_verify_nanos,
        candidates_per_sec,
        hit_rate
    );

    // Internal consistency: hit rate ∈ (0, 1].
    assert!(
        hit_rate > 0.0 && hit_rate <= 1.0,
        "hit_rate must be in (0, 1]"
    );
}
