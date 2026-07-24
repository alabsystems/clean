// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::oracle::{
    OracleCandidate, OracleCandidateRunner, OracleError, OracleRequest, OracleRunError, ProofOracle,
};
use crate::premise::PremiseDatabase;
use clean_kernel::env::Declaration;
use clean_kernel::mode::CleanMode;
use clean_kernel::sorry::{create_trusted_ay_term, reset_sorry_counter, sorry_count};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, LocalContext, Name};
use serial_test::serial;
use std::time::Duration;

fn setup_env_with_eq() -> Environment {
    let mut env = Environment::new();

    // Add Eq type: Eq : {α : Sort u} → α → α → Prop
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
    .unwrap();

    // Add Eq.refl : ∀ {α : Sort u} (a : α), Eq a a
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
    .unwrap();

    // Add a base type A : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants a, b : A
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    env
}

/// Make an Eq expression: Eq A a b
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

fn setup_env_with_prop(name: &str) -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add proposition");
    env
}

struct TestOracle {
    candidates: Vec<OracleCandidate>,
}

impl TestOracle {
    fn new(tactics: &[(&str, f64)]) -> Self {
        Self {
            candidates: tactics
                .iter()
                .map(|(text, confidence)| OracleCandidate::new(*text, *confidence))
                .collect(),
        }
    }
}

impl ProofOracle for TestOracle {
    fn suggest_proof(&self, _request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        Ok(self.candidates.clone())
    }

    fn model_id(&self) -> &str {
        "test-oracle"
    }

    fn is_available(&self) -> bool {
        true
    }
}

struct TestOracleRunner {
    proof_term: Expr,
    proof_text: String,
}

impl OracleCandidateRunner for TestOracleRunner {
    fn try_candidate(
        &self,
        _env: &Environment,
        _local_ctx: Option<&LocalContext>,
        _goal: &Expr,
        _candidate: &OracleCandidate,
        _timeout: Duration,
    ) -> Result<Option<ProofResult>, OracleRunError> {
        Ok(Some(ProofResult::new(
            self.proof_term.clone(),
            self.proof_text.clone(),
            0,
            None,
        )))
    }
}

#[test]
fn test_automation_engine_creation() {
    let engine = AutomationEngine::new();
    assert_eq!(engine.max_smt_rounds, 100);
}

#[test]
fn test_automation_engine_with_config() {
    let engine = AutomationEngine::with_config(50);
    assert_eq!(engine.max_smt_rounds, 50);
}

#[test]
fn test_auto_prove_reflexivity() {
    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();

    // Goal: Eq A a a (reflexive equality)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let result = engine.auto_prove(&env, &goal, Duration::from_secs(5), None);
    assert!(result.is_some(), "Should prove reflexive equality a = a");
    if let Some(r) = result {
        assert!(!r.proof_text().is_empty(), "Should have proof text");
    }
}

#[tokio::test]
async fn test_auto_prove_async() {
    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();

    // Goal: Eq A a a
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let result = engine
        .auto_prove_async(&env, &goal, Duration::from_secs(5), None)
        .await;
    assert!(result.is_some(), "Async auto_prove should also work");
}

#[test]
fn test_auto_prove_with_premises() {
    // Test that premise-guided E-matching integrates correctly
    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();

    // Create a premise database with some theorems
    let mut premise_db = PremiseDatabase::new();

    // Add a premise about Eq (using the same goal structure as test)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let eq_a_a = make_eq(a_ty.clone(), a.clone(), a.clone());
    premise_db.add(Name::from_string("eq_refl_a"), eq_a_a.clone());

    // Goal: Eq A a a
    let goal = make_eq(a_ty, a.clone(), a);

    // No hypotheses needed - reflexivity should prove this
    let hypotheses = vec![];

    let result = engine.auto_prove_with_premises(
        &env,
        &goal,
        hypotheses,
        &premise_db,
        Duration::from_secs(5),
        None,
    );
    assert!(
        result.is_some(),
        "Should prove reflexive equality with premise-guided proving"
    );
    let result = result.unwrap();
    assert!(
        result.proof_context().is_none(),
        "proofs without premises should be closed"
    );
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "closed proof from auto_prove_with_premises should type-check: {:?}",
        inferred.err()
    );
}

#[test]
fn test_auto_prove_with_request_preserves_refuted_outcome() {
    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let engine = AutomationEngine::new();

    let outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));

    assert!(
        matches!(
            outcome,
            AutomationOutcome::Refuted {
                source: AutomationSource::Smt,
                ..
            }
        ),
        "expected SMT refutation to survive the engine boundary, got: {outcome:?}"
    );
}

#[test]
fn test_auto_prove_wrapper_still_collapses_non_verified_outcomes() {
    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let engine = AutomationEngine::new();

    let result = engine.auto_prove(&env, &goal, Duration::from_secs(5), None);
    assert!(
        result.is_none(),
        "legacy auto_prove wrapper should still collapse non-verified outcomes"
    );
}

#[test]
fn test_auto_prove_with_request_uses_local_context_names_for_proof_context() {
    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(42),
        Name::from_string("h"),
        goal.clone(),
        BinderInfo::Default,
    );
    let hypotheses = vec![(goal.clone(), None)];
    let engine = AutomationEngine::new();

    let outcome = engine.auto_prove_with_request(
        &env,
        AutomationRequest::new(&goal, Duration::from_secs(5))
            .with_local_ctx(&local_ctx)
            .with_hypotheses(hypotheses.as_slice()),
    );

    match outcome {
        AutomationOutcome::Verified(result) => {
            let result = *result;
            let proof_context = result
                .proof_context
                .expect("local-context request should preserve proof context");
            let names: Vec<String> = proof_context
                .iter()
                .map(|decl| decl.name.to_string())
                .collect();
            assert_eq!(names, vec!["h".to_string()]);
        }
        other => panic!("expected local hypothesis to prove the goal, got {other:?}"),
    }
}

#[test]
fn test_auto_prove_with_request_uses_oracle_after_unknown_smt() {
    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let quantified_goal = Expr::pi(
        BinderInfo::Default,
        a_ty.clone(),
        make_eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(0)),
    );
    let goal = Expr::pi(BinderInfo::Default, quantified_goal.clone(), a_ty);
    let engine = AutomationEngine::new();
    let oracle = TestOracle::new(&[("exact a", 0.9)]);
    let runner = TestOracleRunner {
        proof_term: Expr::lam(
            BinderInfo::Default,
            quantified_goal,
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        proof_text: "exact a".to_string(),
    };

    let outcome = engine.auto_prove_with_request(
        &env,
        AutomationRequest::new(&goal, Duration::from_secs(5)).with_oracle(&oracle, &runner),
    );

    match outcome {
        AutomationOutcome::Verified(result) => {
            let result = *result;
            assert_eq!(result.proof_text(), "exact a");
            let inferred = result.infer_type(&env);
            assert!(
                inferred.is_ok(),
                "oracle proof should type-check through the detailed API: {:?}",
                inferred.err()
            );
        }
        other => panic!("expected oracle-verified outcome after SMT fallback, got {other:?}"),
    }
}

#[test]
fn test_auto_prove_with_request_preserves_smt_unverified_when_oracle_exhausts() {
    let mut env = setup_env_with_eq();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .expect("add unrelated constant");
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let nat_lt = |lhs: Expr, rhs: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), lhs),
            rhs,
        )
    };
    let nat_eq = |lhs: Expr, rhs: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                lhs,
            ),
            rhs,
        )
    };
    let hypotheses = vec![
        (nat_lt(a.clone(), b.clone()), None),
        (nat_lt(b, a.clone()), None),
    ];
    let goal = nat_eq(a, c);
    let engine = AutomationEngine::new();
    let oracle = TestOracle::new(&[]);
    let runner = TestOracleRunner {
        proof_term: Expr::nat_lit(0),
        proof_text: "unused".to_string(),
    };

    let outcome = engine.auto_prove_with_request(
        &env,
        AutomationRequest::new(&goal, Duration::from_secs(5))
            .with_hypotheses(hypotheses.as_slice())
            .with_oracle(&oracle, &runner),
    );

    assert!(
        matches!(
            outcome,
            AutomationOutcome::Unverified {
                source: AutomationSource::Smt,
                ..
            }
        ),
        "oracle exhaustion must not erase an earlier SMT Unverified outcome, got {outcome:?}"
    );
}

#[test]
fn test_compute_premise_scores() {
    // Test that compute_premise_scores returns expected results
    let mut premise_db = PremiseDatabase::new();

    // Add premises with different constant overlap with goal
    // Note: All constants used in goal must appear in at least one premise
    // for MePo scoring to work correctly (avoids division by ln(1)=0 issue)

    // Create common argument constant to avoid the ln(1)=0 issue
    let arg = Expr::const_(Name::from_string("arg"), vec![]);

    // Premise using Nat.add
    premise_db.add(
        Name::from_string("nat_add_comm"),
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            arg.clone(),
        ),
    );

    // Premise using Nat.mul
    premise_db.add(
        Name::from_string("nat_mul_comm"),
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            arg.clone(),
        ),
    );

    // Premise using List.length
    premise_db.add(
        Name::from_string("list_length"),
        Expr::app(
            Expr::const_(Name::from_string("List.length"), vec![]),
            arg.clone(),
        ),
    );

    // Goal involving Nat.add and the same arg constant (ensures all goal constants
    // appear in the premise database, avoiding MePo's ln(freq+1) edge case at freq=0)
    let goal = Expr::app(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        arg.clone(),
    );

    let scores = AutomationEngine::compute_premise_scores(&premise_db, &goal);

    // Should have scores for premises (nat_add_comm shares both constants with goal)
    assert!(!scores.is_empty(), "Should compute scores for premises");

    // nat_add_comm should have the highest score (shares Nat.add with goal)
    let nat_add_id = premise_db
        .get_by_name(&Name::from_string("nat_add_comm"))
        .unwrap()
        .id;
    let nat_mul_id = premise_db
        .get_by_name(&Name::from_string("nat_mul_comm"))
        .unwrap()
        .id;

    if let (Some(&add_score), Some(&mul_score)) = (scores.get(&nat_add_id), scores.get(&nat_mul_id))
    {
        assert!(
            add_score > mul_score,
            "nat_add_comm (score {}) should rank higher than nat_mul_comm (score {}) for Nat.add goal",
            add_score,
            mul_score
        );
    }
}

// =============================================================================
// Sorry-absence tests for clean-auto create_trusted_ay_term (Part of #1144)
//
// Coverage gap: the two call sites for create_trusted_ay_term in auto_prove
// (lines 194, 272) were not covered by sorry_absence monitoring. The
// sorry_absence tests in clean-elab test decide/decide_eq/simp/aesop/mathverse
// but cannot reach clean-auto's automation engine path.
// =============================================================================

/// Reset all proof counters for test isolation.
fn reset_all_counters() {
    reset_sorry_counter();
    clean_kernel::sorry::reset_ay_counter();
}

#[test]
#[serial]
fn test_create_trusted_ay_term_increments_counter() {
    // When trustedAy axiom exists, create_trusted_ay_term should:
    // 1. Return a trustedAy application (not sorry)
    // 2. Increment AY_PROOF_COUNTER
    // 3. NOT increment SORRY_COUNTER
    reset_all_counters();

    let mut env = setup_env_with_eq();
    env.init_trusted_ay()
        .expect("trustedAy axiom should initialize");

    let goal_ty = Expr::const_(Name::from_string("A"), vec![]);
    let term = create_trusted_ay_term(&env, &goal_ty);

    let ay_used = clean_kernel::sorry::ay_proof_count();
    let sorry_used = sorry_count();

    assert_eq!(
        ay_used, 1,
        "create_trusted_ay_term should increment AY_PROOF_COUNTER (got {ay_used})"
    );
    assert_eq!(
        sorry_used, 0,
        "create_trusted_ay_term should NOT create sorry terms (got {sorry_used})"
    );

    // Verify term is an application (not sorry). Structural checks for
    // trustedAy term shape are in clean-elab/src/tactic/tests/trusted_ay.rs.
    assert!(
        term.is_app(),
        "create_trusted_ay_term should return App(trustedAy, goal), got: {term:?}"
    );
    assert!(
        term.get_app_fn().is_const(),
        "head of trustedAy term should be a const"
    );
}

#[test]
#[serial]
fn test_create_trusted_ay_term_fallback_sorry_when_no_axiom() {
    // When trustedAy axiom is NOT in the environment, create_trusted_ay_term
    // should fall back to sorry (and increment SORRY_COUNTER, not AY_PROOF_COUNTER).
    reset_all_counters();

    // Use Environment::default() to get a bare env WITHOUT trustedAy.
    // Environment::new() auto-initializes trustedAy, so setup_env_with_eq()
    // would already have the axiom.
    let env = Environment::default();
    let goal_ty = Expr::type_(); // Use Type since we have no custom constants
    let _term = create_trusted_ay_term(&env, &goal_ty);

    let ay_used = clean_kernel::sorry::ay_proof_count();
    let sorry_used = sorry_count();

    assert_eq!(
        ay_used, 0,
        "Without trustedAy axiom, AY_PROOF_COUNTER should stay at 0 (got {ay_used})"
    );
    assert!(
        sorry_used >= 1,
        "Without trustedAy axiom, should fall back to sorry (sorry_count={sorry_used})"
    );
}

#[test]
#[serial]
fn test_auto_prove_sorry_absence_on_reflexivity() {
    // Verify auto_prove's trustedAy fallback path is monitored.
    // When SMT proves a goal but returns no proof_term, auto_prove calls
    // create_trusted_ay_term. This test ensures the counter tracks correctly.
    reset_all_counters();

    let mut env = setup_env_with_eq();
    env.init_trusted_ay()
        .expect("trustedAy axiom should initialize");

    let engine = AutomationEngine::new();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let result = engine.auto_prove(&env, &goal, Duration::from_secs(5), None);
    assert!(result.is_some(), "auto_prove should prove a = a");

    let sorry_used = sorry_count();
    assert_eq!(
        sorry_used, 0,
        "SORRY LEAK: auto_prove used {sorry_used} sorry terms for a = a (expected 0)"
    );

    // Ay counter may or may not increment depending on whether SMT
    // produces a proof_term. Either way, sorry must be 0.
    let ay_used = clean_kernel::sorry::ay_proof_count();
    eprintln!(
        "auto_prove(a=a): sorry={sorry_used}, ay={ay_used} (ay>0 means SMT \
         proved but no proof_term; ay=0 means kernel-checkable proof produced)"
    );
}

/// Integration test: try_superposition_prove exercises the full pipeline
/// (clausify → prove → reconstruct → byContradiction wrap).
///
/// Verifies the proof term is kernel-type-checkable, not just `is_some()`.
#[test]
fn test_try_superposition_prove_reflexive_eq() {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testA"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add testA");

    // Goal: Eq Nat testA testA (reflexive equality)
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let engine = AutomationEngine::new();
    let result = engine.try_superposition_prove(&env, &goal);
    assert!(
        result.is_some(),
        "try_superposition_prove should prove testA = testA"
    );

    let proof_result = result.unwrap();
    assert!(
        !proof_result.proof_text.is_empty(),
        "proof description should not be empty"
    );
    let proof_term = proof_result.proof_term;

    // Type-check the proof term: its inferred type must match the goal
    let tc = clean_kernel::TypeChecker::new(&env);
    let inferred_type = tc.infer_type(&proof_term);
    assert!(
        inferred_type.is_ok(),
        "proof term should type-check, got error: {:?}",
        inferred_type.err()
    );
    let inferred = inferred_type.unwrap();

    // The inferred type should be definitionally equal to the goal
    let def_eq = tc.is_def_eq(&inferred, &goal);
    assert!(
        def_eq,
        "inferred type should be definitionally equal to goal, \
         inferred: {inferred:?}, goal: {goal:?}"
    );
}

/// Create an environment with Nat, Eq, Eq.refl, Eq.subst, Not, absurd, False,
/// Or, Classical.byContradiction — everything needed for superposition proofs.
fn setup_full_superposition_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");
    env
}

/// Helper: build `@Eq.{1} Nat a b`
fn make_nat_eq(a: &Expr, b: &Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Integration test: superposition proves a = b given hypothesis h : a = b.
///
/// This exercises the full pipeline with actual superposition steps:
/// 1. GoalClausifier: negated goal (a ≠ b) + hypothesis (a = b) → CNF
/// 2. SuperpositionProver: Superposition(h_eq, ¬goal) → b ≠ b → EqRes → ⊥
/// 3. SuperpositionReconstructor: builds kernel proof with byContradiction
/// 4. TypeChecker: verifies proof term has type (Eq Nat testA testB)
#[test]
fn test_try_superposition_prove_with_hypothesis_type_checks() {
    use clean_kernel::LocalContext;

    let mut env = setup_full_superposition_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let goal = make_nat_eq(&a, &b);

    // Hypothesis: h : Eq Nat testA testB
    let hypotheses = vec![(goal.clone(), None)];

    let engine = AutomationEngine::new();
    let result = engine.try_superposition_prove_with_hypotheses(&env, &goal, &hypotheses);
    assert!(
        result.is_some(),
        "superposition should prove testA = testB from hypothesis testA = testB"
    );

    let proof_result = result.unwrap();
    assert!(
        proof_result.proof_text.contains("byContradiction"),
        "proof should use byContradiction wrapper"
    );
    let proof_term = proof_result.proof_term;

    // Kernel type-check with local context: hypothesis FVarIds are sequential
    // starting after goal clauses (1 goal clause → hypothesis FVarId = 1).
    let mut lctx = LocalContext::new();
    lctx.push_with_id(
        FVarId::new(1),
        Name::from_string("h_eq"),
        goal.clone(),
        BinderInfo::Default,
    );
    let tc = clean_kernel::TypeChecker::with_context(&env, lctx);
    let inferred = tc
        .infer_type(&proof_term)
        .expect("proof term should type-check through kernel");
    assert!(
        tc.is_def_eq(&inferred, &goal),
        "inferred type should equal goal: inferred={inferred:?}, goal={goal:?}"
    );
}

#[test]
fn test_try_superposition_prove_with_hypotheses_returns_none_in_cubical_env() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let goal = make_nat_eq(&a, &b);
    let hypotheses = vec![(goal.clone(), None)];

    let engine = AutomationEngine::new();
    let result = engine.try_superposition_prove_with_hypotheses(&env, &goal, &hypotheses);

    assert!(
        result.is_none(),
        "cubical mode should fail closed before superposition reconstruction uses Classical"
    );
}

/// Integration test: superposition proves a = c from hypotheses a = b ∧ b = c.
///
/// This exercises chained superposition: the prover must compose two equations
/// to derive the transitive equality. The reconstruction must chain multiple
/// Eq.subst applications.
///
/// Pipeline: ¬(a=c), a=b, b=c → Superposition(a=b, ¬(a=c)) → ¬(b=c)
/// → Superposition(b=c, ¬(b=c)) → c≠c → EqRes → ⊥
#[test]
fn test_try_superposition_prove_transitivity_type_checks() {
    use clean_kernel::LocalContext;

    let mut env = setup_full_superposition_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB", "testC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);

    let hyp1 = make_nat_eq(&a, &b);
    let hyp2 = make_nat_eq(&b, &c);
    let goal = make_nat_eq(&a, &c);

    // Hypotheses: h1 : a = b, h2 : b = c
    let hypotheses = vec![(hyp1.clone(), None), (hyp2.clone(), None)];

    let engine = AutomationEngine::new();
    let result = engine.try_superposition_prove_with_hypotheses(&env, &goal, &hypotheses);
    assert!(
        result.is_some(),
        "superposition should prove testA = testC from testA = testB ∧ testB = testC"
    );

    let proof_result = result.unwrap();
    assert!(
        proof_result.proof_text.contains("Superposition"),
        "proof description should mention Superposition"
    );
    let proof_term = proof_result.proof_term;

    // Local context with hypothesis FVars: 1 goal clause → hyp FVarIds = 1, 2
    let mut lctx = LocalContext::new();
    lctx.push_with_id(
        FVarId::new(1),
        Name::from_string("h1"),
        hyp1,
        BinderInfo::Default,
    );
    lctx.push_with_id(
        FVarId::new(2),
        Name::from_string("h2"),
        hyp2,
        BinderInfo::Default,
    );
    let tc = clean_kernel::TypeChecker::with_context(&env, lctx);
    let inferred = tc
        .infer_type(&proof_term)
        .expect("transitivity proof should type-check through kernel");
    assert!(
        tc.is_def_eq(&inferred, &goal),
        "inferred type should equal goal: inferred={inferred:?}, goal={goal:?}"
    );
}

#[test]
fn test_auto_prove_uses_local_context_hypotheses_in_superposition_fallback() {
    let mut env = setup_full_superposition_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .expect("add a");

    // Lambda terms are lossy in the SMT bridge, which pushes auto_prove onto
    // the superposition fallback for this exact-equality hypothesis.
    let fun_ty = Expr::pi(BinderInfo::Default, a_ty.clone(), a_ty.clone());
    let lam_id = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lam_const = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    let goal = make_eq(fun_ty, lam_id, lam_const);

    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(42),
        Name::from_string("h_fun_eq"),
        goal.clone(),
        BinderInfo::Default,
    );

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, Duration::from_secs(5), Some(&local_ctx))
        .expect("auto_prove should use local-context hypotheses in the superposition fallback");

    assert!(
        result.proof_text().contains("Superposition"),
        "expected superposition fallback proof, got {}",
        result.proof_text()
    );
    let proof_context = result
        .proof_context()
        .expect("fallback proof should expose the local context");
    let names: Vec<String> = proof_context
        .iter()
        .map(|decl| decl.name.to_string())
        .collect();
    assert_eq!(names, vec!["h_fun_eq".to_string()]);
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "superposition fallback proof should type-check: {:?}",
        inferred.err()
    );
}

#[test]
fn test_auto_prove_with_request_uses_hypotheses_in_superposition_fallback() {
    let mut env = setup_full_superposition_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .expect("add a");

    // Lambda terms are lossy in the SMT bridge, which pushes auto_prove onto
    // the superposition fallback for this exact-equality hypothesis.
    let fun_ty = Expr::pi(BinderInfo::Default, a_ty.clone(), a_ty.clone());
    let lam_id = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lam_const = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    let goal = make_eq(fun_ty, lam_id, lam_const);
    let hypotheses = vec![(goal.clone(), None)];

    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(77),
        Name::from_string("h_fun_eq"),
        goal.clone(),
        BinderInfo::Default,
    );

    let engine = AutomationEngine::new();
    let outcome = engine.auto_prove_with_request(
        &env,
        AutomationRequest::new(&goal, Duration::from_secs(5))
            .with_local_ctx(&local_ctx)
            .with_hypotheses(hypotheses.as_slice()),
    );

    match outcome {
        AutomationOutcome::Verified(result) => {
            let result = *result;
            assert!(
                result.proof_text().contains("Superposition"),
                "expected superposition fallback proof, got {}",
                result.proof_text()
            );
            let proof_context = result
                .proof_context()
                .expect("fallback proof should expose the local context");
            let names: Vec<String> = proof_context
                .iter()
                .map(|decl| decl.name.to_string())
                .collect();
            assert_eq!(names, vec!["h_fun_eq".to_string()]);
            let inferred = result.infer_type(&env);
            assert!(
                inferred.is_ok(),
                "superposition fallback proof should type-check: {:?}",
                inferred.err()
            );
        }
        other => panic!("expected superposition fallback proof, got {other:?}"),
    }
}

/// Integration test: premise-dependent proofs expose the context needed for
/// kernel verification.
///
/// Uses auto_prove_with_premises (the main entry point) with a non-trivial
/// hypothesis. Verifies the returned proof term type-checks through the kernel
/// without reconstructing hidden FVarIds in the test.
#[test]
fn test_auto_prove_with_premises_superposition_path() {
    let mut env = setup_full_superposition_env();
    env.init_trusted_ay().ok(); // for fallback if SMT doesn't produce proof_term
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let goal = make_nat_eq(&a, &b);

    let hypotheses = vec![(goal.clone(), None)];
    let premise_db = PremiseDatabase::new();

    let engine = AutomationEngine::new();
    let result = engine.auto_prove_with_premises(
        &env,
        &goal,
        hypotheses,
        &premise_db,
        Duration::from_secs(10),
        None,
    );
    assert!(
        result.is_some(),
        "auto_prove_with_premises should prove testA = testB from hypothesis"
    );

    let r = result.unwrap();
    let proof_context = r
        .proof_context()
        .expect("proofs using premises should expose a proof context");
    assert_eq!(
        proof_context.len(),
        1,
        "proof context should contain the single input hypothesis"
    );
    let inferred = r.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "proof term from auto_prove_with_premises should type-check: {:?}",
        inferred.err()
    );
}

#[path = "tests_query.rs"]
mod tests_query;
