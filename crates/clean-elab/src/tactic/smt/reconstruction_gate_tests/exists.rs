// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exists-placeholder closure and solver-backed witness integration coverage.

#[cfg(feature = "ay-smt")]
use super::super::*;
#[cfg(feature = "ay-smt")]
use super::support::*;
#[cfg(feature = "ay-smt")]
use crate::tactic::hypothesis::collect_fvars;
#[cfg(feature = "ay-smt")]
use crate::tactic::{LocalDecl, ProofState};
#[cfg(feature = "ay-smt")]
use clean_kernel::name::Name;
#[cfg(feature = "ay-smt")]
use clean_kernel::{Environment, Expr, Level, TypeChecker};
#[cfg(feature = "ay-smt")]
use serial_test::serial;

#[cfg(feature = "ay-smt")]
fn mk_exists_false_prop() -> (Expr, Expr) {
    let binder_ty = Expr::prop();
    let predicate = Expr::lam(
        clean_kernel::BinderInfo::Default,
        binder_ty.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    let exists_prop = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            binder_ty,
        ),
        predicate.clone(),
    );
    (exists_prop, predicate)
}

/// Environment with Exists, True/False, Classical, plus axiom P : Prop.
#[cfg(feature = "ay-smt")]
fn mk_exists_gate_env() -> (Environment, Expr, Expr, Expr) {
    let mut env = Environment::new();
    env.init_true_false().expect("init True/False");
    env.init_exists().expect("init Exists");
    env.init_classical().expect("init Classical");
    add_axiom(&mut env, "P", Expr::prop());

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let neg_p = mk_negated(&p);
    let (exists_expr, _predicate) = mk_exists_false_prop();
    (env, p, neg_p, exists_expr)
}

/// Register an existential hypothesis through the real solver path and return
/// the solver, hypothesis FVarId, and cloned bindings.
#[cfg(feature = "ay-smt")]
fn register_exists_hypothesis_in_solver(
    exists_expr: &Expr,
) -> (
    SmtSolver,
    clean_kernel::FVarId,
    Vec<ay_solver::ExistsWitnessBinding>,
) {
    use super::super::ay_solver::create_smt_backend;
    use crate::unify::MetaState;
    use clean_auto::bridge::ay_contract::AyLogic;
    use clean_kernel::FVarId;

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    let hyp_fvar = FVarId::new(41);
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("existential hypothesis should register in solver context");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, exists_expr)
        .expect("existential hypothesis should assert through the witness-aware path");

    let bindings = solver.exists_witness_bindings().to_vec();
    (solver, hyp_fvar, bindings)
}

/// Verify the finalized proof type-checks as `expected` in a context with the
/// given hypothesis.
#[cfg(feature = "ay-smt")]
fn assert_proof_typechecks_with_hyp(
    env: Environment,
    expected: &Expr,
    proof: &Expr,
    hyp_fvar: clean_kernel::FVarId,
    hyp_ty: Expr,
) {
    let mut state = ProofState::new(env, expected.clone());
    state
        .goals
        .front_mut()
        .expect("main goal should exist")
        .local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex".to_string(),
        ty: hyp_ty,
        value: None,
    }];
    let goal = state.current_goal().expect("goal should exist").clone();
    let tc = TypeChecker::with_context(state.env(), state.build_local_ctx(&goal));
    let inferred = tc.whnf(&tc.infer_type(proof).expect("proof should typecheck"));
    assert_eq!(inferred, *expected, "proof should prove the expected goal");
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_finalize_kernel_reconstruction_candidate_closes_exists_placeholders_before_validation() {
    let mut env = Environment::new();
    env.init_true_false().expect("init True/False");
    env.init_exists().expect("init Exists");
    env.init_classical().expect("init Classical");
    add_axiom(&mut env, "P", Expr::prop());

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let neg_p = mk_negated(&p);
    let (exists_prop, predicate) = mk_exists_false_prop();
    let source_hyp_fvar = clean_kernel::FVarId::new(41);
    let witness_fvar = clean_kernel::FVarId::new(42);
    let witness_proof_fvar = clean_kernel::FVarId::new(43);
    let binding = ay_solver::ExistsWitnessBinding {
        skolem_smt_name: "sk_exists_0".to_string(),
        source_hyp_fvar,
        source_exists_proof: Expr::fvar(source_hyp_fvar),
        source_exists_levels: vec![Level::succ(Level::zero())],
        binder_type: Expr::prop(),
        predicate,
        witness_fvar,
        witness_proof_fvar,
    };

    let (proof, trust_count, _residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(
            &p,
            &neg_p,
            mk_candidate(Expr::fvar(witness_proof_fvar), None, 0),
            &[binding],
        );

    assert_eq!(trust_count, 0);
    assert!(
        contains_const(&proof, "Exists.elim"),
        "finalized proof should explicitly close witness placeholders with Exists.elim"
    );
    let proof_fvars = collect_fvars(&proof);
    assert!(
        !proof_fvars.contains(&witness_fvar) && !proof_fvars.contains(&witness_proof_fvar),
        "finalized proof must not leak existential placeholder FVars"
    );

    let mut state = ProofState::new(env, p.clone());
    state
        .goals
        .front_mut()
        .expect("main goal should exist")
        .local_ctx = vec![LocalDecl {
        fvar: source_hyp_fvar,
        name: "hex".to_string(),
        ty: exists_prop,
        value: None,
    }];
    let goal = state.current_goal().expect("goal should exist").clone();
    let tc = TypeChecker::with_context(state.env(), state.build_local_ctx(&goal));
    let inferred = tc
        .infer_type(&proof)
        .expect("finalized proof should typecheck in the original goal context");
    let inferred = tc.whnf(&inferred);
    assert_eq!(
        inferred, p,
        "finalized proof should prove the original goal"
    );
}

/// Integration test bridging solver registration with reconstruction closure.
/// Exercises the full ExistsWitnessBinding lifecycle: real translator
/// skolemization → VariableMapping registration → finalize → Exists.elim closing.
/// Addresses #2830 P1 finding: prior tests constructed bindings synthetically.
#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_finalize_with_solver_registered_exists_bindings() {
    let (env, p, neg_p, exists_expr) = mk_exists_gate_env();
    let (solver, hyp_fvar, bindings) = register_exists_hypothesis_in_solver(&exists_expr);
    assert_eq!(
        bindings.len(),
        1,
        "exactly one existential binding expected"
    );
    let binding = &bindings[0];

    // Verify VariableMapping bridges SMT skolem name to the placeholder FVar.
    let (registered_expr, _) = solver
        .registered_var("sk_exists_0")
        .expect("solver VariableMapping should contain the registered skolem");
    assert_eq!(
        registered_expr,
        &Expr::fvar(binding.witness_fvar),
        "VariableMapping must bridge the SMT name to the binding's FVar"
    );

    // Pass a refutation referencing the real placeholder through the gate.
    let (proof, trust_count, _residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(
            &p,
            &neg_p,
            mk_candidate(Expr::fvar(binding.witness_proof_fvar), None, 0),
            &bindings,
        );

    assert_eq!(trust_count, 0);
    assert!(contains_const(&proof, "Exists.elim"));
    let proof_fvars = collect_fvars(&proof);
    assert!(
        !proof_fvars.contains(&binding.witness_fvar)
            && !proof_fvars.contains(&binding.witness_proof_fvar),
        "no placeholder FVars may leak into the final proof"
    );
    assert_proof_typechecks_with_hyp(env, &p, &proof, hyp_fvar, exists_expr);
}
