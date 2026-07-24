// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tactic proof term certification (`proof_cert_verify`).

use clean_kernel::env::Declaration;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId};

use super::core::{ProofState, TacticError};
use super::proof_cert_verify::{
    check_proof_relevance, check_universe_constraints, collect_all_diagnostics,
    collect_universe_levels, format_diagnostic, has_unresolved_metas, is_prop_type, verify_batch,
    verify_completed_proof, VerificationCheck, VerificationDiagnostic,
};
use super::proof_term::{apply, assumption, exact, intro, intros};

// =============================================================================
// Test environment setup
// =============================================================================

/// Minimal environment with types A, B, constants a : A, f : A -> B.
fn setup_env() -> Environment {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("B"), vec![]),
        ),
    })
    .unwrap();

    env
}

/// Environment with Prop-valued types for proof relevance tests.
fn setup_env_with_props() -> Environment {
    let mut env = setup_env();

    // A proposition P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // A proof hp : P
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    // Another proposition Q : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Implication imp : P -> Q
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("imp"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("Q"), vec![]),
        ),
    })
    .unwrap();

    env
}

// =============================================================================
// 1. verify_completed_proof: success cases
// =============================================================================

#[test]
fn test_verify_completed_proof_exact_succeeds() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();
    assert!(state.is_complete());

    let cert = verify_completed_proof(&state);
    assert!(cert.is_ok(), "exact proof should verify: {cert:?}");

    let cert = cert.unwrap();
    assert!(!cert.is_proof_relevant, "A is Type, not Prop");
}

#[test]
fn test_verify_completed_proof_intro_assumption_succeeds() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);
    intro(&mut state, "x").unwrap();
    assumption(&mut state).unwrap();
    assert!(state.is_complete());

    let cert = verify_completed_proof(&state);
    assert!(
        cert.is_ok(),
        "intro+assumption proof must verify (no FVar leak in cert path): {cert:?}"
    );
    let cert = cert.unwrap();
    // The proof term must be FVar-free: after `closed_proof()`, the
    // introduced free variable has been abstracted back into the lambda
    // binder. The proof should be `λ x:A. BVar(0)`, not
    // `λ x:A. FVar(<tactic-scope-id>)`.
    assert!(
        !cert.proof_term.has_fvar_quick(),
        "verified proof term must not leak any FVars; got {:?}",
        cert.proof_term
    );
}

#[test]
fn test_verify_completed_proof_apply_exact_succeeds() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    apply(&mut state, Expr::const_(Name::from_string("f"), vec![])).unwrap();
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();
    assert!(state.is_complete());

    let cert = verify_completed_proof(&state);
    assert!(cert.is_ok(), "apply+exact proof should verify: {cert:?}");
}

#[test]
fn test_verify_completed_proof_multi_binder() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a));

    let mut state = ProofState::new(env, target);
    intros(&mut state, vec!["x".to_string(), "y".to_string()]).unwrap();
    assumption(&mut state).unwrap();
    assert!(state.is_complete());

    let cert = verify_completed_proof(&state);
    assert!(
        cert.is_ok(),
        "multi-binder proof must verify (no cert-path FVar gap): {cert:?}"
    );
    let cert = cert.unwrap();
    // Both introduced FVars must be abstracted out — the closed proof
    // term must be FVar-free.
    assert!(
        !cert.proof_term.has_fvar_quick(),
        "multi-binder verified proof must not leak any FVars; got {:?}",
        cert.proof_term
    );
}

/// Wave 102 negative test: a proof that would only "succeed" by leaking
/// FVars must NOT be accepted. We construct a malformed proof state with
/// an open FVar that isn't bound by any lambda — `verify_completed_proof`
/// must surface this as an error rather than silently passing it through.
///
/// We use an unclosed `intro` (the FVar is still in scope as an open
/// hypothesis, but no `assumption`/`exact` has closed the goal). The
/// completeness check should reject it.
#[test]
fn test_verify_completed_proof_open_fvar_does_not_pass() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);
    intro(&mut state, "x").unwrap();
    // Do NOT close. The goal is open, the FVar is dangling.
    assert!(!state.is_complete());

    let result = verify_completed_proof(&state);
    assert!(
        result.is_err(),
        "an incomplete proof state with a dangling FVar must NOT verify; got {result:?}"
    );
    // The error must specifically flag the open goal — not silently
    // accept a malformed proof term.
    let err = result.unwrap_err();
    assert!(
        matches!(err, TacticError::UnsolvedGoals { .. }),
        "expected UnsolvedGoals on dangling-FVar state; got {err:?}"
    );
}

// =============================================================================
// 2. verify_completed_proof: failure cases
// =============================================================================

#[test]
fn test_verify_incomplete_proof_fails() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);
    intro(&mut state, "x").unwrap();
    // Do NOT close the goal — should fail completeness check.
    assert!(!state.is_complete());

    let result = verify_completed_proof(&state);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, TacticError::UnsolvedGoals { .. }));
}

#[test]
fn test_verify_no_proof_term_fails() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);
    // Never touched the state — no proof term

    let result = verify_completed_proof(&state);
    assert!(result.is_err());
}

// =============================================================================
// 3. has_unresolved_metas
// =============================================================================

#[test]
fn test_has_unresolved_metas_no_metas() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let expr = Expr::const_(Name::from_string("a"), vec![]);
    assert!(!has_unresolved_metas(&expr, &state));
}

#[test]
fn test_has_unresolved_metas_with_unassigned_meta() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    // MetaId(0) was created for the goal; it is unassigned.
    let meta_fvar = crate::unify::MetaState::to_fvar(crate::unify::MetaId(0));
    let expr = Expr::fvar(meta_fvar);
    assert!(has_unresolved_metas(&expr, &state));
}

#[test]
fn test_has_unresolved_metas_with_assigned_meta() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Close the goal so MetaId(0) is assigned.
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    let meta_fvar = crate::unify::MetaState::to_fvar(crate::unify::MetaId(0));
    let expr = Expr::fvar(meta_fvar);
    assert!(!has_unresolved_metas(&expr, &state));
}

#[test]
fn test_has_unresolved_metas_nested_in_app() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let meta_fvar = crate::unify::MetaState::to_fvar(crate::unify::MetaId(0));
    let expr = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::fvar(meta_fvar),
    );
    assert!(has_unresolved_metas(&expr, &state));
}

#[test]
fn test_has_unresolved_metas_in_lambda_domain() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let meta_fvar = crate::unify::MetaState::to_fvar(crate::unify::MetaId(0));
    let expr = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::fvar(meta_fvar),
        Expr::bvar(0),
    );
    assert!(has_unresolved_metas(&expr, &state));
}

#[test]
fn test_has_unresolved_metas_plain_fvar_not_meta() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    // A regular FVar (not a meta-FVar) should not be flagged.
    let expr = Expr::fvar(FVarId::new(42));
    assert!(!has_unresolved_metas(&expr, &state));
}

// =============================================================================
// 4. Universe constraint checks
// =============================================================================

#[test]
fn test_collect_universe_levels_from_sort() {
    let expr = Expr::sort(Level::succ(Level::zero()));
    let levels = collect_universe_levels(&expr);
    assert_eq!(levels.len(), 1);
}

#[test]
fn test_collect_universe_levels_from_nested_pi() {
    let expr = Expr::pi(
        clean_kernel::BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::sort(Level::succ(Level::zero())),
    );
    let levels = collect_universe_levels(&expr);
    assert_eq!(levels.len(), 2);
}

#[test]
fn test_check_universe_constraints_valid() {
    let expr = Expr::sort(Level::succ(Level::zero()));
    assert!(check_universe_constraints(&expr).is_ok());
}

#[test]
fn test_check_universe_constraints_nested_max() {
    let level = Level::max(Level::zero(), Level::succ(Level::zero()));
    let expr = Expr::sort(level);
    assert!(check_universe_constraints(&expr).is_ok());
}

#[test]
fn test_check_universe_constraints_param() {
    let level = Level::param(Name::from_string("u"));
    let expr = Expr::sort(level);
    assert!(check_universe_constraints(&expr).is_ok());
}

#[test]
fn test_collect_universe_levels_no_sorts() {
    let expr = Expr::const_(Name::from_string("A"), vec![]);
    let levels = collect_universe_levels(&expr);
    assert!(levels.is_empty());
}

// =============================================================================
// 5. Proof relevance checks
// =============================================================================

#[test]
fn test_is_prop_type_sort_zero() {
    assert!(is_prop_type(&Expr::prop()));
}

#[test]
fn test_is_prop_type_sort_one_not_prop() {
    assert!(!is_prop_type(&Expr::type_()));
}

#[test]
fn test_is_prop_type_non_sort() {
    assert!(!is_prop_type(&Expr::const_(Name::from_string("A"), vec![])));
}

#[test]
fn test_check_proof_relevance_prop_goal() {
    let env = setup_env_with_props();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let state = ProofState::new(env, p.clone());

    let goal = state.current_goal().unwrap();
    let result = check_proof_relevance(&state, goal);
    assert!(result, "P : Prop should be proof-relevant");
}

#[test]
fn test_check_proof_relevance_type_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, a.clone());

    let goal = state.current_goal().unwrap();
    let result = check_proof_relevance(&state, goal);
    assert!(!result, "A : Type should NOT be proof-relevant");
}

// =============================================================================
// 6. Batch verification
// =============================================================================

#[test]
fn test_verify_batch_all_succeed() {
    let env = setup_env();

    // Proof 1: exact a
    let mut state1 = ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    exact(&mut state1, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    // Proof 2: apply f; exact a
    let mut state2 = ProofState::new(env.clone(), Expr::const_(Name::from_string("B"), vec![]));
    apply(&mut state2, Expr::const_(Name::from_string("f"), vec![])).unwrap();
    exact(&mut state2, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    let result = verify_batch(&[&state1, &state2]);
    assert!(result.all_verified());
    assert_eq!(result.success_count(), 2);
    assert_eq!(result.failure_count(), 0);
}

#[test]
fn test_verify_batch_with_failure() {
    let env = setup_env();

    // Proof 1: exact a (complete)
    let mut state1 = ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    exact(&mut state1, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    // Proof 2: incomplete (just intro, no close)
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state2 = ProofState::new(env.clone(), Expr::arrow(a.clone(), a));
    intro(&mut state2, "x").unwrap();

    let result = verify_batch(&[&state1, &state2]);
    assert!(!result.all_verified());
    assert_eq!(result.success_count(), 1);
    assert_eq!(result.failure_count(), 1);
    assert_eq!(result.failures[0].check, VerificationCheck::Completeness);
    assert_eq!(result.failures[0].goal_index, Some(1));
}

#[test]
fn test_verify_batch_empty() {
    let result = verify_batch(&[]);
    assert!(result.all_verified());
    assert_eq!(result.success_count(), 0);
    assert_eq!(result.failure_count(), 0);
}

// =============================================================================
// 7. Diagnostic helpers
// =============================================================================

#[test]
fn test_format_diagnostic_with_goal_index() {
    let diag = VerificationDiagnostic {
        check: VerificationCheck::WellTypedness,
        message: "type mismatch".to_string(),
        goal_index: Some(2),
    };
    let formatted = format_diagnostic(&diag);
    assert!(formatted.contains("well-typedness"));
    assert!(formatted.contains("proof #2"));
    assert!(formatted.contains("type mismatch"));
}

#[test]
fn test_format_diagnostic_without_goal_index() {
    let diag = VerificationDiagnostic {
        check: VerificationCheck::MetavariableResolution,
        message: "unresolved meta".to_string(),
        goal_index: None,
    };
    let formatted = format_diagnostic(&diag);
    assert!(formatted.contains("metavariable resolution"));
    assert!(!formatted.contains("proof #"));
}

#[test]
fn test_collect_all_diagnostics_complete_proof() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    let diagnostics = collect_all_diagnostics(&state);
    assert!(
        diagnostics.is_empty(),
        "complete proof should have no diagnostics"
    );
}

#[test]
fn test_collect_all_diagnostics_incomplete_proof() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);
    let mut state = ProofState::new(env, target);
    intro(&mut state, "x").unwrap();

    let diagnostics = collect_all_diagnostics(&state);
    assert!(!diagnostics.is_empty());
    assert!(diagnostics
        .iter()
        .any(|d| d.check == VerificationCheck::Completeness));
}

// =============================================================================
// 8. VerificationCheck display
// =============================================================================

#[test]
fn test_verification_check_display() {
    assert_eq!(
        format!("{}", VerificationCheck::WellTypedness),
        "well-typedness"
    );
    assert_eq!(
        format!("{}", VerificationCheck::MetavariableResolution),
        "metavariable resolution"
    );
    assert_eq!(
        format!("{}", VerificationCheck::UniverseConstraints),
        "universe constraints"
    );
    assert_eq!(
        format!("{}", VerificationCheck::ProofRelevance),
        "proof relevance"
    );
    assert_eq!(
        format!("{}", VerificationCheck::CertificateVerification),
        "certificate verification"
    );
    assert_eq!(
        format!("{}", VerificationCheck::Completeness),
        "completeness"
    );
}

// =============================================================================
// 9. Certificate content checks
// =============================================================================

#[test]
fn test_verified_certificate_contains_proof_term() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target.clone());
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    let cert = verify_completed_proof(&state).unwrap();
    // The proof term should be the constant `a`
    assert!(
        matches!(cert.proof_term.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
        "proof term should be `a`, got {:?}",
        cert.proof_term
    );
    // Goal type should match
    assert!(
        matches!(cert.goal_type.kind(), ExprKind::Const(n, _) if n.to_string() == "A"),
        "goal type should be `A`, got {:?}",
        cert.goal_type
    );
}

#[test]
fn test_verified_certificate_prop_valued_goal() {
    let env = setup_env_with_props();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);
    exact(&mut state, Expr::const_(Name::from_string("hp"), vec![])).unwrap();

    let cert = verify_completed_proof(&state).unwrap();
    assert!(
        cert.is_proof_relevant,
        "P : Prop should flag proof relevance"
    );
}

#[test]
fn test_verified_certificate_type_valued_goal() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    let cert = verify_completed_proof(&state).unwrap();
    assert!(
        !cert.is_proof_relevant,
        "A : Type should NOT be proof relevant"
    );
}
