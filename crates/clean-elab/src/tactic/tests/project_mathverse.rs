// Copyright 2026 Andrew Yates
// Author: dbx-clean-ai
// SPDX-License-Identifier: Apache-2.0

//! Tests for the project-specific mathverse wrapper.

use super::*;
use crate::tactic::arith_mathverse_parse::expr_to_linear;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::cast::{rewrite_local_decls_with_cast_lemmas, CastRewriteFlavor};
use crate::tactic::registry::TacticRegistry;
use clean_kernel::env::Declaration;

#[test]
fn test_cert_mathverse_registered() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    assert!(
        registry.get("cert_mathverse").is_some(),
        "cert_mathverse should be registered as a nullary tactic"
    );
}

#[test]
fn test_cert_mathverse_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    let goal = state
        .current_goal()
        .expect("test fixture should have an active goal")
        .clone();
    state
        .close_goal(&goal, proof)
        .expect("test fixture proof should close the current goal");

    let result = cert_mathverse(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_cert_mathverse_runs_cert_simp_hook_before_mathverse() {
    let mut state = cert_simp_equality_state();

    let report = cert_mathverse_with_report(&mut state)
        .expect("cert_mathverse should run cert_simp before mathverse");

    assert!(matches!(
        report.mathverse_result,
        ProjectMathverseOutcome::Closed
    ));
    assert!(
        report.normalized_target_changed || report.normalized_hyp_count > 0,
        "cert_mathverse should record the cert_simp normalization/closeout"
    );
    assert!(state.is_complete(), "cert_simp hook should close the goal");
    assert_eq!(state.trusted_axiom_count(), 0);
}

#[test]
fn test_cert_mathverse_uses_cert_simp_to_expose_certificate_arithmetic() {
    let mut state = cert_pb_bound_contradiction_state();
    let report = cert_mathverse_with_report(&mut state)
        .expect("cert_mathverse should normalize certificate arithmetic before mathverse");

    assert!(matches!(
        report.mathverse_result,
        ProjectMathverseOutcome::Closed
    ));
    assert!(
        report.normalized_hyp_count > 0 || report.normalized_target_changed,
        "cert_mathverse should record the cert_simp normalization that exposed arithmetic"
    );
    assert!(state.is_complete(), "exposed contradiction should close");
    assert_eq!(state.trusted_axiom_count(), 0);
}

#[test]
fn test_cert_mathverse_closes_contradictory_nat_linear_hypothesis() {
    reset_all_counters();

    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3));
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    cert_mathverse(&mut state).expect("cert_mathverse should delegate to mathverse and close");
    assert!(state.is_complete(), "cert_mathverse should close the goal");
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
}

#[test]
fn test_project_mathverse_zify_rewrites_local_hypotheses_without_trust() {
    let mut env = setup_project_mathverse_cast_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    add_axiom(&mut env, "m", nat.clone());
    add_axiom(&mut env, "n", nat);

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = app2("Nat.le", m.clone(), n.clone());
    let target = app2("Int.le", int_of_nat(m), int_of_nat(n));
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    let rewrites =
        rewrite_local_decls_with_cast_lemmas(&mut state, "cert_mathverse", CastRewriteFlavor::Zify)
            .expect("local zify rewrite should succeed");
    assert_eq!(rewrites, 1);
    assert_eq!(state.trusted_axiom_count(), 0);
    let h = state
        .current_goal()
        .expect("goal should remain open")
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should keep its user-facing name");
    assert!(expr_contains_const(&h.ty, "Int.le"));
    assert!(expr_contains_const(&h.ty, "Int.ofNat"));
}

#[test]
fn test_cert_mathverse_records_nat_coercion_before_calling_mathverse() {
    let mut env = setup_project_mathverse_cast_env();
    env.init_true_false().unwrap();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_ty = app2("Nat.le", Expr::nat_lit(5), Expr::nat_lit(3));
    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    let report = cert_mathverse_with_report(&mut state)
        .expect("cert_mathverse should close the zified contradiction");
    assert!(matches!(
        report.mathverse_result,
        ProjectMathverseOutcome::Closed
    ));
    assert!(
        report.nat_coercion_count > 0,
        "cert_mathverse should record proof-carrying Nat-to-Int coercion"
    );
    assert!(
        state.is_complete(),
        "cert_mathverse should close the contradiction"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
}

#[test]
fn test_cert_mathverse_reports_nat_sub_without_mutating_state() {
    let n = FVarId::new(0);
    let m = FVarId::new(1);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_sub_nm = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            Expr::fvar(n),
        ),
        Expr::fvar(m),
    );
    let target = make_nat_le_tc(nat_sub_nm, Expr::fvar(n));
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        target.clone(),
        vec![
            LocalDecl {
                fvar: n,
                name: "n".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: m,
                name: "m".into(),
                ty: nat,
                value: None,
            },
        ],
    );

    let result = cert_mathverse(&mut state);
    let err = result.expect_err("cert_mathverse should block unsupported Nat.sub");
    match err {
        TacticError::ArithmeticFailed { tactic, reason } => {
            assert_eq!(tactic, "cert_mathverse");
            assert!(
                reason.contains("NatSubWithoutSideCondition"),
                "reason should name the Nat.sub blocker: {reason}"
            );
            assert!(
                reason.contains("Nat.sub"),
                "reason should include the unsimplified blocker expression: {reason}"
            );
        }
        other => panic!("expected cert_mathverse ArithmeticFailed, got {other:?}"),
    }
    assert!(
        !state.is_complete(),
        "failed cert_mathverse run must leave the original goal open"
    );
    assert_eq!(
        state.current_goal().expect("goal should remain").target,
        target,
        "failed cert_mathverse run should not mutate the target"
    );
}

#[test]
fn test_cert_mathverse_with_side_conditions_reports_missing_nat_sub_support() {
    let n = FVarId::new(0);
    let m = FVarId::new(1);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_sub_nm = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            Expr::fvar(n),
        ),
        Expr::fvar(m),
    );
    let target = make_nat_le_tc(nat_sub_nm, Expr::fvar(n));
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        target.clone(),
        vec![
            LocalDecl {
                fvar: n,
                name: "n".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: m,
                name: "m".into(),
                ty: nat,
                value: None,
            },
        ],
    );
    let config = ProjectMathverseConfig {
        coerce_nat: NatCoercionPolicy::WithSideConditions,
        ..Default::default()
    };

    let report = cert_mathverse_with_config(&mut state, &config)
        .expect("cert_mathverse should report side-condition blockers structurally");

    assert!(
        matches!(report.mathverse_result, ProjectMathverseOutcome::NoProgress),
        "unexpected report: {report:#?}"
    );
    assert!(
        report
            .blockers
            .iter()
            .any(|blocker| blocker.kind == MathverseBlockerKind::MissingRewriteLemma),
        "WithSideConditions should report that Nat.sub side-condition rewrite support is absent"
    );
    assert!(
        report
            .blockers
            .iter()
            .any(|blocker| blocker.kind == MathverseBlockerKind::NatSubWithoutSideCondition),
        "raw Nat.sub should still be reported as an unsimplified blocker"
    );
    assert!(
        !state.is_complete(),
        "failed cert_mathverse run must leave the original goal open"
    );
    assert_eq!(
        state.current_goal().expect("goal should remain").target,
        target
    );
}

#[test]
fn test_mathverse_linear_parser_strips_int_of_nat() {
    let n = FVarId::new(42);
    let expr = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::fvar(n),
    );

    let lin = expr_to_linear(&expr, None).expect("Int.ofNat fvar should parse as linear");
    assert_eq!(lin.constant, 0);
    assert_eq!(lin.coeff_ref(n.as_u64() as usize), Some(&1));
}

fn setup_project_mathverse_cast_env() -> Environment {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas().unwrap();
    env
}

fn cert_simp_equality_state() -> ProofState {
    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let target = Expr::pi(
        BinderInfo::Default,
        h_ty,
        make_eq(a_ty, Expr::app(f.clone(), a), Expr::app(f, b)),
    );
    let mut state = ProofState::new(env, target);
    intro(&mut state, "h").expect("intro should expose local equality");
    state
}

fn cert_pb_bound_contradiction_state() -> ProofState {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Cert.PB.checkBound"),
        level_params: vec![],
        type_: Expr::prop(),
        value: make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3)),
        is_reducible: true,
    })
    .unwrap();

    ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: Expr::const_(Name::from_string("Cert.PB.checkBound"), vec![]),
            value: None,
        }],
    )
}

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn app2(name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(name), vec![]), lhs),
        rhs,
    )
}

fn int_of_nat(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), expr)
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, arg) => expr_contains_const(f, needle) || expr_contains_const(arg, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, needle)
        }
        _ => false,
    }
}
