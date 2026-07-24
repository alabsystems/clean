// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof construction in finite case-splitting tactics.
//!
//! Covers:
//! - `build_or_elim_chain` structural correctness (P1 gap: zero direct tests prior)
//! - `interval_cases` bound extraction and error paths
//! - `fin_cases` on `Fin n` (Or.rec fallback path)
//!
//! Regression coverage for #2480: the Or.rec fallback path must preserve
//! dependent targets in sub-goals instead of eagerly substituting the split
//! value. Bool/PUnit use proper dependent recursors and continue to specialize
//! targets directly.

use super::super::finite_cases_proof::build_or_elim_chain;
use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;

/// Build `@LT.lt.{0} Nat instLTNat lhs rhs`.
/// Mirrors `make_nat_le_tc` but for strict inequality.
fn make_nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::nat_lt_tc(lhs, rhs)
}

/// Environment with Classical.em + Or + Or.rec + Eq + Nat, suitable for
/// testing `build_or_elim_chain` and `interval_cases`.
fn setup_env_for_interval_cases() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_classical().unwrap();

    // R : Nat → Prop (target predicate for tests)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty, Expr::prop()),
    })
    .unwrap();

    env
}

// =========================================================================
// build_or_elim_chain direct structural tests
// =========================================================================

/// Direct test: build_or_elim_chain for 2 values produces a well-structured
/// Or.rec proof term with the correct head constant.
#[test]
fn test_build_or_elim_chain_two_values_structure() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::prop(); // constant target (no FVar dependency)

    let mut state = ProofState::new(env, target.clone());
    let hyp_fvar = state.fresh_fvar();

    let meta_0 = state.metas.fresh(target.clone());
    let meta_1 = state.metas.fresh(target.clone());
    let goals = vec![
        Goal {
            meta_id: meta_0,
            target: target.clone(),
            local_ctx: vec![],
            tag: None,
        },
        Goal {
            meta_id: meta_1,
            target: target.clone(),
            local_ctx: vec![],
            tag: None,
        },
    ];

    let values = vec![make_nat_literal(0), make_nat_literal(1)];

    let proof = build_or_elim_chain(&mut state, &target, hyp_fvar, &nat_ty, &goals, &values, 0);
    assert!(
        proof.is_ok(),
        "build_or_elim_chain for 2 values should succeed, got: {proof:?}"
    );
    let proof = proof.unwrap();

    // Top level should be Or.rec application
    let head = proof.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Or.rec",
            "proof head should be Or.rec, got: {}",
            name
        );
    } else {
        panic!("proof head should be a Const(Or.rec), got: {head:?}");
    }
}

/// Direct test: build_or_elim_chain for a single value (base case) returns
/// the meta directly without Or.rec wrapping.
#[test]
fn test_build_or_elim_chain_single_value_returns_meta() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::prop();

    let mut state = ProofState::new(env, target.clone());
    let hyp_fvar = state.fresh_fvar();

    let meta_0 = state.metas.fresh(target.clone());
    let goals = vec![Goal {
        meta_id: meta_0,
        target: target.clone(),
        local_ctx: vec![],
        tag: None,
    }];
    let values = vec![make_nat_literal(0)];

    let proof = build_or_elim_chain(&mut state, &target, hyp_fvar, &nat_ty, &goals, &values, 0);
    assert!(proof.is_ok());
    let proof = proof.unwrap();

    // Single value: base case returns FVar(MetaState::to_fvar(meta_0)) directly
    assert!(
        matches!(proof.kind(), ExprKind::FVar(_)),
        "single-value chain should return a bare FVar (meta), got: {proof:?}"
    );
}

/// Direct test: build_or_elim_chain for 3 values produces nested Or.rec.
#[test]
fn test_build_or_elim_chain_three_values_nested() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::prop();

    let mut state = ProofState::new(env, target.clone());
    let hyp_fvar = state.fresh_fvar();

    let mut goals = Vec::new();
    let mut values = Vec::new();
    for i in 0..3 {
        let meta = state.metas.fresh(target.clone());
        goals.push(Goal {
            meta_id: meta,
            target: target.clone(),
            local_ctx: vec![],
            tag: None,
        });
        values.push(make_nat_literal(i));
    }

    let proof = build_or_elim_chain(&mut state, &target, hyp_fvar, &nat_ty, &goals, &values, 0);
    assert!(
        proof.is_ok(),
        "build_or_elim_chain for 3 values should succeed"
    );
    let proof = proof.unwrap();

    // Top-level Or.rec
    let head = proof.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Or.rec");
    } else {
        panic!("expected Or.rec head, got: {head:?}");
    }

    // Count Or.rec nesting depth
    fn count_or_rec_depth(expr: &Expr) -> usize {
        let head = expr.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            if name.to_string() == "Or.rec" {
                let args = expr.get_app_args();
                if args.len() >= 5 {
                    if let ExprKind::Lam(_, _, body) = args[4].kind() {
                        return 1 + count_or_rec_depth(body);
                    }
                }
                return 1;
            }
        }
        0
    }

    let depth = count_or_rec_depth(&proof);
    assert_eq!(
        depth, 2,
        "3-value chain should have Or.rec depth 2 (outer + inner), got {depth}"
    );
}

// =========================================================================
// #2480 regression coverage: dependent targets on the Or.rec fallback path
// =========================================================================

/// Regression for #2480: dependent interval goals now keep their original
/// target and rely on the generated equality hypothesis for case refinement.
#[test]
fn test_interval_cases_dependent_target_succeeds() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    // Goal: R(n) where n : Nat, with 2 ≤ n and n ≤ 4 in context
    let mut state = ProofState::new(env, Expr::prop());
    let n_fvar = state.fresh_fvar();
    let target = Expr::app(r_const.clone(), Expr::fvar(n_fvar));
    state.goals[0].target = target.clone();

    state.goals[0].local_ctx.push(LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    });

    let h_lower_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_lower_fvar,
        name: "h_lower".to_string(),
        ty: make_nat_le_tc(make_nat_literal(2), Expr::fvar(n_fvar)),
        value: None,
    });

    let h_upper_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_upper_fvar,
        name: "h_upper".to_string(),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(4)),
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(
        result.is_ok(),
        "interval_cases with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(
        state.goals.len(),
        3,
        "interval_cases should create 3 sub-goals"
    );
    for goal in &state.goals {
        assert_eq!(
            goal.target, target,
            "dependent interval sub-goals should preserve the original target"
        );
        assert!(
            goal.local_ctx.iter().any(|decl| decl.name == "n_eq"),
            "dependent interval sub-goals should carry the generated equality hypothesis"
        );
    }
}

/// Same regression for LT bounds: 1 < n < 5 with dependent target R(n).
#[test]
fn test_interval_cases_lt_dependent_target_succeeds() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let mut state = ProofState::new(env, Expr::prop());
    let n_fvar = state.fresh_fvar();
    let target = Expr::app(r_const, Expr::fvar(n_fvar));
    state.goals[0].target = target.clone();

    state.goals[0].local_ctx.push(LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    });

    let h_lower_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_lower_fvar,
        name: "h_lower".to_string(),
        ty: make_nat_lt_tc(make_nat_literal(1), Expr::fvar(n_fvar)),
        value: None,
    });

    let h_upper_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_upper_fvar,
        name: "h_upper".to_string(),
        ty: make_nat_lt_tc(Expr::fvar(n_fvar), make_nat_literal(5)),
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(
        result.is_ok(),
        "interval_cases LT with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(
        state.goals.len(),
        3,
        "strict interval should create 3 sub-goals"
    );
    for goal in &state.goals {
        assert_eq!(goal.target, target);
        assert!(goal.local_ctx.iter().any(|decl| decl.name == "n_eq"));
    }
}

/// Single-value intervals also stay type-correct for dependent targets.
#[test]
fn test_interval_cases_single_value_dependent_target_succeeds() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let mut state = ProofState::new(env, Expr::prop());
    let n_fvar = state.fresh_fvar();
    let target = Expr::app(r_const, Expr::fvar(n_fvar));
    state.goals[0].target = target.clone();

    state.goals[0].local_ctx.push(LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    });

    let h_lower_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_lower_fvar,
        name: "h_lower".to_string(),
        ty: make_nat_le_tc(make_nat_literal(3), Expr::fvar(n_fvar)),
        value: None,
    });

    let h_upper_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_upper_fvar,
        name: "h_upper".to_string(),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(3)),
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(
        result.is_ok(),
        "single-value interval_cases with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(state.goals.len(), 1);
    assert_eq!(state.goals[0].target, target);
    assert!(state.goals[0]
        .local_ctx
        .iter()
        .any(|decl| decl.name == "n_eq"));
}

// =========================================================================
// interval_cases error-path tests (these correctly fail)
// =========================================================================

/// interval_cases rejects inconsistent bounds (lower > upper).
#[test]
fn test_interval_cases_inconsistent_bounds_error() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("R"), vec![]));
    let n_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    });

    let h1_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h1_fvar,
        name: "h1".to_string(),
        ty: make_nat_le_tc(make_nat_literal(5), Expr::fvar(n_fvar)),
        value: None,
    });
    let h2_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h2_fvar,
        name: "h2".to_string(),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(2)),
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(result.is_err(), "inconsistent bounds should fail");
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("inconsistent"),
        "error should mention inconsistency, got: {err_msg}"
    );
}

/// interval_cases rejects ranges > 100 values.
#[test]
fn test_interval_cases_rejects_large_range() {
    let env = setup_env_for_interval_cases();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("R"), vec![]));
    let n_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    });

    let h1_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h1_fvar,
        name: "h1".to_string(),
        ty: make_nat_le_tc(make_nat_literal(0), Expr::fvar(n_fvar)),
        value: None,
    });
    let h2_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h2_fvar,
        name: "h2".to_string(),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(200)),
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(result.is_err(), "range > 100 should be rejected");
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("range too large"),
        "error should mention range size, got: {err_msg}"
    );
}

// =========================================================================
// expr_to_int edge cases
// =========================================================================

/// expr_to_int handles Nat.succ chains correctly.
#[test]
fn test_expr_to_int_succ_chain() {
    let expr = make_nat_literal(2);
    assert_eq!(expr_to_int(&expr), Some(2));
}

/// expr_to_int returns None for non-numeric expressions.
#[test]
fn test_expr_to_int_non_numeric() {
    let non_numeric = Expr::const_(Name::from_string("Bool"), vec![]);
    assert_eq!(expr_to_int(&non_numeric), None);
}

/// expr_to_int handles Nat literals (not just succ chains).
#[test]
fn test_expr_to_int_nat_literal() {
    use clean_kernel::expr::{BigNat, Literal};
    let lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    assert_eq!(expr_to_int(&lit), Some(42));
}
