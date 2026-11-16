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
//! The `interval_cases` dependent-target (#2480) and branch-equality (#2533)
//! regressions live in `interval_cases_descent.rs`, since `interval_cases`
//! no longer routes through `build_or_elim_chain`: every branch's `n_eq` must
//! be BOUND by a real binder over a real proof, at an FVar id inside the
//! goal's tactic-binder window. The load-bearing test there is
//! `test_interval_cases_branches_consume_n_eq_and_close_proof`, which actually
//! USES each equality and then demands a fully closed proof term — a "fix"
//! that merely silenced the goal-scope guard cannot pass it.

use super::super::finite_cases_proof::build_or_elim_chain;
use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;

/// Environment with Classical.em + Or + Or.rec + Eq + Nat, suitable for
/// testing `build_or_elim_chain` and `interval_cases`' pre-proof error paths.
///
/// Deliberately thin: its transitive closure is `init_nat` (which only pulls in
/// `init_bool`) plus `init_classical`, so it contains NO `LE`, `LT`, `Nat.le`,
/// and no Nat order lemma whatsoever. `interval_cases`' bound detection is
/// syntactic (`match_le`/`match_lt` head-name matching), so a `≤` hypothesis
/// still parses here — which is exactly what
/// `test_interval_cases_disengages_without_order_lemmas` pins.
pub(super) fn setup_env_for_interval_cases() -> Environment {
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
            case_binders: Vec::new(),
        },
        Goal {
            meta_id: meta_1,
            target: target.clone(),
            local_ctx: vec![],
            tag: None,
            case_binders: Vec::new(),
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
        case_binders: Vec::new(),
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
            case_binders: Vec::new(),
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
        binder_info: Default::default(),
        fvar: n_fvar,
        name: clean_parser::SurfaceName::generated_path("n"),
        ty: nat_ty.clone(),
        value: None,
    });

    let h1_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        binder_info: Default::default(),
        fvar: h1_fvar,
        name: clean_parser::SurfaceName::generated_path("h1"),
        ty: make_nat_le_tc(make_nat_literal(5), Expr::fvar(n_fvar)),
        value: None,
    });
    let h2_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        binder_info: Default::default(),
        fvar: h2_fvar,
        name: clean_parser::SurfaceName::generated_path("h2"),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(2)),
        value: None,
    });

    let result = interval_cases(&mut state, &clean_parser::SurfaceName::generated_path("n"));
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
        binder_info: Default::default(),
        fvar: n_fvar,
        name: clean_parser::SurfaceName::generated_path("n"),
        ty: nat_ty.clone(),
        value: None,
    });

    let h1_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        binder_info: Default::default(),
        fvar: h1_fvar,
        name: clean_parser::SurfaceName::generated_path("h1"),
        ty: make_nat_le_tc(make_nat_literal(0), Expr::fvar(n_fvar)),
        value: None,
    });
    let h2_fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        binder_info: Default::default(),
        fvar: h2_fvar,
        name: clean_parser::SurfaceName::generated_path("h2"),
        ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(200)),
        value: None,
    });

    let result = interval_cases(&mut state, &clean_parser::SurfaceName::generated_path("n"));
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
