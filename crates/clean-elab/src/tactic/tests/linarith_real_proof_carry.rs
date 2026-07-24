// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral regression tests for Real linarith proof reconstruction.
//!
//! These run the public `linarith` entry point end-to-end so Phase 2 replay
//! coverage includes actual Real goals, not just the proof-builder helpers.

use super::*;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use serial_test::serial;

fn mk_rel(rel_name: &str, ty_name: &str, inst_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(rel_name), vec![Level::zero()]),
                    Expr::const_(Name::from_string(ty_name), vec![]),
                ),
                Expr::const_(Name::from_string(inst_name), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn make_real_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LE.le", "Real", "instLEReal", lhs, rhs)
}

fn make_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name == &Name::from_string(needle),
        ExprKind::App(f, a) => expr_contains_const(f, needle) || expr_contains_const(a, needle),
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

fn real_false_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize for Real linarith replay");
    env.init_real_linear_order()
        .expect("Real linear order axioms should initialize for Real linarith replay");
    env
}

/// End-to-end single-hypothesis replay for a concrete Real contradiction.
///
/// Part of #302.
#[test]
#[serial]
fn test_linarith_real_single_concrete_replay_avoids_trusted_axioms() {
    use crate::tactic::arith_linarith::linarith;

    reset_all_counters();

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_real_le_tc(make_real_ofnat(5), make_real_ofnat(3));
    let mut state = ProofState::with_context(
        real_false_env(),
        false_const,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    let axiom_before = axiom_snapshot();
    let result = linarith(&mut state);

    assert!(
        result.is_ok(),
        "linarith should replay the concrete Real contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "linarith should close the concrete Real contradiction goal"
    );
    assert_no_trusted_axiom_usage(
        "linarith",
        "single concrete Real contradiction via certified replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.sorry_count, 0);

    let proof = state
        .proof_term()
        .expect("completed Real contradiction state should retain a proof term");
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "single Real contradiction replay should downcast through Real.ofInt_le_to_Int"
    );
}

/// End-to-end chain replay for concrete Real bounds with an intermediate local.
///
/// Part of #302.
#[test]
#[serial]
fn test_linarith_real_chain_concrete_replay_avoids_trusted_axioms() {
    use crate::tactic::arith_linarith::linarith;

    reset_all_counters();

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let x_id = FVarId::new(0);
    let h1_id = FVarId::new(1);
    let h2_id = FVarId::new(2);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let h1_ty = make_real_le_tc(make_real_ofnat(5), Expr::fvar(x_id));
    let h2_ty = make_real_le_tc(Expr::fvar(x_id), make_real_ofnat(3));
    let mut state = ProofState::with_context(
        real_false_env(),
        false_const,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: real_ty,
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = linarith(&mut state);

    assert!(
        result.is_ok(),
        "linarith should replay the concrete Real chain contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "linarith should close the concrete Real chain contradiction goal"
    );
    assert_no_trusted_axiom_usage(
        "linarith",
        "concrete Real chain contradiction via certified replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.sorry_count, 0);

    let proof = state
        .proof_term()
        .expect("completed Real chain state should retain a proof term");
    assert!(
        expr_contains_const(&proof, "Real.le_trans"),
        "Real chain replay should build the chain with Real.le_trans"
    );
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "Real chain replay should close through the Real-to-Int downcast path"
    );
}

/// End-to-end replay for a symbolic integer-valued Real additive contradiction (#2621).
///
/// Hypothesis: h : Real.add(Real.ofInt m)(Real.ofNat 5) ≤ Real.add(Real.ofInt m)(Real.ofNat 3)
///
/// The additive tree normalizer downcasts to `Int.add m (Int.ofNat 5) ≤ Int.add m (Int.ofNat 3)`,
/// then the Int closer cancels the shared `m` addend and closes concretely.
#[test]
#[serial]
fn test_linarith_real_symbolic_additive_replay_avoids_trusted_axioms() {
    use crate::tactic::arith_linarith::linarith;

    fn make_real_ofint(e: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Real.ofInt"), vec![]), e)
    }
    fn make_real_add(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), a),
            b,
        )
    }

    reset_all_counters();

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let m_id = FVarId::new(0);
    let h_id = FVarId::new(1);
    let m = Expr::fvar(m_id);
    let h_ty = make_real_le_tc(
        make_real_add(make_real_ofint(m.clone()), make_real_ofnat(5)),
        make_real_add(make_real_ofint(m.clone()), make_real_ofnat(3)),
    );
    let mut state = ProofState::with_context(
        real_false_env(),
        false_const,
        vec![
            LocalDecl {
                fvar: m_id,
                name: "m".into(),
                ty: Expr::const_(Name::from_string("Int"), vec![]),
                value: None,
            },
            LocalDecl {
                fvar: h_id,
                name: "h".into(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = linarith(&mut state);

    assert!(
        result.is_ok(),
        "linarith should replay the symbolic Real additive contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "linarith should close the symbolic Real additive contradiction goal"
    );
    assert_no_trusted_axiom_usage(
        "linarith",
        "symbolic integer-valued Real additive contradiction via certified replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.sorry_count, 0);

    let proof = state
        .proof_term()
        .expect("completed symbolic Real additive state should retain a proof term");
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int"),
        "symbolic Real additive replay should downcast through Real.ofInt_le_to_Int"
    );
    assert!(
        expr_contains_const(&proof, "Int.le_of_add_le_add_left")
            || expr_contains_const(&proof, "Int.le_of_add_le_add_right"),
        "symbolic Real additive replay should cancel the shared addend"
    );
}

/// End-to-end additive (non-chaining) replay for two concrete Real contradictions.
///
/// Hypotheses: h1: 3_Real ≤ 2_Real, h2: 5_Real ≤ 4_Real
/// These don't form a chain (no shared intermediate term), so linarith must use
/// the additive path (add_le_add) to sum them into 8_Real ≤ 6_Real, then
/// downcast to Int and close via NonNeg.casesOn.
///
/// Part of #302.
#[test]
#[serial]
fn test_linarith_real_additive_concrete_replay_avoids_trusted_axioms() {
    use crate::tactic::arith_linarith::linarith;

    reset_all_counters();

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);
    let h1_ty = make_real_le_tc(make_real_ofnat(3), make_real_ofnat(2));
    let h2_ty = make_real_le_tc(make_real_ofnat(5), make_real_ofnat(4));
    let mut state = ProofState::with_context(
        real_false_env(),
        false_const,
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = linarith(&mut state);

    assert!(
        result.is_ok(),
        "linarith should replay the additive Real contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "linarith should close the additive Real contradiction goal"
    );
    assert_no_trusted_axiom_usage(
        "linarith",
        "additive concrete Real contradiction via certified replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.sorry_count, 0);

    let proof = state
        .proof_term()
        .expect("completed Real additive state should retain a proof term");
    assert!(
        expr_contains_const(&proof, "Real.ofInt_le_to_Int")
            || expr_contains_const(&proof, "Real.add_le_add_left")
            || expr_contains_const(&proof, "Real.add_le_add_right"),
        "additive Real replay should use Real downcast or additive combination lemmas"
    );
}
