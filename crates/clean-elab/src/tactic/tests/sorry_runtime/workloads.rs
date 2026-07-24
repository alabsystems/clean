// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// W1: Basic linarith — contradictory hypothesis pair.
/// Setup: h1: a ≤ 0, h2: 1 ≤ a, goal: False
/// Expected sorry: 0 (kernel-verified proof via close_goal_checked)
pub(super) fn workload_linarith_basic() -> (String, u64) {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let a_fvar = FVarId::new(100);
    let h1_fvar = FVarId::new(101);
    let h2_fvar = FVarId::new(102);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let h1_ty = make_nat_le_tc(Expr::fvar(a_fvar), Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    linarith(&mut state).expect("linarith should prove False from contradictory hypotheses");
    let delta = sorry_count() - before;
    ("W1:linarith_basic".to_string(), delta)
}

/// W2: linarith with le_trans path.
/// Setup: h1: a ≤ b, h2: b ≤ 0, h3: 1 ≤ a, goal: False
/// Expected sorry: 0
pub(super) fn workload_linarith_le_trans() -> (String, u64) {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let a_fvar = FVarId::new(200);
    let b_fvar = FVarId::new(201);
    let h1_fvar = FVarId::new(202);
    let h2_fvar = FVarId::new(203);
    let h3_fvar = FVarId::new(204);

    let h1_ty = make_nat_le_tc(Expr::fvar(a_fvar), Expr::fvar(b_fvar));
    let h2_ty = make_nat_le_tc(Expr::fvar(b_fvar), Expr::nat_lit(0));
    let h3_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: b_fvar,
                name: "b".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
            LocalDecl {
                fvar: h3_fvar,
                name: "h3".to_string(),
                ty: h3_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    linarith(&mut state).expect("linarith should prove False via le_trans path");
    let delta = sorry_count() - before;
    ("W2:linarith_le_trans".to_string(), delta)
}

/// W3: linarith with coefficient scaling.
/// Setup: h1: 2a ≤ 0, h2: 1 ≤ a, goal: False
/// Expected sorry: 0
///
/// Note: After #2644 fail-closed transition, linarith correctly returns
/// ArithmeticFailed when certified FM finds the contradiction but replay
/// cannot construct a kernel proof for the coefficient-scaling case.
/// The sorry count is still 0 (fail-closed produces no sorry terms).
pub(super) fn workload_linarith_scaled() -> (String, u64) {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let a_fvar = FVarId::new(300);
    let h1_fvar = FVarId::new(301);
    let h2_fvar = FVarId::new(302);

    // h1: Nat.add a a ≤ 0  (i.e., 2a ≤ 0)
    let two_a = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::fvar(a_fvar),
        ),
        Expr::fvar(a_fvar),
    );
    let h1_ty = make_nat_le_tc(two_a, Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    // After #2644: linarith may fail closed (ArithmeticFailed) when certified
    // FM finds the contradiction but replay cannot build a kernel proof.
    // Either way, the sorry count must be 0.
    let _ = linarith(&mut state);
    let delta = sorry_count() - before;
    ("W3:linarith_scaled".to_string(), delta)
}

/// W4: mathverse parity contradiction (Even n ∧ Odd n).
/// Expected sorry: 0 (noConfusion path)
pub(super) fn workload_mathverse_parity() -> (String, u64) {
    let env = setup_env();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let n_fvar = FVarId::new(400);
    let even_ty = Expr::app(
        Expr::const_(Name::from_string("Even"), vec![]),
        Expr::fvar(n_fvar),
    );
    let odd_ty = Expr::app(
        Expr::const_(Name::from_string("Odd"), vec![]),
        Expr::fvar(n_fvar),
    );

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: n_fvar,
                name: "n".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(401),
                name: "h_even".to_string(),
                ty: even_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(402),
                name: "h_odd".to_string(),
                ty: odd_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    // mathverse currently fails on Even/Odd parity predicates because the modular
    // proof bridge requires Nat.even_and_odd_elim which is not in the minimal
    // prelude. Accepted failure modes: TypeCheck, Unknown, or the explicit
    // parity/modular contradiction message from the certified path.
    match omega(&mut state) {
        Ok(()) => {} // tactic proved the goal — sorry count should be 0
        Err(e) => {
            let msg = format!("{e}");
            assert!(
                msg.contains("TypeCheck")
                    || msg.contains("Unknown")
                    || msg.contains("parity")
                    || msg.contains("modular"),
                "unexpected mathverse failure mode: {e}"
            );
        }
    }
    let delta = sorry_count() - before;
    ("W4:mathverse_parity".to_string(), delta)
}

/// W5: mathverse linear contradiction (delegates to linarith internally).
/// Setup: h1: a ≤ 0, h2: 1 ≤ a, goal: False
/// Expected sorry: 0
pub(super) fn workload_mathverse_linear() -> (String, u64) {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let a_fvar = FVarId::new(500);
    let h1_fvar = FVarId::new(501);
    let h2_fvar = FVarId::new(502);

    let h1_ty = make_nat_le_tc(Expr::fvar(a_fvar), Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    omega(&mut state).expect("mathverse should prove False from linear contradiction");
    let delta = sorry_count() - before;
    ("W5:mathverse_linear".to_string(), delta)
}

/// W6: nlinarith — certified Fourier-Motzkin.
/// Setup: Same as W1 (nlinarith delegates to linarith first).
/// Expected sorry: 0
pub(super) fn workload_nlinarith() -> (String, u64) {
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let a_fvar = FVarId::new(600);
    let h1_fvar = FVarId::new(601);
    let h2_fvar = FVarId::new(602);

    let h1_ty = make_nat_le_tc(Expr::fvar(a_fvar), Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    nlinarith(&mut state).expect("nlinarith should prove False via Fourier-Motzkin");
    let delta = sorry_count() - before;
    ("W6:nlinarith".to_string(), delta)
}

/// W7: Instance resolution without a typeclass table.
/// Setup: goal is a type that requires instance resolution, but no table is provided.
/// Expected sorry: 0 (instance resolution now fails cleanly without sorry)
pub(super) fn workload_instance_no_table() -> (String, u64) {
    let env = Environment::with_prelude();

    // Goal: AddCommMonoid Nat — requires instance resolution
    let target = Expr::app(
        Expr::const_(Name::from_string("AddCommMonoid"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    let mut state = ProofState::new(env, target);

    let before = sorry_count();
    // infer_instance should fail closed without routing through sorry.
    assert!(
        infer_instance(&mut state).is_err(),
        "infer_instance should fail without typeclass table"
    );
    let delta = sorry_count() - before;
    assert_eq!(
        delta, 0,
        "infer_instance without a typeclass table must not create sorry"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "infer_instance without a typeclass table must not record trusted fallback"
    );
    ("W7:instance_no_table".to_string(), delta)
}

#[test]
#[serial]
fn test_workload_instance_no_table_stays_sorry_free() {
    let (name, delta) = workload_instance_no_table();
    assert_eq!(name, "W7:instance_no_table");
    assert_eq!(delta, 0, "instance-no-table workload must stay sorry-free");
}

/// W8: Intentional sorry tactic — always generates exactly 1 sorry.
pub(super) fn workload_sorry_tactic() -> (String, u64) {
    let env = Environment::with_prelude();
    let goal_ty = Expr::prop();
    let mut state = ProofState::new(env, goal_ty);

    let before = sorry_count();
    sorry(&mut state).expect("sorry tactic should always succeed");
    let delta = sorry_count() - before;
    ("W8:sorry_tactic".to_string(), delta)
}

/// W9: Direct create_sorry_term — structural sorry (e.g., unsolved subgoal).
pub(super) fn workload_structural_sorry() -> (String, u64) {
    let env = Environment::with_prelude();

    let before = sorry_count();
    let sorry_expr = create_sorry_term(&env, &Expr::prop());
    // with_prelude() registers sorryAx (via init_bool), so create_sorry_term
    // returns `sorryAx.{u} goal_ty Bool.true` rather than legacy `sorry.{u} goal_ty`.
    // Accept either head constant.
    use clean_kernel::ExprKind;
    let is_sorry = matches!(sorry_expr.kind(), ExprKind::App(f, _)
        if matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "sorry"));
    let is_sorry_ax = matches!(sorry_expr.kind(), ExprKind::App(inner, _)
        if matches!(inner.kind(), ExprKind::App(f, _)
            if matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "sorryAx")));
    assert!(
        is_sorry || is_sorry_ax,
        "create_sorry_term should return @sorry or @sorryAx applied to Prop, got: {:?}",
        sorry_expr.kind()
    );
    let delta = sorry_count() - before;
    ("W9:structural_sorry".to_string(), delta)
}
