// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused end-to-end proof-chain regressions for `field_simp` (#1143).

use super::*;
use clean_kernel::{env::Declaration, ExprKind};
use serial_test::serial;

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn field_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Div.div"), vec![]), lhs),
        rhs,
    )
}

fn field_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Mul.mul"), vec![]), lhs),
        rhs,
    )
}

fn field_ne_zero(carrier: &Expr, value: Expr, zero: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                carrier.clone(),
            ),
            value,
        ),
        zero.clone(),
    )
}

fn field_iff(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lhs),
        rhs,
    )
}

fn make_div_eq_div_test_env() -> (Environment, Expr, Expr, Expr, Expr) {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_iff().unwrap();
    env.init_propext().unwrap();

    let carrier = Expr::const_(Name::from_string("Carrier"), vec![]);
    let zero = Expr::const_(Name::from_string("zero"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let binop = Expr::arrow(
        carrier.clone(),
        Expr::arrow(carrier.clone(), carrier.clone()),
    );

    add_axiom(&mut env, "Carrier", Expr::type_());
    add_axiom(&mut env, "zero", carrier.clone());
    add_axiom(&mut env, "x", carrier.clone());
    add_axiom(&mut env, "y", carrier.clone());
    add_axiom(&mut env, "Div.div", binop.clone());
    add_axiom(&mut env, "Mul.mul", binop);
    add_axiom(
        &mut env,
        "div_eq_div_iff",
        Expr::arrow(
            field_ne_zero(&carrier, y.clone(), &zero),
            Expr::arrow(
                field_ne_zero(&carrier, y.clone(), &zero),
                field_iff(
                    make_eq(
                        carrier.clone(),
                        field_div(x.clone(), y.clone()),
                        field_div(x.clone(), y.clone()),
                    ),
                    make_eq(
                        carrier.clone(),
                        field_mul(x.clone(), y.clone()),
                        field_mul(x.clone(), y.clone()),
                    ),
                ),
            ),
        ),
    );

    (env, carrier, zero, x, y)
}

fn assert_field_simp_closed_proof_chain(state: &ProofState, check_ctx: clean_kernel::LocalContext) {
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "field_simp should stay trust-free on the fully discharged path"
    );
    assert!(
        state.is_complete(),
        "field_simp should close the rewritten goal and both denominator premises"
    );
    assert!(
        state.metas().unassigned().is_empty(),
        "field_simp should not leave any unassigned metas after the proof completes"
    );

    let proof_term = state
        .proof_term()
        .expect("field_simp should preserve proof_term() extraction");
    let proof_args: Vec<_> = proof_term.get_app_args().into_iter().cloned().collect();
    assert_eq!(
        proof_args.len(),
        4,
        "field_simp proof chain should remain an Eq.mpr application"
    );
    assert!(
        matches!(
            proof_term.get_app_fn().kind(),
            ExprKind::Const(name, _) if name.to_string() == "Eq.mpr"
        ),
        "field_simp proof term should be rooted in Eq.mpr, got {proof_term:?}"
    );
    assert!(
        matches!(
            proof_args[2].get_app_fn().kind(),
            ExprKind::Const(name, _) if name.to_string() == "propext"
        ),
        "field_simp target-rewrite proof should be rooted in propext, got {:?}",
        proof_args[2]
    );

    let closed_proof = state
        .closed_proof()
        .expect("field_simp should preserve closed_proof() extraction");
    let goal_ty = state
        .goal_type()
        .expect("completed field_simp state should retain the original goal type");
    let tc = TypeChecker::with_context(state.env(), check_ctx);
    assert!(
        tc.check_type(&closed_proof, &goal_ty).is_ok(),
        "field_simp closed proof must type-check against the original goal type"
    );
}

#[test]
#[serial]
fn test_field_simp_div_eq_div_refl_assumption_path_preserves_proof_chain() {
    let (env, carrier, zero, x, y) = make_div_eq_div_test_env();
    let goal_target = make_eq(
        carrier.clone(),
        field_div(x.clone(), y.clone()),
        field_div(x.clone(), y.clone()),
    );
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "hy".to_string(),
        ty: field_ne_zero(&carrier, y.clone(), &zero),
        value: None,
    }];

    reset_all_counters();
    let mut state = ProofState::with_context(env, goal_target, ctx);
    state.fvar_base = state.next_fvar;
    let original_goal = state
        .current_goal()
        .expect("field_simp test needs a goal")
        .clone();

    let result = field_simp(&mut state);
    assert!(
        result.is_ok(),
        "field_simp on x/y = x/y with y != 0 in context should succeed: {result:?}"
    );
    let check_ctx = state.build_local_ctx(&original_goal);
    assert_field_simp_closed_proof_chain(&state, check_ctx);
}
