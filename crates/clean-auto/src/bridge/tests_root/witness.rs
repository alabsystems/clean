// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_create_witness_term_registers_in_maps() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let tid = bridge.create_witness_term("test_witness_0", &a_ty);

    assert!(
        bridge.term_to_expr.contains_key(&tid),
        "create_witness_term must register in term_to_expr"
    );

    let stored_ty = bridge.term_to_type.get(&tid).cloned();
    assert_eq!(
        stored_ty,
        Some(a_ty),
        "create_witness_term must register witness type in term_to_type"
    );

    let expr = bridge
        .term_to_expr
        .get(&tid)
        .expect("create_witness_term must register an expression");
    assert!(
        matches!(expr.kind(), ExprKind::FVar(_)),
        "witness expr should be an FVar"
    );
}

#[test]
fn test_instantiate_body_with_witness_terms() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let witness_tid = bridge.create_witness_term("witness_0", &a_ty);
    let body = make_eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(0));

    let result = bridge.instantiate_body_with_terms(&body, &[0], &[witness_tid]);
    assert!(
        result.is_some(),
        "instantiate_body_with_terms must return Some when witnesses are registered"
    );

    let instantiated = result.expect("registered witness terms should instantiate");
    let witness_expr = bridge
        .term_to_expr
        .get(&witness_tid)
        .expect("witness term must have a registered expression")
        .clone();
    let expected = make_eq(a_ty, witness_expr.clone(), witness_expr);
    assert_eq!(
        instantiated, expected,
        "instantiated body should have witness FVar substituted for BVar"
    );
}
