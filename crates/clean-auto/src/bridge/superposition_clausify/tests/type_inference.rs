// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment-backed and fail-closed type inference tests.

use super::super::*;
use super::support::{mk_eq, mk_nat_env_with_test_consts};

#[test]
fn test_clausifier_with_env_infers_nat_type() {
    let (env, nat_ty, a, b) = mk_nat_env_with_test_consts();
    let goal = mk_eq(nat_ty.clone(), a, b);

    let mut clausifier = GoalClausifier::new_with_env(&env);
    let (clauses, symbol_map) = clausifier.clausify_goal(&goal);

    assert_eq!(clauses.len(), 1);
    let lit = &clauses[0][0];
    let lhs_type = symbol_map.term_type(&lit.lhs).expect("lhs type");
    assert_eq!(lhs_type, nat_ty, "with env, term_type(testA) should be Nat");
}

#[test]
fn test_clausifier_without_env_reports_missing_type() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = mk_eq(nat, a, b);

    let mut clausifier = GoalClausifier::new();
    let (clauses, symbol_map) = clausifier.clausify_goal(&goal);

    assert_eq!(clauses.len(), 1);
    let lit = &clauses[0][0];
    let result = symbol_map.term_type(&lit.lhs);
    assert!(
        result.is_err(),
        "without env, term_type should return an error for missing type metadata, \
         but got: {result:?}"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("sort inference failed"),
        "error should be SortInferenceFailed, got: {err_msg}"
    );
}

#[test]
fn test_clausifier_with_env_fvar_reports_missing_type() {
    let (env, nat_ty, _, _) = mk_nat_env_with_test_consts();
    let fvar_expr = Expr::fvar(FVarId::new(42));
    let goal = mk_eq(
        nat_ty,
        fvar_expr,
        Expr::const_(Name::from_string("testA"), vec![]),
    );

    let mut clausifier = GoalClausifier::new_with_env(&env);
    let (clauses, symbol_map) = clausifier.clausify_goal(&goal);

    assert_eq!(clauses.len(), 1);
    let lit = &clauses[0][0];
    let fvar_result = symbol_map.term_type(&lit.lhs);
    assert!(
        fvar_result.is_err(),
        "FVar without local context should produce a type error, got: {fvar_result:?}"
    );
    let err_msg = format!("{}", fvar_result.unwrap_err());
    assert!(
        err_msg.contains("sort inference failed"),
        "FVar type error should be SortInferenceFailed, got: {err_msg}"
    );
}
