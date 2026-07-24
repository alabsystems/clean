// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier and Skolemization tests.

use super::super::*;
use super::support::mk_eq;
use clean_kernel::ExprKind;

#[test]
fn test_clausify_forall_goal_skolemizes() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let forall_goal = Expr::pi(BinderInfo::Default, nat, eq_x_x);

    let (clauses, map) = clausifier.clausify_goal(&forall_goal);

    assert_eq!(
        clauses.len(),
        1,
        "negated forall goal should produce 1 clause"
    );
    assert_eq!(
        clauses[0].len(),
        1,
        "the Skolemized clause should have 1 literal"
    );
    assert!(
        !clauses[0][0].positive,
        "negated equality should be negative"
    );
    assert_eq!(
        clauses[0][0].lhs, clauses[0][0].rhs,
        "Skolemized x=x should have same lhs and rhs term"
    );

    let resolved = map
        .term_to_expr(&clauses[0][0].lhs)
        .expect("Skolem symbol should be in symbol map");
    match resolved.kind() {
        ExprKind::Const(name, _) => {
            let name_str = format!("{name:?}");
            assert!(
                name_str.contains("sk_"),
                "resolved Skolem should have sk_ prefix, got {name_str}"
            );
        }
        _ => panic!(
            "Skolem term should resolve to Const expression, got {:?}",
            resolved
        ),
    }
}

#[test]
fn test_clausify_skolem_declarations_registered() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let forall_goal = Expr::pi(BinderInfo::Default, nat.clone(), eq_x_x);

    let (_clauses, map) = clausifier.clausify_goal(&forall_goal);

    let skolems = map.skolem_declarations();
    assert_eq!(
        skolems.len(),
        1,
        "should produce 1 Skolem constant, got {}",
        skolems.len()
    );

    let (name, ty) = &skolems[0];
    let name_str = format!("{name:?}");
    assert!(
        name_str.contains("sk_"),
        "Skolem name should start with 'sk_', got {name_str}"
    );
    assert_eq!(*ty, nat, "Skolem constant type should be Nat");
}

#[test]
fn test_clausify_forall_hypothesis_uses_var() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let forall_hyp = Expr::pi(BinderInfo::Default, nat, eq_x_x);

    let fvar_id = FVarId::new(500);
    let clauses = clausifier.clausify_hypothesis(&forall_hyp, 10, fvar_id);

    assert_eq!(
        clauses.len(),
        1,
        "universal hypothesis should produce 1 clause"
    );
    assert_eq!(clauses[0].len(), 1);
    assert!(clauses[0][0].positive, "hypothesis should be positive");
    assert!(
        clauses[0][0].lhs.is_var(),
        "lhs should be Term::Var, got {:?}",
        clauses[0][0].lhs
    );
    assert!(
        clauses[0][0].rhs.is_var(),
        "rhs should be Term::Var, got {:?}",
        clauses[0][0].rhs
    );
    assert_eq!(
        clauses[0][0].lhs, clauses[0][0].rhs,
        "forall x. x=x should have same variable"
    );
}

#[test]
fn test_clausify_forall_goal_still_skolemizes() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let forall_goal = Expr::pi(BinderInfo::Default, nat, eq_x_x);

    let (clauses, _map) = clausifier.clausify_goal(&forall_goal);

    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 1);
    assert!(
        !clauses[0][0].lhs.is_var(),
        "negated forall (goal) should Skolemize to Term::Const, not Term::Var"
    );
}

#[test]
fn test_clausify_exists_goal_uses_var() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let exists_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            nat.clone(),
        ),
        Expr::lam(BinderInfo::Default, nat, eq_x_x),
    );

    let (clauses, _map) = clausifier.clausify_goal(&exists_goal);

    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 1);
    assert!(
        clauses[0][0].lhs.is_var(),
        "negated exists should use Term::Var, got {:?}",
        clauses[0][0].lhs
    );
}

#[test]
fn test_clausify_exists_hypothesis_still_skolemizes() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let bvar0 = Expr::bvar(0);
    let eq_x_x = mk_eq(nat.clone(), bvar0.clone(), bvar0);
    let exists_hyp = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            nat.clone(),
        ),
        Expr::lam(BinderInfo::Default, nat, eq_x_x),
    );

    let fvar_id = FVarId::new(501);
    let clauses = clausifier.clausify_hypothesis(&exists_hyp, 11, fvar_id);

    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 1);
    assert!(
        !clauses[0][0].lhs.is_var(),
        "exists hypothesis should Skolemize to Term::Const, not Term::Var"
    );
}

#[test]
fn test_clausify_nested_forall_distinct_vars() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fx = Expr::app(f.clone(), Expr::bvar(1));
    let fy = Expr::app(f, Expr::bvar(0));
    let eq_fx_fy = mk_eq(nat.clone(), fx, fy);
    let inner_forall = Expr::pi(BinderInfo::Default, nat.clone(), eq_fx_fy);
    let outer_forall = Expr::pi(BinderInfo::Default, nat, inner_forall);

    let fvar_id = FVarId::new(502);
    let clauses = clausifier.clausify_hypothesis(&outer_forall, 12, fvar_id);

    assert_eq!(clauses.len(), 1, "nested forall should produce 1 clause");
    assert_eq!(clauses[0].len(), 1);

    let lhs = &clauses[0][0].lhs;
    let rhs = &clauses[0][0].rhs;
    match (lhs, rhs) {
        (Term::App(_, lhs_args), Term::App(_, rhs_args)) => {
            assert_eq!(lhs_args.len(), 1);
            assert_eq!(rhs_args.len(), 1);
            assert!(
                lhs_args[0].is_var(),
                "f's arg should be a variable, got {:?}",
                lhs_args[0]
            );
            assert!(
                rhs_args[0].is_var(),
                "f's arg should be a variable, got {:?}",
                rhs_args[0]
            );
            assert_ne!(
                lhs_args[0], rhs_args[0],
                "nested forall should produce distinct variables"
            );
        }
        _ => panic!(
            "expected App terms for f(x) and f(y), got {:?} and {:?}",
            lhs, rhs
        ),
    }
}
