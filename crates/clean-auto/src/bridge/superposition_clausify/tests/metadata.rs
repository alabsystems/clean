// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metadata-stripping regressions for clausification.

use super::super::*;
use super::support::{mk_eq, wrap_mdata};

#[test]
fn test_clausify_mdata_wrapped_conjunction() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let eq_a_a = mk_eq(nat.clone(), a.clone(), a);
    let eq_b_b = mk_eq(nat, b.clone(), b);

    let and_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), eq_a_a),
        eq_b_b,
    );

    let mut plain = GoalClausifier::new();
    let (plain_clauses, _) = plain.clausify_goal(&and_expr);

    let mdata_and = wrap_mdata(and_expr);
    let mut mdata = GoalClausifier::new();
    let (mdata_clauses, _) = mdata.clausify_goal(&mdata_and);

    assert_eq!(
        plain_clauses.len(),
        mdata_clauses.len(),
        "MData-wrapped And should match"
    );
    for (plain_clause, mdata_clause) in plain_clauses.iter().zip(mdata_clauses.iter()) {
        assert_eq!(
            plain_clause.len(),
            mdata_clause.len(),
            "clause literal counts should match"
        );
    }
}

#[test]
fn test_expr_to_term_mdata_stripped() {
    let a = Expr::const_(Name::from_string("delta"), vec![]);
    let mdata_a = wrap_mdata(a.clone());

    let mut clausifier = GoalClausifier::new();
    let term_plain = clausifier.expr_to_term(&a);
    let term_mdata = clausifier.expr_to_term(&mdata_a);

    assert_eq!(
        term_plain, term_mdata,
        "MData-wrapped should produce same term"
    );
}

#[test]
fn test_expr_to_term_mdata_on_head() {
    let f = Expr::const_(Name::from_string("myFunc"), vec![]);
    let a = Expr::const_(Name::from_string("arg1"), vec![]);

    let plain_app = Expr::app(f.clone(), a.clone());
    let mdata_f = wrap_mdata(f);
    let mdata_app = Expr::app(mdata_f, a);

    let mut clausifier = GoalClausifier::new();
    let term_plain = clausifier.expr_to_term(&plain_app);
    let term_mdata = clausifier.expr_to_term(&mdata_app);

    assert_eq!(term_plain, term_mdata, "MData on head should be stripped");
}

#[test]
fn test_clausify_mdata_wrapped_or_not_atomic() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let eq_a_a = mk_eq(nat.clone(), a.clone(), a);
    let eq_b_b = mk_eq(nat, b.clone(), b);

    let or_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_a_a),
        eq_b_b,
    );
    let mdata_or = wrap_mdata(or_expr);

    let mut clausifier = GoalClausifier::new();
    let (clauses, _) = clausifier.clausify_goal(&mdata_or);

    assert_eq!(
        clauses.len(),
        2,
        "MData-wrapped Or should decompose into 2 clauses"
    );
}
