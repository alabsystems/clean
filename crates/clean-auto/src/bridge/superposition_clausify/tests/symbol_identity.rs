// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symbol identity regressions for `expr_to_term`.

use super::super::*;

#[test]
fn test_distinct_exprs_get_distinct_symbols() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("alpha"), vec![]);
    let b = Expr::const_(Name::from_string("beta"), vec![]);

    let term_a = clausifier.expr_to_term(&a);
    let term_b = clausifier.expr_to_term(&b);

    assert_ne!(
        term_a, term_b,
        "distinct constants must get distinct symbols"
    );
}

#[test]
fn test_same_expr_gets_same_symbol() {
    let mut clausifier = GoalClausifier::new();
    let a1 = Expr::const_(Name::from_string("gamma"), vec![]);
    let a2 = Expr::const_(Name::from_string("gamma"), vec![]);

    let term1 = clausifier.expr_to_term(&a1);
    let term2 = clausifier.expr_to_term(&a2);

    assert_eq!(
        term1, term2,
        "identical expressions must map to the same symbol"
    );
}

#[test]
fn test_fvar_exprs_distinct_symbols() {
    let mut clausifier = GoalClausifier::new();
    let fvar1 = Expr::fvar(FVarId::new(1));
    let fvar2 = Expr::fvar(FVarId::new(2));

    let term1 = clausifier.expr_to_term(&fvar1);
    let term2 = clausifier.expr_to_term(&fvar2);

    assert_ne!(
        term1, term2,
        "FVars with different ids must get distinct symbols"
    );
}

#[test]
fn test_unkeyable_exprs_get_fresh_symbols() {
    let mut clausifier = GoalClausifier::new();
    let sort1 = Expr::type_();
    let sort2 = Expr::type_();

    let term1 = clausifier.expr_to_term(&sort1);
    let term2 = clausifier.expr_to_term(&sort2);

    assert_ne!(
        term1, term2,
        "un-keyable expressions must get fresh symbols each time"
    );
}
