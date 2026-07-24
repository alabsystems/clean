// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for equality factoring proof reconstruction with >2 literal parents.
//!
//! Split from tests.rs to stay within file size limits.
//! Covers the multi-literal Or.rec recursion path that tests.rs's
//! 2-literal test does not exercise.

use super::*;
use crate::superposition::{Clause, Inference, Literal, ProofTrace, Term};
use clean_kernel::{Environment, ExprKind, FVarId};

/// Create a minimal environment with Nat so sort inference works in unit tests.
fn mk_test_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env
}

/// Decompose an expression into head + spine of App arguments (by reference).
fn decompose_app_spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut current = expr;
    let mut args = vec![];
    while let ExprKind::App(f, a) = current.kind() {
        args.push(a.as_ref());
        current = f;
    }
    args.reverse();
    (current, args)
}

/// Build a trace with 3 positive literals: s=t1 ∨ s=t2 ∨ s=t3.
///
/// Result: s=t1 ∨ t1≠t2 ∨ s=t3 (3 literals).
fn mk_three_lit_trace() -> (ProofTrace, SymbolMap) {
    let mut map = SymbolMap::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(0, Expr::const_(Name::from_string("s"), vec![]), nat.clone());
    map.add_symbol(
        1,
        Expr::const_(Name::from_string("t1"), vec![]),
        nat.clone(),
    );
    map.add_symbol(
        2,
        Expr::const_(Name::from_string("t2"), vec![]),
        nat.clone(),
    );
    map.add_symbol(3, Expr::const_(Name::from_string("t3"), vec![]), nat);
    map.add_input_clause(
        0,
        FVarId::new(1),
        Expr::const_(Name::from_string("h_parent"), vec![]),
    );

    let mk_eq = |l, r| Literal {
        lhs: Term::Const(l),
        rhs: Term::Const(r),
        positive: true,
    };
    let mk_neq = |l, r| Literal {
        lhs: Term::Const(l),
        rhs: Term::Const(r),
        positive: false,
    };

    let parent = Clause {
        literals: vec![mk_eq(0, 1), mk_eq(0, 2), mk_eq(0, 3)],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let factored = Clause {
        literals: vec![mk_eq(0, 1), mk_neq(1, 2), mk_eq(0, 3)],
        id: 1,
        parents: vec![0],
        inference: Inference::EqualityFactoring(0),
    };
    let trace = ProofTrace {
        empty_clause: factored.clone(),
        clauses: vec![parent, factored],
    };
    (trace, map)
}

/// Test equality factoring reconstruction with 3-literal parent.
///
/// Parent: s=t1 ∨ s=t2 ∨ s=t3
/// Result: s=t1 ∨ t1≠t2 ∨ s=t3
///
/// Exercises the recursive Or.rec path for >2 literals that the
/// 2-literal test in tests.rs does not cover.
#[test]
fn test_reconstruct_equality_factoring_three_literals() {
    let (trace, map) = mk_three_lit_trace();
    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let proof = reconstructor
        .reconstruct_clause(1)
        .expect("3-literal factoring reconstruction should succeed");

    // Top-level: Or.rec case analysis on the 3-literal parent
    let (head, args) = decompose_app_spine(&proof);
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or.rec")),
        "3-literal factoring proof head should be Or.rec, got {:?}",
        head.kind()
    );
    assert_eq!(
        args.len(),
        6,
        "Or.rec needs 6 args (a, b, motive, f_inl, f_inr, h)"
    );

    // f_inr (args[4]): lambda whose body is a NESTED Or.rec
    // for the remaining 2 parent literals (s=t2 ∨ s=t3)
    if let ExprKind::Lam(_, _, body) = args[4].kind() {
        let (inner_head, inner_args) = decompose_app_spine(body);
        assert!(
            matches!(inner_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or.rec")),
            "inner f_inr body should be nested Or.rec for 3-literal parent, got {:?}",
            inner_head.kind()
        );
        assert_eq!(inner_args.len(), 6, "inner Or.rec needs 6 args");
    } else {
        panic!("f_inr should be a lambda, got {:?}", args[4].kind());
    }
}
