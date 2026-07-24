// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for clause-to-proposition conversion and literal shape.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, ProofTrace, Term};
use clean_kernel::{ExprKind, FVarId};

/// Test clause_to_prop produces correct propositions.
#[test]
fn test_clause_to_prop() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let b_expr = Expr::const_(Name::from_string("b"), vec![]);
    map.add_symbol(0, a_expr, nat_ty.clone());
    map.add_symbol(1, b_expr, nat_ty);

    let dummy_clause = Clause {
        literals: vec![],
        id: 999,
        parents: vec![],
        inference: Inference::Input,
    };
    let trace = ProofTrace {
        empty_clause: dummy_clause.clone(),
        clauses: vec![dummy_clause],
    };
    let env = mk_test_env();
    let reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);

    // Empty clause -> False
    let empty = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let prop = reconstructor
        .clause_to_prop(&empty)
        .expect("invariant: clause_to_prop succeeded");
    assert_eq!(prop, Expr::const_(Name::from_string("False"), vec![]));

    // Single positive literal a = b -> @Eq Nat a b
    let single = Clause {
        literals: vec![Literal {
            lhs: Term::Const(0),
            rhs: Term::Const(1),
            positive: true,
        }],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let prop = reconstructor
        .clause_to_prop(&single)
        .expect("invariant: clause_to_prop succeeded");
    // Should be App(App(App(Eq, Nat), a), b)
    match prop.kind() {
        ExprKind::App(_, _) => {
            let head = prop.get_app_fn();
            assert!(
                matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq")),
                "single literal prop should be Eq application"
            );
        }
        _ => panic!("expected Eq application"),
    }

    // Negative literal a != b -> Not (@Eq Nat a b)
    let neg = Clause {
        literals: vec![Literal {
            lhs: Term::Const(0),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 2,
        parents: vec![],
        inference: Inference::Input,
    };
    let prop = reconstructor
        .clause_to_prop(&neg)
        .expect("invariant: clause_to_prop succeeded");
    let head = prop.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Not")),
        "negative literal should be Not application"
    );
}

/// Test that equality resolution `absurd` has correct 4-argument structure.
///
/// Lean 4 kernel `absurd` signature:
///   @absurd.{u} : {a : Prop} -> {b : Sort u} -> a -> not a -> b
///
/// All 4 arguments must be explicit in kernel Expr (kernel doesn't infer implicits):
///   1. a (the proposition, e.g., s = s)
///   2. b (the target, e.g., False)
///   3. h : a (proof of a, e.g., Eq.refl s)
///   4. h' : not a (proof of not a, from the parent clause)
#[test]
fn test_equality_resolution_absurd_four_args() {
    let mut map = SymbolMap::new();
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(0, a_expr, nat_ty);

    let fvar = FVarId::new(1);
    let neg_prop = Expr::const_(Name::from_string("h_neg"), vec![]);
    map.add_input_clause(0, fvar, neg_prop);

    let input_clause = Clause {
        literals: vec![Literal {
            lhs: Term::Const(0),
            rhs: Term::Const(0),
            positive: false,
        }],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    let empty_clause = Clause {
        literals: vec![],
        id: 1,
        parents: vec![0],
        inference: Inference::EqualityResolution(0),
    };

    let trace = ProofTrace {
        empty_clause: empty_clause.clone(),
        clauses: vec![input_clause, empty_clause],
    };

    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let (proof_term, _) = reconstructor
        .reconstruct()
        .expect("invariant: reconstruction succeeded");

    let (head, args) = decompose_app_spine(&proof_term);
    match head.kind() {
        ExprKind::Const(name, levels) if *name == Name::from_string("absurd") => {
            assert_eq!(
                args.len(),
                4,
                "absurd should have 4 args: a (prop), b (target), h_a, h_not_a"
            );
            assert_eq!(levels.len(), 1, "absurd has 1 universe level");
            assert!(
                levels[0].is_zero(),
                "absurd universe should be zero (target is False)"
            );

            // arg[0] = a (the Eq proposition: @Eq Nat a a)
            let a_head = args[0].get_app_fn();
            assert!(
                matches!(a_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq")),
                "first arg should be Eq proposition"
            );

            // arg[1] = b (False)
            assert!(
                matches!(args[1].kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
                "second arg should be False"
            );

            // arg[2] = h_a (Eq.refl proof)
            let h_a_head = args[2].get_app_fn();
            assert!(
                matches!(h_a_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq.refl")),
                "third arg should be Eq.refl proof"
            );

            // arg[3] = h_not_a (parent proof = FVar)
            assert!(
                matches!(args[3].kind(), ExprKind::FVar(_)),
                "fourth arg should be parent hypothesis (FVar)"
            );
        }
        other => panic!("expected absurd Const, got {other:?}"),
    }
}

/// Test literal_to_prop builds correct Eq and Not expressions.
#[test]
fn test_literal_to_prop_positive_and_negative() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    map.add_symbol(0, a_expr, nat_ty);

    let dummy_clause = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let trace = ProofTrace {
        empty_clause: dummy_clause.clone(),
        clauses: vec![dummy_clause],
    };
    let env = mk_test_env();
    let reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);

    // Positive: a = a -> Eq Nat a a
    let pos_lit = Literal {
        lhs: Term::Const(0),
        rhs: Term::Const(0),
        positive: true,
    };
    let pos_prop = reconstructor
        .literal_to_prop(&pos_lit)
        .expect("invariant: literal_to_prop succeeded");
    let args = pos_prop.get_app_args();
    assert_eq!(args.len(), 3, "Eq should have 3 args (type, lhs, rhs)");

    // Negative: a != a -> Not (Eq Nat a a)
    let neg_lit = Literal {
        lhs: Term::Const(0),
        rhs: Term::Const(0),
        positive: false,
    };
    let neg_prop = reconstructor
        .literal_to_prop(&neg_lit)
        .expect("invariant: literal_to_prop succeeded");
    let head = neg_prop.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Not"));
        }
        _ => panic!("expected Not constant"),
    }
}
