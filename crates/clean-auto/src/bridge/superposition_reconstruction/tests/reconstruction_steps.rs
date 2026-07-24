// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for individual reconstruction steps (input, equality resolution,
//! superposition, demodulation, equality factoring).

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::{BinderInfo, ExprKind, FVarId};

/// Test reconstruction of a trivial input clause.
#[test]
fn test_reconstruct_input() {
    let mut map = SymbolMap::new();
    let fvar = FVarId::new(42);
    let prop = Expr::const_(Name::from_string("True"), vec![]);
    map.add_input_clause(0, fvar, prop);

    let input_clause = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    let trace = ProofTrace {
        empty_clause: input_clause.clone(),
        clauses: vec![input_clause],
    };

    let reconstructor = SuperpositionReconstructor::new(&trace, &map);
    let _proof_term = reconstructor
        .reconstruct_input(0)
        .expect("reconstruct_input should succeed for mapped clause");
}

/// Test reconstruction of equality resolution: from s != s derive false.
#[test]
fn test_reconstruct_equality_resolution() {
    let mut map = SymbolMap::new();
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(0, a_expr, nat_ty);

    // Input clause: a != a (the negated goal)
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

    // Empty clause derived by equality resolution on the input
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
    let result = reconstructor.reconstruct();
    assert!(
        result.is_ok(),
        "reconstruction should succeed: {:?}",
        result.err()
    );
    let (proof_term, description) = result.expect("invariant: reconstruction succeeded");
    assert!(
        description.contains("Superposition"),
        "description should mention superposition"
    );
    // The proof term should be an application (absurd applied to args)
    assert!(
        matches!(proof_term.kind(), clean_kernel::ExprKind::App(_, _)),
        "proof should be an application"
    );
}

/// Test that missing input hypothesis produces errors.
#[test]
fn test_missing_input_hypothesis() {
    let map = SymbolMap::new();

    let input_clause = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    let trace = ProofTrace {
        empty_clause: input_clause.clone(),
        clauses: vec![input_clause],
    };

    let reconstructor = SuperpositionReconstructor::new(&trace, &map);
    let err = reconstructor
        .reconstruct_input(0)
        .expect_err("missing input hypothesis should produce error");
    assert!(
        matches!(err, ReconstructionError::MissingInputHypothesis(0)),
        "expected MissingInputHypothesis(0), got {err:?}"
    );
}

/// Test that superposition reconstruction produces correct 6-arg Eq.subst.
#[test]
fn test_reconstruct_superposition_six_args() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let f_type = Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty.clone());

    map.add_symbol(
        0,
        Expr::const_(Name::from_string("a"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(
        1,
        Expr::const_(Name::from_string("b"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(2, Expr::const_(Name::from_string("c"), vec![]), nat_ty);
    map.add_symbol(3, Expr::const_(Name::from_string("f"), vec![]), f_type);

    map.add_input_clause(
        0,
        FVarId::new(1),
        Expr::const_(Name::from_string("h_eq"), vec![]),
    );
    map.add_input_clause(
        1,
        FVarId::new(2),
        Expr::const_(Name::from_string("h_fa"), vec![]),
    );

    let c1 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c2 = mk_input_eq(1, Term::App(3, vec![Term::Const(0)]), Term::Const(2));
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::App(3, vec![Term::Const(1)]),
            rhs: Term::Const(2),
            positive: true,
        }],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
    };

    let trace = ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c1, c2, c3],
    };
    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let proof = reconstructor
        .reconstruct_clause(2)
        .expect("superposition should succeed");
    assert_eq_subst_structure(&proof);
}

/// Test that demodulation reconstruction produces correct 6-arg Eq.subst.
#[test]
fn test_reconstruct_demodulation_six_args() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    map.add_symbol(
        0,
        Expr::const_(Name::from_string("a"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(1, Expr::const_(Name::from_string("b"), vec![]), nat_ty);

    map.add_input_clause(
        0,
        FVarId::new(1),
        Expr::const_(Name::from_string("h_eq"), vec![]),
    );
    map.add_input_clause(
        1,
        FVarId::new(2),
        Expr::const_(Name::from_string("h_orig"), vec![]),
    );

    let unit_clause = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let orig_clause = mk_input_eq(1, Term::Const(0), Term::Const(0));
    let demod_clause = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(0),
            positive: true,
        }],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Demodulation(1, 0),
    };

    let trace = ProofTrace {
        empty_clause: demod_clause.clone(),
        clauses: vec![unit_clause, orig_clause, demod_clause],
    };
    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let proof = reconstructor
        .reconstruct_clause(2)
        .expect("demodulation should succeed");
    assert_eq_subst_structure(&proof);
}

/// Test that the motive in Eq.subst is a lambda abstraction.
#[test]
fn test_superposition_motive_is_lambda() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    map.add_symbol(
        0,
        Expr::const_(Name::from_string("a"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(1, Expr::const_(Name::from_string("b"), vec![]), nat_ty);

    map.add_input_clause(
        0,
        FVarId::new(1),
        Expr::const_(Name::from_string("h_eq"), vec![]),
    );
    map.add_input_clause(
        1,
        FVarId::new(2),
        Expr::const_(Name::from_string("h2"), vec![]),
    );

    let c1 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c2 = mk_input_eq(1, Term::Const(0), Term::Const(0));
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(0),
            positive: true,
        }],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
    };

    let trace = ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c1, c2, c3],
    };
    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let proof = reconstructor
        .reconstruct_clause(2)
        .expect("invariant: reconstruct_clause succeeded");

    // Extract args: App(App(App(App(App(App(Eq.subst, a), motive), a), b), h), m)
    let mut current = &proof;
    let mut args = vec![];
    while let ExprKind::App(f, a) = current.kind() {
        args.push(a.clone());
        current = f;
    }
    args.reverse(); // [a, motive, a, b, h, m]
    assert_eq!(args.len(), 6, "should have 6 args");

    let motive = &args[1];
    assert!(
        matches!(motive.kind(), ExprKind::Lam(_, _, _)),
        "motive should be a lambda abstraction, got {:?}",
        motive.kind()
    );
}

/// Test that equality factoring builds Or.rec proof with Classical.em.
///
/// Parent: s=t1 | s=t2 -> Result: (s=t1) | (t1!=t2)
/// Proof uses Or.rec to case-split on the parent disjunction.
#[test]
fn test_reconstruct_equality_factoring_or_rec() {
    let (trace, map) = mk_equality_factoring_trace();
    let env = mk_test_env();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    let proof = reconstructor
        .reconstruct_clause(1)
        .expect("factoring should succeed");

    // Top-level should be Or.rec (case analysis on parent)
    let (head, args) = decompose_app_spine(&proof);
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or.rec")),
        "factoring proof head should be Or.rec, got {:?}",
        head.kind()
    );
    assert_eq!(
        args.len(),
        6,
        "Or.rec should have 6 args (a, b, motive, f_inl, f_inr, h)"
    );

    // args[3] = f_inl (case s=t1 branch) -- should be a lambda
    assert!(
        matches!(args[3].kind(), ExprKind::Lam(..)),
        "f_inl should be a lambda, got {:?}",
        args[3].kind()
    );

    // args[4] = f_inr (case s=t2 branch) -- should be a lambda containing
    // an inner Or.rec for Classical.em case split
    assert!(
        matches!(args[4].kind(), ExprKind::Lam(..)),
        "f_inr should be a lambda, got {:?}",
        args[4].kind()
    );
}
