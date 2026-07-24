// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for superposition reconstruction tests.

use super::super::*;
use crate::superposition::{Clause, Inference, Literal, ProofTrace, Term};
use clean_kernel::{Environment, ExprKind, FVarId};

/// Create a minimal environment with Nat so sort inference works in unit tests.
pub(super) fn mk_test_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env
}

/// Verify a proof term is an Eq.subst with exactly 6 args and 1 universe level.
///
/// Clean kernel `Eq.subst` has 1 universe param (motive fixed to Prop).
pub(super) fn assert_eq_subst_structure(proof: &Expr) {
    let mut current = proof;
    let mut arg_count = 0;
    while let ExprKind::App(f, _) = current.kind() {
        arg_count += 1;
        current = f;
    }
    assert_eq!(
        arg_count, 6,
        "Eq.subst should have exactly 6 arguments (α, motive, a, b, h, m)"
    );
    match current.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Eq.subst"));
            assert_eq!(
                levels.len(),
                1,
                "Eq.subst should have 1 universe level (clean motive fixed to Prop)"
            );
        }
        other => panic!("expected Const for Eq.subst, got {other:?}"),
    }
}

/// Build a unit equation input clause: `lhs = rhs`.
pub(super) fn mk_input_eq(id: u64, lhs: Term, rhs: Term) -> Clause {
    Clause {
        literals: vec![Literal {
            lhs,
            rhs,
            positive: true,
        }],
        id,
        parents: vec![],
        inference: Inference::Input,
    }
}

/// Count App-spine args and return (head, args) for structural inspection.
pub(super) fn decompose_app_spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut current = expr;
    let mut args = vec![];
    while let ExprKind::App(f, a) = current.kind() {
        args.push(a.as_ref());
        current = f;
    }
    args.reverse();
    (current, args)
}

/// Build a 3-symbol Nat SymbolMap with an input clause and equality factoring trace.
///
/// Returns (trace, map) for s=t1 | s=t2 -> factored clause [s=t1, t1!=t2].
/// Matches the real `equality_factoring` output: kept equation + new disequation.
pub(super) fn mk_equality_factoring_trace() -> (ProofTrace, SymbolMap) {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(
        0,
        Expr::const_(Name::from_string("s"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(
        1,
        Expr::const_(Name::from_string("t1"), vec![]),
        nat_ty.clone(),
    );
    map.add_symbol(2, Expr::const_(Name::from_string("t2"), vec![]), nat_ty);
    map.add_input_clause(
        0,
        FVarId::new(1),
        Expr::const_(Name::from_string("h_parent"), vec![]),
    );

    let parent = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(2),
                positive: true,
            },
        ],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    // Correct factoring output: [s=t1 (kept), t1!=t2 (new disequation)]
    let factored = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
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

pub(super) fn mk_nat_eq_refl(nat_ty: &Expr, val: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            nat_ty.clone(),
        ),
        val.clone(),
    )
}

pub(super) fn mk_eq_subst_term(motive: &Expr, a: &Expr, b: &Expr, h: &Expr, m: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq.subst"),
                                vec![Level::succ(Level::zero())],
                            ),
                            Expr::const_(Name::from_string("Nat"), vec![]),
                        ),
                        motive.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            ),
            h.clone(),
        ),
        m.clone(),
    )
}
