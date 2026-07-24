// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stack-safety regression tests for recursive clausifier entry points.

use super::super::*;
use crate::superposition::Term;
use clean_kernel::name::Name;
use clean_kernel::Expr;

const CONSTRAINED_STACK: usize = 1024 * 1024;
const CLAUSIFIER_STACK: usize = 2 * CONSTRAINED_STACK;
const STRESS_DEPTH: usize = 10_000;

fn build_deep_app_chain(func: &Expr, leaf: &Expr, depth: usize) -> Expr {
    let mut expr = leaf.clone();
    for _ in 0..depth {
        expr = Expr::app(func.clone(), expr);
    }
    expr
}

fn build_deep_and_chain(atom: &Expr, depth: usize) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let mut expr = atom.clone();
    for _ in 0..depth {
        expr = Expr::app(Expr::app(and_const.clone(), atom.clone()), expr);
    }
    expr
}

#[test]
fn test_clausify_goal_handles_deep_conjunction() {
    let handle = std::thread::Builder::new()
        .stack_size(CLAUSIFIER_STACK)
        .spawn(|| {
            let atom = Expr::fvar(FVarId::new(7));
            let deep_and = build_deep_and_chain(&atom, STRESS_DEPTH);
            let mut clausifier = GoalClausifier::new();

            let (clauses, _symbol_map) = clausifier.clausify_goal(&deep_and);
            assert_eq!(
                clauses.len(),
                1,
                "negating a deep conjunction goal should yield one clause"
            );
            assert_eq!(
                clauses[0].len(),
                STRESS_DEPTH + 1,
                "deep conjunction should contribute one literal per layer"
            );
            assert!(
                clauses[0].iter().all(|literal| !literal.positive),
                "negated atomic goal literals should stay negative"
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("deep conjunction clausification should not panic");
}

#[test]
fn test_expr_to_term_handles_deep_app_chain() {
    let handle = std::thread::Builder::new()
        .stack_size(CLAUSIFIER_STACK)
        .spawn(|| {
            let f = Expr::const_(Name::from_string("f"), vec![]);
            let x = Expr::const_(Name::from_string("x"), vec![]);
            let deep = build_deep_app_chain(&f, &x, STRESS_DEPTH);
            let mut clausifier = GoalClausifier::new();

            let term = clausifier.expr_to_term(&deep);
            let mut current = &term;
            for depth in 0..STRESS_DEPTH {
                match current {
                    Term::App(func, args) => {
                        assert_eq!(
                            *func, 100,
                            "deep app chain should reuse the same function symbol at depth {depth}"
                        );
                        assert_eq!(args.len(), 1, "deep app node should have one argument");
                        current = &args[0];
                    }
                    other => panic!("expected Term::App at depth {depth}, got {other:?}"),
                }
            }

            match current {
                Term::Const(sym) => {
                    assert_eq!(*sym, 101, "leaf constant should lower distinctly")
                }
                other => panic!("expected Term::Const at leaf, got {other:?}"),
            }
        })
        .expect("constrained-stack thread spawn should succeed");

    handle.join().expect("deep app lowering should not panic");
}
