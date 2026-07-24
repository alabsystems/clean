// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Depth-stress tests for stack-safety guards on recursive bridge functions.
//!
//! Each test runs on a constrained-stack thread (1 MiB) to make regressions
//! of `stacker::maybe_grow` guards detectable — the default test thread stack
//! (8 MiB on most platforms) would mask missing guards up to moderate depths.
//!
//! Acceptance criteria: #2722, Phase 1 — "at least 2 new depth-stress tests
//! (for ExprKey::from_expr and one ay_backend function)". This module covers
//! ExprKey::from_expr and prop_to_literal (bridge-level). The ay_backend
//! stack-safety tests are in ay_backend/proof_reconstruct/tests/stack_safe.rs.

use super::superposition_clausify::GoalClausifier;
use super::*;
use crate::bridge::translate::ExprKey;
use crate::superposition::Term;
use clean_kernel::name::Name;
use clean_kernel::Expr;

/// Thread stack size for constrained-stack tests: 1 MiB.
///
/// Below the standard 2 MiB minimum on Unix/libtest. This ensures that
/// missing `stacker::maybe_grow` guards cause a stack overflow instead of
/// silently passing on the generous default test stack.
const CONSTRAINED_STACK: usize = 1024 * 1024;
const CLAUSIFIER_CONSTRAINED_STACK: usize = 2 * CONSTRAINED_STACK;

/// Recursion stress depth. 10,000 layers of nesting exercises the
/// `stacker::maybe_grow` guard meaningfully — each frame consumes stack
/// for the match, Box allocation, and return, so 10k deep on a 1 MiB
/// stack would overflow without the guard.
const STRESS_DEPTH: usize = 10_000;

/// Build a deeply nested `App` chain: `f(f(f(...f(leaf)...)))`.
fn build_deep_app_chain(func: &Expr, leaf: &Expr, depth: usize) -> Expr {
    let mut expr = leaf.clone();
    for _ in 0..depth {
        expr = Expr::app(func.clone(), expr);
    }
    expr
}

/// Build a deeply nested right-associative `And` chain:
/// `And(atom, And(atom, And(atom, ...And(atom, atom)...)))`.
///
/// Each `And(a, b)` is `@And a b` = `App(App(Const("And"), a), b)`.
/// The rightmost leaf is an atomic proposition so `classify_prop` sees
/// `And(atom, <deeper And>)` at every level, forcing `prop_to_literal`
/// to recurse to the full depth.
fn build_deep_and_chain(atom: &Expr, depth: usize) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let mut expr = atom.clone();
    for _ in 0..depth {
        // And(atom, expr) = App(App(Const("And"), atom), expr)
        expr = Expr::app(Expr::app(and_const.clone(), atom.clone()), expr);
    }
    expr
}

// ---------------------------------------------------------------------------
// Test 1: ExprKey::from_expr on a deeply nested App chain
// ---------------------------------------------------------------------------

/// Verify that `ExprKey::from_expr` handles 10,000-deep `App` nesting without
/// stack overflow on a constrained 1 MiB thread stack.
///
/// Regression anchor for the `stack_safe` guard added in #2722 Phase 1.
#[test]
fn test_expr_key_from_expr_deep_app_chain() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let f = Expr::const_(Name::from_string("f"), vec![]);
            let x = Expr::const_(Name::from_string("x"), vec![]);
            let deep = build_deep_app_chain(&f, &x, STRESS_DEPTH);

            let key = ExprKey::from_expr(&deep)
                .expect("ExprKey::from_expr should succeed on deep App chain");

            // Walk the key structure to verify correctness:
            // outermost is App(Const("f"), App(Const("f"), ...))
            let mut current = &key;
            for i in 0..STRESS_DEPTH {
                match current {
                    ExprKey::App(func_key, arg_key) => {
                        match func_key.as_ref() {
                            ExprKey::Const(name, levels) => {
                                assert_eq!(
                                    name.to_string(),
                                    "f",
                                    "function key should be Const(\"f\") at depth {i}"
                                );
                                assert!(
                                    levels.is_empty(),
                                    "function key should have no universe levels at depth {i}"
                                );
                            }
                            other => panic!(
                                "expected Const(\"f\") as function key at depth {i}, got {other:?}"
                            ),
                        }
                        current = arg_key.as_ref();
                    }
                    other => panic!("expected App at depth {i}, got {other:?}"),
                }
            }
            // Innermost: Const("x")
            match current {
                ExprKey::Const(name, levels) => {
                    assert_eq!(name.to_string(), "x", "leaf should be Const(\"x\")");
                    assert!(levels.is_empty(), "leaf should have no universe levels");
                }
                other => panic!("expected Const(\"x\") at leaf, got {other:?}"),
            }

            eprintln!(
                "ExprKey::from_expr depth-stress: depth={STRESS_DEPTH} completed \
                 on a {CONSTRAINED_STACK}-byte stack with stacker::maybe_grow guard."
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

// ---------------------------------------------------------------------------
// Test 2: prop_to_literal on a deeply nested And chain
// ---------------------------------------------------------------------------

/// Verify that `prop_to_literal` handles 10,000-deep `And(...)` nesting without
/// stack overflow on a constrained 1 MiB thread stack.
///
/// The `And` chain forces `prop_to_literal` to recurse once per level via
/// `classify_prop → LogicalForm::And(a, b) → prop_to_literal(b, ...)`.
///
/// Regression anchor for the `stack_safe` guard added in #2722 Phase 1.
#[test]
fn test_prop_to_literal_deep_and_chain() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let env = Environment::new();
            let mut bridge = SmtBridge::new(&env);

            // Atomic proposition: a simple constant that classify_prop treats as Atom
            let atom = Expr::fvar(FVarId::new(42));
            let deep_and = build_deep_and_chain(&atom, STRESS_DEPTH);

            let result = bridge.prop_to_literal(&deep_and, true);
            assert!(
                result.is_ok(),
                "prop_to_literal should succeed on deep And chain, got: {:?}",
                result.err()
            );

            // The Tseitin encoding introduces one fresh variable per And node,
            // so fresh_counter should have advanced by at least STRESS_DEPTH
            // (one for each And level, plus the leaf atoms).
            assert!(
                bridge.fresh_counter >= STRESS_DEPTH as u32,
                "Tseitin encoding should have allocated at least {STRESS_DEPTH} fresh variables, \
                 got {}",
                bridge.fresh_counter
            );

            eprintln!(
                "prop_to_literal depth-stress: depth={STRESS_DEPTH} completed \
                 on a {CONSTRAINED_STACK}-byte stack with stacker::maybe_grow guard. \
                 Tseitin vars allocated: {}",
                bridge.fresh_counter
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

// ---------------------------------------------------------------------------
// Test 3: GoalClausifier on a deeply nested conjunction goal
// ---------------------------------------------------------------------------

/// Verify that `GoalClausifier::clausify_goal` handles 10,000-deep conjunction
/// nesting without stack overflow on a constrained 2 MiB thread stack.
///
/// This exercises both recursive clausifier paths:
/// `expr_to_nnf` over the input `Expr`, then `nnf_to_cnf` over the generated
/// NNF tree. Without the `stack_safe` guards in `superposition_clausify.rs`,
/// this depth overflows the constrained test stack.
#[test]
fn test_goal_clausifier_deep_and_goal() {
    // GoalClausifier allocates HashMap entries + SymbolMap metadata per recursion
    // level, so each frame is heavier than the simpler ExprKey/prop_to_literal
    // tests. Use 2 MiB to remain constrained while accommodating this overhead.
    let handle = std::thread::Builder::new()
        .stack_size(CLAUSIFIER_CONSTRAINED_STACK)
        .spawn(|| {
            let atom = Expr::fvar(FVarId::new(7));
            let deep_and = build_deep_and_chain(&atom, STRESS_DEPTH);
            let mut clausifier = GoalClausifier::new();

            let (clauses, _symbol_map) = clausifier.clausify_goal(&deep_and);
            assert_eq!(
                clauses.len(),
                1,
                "negating a deep conjunction goal should yield one disjunctive clause"
            );
            assert_eq!(
                clauses[0].len(),
                STRESS_DEPTH + 1,
                "the single clause should contain one literal per conjunction layer"
            );
            assert!(
                clauses[0].iter().all(|literal| !literal.positive),
                "negated atomic goal literals should all be negative"
            );

            eprintln!(
                "GoalClausifier depth-stress: depth={STRESS_DEPTH} completed \
                 on a {CLAUSIFIER_CONSTRAINED_STACK}-byte stack with stacker::maybe_grow guard. \
                 Clause count: {}, literals in clause 0: {}",
                clauses.len(),
                clauses[0].len()
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

// ---------------------------------------------------------------------------
// Test 4: GoalClausifier::expr_to_term on a deeply nested App chain
// ---------------------------------------------------------------------------

/// Verify that `GoalClausifier::expr_to_term` handles 10,000-deep `Expr::App`
/// nesting without stack overflow on a constrained 2 MiB thread stack.
///
/// The prover self-audit for #2979 found this additional recursion path after
/// the initial NNF/CNF scan. Deep application terms appear in Mathlib goals,
/// so the term-lowering path needs the same stack-growth guard as the boolean
/// clausifier passes.
#[test]
fn test_goal_clausifier_expr_to_term_deep_app_chain() {
    // Same overhead rationale as test_goal_clausifier_deep_and_goal above.
    let handle = std::thread::Builder::new()
        .stack_size(CLAUSIFIER_CONSTRAINED_STACK)
        .spawn(|| {
            let f = Expr::const_(Name::from_string("f"), vec![]);
            let x = Expr::const_(Name::from_string("x"), vec![]);
            let deep = build_deep_app_chain(&f, &x, STRESS_DEPTH);
            let mut clausifier = GoalClausifier::new();

            let term = clausifier.expr_to_term(&deep);
            let mut current = &term;
            let mut func_symbol = None;
            for i in 0..STRESS_DEPTH {
                match current {
                    Term::App(func, args) => {
                        let expected_func = func_symbol.get_or_insert(*func);
                        assert_eq!(
                            *func, *expected_func,
                            "deep app chain should reuse the same function symbol at depth {i}"
                        );
                        assert_eq!(args.len(), 1, "deep app node should have one argument");
                        current = &args[0];
                    }
                    other => panic!("expected Term::App at depth {i}, got {other:?}"),
                }
            }

            let func_symbol =
                func_symbol.expect("deep app chain should visit at least one function symbol");
            match current {
                Term::Const(sym) => assert_ne!(
                    *sym, func_symbol,
                    "leaf constant should lower to a distinct symbol from the function head"
                ),
                other => panic!("expected Term::Const at leaf, got {other:?}"),
            }

            eprintln!(
                "GoalClausifier expr_to_term depth-stress: depth={STRESS_DEPTH} completed \
                 on a {CLAUSIFIER_CONSTRAINED_STACK}-byte stack with stacker::maybe_grow guard."
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}
