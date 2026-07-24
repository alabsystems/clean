// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constrained-stack regression tests for deep hypothesis recursion paths.

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;

// Must survive initial SmtBridge::new + add_hypothesis frame setup before
// stacker::maybe_grow kicks in. The workspace-compiled binary has larger
// frames than the standalone binary due to different inlining/
// monomorphization from unified feature flags and ay generics.
const CONSTRAINED_STACK: usize = 8 * 1024 * 1024;
// add_hypothesis allocates solver clauses and Tseitin state per level, so keep
// this regression modest enough to finish in the shared tree while still
// recursing deeply on a constrained thread.
const ASSERT_STRESS_DEPTH: usize = 256;
const QUANTIFIER_STRESS_DEPTH: usize = 224;
// Guided equality/arithmetic traversals are lighter because they only walk the
// stored hypothesis tree, so they can stay substantially deeper.
const GUIDED_STRESS_DEPTH: usize = 2_000;

fn mk_and(left: &Expr, right: &Expr) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    Expr::app(Expr::app(and_const, left.clone()), right.clone())
}

fn build_deep_and_chain(leaf: &Expr, depth: usize) -> Expr {
    let mut expr = leaf.clone();
    for _ in 0..depth {
        expr = mk_and(leaf, &expr);
    }
    expr
}

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

fn make_forall(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}

fn make_exists(ty: Expr, body: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            ty.clone(),
        ),
        Expr::lam(BinderInfo::Default, ty, body),
    )
}

fn make_combine(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("combine"), vec![]), lhs),
        rhs,
    )
}

fn build_bound_term(depth: usize) -> Expr {
    let mut layer: Vec<Expr> = (0..depth).map(|idx| Expr::bvar(idx as u32)).collect();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut iter = layer.into_iter();
        while let Some(lhs) = iter.next() {
            if let Some(rhs) = iter.next() {
                next.push(make_combine(lhs, rhs));
            } else {
                next.push(lhs);
            }
        }
        layer = next;
    }
    layer
        .pop()
        .expect("alternating quantifier term should contain at least one binder")
}

fn build_alternating_quantifier_chain(depth: usize) -> Expr {
    assert!(depth > 0, "alternating quantifier chain must be non-empty");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let term = build_bound_term(depth);
    let mut expr = make_eq(a_ty.clone(), term.clone(), term);

    for binder_idx in (0..depth).rev() {
        expr = if binder_idx % 2 == 0 {
            make_forall(a_ty.clone(), expr)
        } else {
            make_exists(a_ty.clone(), expr)
        };
    }

    expr
}

pub(crate) fn run_test_add_hypothesis_deep_and_chain_stack_safe() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let mut env = setup_env();
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("p"),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("test proposition should register in the constrained-stack environment");
            let mut bridge = SmtBridge::new(&env);
            let atom = Expr::const_(Name::from_string("p"), vec![]);
            let deep_and = build_deep_and_chain(&atom, ASSERT_STRESS_DEPTH);

            bridge
                .add_hypothesis(&deep_and)
                .expect("add_hypothesis should succeed on a deep And chain");
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

#[test]
fn test_add_hypothesis_deep_and_chain_stack_safe() {
    run_test_add_hypothesis_deep_and_chain_stack_safe();
}

pub(crate) fn run_test_add_hypothesis_alternating_quantifiers_stack_safe() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let mut env = setup_env();
            let a_ty = Expr::const_(Name::from_string("A"), vec![]);
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("combine"),
                level_params: vec![],
                type_: Expr::arrow(a_ty.clone(), Expr::arrow(a_ty.clone(), a_ty)),
            })
            .expect("combine should register in the constrained-stack environment");

            let mut bridge = SmtBridge::new(&env);
            let alternating = build_alternating_quantifier_chain(QUANTIFIER_STRESS_DEPTH);

            bridge
                .add_hypothesis(&alternating)
                .expect("add_hypothesis should succeed on alternating quantified hypotheses");
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

#[test]
fn test_add_hypothesis_alternating_quantifiers_stack_safe() {
    run_test_add_hypothesis_alternating_quantifiers_stack_safe();
}

pub(crate) fn run_test_collect_equality_hypothesis_edges_deep_and_chain_stack_safe() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let env = setup_env();
            let mut bridge = SmtBridge::new(&env);
            let a_ty = Expr::const_(Name::from_string("A"), vec![]);
            let a = Expr::const_(Name::from_string("a"), vec![]);
            let b = Expr::const_(Name::from_string("b"), vec![]);
            let leaf = make_eq(a_ty.clone(), a.clone(), b.clone());
            let deep_and = build_deep_and_chain(&leaf, GUIDED_STRESS_DEPTH);
            let fvar = FVarId::new(43);
            bridge.prop_hypotheses.push((fvar, deep_and));

            let lhs_term = bridge
                .translate_term(&a)
                .expect("lhs term should register before guided equality proof search");
            let rhs_term = bridge
                .translate_term(&b)
                .expect("rhs term should register before guided equality proof search");

            let result = bridge
                .try_guided_hypothesis_equality_proof(lhs_term, rhs_term, &a, &b, &a_ty)
                .expect("guided equality proof search should succeed on a deep And chain");

            assert!(
                result.is_some(),
                "guided equality reconstruction should find a proof from a deep And chain"
            );
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

#[test]
fn test_collect_equality_hypothesis_edges_deep_and_chain_stack_safe() {
    run_test_collect_equality_hypothesis_edges_deep_and_chain_stack_safe();
}

pub(crate) fn run_test_collect_arithmetic_hypothesis_edges_deep_and_chain_stack_safe() {
    let handle = std::thread::Builder::new()
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let env = setup_env();
            let mut bridge = SmtBridge::new(&env);
            let a = Expr::const_(Name::from_string("a"), vec![]);
            let b = Expr::const_(Name::from_string("b"), vec![]);
            let leaf = make_nat_le(a.clone(), b.clone());
            let deep_and = build_deep_and_chain(&leaf, GUIDED_STRESS_DEPTH);
            let fvar = FVarId::new(44);
            bridge.prop_hypotheses.push((fvar, deep_and));
            bridge
                .translate_term(&a)
                .expect("lhs arithmetic term should register before guided reconstruction");
            bridge
                .translate_term(&b)
                .expect("rhs arithmetic term should register before guided reconstruction");

            let goal_class = bridge.classify_prop(&leaf);
            let (_proof_step, _proof_term) = bridge
                .build_arithmetic_goal_proof(&goal_class, &leaf)
                .expect("guided arithmetic reconstruction should succeed on a deep And chain");
        })
        .expect("constrained-stack thread spawn should succeed");

    handle
        .join()
        .expect("constrained-stack thread should not panic");
}

#[test]
fn test_collect_arithmetic_hypothesis_edges_deep_and_chain_stack_safe() {
    run_test_collect_arithmetic_hypothesis_edges_deep_and_chain_stack_safe();
}
