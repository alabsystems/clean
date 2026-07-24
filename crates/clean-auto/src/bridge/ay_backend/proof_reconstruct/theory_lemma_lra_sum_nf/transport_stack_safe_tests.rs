// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, ExprKind, LocalContext, TypeChecker};

use super::super::tests_e2e_lra::mk_env_for_lra;
use super::super::theory_lemma_lra_additive::mk_int_add;
use super::*;

/// Assert that a proof term type-checks to False using definitional equality.
///
/// Unlike `assert_proof_type_checks_to_false` (which checks for syntactic `False`),
/// this uses `is_def_eq` to handle cases where the inferred type requires WHNF
/// reduction (e.g. `Int.NonNeg.casesOn` on a concrete negative discriminant).
fn assert_proof_def_eq_false(env: &Environment, ctx: LocalContext, proof: &Expr, msg: &str) {
    let tc = TypeChecker::with_context(env, ctx);
    let ty = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("{msg}: type-check failed: {e:?}"));
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    assert!(
        tc.is_def_eq(&ty, &false_expr),
        "{msg}: expected type definitionally equal to False, got {:?}",
        ty.kind(),
    );
}

fn mk_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_left_assoc_int_add_chain(terms: &[Expr]) -> Expr {
    let mut iter = terms.iter();
    let mut chain = iter
        .next()
        .expect("left-associative Int.add fixture requires at least one term")
        .clone();
    for term in iter {
        chain = mk_int_add(&chain, term);
    }
    chain
}

fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => expr_contains_const(f, target) || expr_contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, target)
                || expr_contains_const(val, target)
                || expr_contains_const(body, target)
        }
        _ => false,
    }
}

#[test]
fn test_try_close_int_additive_nf_handles_deep_transport_recursion() {
    // Keep the fixture deep enough to exercise the recursive transport helpers
    // while avoiding quadratic proof-construction blowups in unit-test runtime.
    let depth = 32;
    let mut lhs_terms = vec![mk_int_literal(1)];
    let mut rhs_terms = vec![mk_int_literal(0)];

    for idx in 0..depth {
        let shared = mk_var(&format!("shared_{idx}"));
        lhs_terms.push(shared.clone());
        rhs_terms.push(shared);
    }

    let lhs = mk_left_assoc_int_add_chain(&lhs_terms);
    let rhs = mk_left_assoc_int_add_chain(&rhs_terms);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("deep additive transport should stay stack-safe");

    assert!(
        expr_contains_const(&false_proof, "Int.le_of_add_le_add_right"),
        "deep shared suffix should still cancel after transport normalization"
    );
    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "deep transport path should still finish with the concrete contradiction builder"
    );

    // Kernel type-check: verify the proof term actually proves False, not just
    // that it contains the right constant names.
    let mut env = mk_env_for_lra();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for idx in 0..depth {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("shared_{idx}")),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("add shared var axiom");
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: mk_cmp_prop(CmpOp::Le, &lhs, &rhs),
    })
    .expect("add hypothesis axiom");
    let ctx = LocalContext::new();
    assert_proof_def_eq_false(
        &env,
        ctx,
        &false_proof,
        "deep transport proof should type-check to False",
    );
}

#[test]
fn test_try_close_int_additive_nf_reorders_interleaved_constants_before_grouping_suffix() {
    let a = mk_var("a");
    let b = mk_var("b");
    let c = mk_var("c");
    let lhs_terms = vec![
        a.clone(),
        mk_int_literal(2),
        b.clone(),
        mk_int_literal(1),
        c.clone(),
    ];
    let rhs_terms = vec![
        a.clone(),
        mk_int_literal(0),
        b.clone(),
        mk_int_literal(0),
        c.clone(),
    ];
    let lhs = mk_left_assoc_int_add_chain(&lhs_terms);
    let rhs = mk_left_assoc_int_add_chain(&rhs_terms);
    let proof = mk_var("h");

    let false_proof = try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof)
        .expect("interleaved constants should reorder and regroup before closeout");

    assert!(
        expr_contains_const(&false_proof, "Int.add_comm"),
        "transport should use adjacent swaps when constants are interleaved with shared atoms"
    );
    assert!(
        expr_contains_const(&false_proof, "Int.le_of_add_le_add_right"),
        "shared suffix should still cancel after regrouping"
    );
    assert!(
        expr_contains_const(&false_proof, "Int.NonNeg.casesOn"),
        "reordered closeout should still finish with the concrete contradiction builder"
    );

    // Kernel type-check: verify the proof term is sound, not just structurally plausible.
    let mut env = mk_env_for_lra();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("add symbolic var axiom");
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: mk_cmp_prop(CmpOp::Le, &lhs, &rhs),
    })
    .expect("add hypothesis axiom");
    let ctx = LocalContext::new();
    assert_proof_def_eq_false(
        &env,
        ctx,
        &false_proof,
        "interleaved constant reordering proof should type-check to False",
    );
}
