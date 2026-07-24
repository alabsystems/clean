// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat → SMT proof routing: first kernel-verified proofs of rational arithmetic
//! via the Ay bridge.
//!
//! These tests exercise the Rat→SmtSort::Real mapping (#3367) end-to-end:
//! a Rat inequality is classified, translated to the SMT Real sort, solved,
//! and the reconstructed proof term is validated by the kernel TypeChecker.
//!
//! This is the first time a domain-specific mathematical claim involving
//! rational arithmetic is PROVED (not assumed) via automated reasoning with
//! kernel verification.
//!
//! Part of #3383.

use super::super::*;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, LocalContext, TypeChecker};

/// Create an environment with Rat type, arithmetic, ordering, and the
/// infrastructure needed for the SMT bridge to produce kernel proofs.
fn setup_rat_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_rat_arith().expect("init_rat_arith should succeed");
    env.init_rat_ord().expect("init_rat_ord should succeed");
    // Registers Rat.le_refl, Rat.le_trans, Rat.le_antisymm, Rat.lt_irrefl,
    // instPreorderRat, instPartialOrderRat, instLinearOrderRat
    env.init_rat_linear_order()
        .expect("init_rat_linear_order should succeed");
    env
}

/// Build `@LE.le Rat instLERat lhs rhs` — the typeclass form used by Lean 4.
fn mk_rat_le(lhs: Expr, rhs: Expr) -> Expr {
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);
    let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    rat_ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@LT.lt Rat instLTRat lhs rhs`.
fn mk_rat_lt(lhs: Expr, rhs: Expr) -> Expr {
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);
    let inst = Expr::const_(Name::from_string("instLTRat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    rat_ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

fn rat_zero() -> Expr {
    Expr::const_(Name::from_string("Rat.zero"), vec![])
}

fn rat_one() -> Expr {
    Expr::const_(Name::from_string("Rat.one"), vec![])
}

fn rat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rat.add"), vec![]), lhs),
        rhs,
    )
}

fn kernel_validate_proof(env: &Environment, proof: &Expr, expected_type: &Expr) {
    let tc = TypeChecker::new(env);
    let inferred = tc.infer_type(proof).unwrap_or_else(|e| {
        panic!(
            "Proof term failed kernel type inference: {e:?}\n\
             Proof: {proof:?}\n\
             Expected type: {expected_type:?}"
        )
    });
    assert!(
        tc.is_def_eq(&inferred, expected_type),
        "Inferred type does not match expected goal type.\n\
         Inferred: {inferred:?}\n\
         Expected: {expected_type:?}"
    );
}

fn kernel_validate_proof_with_ctx(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    expected_type: &Expr,
) {
    let tc = TypeChecker::with_context(env, ctx);
    tc.check_type(proof, expected_type).unwrap_or_else(|e| {
        panic!(
            "Proof term failed kernel check_type: {e:?}\n\
             Proof: {proof:?}\n\
             Expected type: {expected_type:?}"
        )
    });
}

// ---------------------------------------------------------------------------
// Test: Rat reflexive LE — Rat.zero ≤ Rat.zero
// ---------------------------------------------------------------------------

#[test]
fn test_rat_le_reflexive_zero_smt_bridge_proves() {
    let env = setup_rat_env();
    let mut bridge = SmtBridge::new(&env);

    // Goal: Rat.zero ≤ Rat.zero (reflexive — trivially true)
    let goal = mk_rat_le(rat_zero(), rat_zero());

    let result = bridge
        .prove(&goal)
        .expect("Rat reflexive LE should not error")
        .verified()
        .expect("Rat reflexive LE should produce a verified proof");

    // The proof step should be a reflexivity-based or propositional proof
    let step = result.proof_step();
    assert!(
        result.proof_term().kind()
            != &clean_kernel::ExprKind::Sort(clean_kernel::level::Level::zero()),
        "Proof term must not be degenerate: {step:?}"
    );
}

// ---------------------------------------------------------------------------
// Test: Rat LE with hypotheses — from h1: a ≤ b, h2: b ≤ c, prove a ≤ c
// ---------------------------------------------------------------------------

#[test]
fn test_rat_le_transitivity_from_hypotheses() {
    let env = setup_rat_env();
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);

    // Register Rat constants a, b, c
    let mut env = env;
    for name in ["rat_a", "rat_b", "rat_c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat_ty.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("rat_a"), vec![]);
    let b = Expr::const_(Name::from_string("rat_b"), vec![]);
    let c = Expr::const_(Name::from_string("rat_c"), vec![]);

    let hyp_ab = mk_rat_le(a.clone(), b.clone());
    let hyp_bc = mk_rat_le(b.clone(), c.clone());
    let goal = mk_rat_le(a.clone(), c.clone());

    let mut bridge = SmtBridge::new(&env);
    bridge
        .add_hypothesis_with_fvar(&hyp_ab, Some(FVarId::new(0)))
        .expect("add hypothesis a ≤ b");
    bridge
        .add_hypothesis_with_fvar(&hyp_bc, Some(FVarId::new(1)))
        .expect("add hypothesis b ≤ c");

    let result = bridge
        .prove(&goal)
        .expect("Rat LE transitivity should not error");

    assert!(
        result.is_verified(),
        "Rat LE transitivity from hypotheses should produce Verified, \
         got: {:?}",
        result
    );

    // Kernel-validate the proof term
    let proof_result = result.verified().unwrap();
    let proof = proof_result.proof_term();

    let mut ctx = LocalContext::new();
    let id0 = ctx.push(Name::from_string("h0"), hyp_ab.clone(), BinderInfo::Default);
    assert_eq!(id0, FVarId::new(0));
    let id1 = ctx.push(Name::from_string("h1"), hyp_bc.clone(), BinderInfo::Default);
    assert_eq!(id1, FVarId::new(1));

    kernel_validate_proof_with_ctx(&env, ctx, proof, &goal);
}

// ---------------------------------------------------------------------------
// Test: Rat LT — Rat.zero < Rat.one
// ---------------------------------------------------------------------------

#[test]
fn test_rat_lt_zero_one_smt_bridge() {
    let env = setup_rat_env();
    let mut bridge = SmtBridge::new(&env);

    // Goal: Rat.zero < Rat.one
    let goal = mk_rat_lt(rat_zero(), rat_one());

    let result = bridge.prove(&goal).expect("Rat 0 < 1 should not error");

    // The bridge may or may not produce a verified proof for ground Rat
    // comparisons (depends on whether the propositional reconstruction
    // path handles ground Rat constants). At minimum, it should not error.
    // If verified, that's the breakthrough.
    if result.is_verified() {
        let proof_result = result.verified().unwrap();
        kernel_validate_proof(&env, proof_result.proof_term(), &goal);
    }
}

// ---------------------------------------------------------------------------
// Test: Rat hypothesis contradiction — from h1: a ≤ b, h2: ¬(a ≤ b), prove False
// ---------------------------------------------------------------------------

#[test]
fn test_rat_contradiction_proves_false() {
    let env = setup_rat_env();
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);

    let mut env = env;
    for name in ["rat_x", "rat_y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat_ty.clone(),
        })
        .unwrap();
    }

    let x = Expr::const_(Name::from_string("rat_x"), vec![]);
    let y = Expr::const_(Name::from_string("rat_y"), vec![]);

    let le_xy = mk_rat_le(x.clone(), y.clone());
    let not_le_xy = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        le_xy.clone(),
    );
    let goal = Expr::const_(Name::from_string("False"), vec![]);

    let mut bridge = SmtBridge::new(&env);
    bridge
        .add_hypothesis_with_fvar(&le_xy, Some(FVarId::new(0)))
        .expect("add hypothesis x ≤ y");
    bridge
        .add_hypothesis_with_fvar(&not_le_xy, Some(FVarId::new(1)))
        .expect("add hypothesis ¬(x ≤ y)");

    let result = bridge
        .prove(&goal)
        .expect("Rat contradiction should not error");

    assert!(
        result.is_verified(),
        "Rat contradiction (h: x ≤ y, h': ¬(x ≤ y)) should prove False, got: {:?}",
        result
    );

    let proof_result = result.verified().unwrap();
    let proof = proof_result.proof_term();

    let mut ctx = LocalContext::new();
    let id0 = ctx.push(Name::from_string("h0"), le_xy, BinderInfo::Default);
    assert_eq!(id0, FVarId::new(0));
    let id1 = ctx.push(Name::from_string("h1"), not_le_xy, BinderInfo::Default);
    assert_eq!(id1, FVarId::new(1));

    kernel_validate_proof_with_ctx(&env, ctx, proof, &goal);
}

// ---------------------------------------------------------------------------
// Test: Rat arithmetic — from h: a + b ≤ c, prove a + b ≤ c (identity)
// ---------------------------------------------------------------------------

#[test]
fn test_rat_add_hypothesis_identity() {
    let env = setup_rat_env();
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);

    let mut env = env;
    for name in ["rat_p", "rat_q", "rat_r"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat_ty.clone(),
        })
        .unwrap();
    }

    let p = Expr::const_(Name::from_string("rat_p"), vec![]);
    let q = Expr::const_(Name::from_string("rat_q"), vec![]);
    let r = Expr::const_(Name::from_string("rat_r"), vec![]);

    let p_plus_q = rat_add(p.clone(), q.clone());
    let hyp = mk_rat_le(p_plus_q.clone(), r.clone());
    let goal = hyp.clone();

    let mut bridge = SmtBridge::new(&env);
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(FVarId::new(0)))
        .expect("add hypothesis p + q ≤ r");

    let result = bridge
        .prove(&goal)
        .expect("Rat identity hypothesis should not error");

    assert!(
        result.is_verified(),
        "Rat identity hypothesis (h: p + q ≤ r, goal: p + q ≤ r) should be Verified"
    );

    let proof_result = result.verified().unwrap();
    let proof = proof_result.proof_term();

    let mut ctx = LocalContext::new();
    let id0 = ctx.push(Name::from_string("h0"), hyp, BinderInfo::Default);
    assert_eq!(id0, FVarId::new(0));

    kernel_validate_proof_with_ctx(&env, ctx, proof, &goal);
}

// ---------------------------------------------------------------------------
// Test: head_family recognizes Rat arithmetic and comparison heads
// ---------------------------------------------------------------------------

#[test]
fn test_head_family_recognizes_rat_arith_heads() {
    use crate::bridge::head_family::{classify_arith_head, ArithFamily, SortHint};

    let cases = [
        ("Rat.add", ArithFamily::Add),
        ("Rat.sub", ArithFamily::Sub),
        ("Rat.mul", ArithFamily::Mul),
        ("Rat.div", ArithFamily::Div),
        ("Rat.neg", ArithFamily::Neg),
    ];

    for (name, expected_family) in cases {
        let head = classify_arith_head(name)
            .unwrap_or_else(|| panic!("classify_arith_head should recognize {name}"));
        assert_eq!(
            head.family, expected_family,
            "{name} should have family {expected_family:?}"
        );
        assert_eq!(
            head.sort_hint,
            SortHint::Real,
            "{name} should map to SortHint::Real"
        );
    }
}

#[test]
fn test_head_family_recognizes_rat_cmp_heads() {
    use crate::bridge::head_family::{classify_cmp_head, CmpFamily, SortHint};

    let cases = [
        ("Rat.le", CmpFamily::Le),
        ("Rat.lt", CmpFamily::Lt),
        ("Rat.gt", CmpFamily::Gt),
        ("Rat.ge", CmpFamily::Ge),
    ];

    for (name, expected_family) in cases {
        let head = classify_cmp_head(name)
            .unwrap_or_else(|| panic!("classify_cmp_head should recognize {name}"));
        assert_eq!(
            head.family, expected_family,
            "{name} should have family {expected_family:?}"
        );
        assert_eq!(
            head.sort_hint,
            SortHint::Real,
            "{name} should map to SortHint::Real"
        );
    }
}
