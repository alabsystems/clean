// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discriminator tests for faithful-carrier declarations in
//! `nn_verify_blockwise_crown_ext_carriers.rs`.
//!
//! Each test enforces the Rule M1/M2/M3 acceptance criteria from
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` on a carrier
//! declaration that future demasquerade work will bind to. A carrier
//! that fails its discriminator cannot support a non-vacuous theorem.
//!
//! Split from `tests_nn_verify_blockwise_crown_ext.rs` to keep that
//! file under the 500-line ceiling.
//!
//! Part of #3492, #3495, #3500 Phase 1/2.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext");
    env
}

/// Returns true iff the expression (or any of its subexpressions)
/// references `target_const` as a `Const` head. Mirrors the helper in
/// `tests_nn_verify_blockwise_crown_ext.rs` so each test module is
/// self-contained.
fn expr_references_const(expr: &Expr, target_const: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target_const,
        ExprKind::App(f, a) => {
            expr_references_const(f, target_const) || expr_references_const(a, target_const)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_references_const(ty, target_const) || expr_references_const(body, target_const)
        }
        ExprKind::Let(_, ty, val, body, _nondep) => {
            expr_references_const(ty, target_const)
                || expr_references_const(val, target_const)
                || expr_references_const(body, target_const)
        }
        ExprKind::Proj(_, _, inner) => expr_references_const(inner, target_const),
        ExprKind::MData(_, inner) => expr_references_const(inner, target_const),
        _ => false,
    }
}

// =============================================================================
// NNVerify.Block.compose_count — faithful Block-count carrier
// Part of #3492 Phase-2 foundation.
// =============================================================================

#[test]
fn test_block_compose_count_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose_count"))
            .is_some(),
        "compose_count should be registered by init_nn_verify_blockwise_crown_ext",
    );
}

#[test]
fn test_block_compose_count_body_uses_nat_rec() {
    // Rule M2 discriminator: the body must structurally reference
    // `Nat.rec` so that evaluation threads through the inductive
    // argument. A body of the form `fun _ => const` would fail this
    // check and signal MASQUERADE.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.compose_count"))
        .expect("compose_count should exist");
    let value = ci
        .value
        .as_ref()
        .expect("compose_count must be a Definition with a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "compose_count body does not reference Nat.rec — carrier is not \
         faithfully inductive and would propagate MASQUERADE to any \
         theorem bound against it.",
    );
    // Sanity: the body also references Nat.succ (step branch output).
    // If Nat.succ were absent the step case would collapse to a
    // constant, defeating the faithful-carrier property.
    assert!(
        expr_references_const(value, "Nat.succ"),
        "compose_count body does not reference Nat.succ — step branch \
         must produce `Nat.succ ih` for the induction to vary with k.",
    );
}

#[test]
fn test_block_compose_count_type_is_nat_to_nat() {
    // The carrier must have signature `Nat -> Nat`. Verified via kernel
    // `infer_type`. Anything else would mean this is not the scaffold
    // the Phase-2 demasquerade plan binds to.
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.Block.compose_count"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("kernel must infer compose_count type");
    // Type should be `Nat -> Nat` (single Pi binder of type Nat,
    // codomain Nat).
    if let ExprKind::Pi(_, dom, codom) = ty.kind() {
        assert!(
            matches!(dom.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"),
            "compose_count domain should be Nat, got {:?}",
            dom.kind(),
        );
        assert!(
            matches!(codom.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"),
            "compose_count codomain should be Nat, got {:?}",
            codom.kind(),
        );
    } else {
        panic!(
            "compose_count should have type `Nat -> Nat` (single Pi), \
             got top-level shape {:?}",
            ty.kind(),
        );
    }
}

#[test]
fn test_block_compose_count_whnf_distinguishes_inputs() {
    // Rule M1 / Rule M2 discriminator: `compose_count 0` and
    // `compose_count 1` must reduce to syntactically distinct normal
    // forms (`Nat.zero` vs `Nat.succ Nat.zero`). If the kernel reduced
    // both to the same term, the carrier would be argument-discarding
    // and could not distinguish induction steps.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let compose_count = Expr::const_(Name::from_string("NNVerify.Block.compose_count"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());

    let at_zero = Expr::app(compose_count.clone(), nat_zero.clone());
    let at_one = Expr::app(compose_count, nat_one);

    let whnf_zero = tc.whnf(&at_zero);
    let whnf_one = tc.whnf(&at_one);

    // whnf_zero should reduce to something that normalises to Nat.zero;
    // whnf_one should reduce to Nat.succ _. The two must be distinct.
    assert!(
        !tc.is_def_eq(&whnf_zero, &whnf_one),
        "compose_count 0 and compose_count 1 reduce to def-equal terms — \
         carrier is argument-discarding (Rule M2 violation).",
    );

    // whnf_zero must be def-equal to Nat.zero; whnf_one must be
    // def-equal to `Nat.succ Nat.zero`. This confirms the Nat.rec
    // reduction actually fires and produces the expected counts.
    assert!(
        tc.is_def_eq(&whnf_zero, &nat_zero),
        "compose_count 0 should reduce to Nat.zero; reduction must \
         fire so downstream proofs can chain by `Eq.refl` at the base.",
    );
    let expected_one = Expr::app(nat_succ, nat_zero);
    assert!(
        tc.is_def_eq(&whnf_one, &expected_one),
        "compose_count 1 should reduce to Nat.succ Nat.zero; step-branch \
         must fire the IH reference (Rule M3 passes).",
    );
}

#[test]
fn test_block_compose_count_idempotent_init() {
    // Running init twice must not error or duplicate-register the
    // carrier. Mirrors the idempotence pattern for the other
    // nn_verify_blockwise_crown_ext declarations.
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("first init must succeed");
    env.init_nn_verify_blockwise_crown_ext()
        .expect("second init must be a no-op");
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose_count"))
            .is_some(),
        "compose_count must still be present after a second init call",
    );
}

// Note: tests for `NNVerify.LayerNorm.effective_generators` are deferred
// until `register_effective_generators` is wired into
// `init_nn_verify_blockwise_crown_ext`. That is a separate Phase-1
// follow-up not in scope for #3515.

// =============================================================================
// NNVerify.Block.compose_count_eq_self — genuine Nat.rec induction proof
// Part of #3375 — constructive helper lemma on the C006 carrier.
// =============================================================================

/// Registration guard: the theorem must land in the env when init runs.
#[test]
fn test_compose_count_eq_self_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose_count_eq_self"))
            .is_some(),
        "compose_count_eq_self should be registered by \
         init_nn_verify_blockwise_crown_ext",
    );
}

/// Declaration-shape guard: must be a `Declaration::Theorem` with a
/// concrete proof term — NOT a `Declaration::Axiom` restatement.
///
/// If this ever flips to `ConstantKind::Axiom`, the proof was silently
/// demoted and the helper no longer carries its proof.
#[test]
fn test_compose_count_eq_self_is_theorem_with_value() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.compose_count_eq_self"))
        .expect("compose_count_eq_self should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "compose_count_eq_self must be a Declaration::Theorem \
         (Axiom/Opaque/Definition would mean the proof was demoted)",
    );
    assert!(
        ci.value.is_some(),
        "compose_count_eq_self must have a proof value (not a bare \
         axiom-kind shell)",
    );
}

/// Content guard: the proof term must structurally reference `Nat.rec`,
/// `Eq.refl`, `congrArg`, and `Nat.succ`. These are the four ingredients
/// that prove the theorem is a genuine induction proof and not a
/// reflexivity shortcut — if the proof could collapse to `Eq.refl` alone
/// without `Nat.rec` or `congrArg`, the carrier must be discarding its
/// argument and the helper is a masquerade.
///
/// Rule M1/M3 inversion: a faithful Nat-induction proof MUST reference
/// `Nat.rec` (the recursor) and `congrArg` (step-case IH lifting). A
/// proof without `Nat.rec` would be universe-0 sleight of hand; a proof
/// without `congrArg` would mean the step case ignored its IH.
#[test]
fn test_compose_count_eq_self_body_references_induction_primitives() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.compose_count_eq_self"))
        .expect("compose_count_eq_self should exist");
    let value = ci
        .value
        .as_ref()
        .expect("compose_count_eq_self must be a Theorem with a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "proof body must reference Nat.rec — a proof without Nat.rec is \
         not an induction proof, it is a reflexivity shortcut",
    );
    assert!(
        expr_references_const(value, "Eq.refl"),
        "proof body must reference Eq.refl (base case witness)",
    );
    assert!(
        expr_references_const(value, "congrArg"),
        "proof body must reference congrArg — step case must lift the IH \
         through Nat.succ, a step case without congrArg means the IH was \
         discarded (Rule M3 violation)",
    );
    assert!(
        expr_references_const(value, "Nat.succ"),
        "proof body must reference Nat.succ — the step case lifts the IH \
         through the successor, if Nat.succ is absent the step case is \
         the identity and the proof is vacuous",
    );
    assert!(
        expr_references_const(value, "NNVerify.Block.compose_count"),
        "proof body must reference compose_count — the theorem is about \
         the carrier, not some aliased substitute",
    );
}

/// Type-check guard: the kernel must be able to infer the theorem's
/// stated type. If the proof were ill-typed (wrong universe, wrong
/// congrArg arity, etc.), kernel registration would have errored, so
/// this test is a belt-and-suspenders check that the stored type is
/// independently re-derivable from the proof term.
#[test]
fn test_compose_count_eq_self_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.Block.compose_count_eq_self"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("kernel must infer compose_count_eq_self type");
    // Stated type is `forall (k : Nat), compose_count k = k`.
    // Top-level must be a Pi with domain Nat.
    if let ExprKind::Pi(_, dom, _codom) = ty.kind() {
        assert!(
            matches!(dom.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"),
            "compose_count_eq_self should bind `k : Nat` (got \
             domain {:?})",
            dom.kind(),
        );
    } else {
        panic!(
            "compose_count_eq_self should have forall-over-Nat shape, \
             got {:?}",
            ty.kind(),
        );
    }
}

/// Idempotence guard: running init twice must not re-register or error.
#[test]
fn test_compose_count_eq_self_idempotent_init() {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("first init must succeed");
    env.init_nn_verify_blockwise_crown_ext()
        .expect("second init must be a no-op");
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose_count_eq_self"))
            .is_some(),
        "compose_count_eq_self must still be present after second init",
    );
}
