// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3586 Branch A demasquerade of
//! `NNVerify.C001.compress_tightness_helper`.
//!
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` (Rules M2 + M4),
//! the prior #3457 "constructive" proof was a MASQUERADE: the bound
//! `A ≤ B + 2 * tail_norm_sum n k' z` δ-reduced to `B ≤ B + 2 * 0` under
//! the argument-discarding reducible Definition
//! `tail_norm_sum := fun _ _ {_} _ => Rat.zero`, which the
//! `Rat.mul_zero + Rat.le_refl + Rat.le_add_of_nonneg_right` proof term
//! discharged via δ-collapse — no real tightness content.
//!
//! Branch A remediation (this file's guards):
//! 1. `compress_tightness_helper` is now a hypothesis-wrapped
//!    `Declaration::Theorem` on the strengthened C001b Pi type.
//! 2. `tail_norm_sum` is now `Declaration::Opaque` with the SAME body
//!    (`Rat.zero`) — only opacity changes. This closes the δ-reduction
//!    path that let the #3457 proof type-check via alias-collapse.
//! 3. The `compress_tightness_helper` type still type-checks through
//!    the kernel TypeChecker (as a Pi) to ensure the demotion did not
//!    regress the declaration's well-formedness.
//!
//! Mirrors the sibling demasquerade guard files for #3578 (C010
//! `certified_implies_lipschitz_local`), #3579 (C012 `single_lp_form`),
//! and #3583 (C004 `interval_hull_eq_ibp_forward`).
//!
//! Part of #3586.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Recursively search an expression for any `Expr::Const(name)` whose
/// string equals `target`. Used by the faithful-body guard
/// (`test_c001_tail_norm_sum_body_is_faithful_not_rat_zero`) to ensure the
/// Opaque body references the real L1-norm / width / to_ibp carrier chain
/// rather than the `Rat.zero` placeholder that wave-10 reverted to.
fn expr_contains_const(e: &Expr, target: &str) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == target,
        ExprKind::App(f, a) => expr_contains_const(f, target) || expr_contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, target)
                || expr_contains_const(val, target)
                || expr_contains_const(body, target)
        }
        ExprKind::Proj(_, _, arg) => expr_contains_const(arg, target),
        ExprKind::MData(_, inner) => expr_contains_const(inner, target),
        _ => false,
    }
}

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_c001()
        .expect("init_nn_verify_c001 should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: compress_tightness_helper is an honest hypothesis-wrapped Theorem
// ---------------------------------------------------------------

#[test]
fn test_c001_compress_tightness_helper_is_theorem_hypothesis_wrapped() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.C001.compress_tightness_helper",
        ))
        .expect("compress_tightness_helper should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "compress_tightness_helper should now be a hypothesis-wrapped \
         Theorem, not a C001-prefix Axiom; got {:?}",
        info.kind
    );
}

/// Structural guard: the theorem carries the local-hypothesis proof term.
#[test]
fn test_c001_compress_tightness_helper_has_proof_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.C001.compress_tightness_helper",
        ))
        .expect("compress_tightness_helper should be registered");
    assert!(
        info.value.is_some(),
        "hypothesis-wrapped theorem must carry a proof value; got value={:?}",
        info.value
    );
}

// ---------------------------------------------------------------
// Guard 2: tail_norm_sum is Opaque (not a reducible Definition)
// ---------------------------------------------------------------

#[test]
fn test_c001_tail_norm_sum_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "#3586 Branch A demasquerade: tail_norm_sum MUST be \
         Declaration::Opaque (demoted from reducible Definition to block \
         δ-unfolding of `tail_norm_sum n k' z -> Rat.zero`); got {:?}",
        info.kind
    );
}

/// Structural guard: tail_norm_sum has a value (Opaque does, Axiom does
/// not) AND is non-reducible (reducible Definition would re-open the
/// δ-reduction path that let the #3457 proof collapse the tightness
/// bound to `B ≤ B + 2 * 0`).
#[test]
fn test_c001_tail_norm_sum_is_opaque_non_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should be registered");
    assert!(
        info.value.is_some(),
        "#3586: tail_norm_sum should carry an Opaque value (well-typed \
         placeholder `Rat.zero`); got value=None"
    );
    assert!(
        !info.is_reducible,
        "#3586: tail_norm_sum must be non-reducible (Opaque). A reducible \
         Definition with body `Rat.zero` would re-open the δ-reduction \
         path that enabled the #3457 tightness-bound masquerade."
    );
}

// ---------------------------------------------------------------
// Guard 3: compress_tightness_helper type still type-checks as Pi
// ---------------------------------------------------------------

#[test]
fn test_c001_compress_tightness_helper_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C001.compress_tightness_helper"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!(
            "compress_tightness_helper hypothesis-wrapped type should still \
             type-check, got: {err:?}"
        )
    });
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3586: compress_tightness_helper type should be Pi (same shape \
         as C001b), got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// #3618 Branch B: faithful tail_norm_sum body guard tests
// ---------------------------------------------------------------

/// Guard against regressing the faithful carrier back to the `Rat.zero`
/// placeholder that enabled the wave-10 masquerade. The body must:
///
/// 1. Not be syntactically equal to `Rat.zero` (argument-discarding lambda
///    whose tail was `Const("Rat.zero")`).
/// 2. Reference `NNVerify.NNVec.l1_norm` — the published L1-norm primitive
///    the proxy carrier uses.
/// 3. Reference `NNVerify.Zonotope.to_ibp` — the zonotope-to-IBP projection
///    that makes the body depend non-trivially on the input zonotope.
///
/// A regression to a constant body would trip (1); any "fix" that drops the
/// z-dependence (e.g. using a raw Rat literal or a constant nonneg Rat) would
/// trip (3).
#[test]
fn test_c001_tail_norm_sum_body_is_faithful_not_rat_zero() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should be registered");
    let value = info
        .value
        .as_ref()
        .expect("#3618: Opaque tail_norm_sum must carry a value");

    // Guard (1): the body is no longer the argument-discarding Rat.zero
    // placeholder. We check the innermost body under the four-lambda stack.
    let mut innermost: Expr = value.clone();
    while let ExprKind::Lam(_, _, body) = innermost.kind() {
        let next = (**body).clone();
        innermost = next;
    }
    match innermost.kind() {
        ExprKind::Const(n, _) => {
            assert_ne!(
                n.to_string(),
                "Rat.zero",
                "#3618 Branch B: tail_norm_sum innermost body must NOT be the \
                 bare `Rat.zero` placeholder — wave-10 masquerade carrier. \
                 Got Const({n:?})."
            );
        }
        _ => {
            // Non-Const body is inherently non-placeholder; fine.
        }
    }

    // Guard (2): the body cites NNVec.l1_norm.
    assert!(
        expr_contains_const(value, "NNVerify.NNVec.l1_norm"),
        "#3618 Branch B: tail_norm_sum body must reference \
         NNVerify.NNVec.l1_norm (faithful L1 proxy carrier). Body: {value:?}"
    );

    // Guard (3): the body cites Zonotope.to_ibp (ensures z-dependence).
    assert!(
        expr_contains_const(value, "NNVerify.Zonotope.to_ibp"),
        "#3618 Branch B: tail_norm_sum body must reference \
         NNVerify.Zonotope.to_ibp so the result depends non-trivially on the \
         input zonotope. Body: {value:?}"
    );
}

/// Pin Opaque kind + non-reducibility post-#3618 Branch B. Redundant with
/// the #3586 guards but worth asserting here so a future regression that
/// flips the faithful body into a reducible Definition (re-opening the
/// δ-reduction path) trips specifically against the Branch B invariant,
/// not just the original wave-10 guard.
#[test]
fn test_c001_tail_norm_sum_still_opaque_after_branch_b() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "#3618 Branch B: tail_norm_sum kind MUST remain Opaque after \
         promoting to the faithful L1-proxy body. Got {:?}",
        info.kind
    );
    assert!(
        !info.is_reducible,
        "#3618 Branch B: tail_norm_sum must remain non-reducible. A reducible \
         Definition with the new faithful body would re-enable δ-reduction \
         through the carrier; Rule M2 defense requires opacity independent \
         of body content."
    );
}

/// Type-level sanity: after promoting the body, the Opaque's registered
/// type must still be the original `(n k' : Nat) → {k : Nat} → Zonotope n k
/// → Rat` Pi. Body promotion should change neither the Pi nor the Rat
/// return type.
#[test]
fn test_c001_tail_norm_sum_type_unchanged_after_branch_b() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C001.tail_norm_sum"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!(
            "#3618: tail_norm_sum type should type-check after Branch B body \
             promotion, got: {err:?}"
        )
    });
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3618: tail_norm_sum type should still be Pi, got {:?}",
        ty.kind()
    );
}

/// The Opaque body must itself type-check under the kernel `TypeChecker`.
/// This is the strongest structural guard: a body that fails to infer a
/// type cannot serve as a faithful carrier. Confirms that
/// `l1_norm ∘ width ∘ to_ibp` composes at all four lambda scopes.
#[test]
fn test_c001_tail_norm_sum_body_type_checks_after_branch_b() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C001.tail_norm_sum"))
        .expect("tail_norm_sum should be registered");
    let value = info
        .value
        .as_ref()
        .expect("#3618: Opaque tail_norm_sum must carry a value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc.infer_type(value).unwrap_or_else(|err| {
        panic!(
            "#3618 Branch B: tail_norm_sum Opaque body must type-check under \
             the kernel. Got: {err:?}"
        )
    });
}
