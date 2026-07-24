// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for `NNVerify.Zonotope.to_ibp`.
//!
//! ## History
//!
//! The #3591 Option A remediation made `to_ibp` a `Declaration::Opaque` with
//! the FAKE zero-interval carrier
//! `fun n k _z => IntervalBounds.mk n (fun _ => 0) (fun _ => 0) (fun _ => Rat.le_refl 0)`.
//! Opacity was needed because that body was an *argument-discarding constant
//! carrier* (Rule M2): a reducible Definition over it was a latent M1 attack
//! surface — `to_ibp z₁ = to_ibp z₂` or `lo (to_ibp z) i = Rat.zero` could
//! close by `Eq.refl` via δ-unfolding without any real geometric content.
//!
//! ## Faithful zonotope→IBP (current)
//!
//! `to_ibp` now carries the mathematically FAITHFUL element-wise range
//! ```text
//! radius_i = Fin.sum k (fun j => Rat.abs (z.generators i j))
//! lower_i  = Rat.sub (z.center i) radius_i
//! upper_i  = Rat.add (z.center i) radius_i
//! ```
//! with a REAL `valid : ∀ i, lower_i ≤ upper_i` proof (see
//! `nn_verify_zonotope_to_ibp_faithful`). It is registered as a REDUCIBLE
//! `Declaration::Definition` again, because `to_ibp_sound` (T12) must δ-unfold
//! it to reach `(to_ibp z).lower i = center i - radius i`.
//!
//! The #3591 M1 concern was *specific to the argument-discarding zero body*.
//! With a faithful body that genuinely depends on `z.center` / `z.generators`,
//! the masquerade is closed STRUCTURALLY (not by opacity): a false
//! `to_ibp z₁ = to_ibp z₂` cannot close by `Eq.refl` (the δ-unfolded bodies
//! differ when the zonotopes differ), and `lo (to_ibp z) i` reduces to
//! `center i - Σ|G_ij|`, never to `Rat.zero`. This is the same demasquerade
//! technique used for `Rat.abs` (TCB-shrink Tier 1, `algebra_rat_abs_proof.rs`):
//! a non-trivial body closes the attack surface that opacity previously masked.
//!
//! These guards therefore now pin the FAITHFUL + reducible state and the
//! structural (body-cites-`z`) demasquerade, replacing the obsolete asserts
//! about the FAKE zero body.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_zonotope()
        .expect("init_nn_verify_zonotope should succeed");
    env
}

/// Recursively check whether `e` mentions the const named `target`.
fn expr_contains_const(e: &Expr, target: &str) -> bool {
    let target_name = Name::from_string(target);
    fn go(e: &Expr, t: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == t,
            ExprKind::App(f, a) => go(f, t) || go(a, t),
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => go(ty, t) || go(b, t),
            ExprKind::Let(_, ty, v, b, _) => go(ty, t) || go(v, t) || go(b, t),
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => go(x, t),
            _ => false,
        }
    }
    go(e, &target_name)
}

// ---------------------------------------------------------------
// Guard 1: to_ibp is now the FAITHFUL reducible Definition
// ---------------------------------------------------------------

/// Primary guard: `NNVerify.Zonotope.to_ibp` is a `Declaration::Definition`
/// (the faithful `[center − Σ|G|, center + Σ|G|]` carrier), not the old FAKE
/// zero-interval `Declaration::Opaque`. `to_ibp_sound` (T12) needs to δ-unfold
/// it, so reducibility is required and the structural demasquerade (Guard 3)
/// keeps the M1 surface closed.
#[test]
fn test_zonotope_to_ibp_is_faithful_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
        .expect("NNVerify.Zonotope.to_ibp should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Faithful zonotope→IBP: NNVerify.Zonotope.to_ibp MUST be a \
         Declaration::Definition (the faithful range carrier); the old FAKE \
         zero-interval Opaque body is retired. Got {:?}",
        info.kind
    );
}

/// Structural guard: `to_ibp` carries a value (Definition body) AND is
/// reducible, so `to_ibp_sound` can δ-unfold `(to_ibp z).lower/upper`.
#[test]
fn test_zonotope_to_ibp_is_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
        .expect("NNVerify.Zonotope.to_ibp should be registered");

    assert!(
        info.value.is_some(),
        "Faithful zonotope→IBP: to_ibp should carry its Definition body; \
         got value=None"
    );
    assert!(
        info.is_reducible,
        "Faithful zonotope→IBP: to_ibp must be reducible so T12 \
         (to_ibp_sound) can δ-unfold (to_ibp z).lower / .upper to the \
         faithful range terms."
    );
}

// ---------------------------------------------------------------
// Guard 2: to_ibp type still type-checks as Pi
// ---------------------------------------------------------------

/// The faithful body must not regress the declaration's well-formedness.
/// `to_ibp` should type-check as a Pi
/// `Nat -> Nat -> Zonotope n k -> IntervalBounds n`.
#[test]
fn test_zonotope_to_ibp_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("Faithful to_ibp type should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "to_ibp type should be Pi \
         (Nat -> Nat -> Zonotope n k -> IntervalBounds n), got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Guard 3: M1 masquerade closed STRUCTURALLY by the z-dependent body
// ---------------------------------------------------------------

/// Regression guard for the structural demasquerade: the `to_ibp` body MUST
/// genuinely depend on the zonotope `z` by projecting its generators (it cites
/// `Rat.abs` over `z.generators` summed by `Fin.sum`). The OLD FAKE body was
/// argument-discarding (`fun _z => mk 0 0 _`), which is exactly what made the
/// M1 alias-collapse path (`to_ibp z₁ = to_ibp z₂ ~> Eq.refl`) dangerous. A
/// faithful body that mentions `Rat.abs` + `Fin.sum` cannot collapse two
/// distinct zonotopes to the same interval by `Eq.refl`, so reducibility is
/// safe.
#[test]
fn test_zonotope_to_ibp_body_depends_on_generators() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
        .expect("NNVerify.Zonotope.to_ibp should be registered");
    let value = info
        .value
        .as_ref()
        .expect("to_ibp should carry a Definition body");

    assert!(
        expr_contains_const(value, "Rat.abs"),
        "Faithful zonotope→IBP: to_ibp body MUST cite Rat.abs (the radius is \
         Σ|G_ij|), proving it is no longer the argument-discarding zero \
         carrier that made the M1 masquerade dangerous."
    );
    assert!(
        expr_contains_const(value, "Fin.sum"),
        "Faithful zonotope→IBP: to_ibp body MUST cite Fin.sum (the radius \
         sums |G_ij| over the generator row), so the result depends \
         non-trivially on z.generators."
    );
}

// ---------------------------------------------------------------
// Guard 4: T12 to_ibp_sound is a proven Theorem; its closure is recorded
// ---------------------------------------------------------------

/// `to_ibp_sound` (T12) is now a genuine `Declaration::Theorem` with a real
/// proof term (the summed triangle inequality), built over the FAITHFUL
/// `to_ibp`. Its transitive non-foundational axiom closure is asserted here so
/// any future regression that smuggles a NEW domain axiom into the proof is
/// caught. Today the closure (in the overlays build) is FOUNDATIONAL-ONLY: all
/// bricks (`Fin.sum_le`, `Fin.sum_neg`, `Fin.sum_nonneg`, `Rat.abs_mul`,
/// `Rat.abs_nonneg`, `NNVerify.mul_nonneg_le_left`, the `Rat.max`/`Rat.neg`
/// order lemmas, `Rat.le_abs_self`/`Rat.neg_abs_le`) are constructive theorems.
#[test]
fn test_t12_to_ibp_sound_is_proven_theorem_foundational_closure() {
    use crate::env::types::ConstantKind;
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_compress()
        .expect("init_nn_verify_zonotope_compress should succeed");

    let name = Name::from_string("NNVerify.Zonotope.to_ibp_sound");
    let info = env
        .get_const(&name)
        .expect("T12 to_ibp_sound should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "T12 to_ibp_sound must be a proven Theorem (faithful zonotope→IBP)"
    );

    let domain_axioms = env
        .axiom_deps(&name)
        .expect("to_ibp_sound should have an axiom-deps closure");
    assert!(
        domain_axioms.is_empty(),
        "T12 to_ibp_sound transitive closure must be FOUNDATIONAL-only \
         (⊆ FOUNDATIONAL_AXIOMS); a non-empty domain-axiom set means a new \
         axiom leaked into the faithful soundness proof: {domain_axioms:?}"
    );
}
