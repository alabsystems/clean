// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.holder3_cross_mono`, the cube-hypothesis-driven
//! MONOTONE core of the cubed cube-Hölder CH3 merge's cross term.
//!
//! # Why this module exists (the CH3 induction's cross-term, complete half)
//!
//! CH3 `(Σ A²B)³ ≤ (Σ A³)²·(Σ B³)` (the sqrt-free dual `(4/3,4)` tensorization
//! rung, design `2026-06-20-hc43-dual-tensorization-cross-term.md`) is proven by
//! induction on the term count `m` via the superadditive merge
//! ```text
//!   U₁³≤S₁²T₁ ∧ U₂³≤S₂²T₂  →  (U₁+U₂)³ ≤ (S₁+S₂)²·(T₁+T₂).
//! ```
//! Expanding both sides, the merge reduces (refute-verified, 0 violations over
//! 2M samples) to the two cube hypotheses PLUS a hypothesis-free CROSS inequality
//! ```text
//!   3U₁²U₂ + 3U₁U₂²  ≤  S₁²T₂ + 2S₁S₂T₁ + 2S₁S₂T₂ + S₂²T₁,
//! ```
//! which splits symmetrically into `3U₁²U₂ ≤ 2P+Q` (`P:=S₁S₂T₁`, `Q:=S₁²T₂`) and
//! its mirror. Each split closes ROOT-FREELY via the landed
//! `NNReal.le_of_cube_le_cube`: `(3U₁²U₂)³ = 27·U₁⁶·U₂³ ≤ 27·P²·Q ≤ (2P+Q)³`,
//! where the FIRST `≤` is pure cube-hypothesis MONOTONICITY and the SECOND `≤` is
//! the rational AM-GM `27P²Q ≤ (2P+Q)³` (= `(P−Q)²(8P+Q) ≥ 0`).
//!
//! This module lands the FIRST `≤` — the complete, AM-GM-free monotone core. With
//! `U₁³ := (U₁·U₁)·U₁` and `S₁²T₁ := (S₁·S₁)·T₁` (left-nested, matching
//! `NNReal.le_of_cube_le_cube`):
//! ```text
//!   NNReal.holder3_cross_mono : ∀ U₁ S₁ T₁ U₂ S₂ T₂ : NNReal,
//!     NNReal.le ((U₁·U₁)·U₁) ((S₁·S₁)·T₁) →
//!     NNReal.le ((U₂·U₂)·U₂) ((S₂·S₂)·T₂) →
//!     NNReal.le (((U₁·U₁·U₁) · (U₁·U₁·U₁)) · (U₂·U₂·U₂))
//!               ((((S₁·S₁)·T₁) · ((S₁·S₁)·T₁)) · ((S₂·S₂)·T₂))
//! ```
//! i.e. `(U₁³·U₁³)·U₂³ ≤ ((S₁²T₁)·(S₁²T₁))·(S₂²T₂)` — the `U₁⁶·U₂³` value bounded
//! by `(S₁²T₁)²·(S₂²T₂)` (which, up to the constant `27` and a monomial reshuffle,
//! is `27·P²·Q`).
//!
//! # Proof shape (axiom-free, monotone-only — two landed `NNReal.mul_le_mul`)
//!
//! `NNReal.mul_le_mul a b c d (a≤b)(c≤d) : a·c ≤ b·d`. Apply it twice:
//! - `mul_le_mul U₁³ (S₁²T₁) U₁³ (S₁²T₁) h1 h1 : U₁³·U₁³ ≤ (S₁²T₁)·(S₁²T₁)`,
//! - `mul_le_mul (U₁³·U₁³) ((S₁²T₁)·(S₁²T₁)) U₂³ (S₂²T₂) (…) h2`.
//!
//! No identity, no AM-GM, no root.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.holder3_cross_mono`.
struct Holder3CrossMonoConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_mul_le_mul: Expr,
}

impl Holder3CrossMonoConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul_le_mul: k("NNReal.mul_le_mul"),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    /// `(a·a)·a` — left-nested cube (matches `NNReal.le_of_cube_le_cube`).
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    /// `(s·s)·t` — the left-nested `s²·t` Hölder corner.
    fn sq_t(&self, s: &Expr, t: &Expr) -> Expr {
        self.nnmul(&self.nnmul(s, s), t)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_le_mul a b c d hab hcd : a·c ≤ b·d`.
    #[allow(clippy::too_many_arguments)]
    fn mul_le_mul(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
}

impl Environment {
    /// Register `NNReal.holder3_cross_mono`. Idempotent; foundational-only.
    ///
    /// Depends only on the landed `NNReal.mul_le_mul` (`cube_mono`). No axiom is
    /// added or removed.
    pub fn init_algebra_nnreal_holder3_cross_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul

        let c = Holder3CrossMonoConsts::new();
        self.register_holder3_cross_mono(&c)?;
        Ok(())
    }

    fn register_holder3_cross_mono(&mut self, c: &Holder3CrossMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.holder3_cross_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
            let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
            let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
            let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
            let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
            let (t2_id, t2) = b.fresh_local(c.nnreal.clone());

            let u1c = c.nncube(&u1);
            let u2c = c.nncube(&u2);
            let p1 = c.sq_t(&s1, &t1); // S₁²·T₁
            let p2 = c.sq_t(&s2, &t2); // S₂²·T₂

            let h1_ty = c.nnle(&u1c, &p1);
            let (h1_id, _) = b.fresh_local(h1_ty.clone());
            let h2_ty = c.nnle(&u2c, &p2);
            let (h2_id, _) = b.fresh_local(h2_ty.clone());

            let concl = c.nnle(
                &c.nnmul(&c.nnmul(&u1c, &u1c), &u2c),
                &c.nnmul(&c.nnmul(&p1, &p1), &p2),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_cross_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The `NNReal.holder3_cross_mono` proof term: two landed `NNReal.mul_le_mul`.
fn build_cross_mono_value(c: &Holder3CrossMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
    let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
    let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
    let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
    let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
    let (t2_id, t2) = b.fresh_local(c.nnreal.clone());

    let u1c = c.nncube(&u1);
    let u2c = c.nncube(&u2);
    let p1 = c.sq_t(&s1, &t1);
    let p2 = c.sq_t(&s2, &t2);

    let h1_ty = c.nnle(&u1c, &p1);
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let h2_ty = c.nnle(&u2c, &p2);
    let (h2_id, h2) = b.fresh_local(h2_ty.clone());

    // step1 : U₁³·U₁³ ≤ (S₁²T₁)·(S₁²T₁)   [mul_le_mul U₁³ P₁ U₁³ P₁ h1 h1].
    let step1 = c.mul_le_mul(&u1c, &p1, &u1c, &p1, h1.clone(), h1);
    let u1c2 = c.nnmul(&u1c, &u1c); // U₁³·U₁³
    let p1sq = c.nnmul(&p1, &p1); // (S₁²T₁)·(S₁²T₁)

    // step2 : (U₁³·U₁³)·U₂³ ≤ ((S₁²T₁)·(S₁²T₁))·(S₂²T₂)
    //         [mul_le_mul (U₁³·U₁³) (P₁·P₁) U₂³ P₂ step1 h2].
    let proof = c.mul_le_mul(&u1c2, &p1sq, &u2c, &p2, step1, h2);

    let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, proof);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_holder3_cross_mono()
            .expect("init_algebra_nnreal_holder3_cross_mono");
        env.init_algebra_nnreal_holder3_cross_mono()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_holder3_cross_mono_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.holder3_cross_mono");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.holder3_cross_mono must kernel-check: {e:?}"));
    }

    #[test]
    fn test_holder3_cross_mono_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.holder3_cross_mono");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
