// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive Farkas-combination theorems (T09 successor).
//!
//! The legacy `NNVerify.farkas_to_interval` (in
//! `nn_verify_foundation_theorems_farkas.rs`) is a `Declaration::Axiom`
//! whose hypothesis `farkas_certificate_valid` is itself an opaque axiom
//! predicate with no computational content — there is nothing to
//! eliminate, so no constructive proof term can be produced from that
//! exact statement.
//!
//! This module replaces the *content* of Farkas-to-interval with three
//! `Declaration::Theorem`s whose proof terms `TypeChecker::infer_type`
//! accepts and which are **sorry-free**. They state the actual
//! Farkas multiplier-combination facts over `Rat` — exactly what the cert
//! parser (`nn_verify_cert_parser.rs:292`) said had to "be added when
//! gamma-crown emits exact rational coefficients":
//!
//! - `NNVerify.farkas_scale` — single-row Farkas scaling:
//!     `0 ≤ μ → a ≤ b → μ*a ≤ μ*b`.
//!   (One non-negative multiplier applied to one premise inequality.)
//!
//! - `NNVerify.farkas_combine_2` — two-row Farkas combination:
//!     `0 ≤ μ₁ → 0 ≤ μ₂ → a₁ ≤ b₁ → a₂ ≤ b₂
//!       → μ₁*a₁ + μ₂*a₂ ≤ μ₁*b₁ + μ₂*b₂`.
//!   (A non-negative combination of two premises preserves the bound:
//!    the lower combination is dominated by the upper combination.)
//!
//! - `NNVerify.farkas_combine_2_le_bound` — Farkas combination meets a
//!   dominating constant (the "yields the claimed bound" step):
//!     `0 ≤ μ₁ → 0 ≤ μ₂ → a₁ ≤ b₁ → a₂ ≤ b₂
//!       → (μ₁*b₁ + μ₂*b₂ ≤ bound)
//!       → μ₁*a₁ + μ₂*a₂ ≤ bound`.
//!   This is the interval/bound conclusion of Farkas: a non-negative
//!   combination of the premises, dominated by `bound`, bounds the
//!   combined linear form by `bound`.
//!
//! ## Proof strategy (all constructive, zero sorry)
//!
//! Each proof composes already-constructive kernel theorems:
//! - `NNVerify.mul_nonneg_le_left : 0 ≤ w → a ≤ b → w*a ≤ w*b`
//!   (constructive `Declaration::Theorem`, #3490 T3 / #3503)
//! - `NNVerify.add_le_add : a₁ ≤ b₁ → a₂ ≤ b₂ → a₁+a₂ ≤ b₁+b₂`
//!   (constructive `Declaration::Theorem`, #3490 Batch 0)
//! - `Rat.le_trans : a ≤ b → b ≤ c → a ≤ c` (foundational order axiom)
//!
//! `farkas_scale` is `mul_nonneg_le_left` re-exposed under the Farkas
//! name. `farkas_combine_2 = add_le_add (mul_nonneg_le_left …)
//! (mul_nonneg_le_left …)`. `farkas_combine_2_le_bound =
//! Rat.le_trans (farkas_combine_2 …) h_dom`.
//!
//! Their transitive axiom closures contain only honest Rat
//! ordered-field axioms; they do NOT depend on `farkas_certificate_valid`
//! or any opaque/sorry predicate.
//!
//! The proof-term builders and the shared `FarkasConsts` live in
//! `nn_verify_foundation_theorems_farkas_constructive_proofs.rs` to keep
//! this module under the 500-line limit.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_foundation_theorems_farkas_constructive_proofs::{
    build_farkas_combine_2_le_bound_proof, build_farkas_combine_2_proof, FarkasConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Initialize the constructive Farkas-combination theorems.
    ///
    /// Depends on: `init_nn_verify_foundation_theorems` (which itself
    /// initializes `init_nn_verify_ibp_linear`, providing
    /// `mul_nonneg_le_left` / `add_le_add`, and `init_nn_verify_proofs`,
    /// providing `Rat.le_trans`).
    ///
    /// # Contract
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `farkas_scale`, `farkas_combine_2`,
    ///          `farkas_combine_2_le_bound` registered as constructive
    ///          `Declaration::Theorem`s
    /// ENSURES: Idempotent
    pub fn init_nn_verify_farkas_constructive(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_farkas_constructive_init {
            return Ok(());
        }
        self.init_nn_verify_foundation_theorems()?;

        let c = FarkasConsts::new();
        self.register_farkas_scale(&c)?;
        self.register_farkas_combine_2(&c)?;
        self.register_farkas_combine_2_le_bound(&c)?;

        self.nn_verify_farkas_constructive_init = true;
        Ok(())
    }

    /// `NNVerify.farkas_scale`:
    /// `∀ (mu a b : Rat), 0 ≤ mu → a ≤ b → mu*a ≤ mu*b`.
    ///
    /// Single-row Farkas scaling. Constructive proof: directly applies
    /// `NNVerify.mul_nonneg_le_left`.
    fn register_farkas_scale(&mut self, c: &FarkasConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_scale");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (mu_id, mu) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nn = c.rat_le(c.rat_zero.clone(), mu.clone());
            let h_ab = c.rat_le(a.clone(), bv.clone());
            let concl = c.rat_le(c.mul(mu.clone(), a.clone()), c.mul(mu.clone(), bv.clone()));
            let (h2_id, _) = b.fresh_local(h_ab.clone());
            let (h1_id, _) = b.fresh_local(h_nn.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_ab, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(mu_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mu_id, mu) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nn = c.rat_le(c.rat_zero.clone(), mu.clone());
            let h_ab = c.rat_le(a.clone(), bv.clone());
            let (h1_id, h1) = b.fresh_local(h_nn.clone());
            let (h2_id, h2) = b.fresh_local(h_ab.clone());
            let body = c.scale(mu.clone(), a.clone(), bv.clone(), h1, h2);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h_ab, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(mu_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.farkas_combine_2`:
    /// `∀ (mu1 mu2 a1 b1 a2 b2 : Rat),
    ///    0 ≤ mu1 → 0 ≤ mu2 → a1 ≤ b1 → a2 ≤ b2
    ///    → mu1*a1 + mu2*a2 ≤ mu1*b1 + mu2*b2`.
    ///
    /// Two-row Farkas combination. Constructive proof:
    /// `add_le_add (mul_nonneg_le_left mu1 a1 b1 ..)
    ///             (mul_nonneg_le_left mu2 a2 b2 ..)`.
    fn register_farkas_combine_2(&mut self, c: &FarkasConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_combine_2");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (mu1_id, mu1) = b.fresh_local(c.rat.clone());
            let (mu2_id, mu2) = b.fresh_local(c.rat.clone());
            let (a1_id, a1) = b.fresh_local(c.rat.clone());
            let (b1_id, b1v) = b.fresh_local(c.rat.clone());
            let (a2_id, a2) = b.fresh_local(c.rat.clone());
            let (b2_id, b2v) = b.fresh_local(c.rat.clone());
            let h_mu1 = c.rat_le(c.rat_zero.clone(), mu1.clone());
            let h_mu2 = c.rat_le(c.rat_zero.clone(), mu2.clone());
            let h_ab1 = c.rat_le(a1.clone(), b1v.clone());
            let h_ab2 = c.rat_le(a2.clone(), b2v.clone());
            let lhs = c.add(
                c.mul(mu1.clone(), a1.clone()),
                c.mul(mu2.clone(), a2.clone()),
            );
            let rhs = c.add(
                c.mul(mu1.clone(), b1v.clone()),
                c.mul(mu2.clone(), b2v.clone()),
            );
            let concl = c.rat_le(lhs, rhs);
            let (hab2_id, _) = b.fresh_local(h_ab2.clone());
            let (hab1_id, _) = b.fresh_local(h_ab1.clone());
            let (hmu2_id, _) = b.fresh_local(h_mu2.clone());
            let (hmu1_id, _) = b.fresh_local(h_mu1.clone());
            let e = b.mk_pi(hab2_id, BinderInfo::Default, h_ab2, concl);
            let e = b.mk_pi(hab1_id, BinderInfo::Default, h_ab1, e);
            let e = b.mk_pi(hmu2_id, BinderInfo::Default, h_mu2, e);
            let e = b.mk_pi(hmu1_id, BinderInfo::Default, h_mu1, e);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(mu2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(mu1_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_farkas_combine_2_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.farkas_combine_2_le_bound`:
    /// `∀ (mu1 mu2 a1 b1 a2 b2 bound : Rat),
    ///    0 ≤ mu1 → 0 ≤ mu2 → a1 ≤ b1 → a2 ≤ b2
    ///    → (mu1*b1 + mu2*b2 ≤ bound)
    ///    → mu1*a1 + mu2*a2 ≤ bound`.
    ///
    /// The Farkas-to-bound conclusion: a non-negative combination of the
    /// premises, dominated by `bound`, bounds the combined linear form by
    /// `bound`. Constructive proof: `Rat.le_trans` of `farkas_combine_2`
    /// with the dominating hypothesis.
    fn register_farkas_combine_2_le_bound(&mut self, c: &FarkasConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_combine_2_le_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (mu1_id, mu1) = b.fresh_local(c.rat.clone());
            let (mu2_id, mu2) = b.fresh_local(c.rat.clone());
            let (a1_id, a1) = b.fresh_local(c.rat.clone());
            let (b1_id, b1v) = b.fresh_local(c.rat.clone());
            let (a2_id, a2) = b.fresh_local(c.rat.clone());
            let (b2_id, b2v) = b.fresh_local(c.rat.clone());
            let (bound_id, bound) = b.fresh_local(c.rat.clone());
            let h_mu1 = c.rat_le(c.rat_zero.clone(), mu1.clone());
            let h_mu2 = c.rat_le(c.rat_zero.clone(), mu2.clone());
            let h_ab1 = c.rat_le(a1.clone(), b1v.clone());
            let h_ab2 = c.rat_le(a2.clone(), b2v.clone());
            let upper = c.add(
                c.mul(mu1.clone(), b1v.clone()),
                c.mul(mu2.clone(), b2v.clone()),
            );
            let h_dom = c.rat_le(upper.clone(), bound.clone());
            let lower = c.add(
                c.mul(mu1.clone(), a1.clone()),
                c.mul(mu2.clone(), a2.clone()),
            );
            let concl = c.rat_le(lower, bound.clone());
            let (hdom_id, _) = b.fresh_local(h_dom.clone());
            let (hab2_id, _) = b.fresh_local(h_ab2.clone());
            let (hab1_id, _) = b.fresh_local(h_ab1.clone());
            let (hmu2_id, _) = b.fresh_local(h_mu2.clone());
            let (hmu1_id, _) = b.fresh_local(h_mu1.clone());
            let e = b.mk_pi(hdom_id, BinderInfo::Default, h_dom, concl);
            let e = b.mk_pi(hab2_id, BinderInfo::Default, h_ab2, e);
            let e = b.mk_pi(hab1_id, BinderInfo::Default, h_ab1, e);
            let e = b.mk_pi(hmu2_id, BinderInfo::Default, h_mu2, e);
            let e = b.mk_pi(hmu1_id, BinderInfo::Default, h_mu1, e);
            let e = b.mk_pi(bound_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(mu2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(mu1_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_farkas_combine_2_le_bound_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_farkas_constructive()
            .expect("init_nn_verify_farkas_constructive");
        env
    }

    /// A constructive Farkas theorem: registered, is a Theorem, has a
    /// proof term, the proof term type-checks against the declared type,
    /// and is sorry-free.
    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a Theorem, got {:?}",
            info.kind
        );
        let proof = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a proof term"));
        assert!(
            !info.sorry_summary().has_sorry,
            "{name} proof should be sorry-free"
        );
        let tc = TypeChecker::with_mode(env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .unwrap_or_else(|e| panic!("{name} proof should type-check, got {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred type should match declared type"
        );
        assert!(
            matches!(info.type_.kind(), ExprKind::Pi(..)),
            "{name} type should be a Pi"
        );
        // The const itself must also infer (validates the whole declaration).
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} const should type-check, got {e:?}"));
    }

    #[test]
    fn test_farkas_scale_constructive() {
        assert_constructive_theorem(&make_env(), "NNVerify.farkas_scale");
    }

    #[test]
    fn test_farkas_combine_2_constructive() {
        assert_constructive_theorem(&make_env(), "NNVerify.farkas_combine_2");
    }

    #[test]
    fn test_farkas_combine_2_le_bound_constructive() {
        assert_constructive_theorem(&make_env(), "NNVerify.farkas_combine_2_le_bound");
    }

    #[test]
    fn test_all_three_constructive_and_sorry_free() {
        let env = make_env();
        for name in [
            "NNVerify.farkas_scale",
            "NNVerify.farkas_combine_2",
            "NNVerify.farkas_combine_2_le_bound",
        ] {
            assert_constructive_theorem(&env, name);
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_farkas_constructive().expect("first");
        env.init_nn_verify_farkas_constructive().expect("second");
    }
}
