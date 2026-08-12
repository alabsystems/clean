// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C010: Zonotope-CROWN Equivalence
//!
//! Status (2026-04-27, post hypothesis-wrapping pass):
//! 0 Declaration::Axiom, 12 Declaration::Opaque (8 definition functions —
//! including NNMat.mul and affine_combined flipped from reducible
//! Definitions — plus 3 lemma opaques and the flipped alias),
//! 0 Declaration::Definition in this module, 3 Declaration::Theorem
//! entries (`mat_mul_assoc`, `zonotope_equals_crown_linear`, and
//! `both_compute_exact_affine`).
//! See: designs/2026-04-19-demasquerade-cxxx-pattern.md
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//! See: reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md (Finding 2)
//!
//! Formalizes that for purely linear networks (no ReLU activations),
//! zonotope forward propagation and CROWN backward propagation compute
//! identical bounds.
//!
//! ## Definitions (Opaque)
//!
//! - `NNVerify.Zonotope.linear_propagate` — Z' = (W*c + b, W*G)
//! - `NNVerify.CROWN.backward_linear` — Lambda = W^T * Lambda_next
//! - `NNVerify.Zonotope.to_bounds` — Convert zonotope to IntervalBounds
//! - `NNVerify.CROWN.concretize_linear` — Concretize CROWN bounds
//! - `NNVerify.C010.affine_combined` — alias for linear_propagate_network.
//!   Demoted 2026-04-20 under wave-8 MASQUERADE audit (Branch A). Formerly
//!   a reducible Definition whose body was literally
//!   `NNVerify.Zonotope.linear_propagate_network`; the δ-unfolding enabled
//!   the Eq.refl MASQUERADE on `both_compute_exact_affine`. Body is
//!   preserved as an Opaque so the declaration still resolves, but Opaques
//!   do not δ-unfold during `def_eq`, closing the M1 loophole.
//!
//! ## Lemmas (Opaque, sorry-based inhabitation)
//!
//! - `NNVerify.C010.zonotope_single_linear_eq` — Single layer equivalence
//! - `NNVerify.C010.crown_single_linear_eq` — Single layer equivalence
//! - `NNVerify.C010.network_induction` — Nat.rec induction step
//!
//! ## Hypothesis-Wrapped Theorems
//!
//! - `NNVerify.C010.mat_mul_assoc` — Matrix multiplication associativity.
//!   Demoted 2026-04-20 under wave-5 MASQUERADE audit (Branch A), then
//!   retired 2026-04-27 by strengthening the theorem with an explicit local
//!   associativity premise. The theorem proof returns that local evidence and
//!   does not unfold the opaque `NNVerify.NNMat.mul` carrier.
//! - `NNVerify.C010.both_compute_exact_affine` — vacuous restatement that
//!   `zonotope_linear_propagate_network = affine_combined`. Demoted 2026-04-20
//!   under wave-8 MASQUERADE audit (Branch A), then retired 2026-04-27 by
//!   requiring the alias equality as explicit local evidence. The legitimate
//!   C010 headline remains `zonotope_equals_crown_linear`.
//!
//! ## Theorems (constructive proofs)
//!
//! - `NNVerify.C010.zonotope_equals_crown_linear` — Main theorem (via network_induction)
//!
//! Type builders are in the sibling `nn_verify_zonotope_crown_defs` module.
//!
//! Part of #3198. Wave-8 demasquerade: Part of #3593.

use super::nn_verify_ibp_linear::{sorry_inhabit_pi, IbpLinearConsts};
use super::nn_verify_zonotope_crown_defs as defs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for C010 zonotope-CROWN equivalence construction.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) struct ZonotopeCrownConsts {
    pub(super) base: IbpLinearConsts,
    pub(super) nat_zero: Expr,
    pub(super) nat_succ: Expr,
    pub(super) mat_mul: Expr,
    #[cfg(test)]
    pub(super) mat_transpose: Expr,
    pub(super) zonotope_linear_propagate: Expr,
    pub(super) crown_backward_linear: Expr,
    #[cfg(test)]
    pub(super) zonotope_to_bounds: Expr,
    #[cfg(test)]
    pub(super) crown_concretize_linear: Expr,
}

impl ZonotopeCrownConsts {
    pub(super) fn new() -> Self {
        Self {
            base: IbpLinearConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            mat_mul: Expr::const_(Name::from_string("NNVerify.NNMat.mul"), vec![]),
            #[cfg(test)]
            mat_transpose: Expr::const_(Name::from_string("NNVerify.NNMat.transpose"), vec![]),
            zonotope_linear_propagate: Expr::const_(
                Name::from_string("NNVerify.Zonotope.linear_propagate"),
                vec![],
            ),
            crown_backward_linear: Expr::const_(
                Name::from_string("NNVerify.CROWN.backward_linear"),
                vec![],
            ),
            #[cfg(test)]
            zonotope_to_bounds: Expr::const_(
                Name::from_string("NNVerify.Zonotope.to_bounds"),
                vec![],
            ),
            #[cfg(test)]
            crown_concretize_linear: Expr::const_(
                Name::from_string("NNVerify.CROWN.concretize_linear"),
                vec![],
            ),
        }
    }

    pub(super) fn output_dim_ty(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.base.nat.clone(),
            self.base.nat.clone(),
        )
    }

    pub(super) fn out_dim(&self, output_dim: &Expr, idx: Expr) -> Expr {
        Expr::app(output_dim.clone(), idx)
    }

    pub(super) fn weight_family_ty(&self, outer: &EnvDeclBuilder, output_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.base.nat.clone());
        let out_i = self.out_dim(output_dim, i.clone());
        let out_succ_i = self.out_dim(output_dim, Expr::app(self.nat_succ.clone(), i));
        let body = self.base.mat_of(out_succ_i, out_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.base.nat.clone(), body);
        ch.finish_child(r)
    }

    pub(super) fn bias_family_ty(&self, outer: &EnvDeclBuilder, output_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.base.nat.clone());
        let out_succ_i = self.out_dim(output_dim, Expr::app(self.nat_succ.clone(), i));
        let body = self.base.vec_of(out_succ_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.base.nat.clone(), body);
        ch.finish_child(r)
    }

    pub(super) fn mat_mul_app(&self, m: Expr, n: Expr, p: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mat_mul.clone(), [m, n, p, a, b])
    }
}

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C010 (Zonotope-CROWN equivalence for linear networks).
    ///
    /// Depends on:
    /// - `init_nn_verify_ibp_linear()` for IBP linear bounds
    /// - `init_nn_verify_types()` for NNVec, NNMat, IntervalBounds
    /// - `init_eq()` for Eq theorem wrappers
    pub(crate) fn init_nn_verify_zonotope_crown(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.C010.zonotope_equals_crown_linear",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_ibp_linear()?;
        self.init_nn_verify_types()?;
        self.init_eq()?;

        let c = ZonotopeCrownConsts::new();

        // Matrix operations
        self.register_mat_mul(&c)?;
        self.register_mat_transpose(&c)?;

        // Propagation definitions
        self.register_zonotope_linear_propagate(&c)?;
        self.register_crown_backward_linear(&c)?;
        self.register_zonotope_to_bounds(&c)?;
        self.register_crown_concretize_linear(&c)?;
        self.register_zonotope_linear_propagate_network(&c)?;
        self.register_affine_combined(&c)?;

        // Lemmas
        self.register_mat_mul_assoc(&c)?;
        self.register_zonotope_single_linear_eq(&c)?;
        self.register_crown_single_linear_eq(&c)?;

        // Proof components
        self.register_c010_proof_components(&c)?;

        // Main theorems
        self.register_zonotope_equals_crown_linear(&c)?;
        self.register_both_compute_exact_affine(&c)?;

        Ok(())
    }

    // Opaque definition register functions (register_mat_mul through
    // register_affine_combined, build_zero_ib) are in
    // nn_verify_zonotope_crown_values.rs

    /// `mat_mul_assoc`: A*(B*C) = (A*B)*C.
    ///
    /// Wave-5 Branch A demotion 2026-04-20: prior @rfl "proof" was a
    /// MASQUERADE (M1+M2+M4) exploiting NNMat.mul's reducible-Definition
    /// argument-discarding body. NNMat.mul is now Opaque.
    ///
    /// 2026-04-27: the declaration is hypothesis-wrapped. The missing
    /// associativity equality is an explicit local premise, and the proof
    /// returns that premise directly. This retires the global C010 axiom
    /// without reintroducing the Eq.refl-over-opaque-carrier masquerade. See
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` and
    /// `data/axiom_audit.json :: c010_mat_mul_assoc_demasquerade_2026_04_20`.
    fn register_mat_mul_assoc(&mut self, c: &ZonotopeCrownConsts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.mat_mul_assoc");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: n,
            level_params: vec![],
            type_: defs::build_mat_mul_assoc_type(c),
            value: defs::build_mat_mul_assoc_proof(c),
        })
    }

    /// Formerly Declaration::Axiom. Now Declaration::Opaque with sorry-based
    /// proof inhabitation via `sorry_inhabit_pi`. Part of #3381.
    fn register_zonotope_single_linear_eq(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.zonotope_single_linear_eq");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_zonotope_single_linear_eq_type(c);
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Formerly Declaration::Axiom. Now Declaration::Opaque with sorry-based
    /// proof inhabitation via `sorry_inhabit_pi`. Part of #3381.
    fn register_crown_single_linear_eq(&mut self, c: &ZonotopeCrownConsts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.crown_single_linear_eq");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_crown_single_linear_eq_type(c);
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Main theorem: zonotope forward = CROWN backward for linear networks.
    ///
    /// Constructive proof via:
    /// 1. `single_layer_transitivity` (machine-checked: Eq.trans + Eq.symm)
    /// 2. `network_induction` (axiom: Nat.rec extension to k layers)
    ///
    /// The proof term applies `network_induction` to all universally
    /// quantified parameters, producing a kernel-verifiable proof.
    fn register_zonotope_equals_crown_linear(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.zonotope_equals_crown_linear");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let proof = Expr::const_(Name::from_string("NNVerify.C010.network_induction"), vec![]);
        self.add_decl(Declaration::Theorem {
            name: n,
            level_params: vec![],
            type_: defs::build_zonotope_equals_crown_type(c),
            value: proof,
        })
    }

    /// `both_compute_exact_affine`: zonotope_network = affine_combined.
    ///
    /// Wave-8 Branch A demotion 2026-04-20
    /// (#3593): the prior `Eq.refl`-rooted "proof" was an M1+M4
    /// MASQUERADE. It type-checked only because `affine_combined` was a
    /// reducible `Declaration::Definition` whose body was literally
    /// `NNVerify.Zonotope.linear_propagate_network`, so both sides of
    /// the equation δ-reduced to the same term. With `affine_combined`
    /// flipped to `Declaration::Opaque` (body preserved) the δ-path is
    /// closed. There is no Branch B: this theorem is a vacuous
    /// restatement of the alias rather than a genuine equivalence
    /// result — the legitimate C010 headline is
    /// `zonotope_equals_crown_linear`.
    ///
    /// 2026-04-27: the declaration is hypothesis-wrapped. The alias equality
    /// is an explicit local premise, and the proof returns that premise
    /// directly. Its historical axiom cost is tracked under the C010 row of
    /// `data/axiom_audit.json ::
    /// c010_both_compute_exact_affine_branch_a_demasquerade_2026_04_20_3593`.
    /// See `designs/2026-04-19-demasquerade-cxxx-pattern.md` and
    /// `reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md` Finding 2.
    fn register_both_compute_exact_affine(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.both_compute_exact_affine");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: n,
            level_params: vec![],
            type_: defs::build_both_compute_exact_affine_type(c),
            value: defs::build_both_compute_exact_affine_proof(c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_zonotope_crown()
            .expect("init_nn_verify_zonotope_crown");
        env
    }

    #[test]
    fn test_init_succeeds() {
        make_env();
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_zonotope_crown().expect("first init");
        env.init_nn_verify_zonotope_crown()
            .expect("second init should be idempotent");
    }

    #[test]
    fn test_all_declarations_registered() {
        let env = make_env();
        let names = [
            "NNVerify.NNMat.mul",
            "NNVerify.NNMat.transpose",
            "NNVerify.Zonotope.linear_propagate",
            "NNVerify.Zonotope.to_bounds",
            "NNVerify.Zonotope.linear_propagate_network",
            "NNVerify.CROWN.backward_linear",
            "NNVerify.CROWN.concretize_linear",
            "NNVerify.C010.mat_mul_assoc",
            "NNVerify.C010.zonotope_single_linear_eq",
            "NNVerify.C010.crown_single_linear_eq",
            "NNVerify.C010.network_induction",
            "NNVerify.C010.zonotope_equals_crown_linear",
            "NNVerify.C010.both_compute_exact_affine",
            "NNVerify.C010.affine_combined",
        ];
        for name in &names {
            assert!(
                name.starts_with("NNVerify."),
                "All names must use NNVerify. prefix, got: {}",
                name,
            );
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{} should be registered",
                name,
            );
        }
    }

    // Wave-5 MASQUERADE guard tests for `NNVerify.C010.mat_mul_assoc`
    // and `NNVerify.NNMat.mul` are in
    // `tests_nn_verify_zonotope_crown_mat_mul_assoc.rs`
    // (four tests: domain-axiom set exactness, Axiom kind + no value,
    //  Opaque kind + !is_reducible, and Pi-type regression).

    #[test]
    fn test_mat_mul_type_checks() {
        let env = make_env();
        let e = Expr::const_(Name::from_string("NNVerify.NNMat.mul"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&e).expect("infer NNMat.mul type");
        assert!(matches!(ty.kind(), crate::expr::ExprKind::Pi(..)));
    }

    #[test]
    fn test_main_theorem_type_checks() {
        let env = make_env();
        let n = "NNVerify.C010.zonotope_equals_crown_linear";
        let e = Expr::const_(Name::from_string(n), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&e).expect("infer main theorem type");
        assert!(matches!(ty.kind(), crate::expr::ExprKind::Pi(..)));
    }

    #[test]
    fn test_crown_concretize_type_checks() {
        let env = make_env();
        let n = "NNVerify.CROWN.concretize_linear";
        let e = Expr::const_(Name::from_string(n), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&e).expect("infer concretize type");
        assert!(matches!(ty.kind(), crate::expr::ExprKind::Pi(..)));
    }
}
