// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C010 Robustness-generalization Opaque definition value builders.
//!
//! Contains well-typed placeholder values for the 8 definition functions
//! that were upgraded from `Declaration::Axiom` to `Declaration::Opaque`.
//! Split from `nn_verify_robustness_generalization.rs` for file-size compliance.

use super::nn_verify_robustness_generalization::RobustnessGenConsts;
use super::nn_verify_robustness_generalization_defs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // -- Definitions (Opaque — Category A: definitions-masquerading-as-axioms) -

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_certified_robust(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_certified_robust_type(c);
        // Value: fun (n : Nat) (_ : NNVec n -> NNVec n) (_ : Rat) => True
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n_var) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n_var);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let true_val = Expr::const_(Name::from_string("True"), vec![]);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), true_val);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.certified_robust"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.RobustnessGen.lipschitz_local`:
    /// `(n : Nat) -> (NNVec n -> NNVec n) -> Rat -> Rat -> Prop`.
    ///
    /// **#3578 Branch A demasquerade (2026-04-20).** Reverted from the
    /// #3463 reducible `Declaration::Definition` (body `fun _ _ _ _ =>
    /// True`) back to `Declaration::Opaque` with the same placeholder
    /// body. Opaques are NOT delta-unfolded by kernel `def_eq`, so
    /// `lipschitz_local d f eps L` can no longer collapse to `True`
    /// during proof type-checking. This closes the delta-reduction path
    /// that enabled the `certified_implies_lipschitz_local` `True.intro`
    /// masquerade (MASQUERADE per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4).
    /// Sibling pattern: #3568 C007 `cert_sound`, #3566 C011 softmax.
    ///
    /// **Vacuity caveat:** `lipschitz_local`'s body remains the `True`
    /// placeholder. Substantive Lipschitz content arrives only when the
    /// body is replaced with a real Lipschitz predicate (`forall x y, |f x
    /// - f y| <= L * |x - y|`) — blocked on Rat-inequality infrastructure
    ///   and NNVec norm formalization (Branch B, epic #3470).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_lipschitz_local(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_lipschitz_local_type(c);
        // Placeholder body: fun (n : Nat) (_ : NNVec n -> NNVec n) (_ _ : Rat) => True.
        // Retained so the Opaque has a well-typed value; Opaque's non-unfolding
        // behavior is what breaks the #3463 masquerade path.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n_var) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n_var);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (l_id, _) = b.fresh_local(c.rat.clone());
            let true_val = Expr::const_(Name::from_string("True"), vec![]);
            let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), true_val);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.lipschitz_local"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_nat_to_rat(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_nat_to_rat_type(c);
        // Value: fun (_ : Nat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.nat_to_rat"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_sqrt(&mut self, c: &RobustnessGenConsts) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_sqrt_type(c);
        // Value: fun (x : Rat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.sqrt"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_ln(&mut self, c: &RobustnessGenConsts) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_ln_type(c);
        // Value: fun (x : Rat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.ln"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_rademacher_complexity(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_rademacher_complexity_type(c);
        // Value: fun (_ : Nat) (_ : Rat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, _) = b.fresh_local(c.nat.clone());
            let (l_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.rademacher_complexity"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_generalization_gap(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_generalization_gap_type(c);
        // Value: fun (_ _ : Rat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (tr_id, _) = b.fresh_local(c.rat.clone());
            let (te_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(
                te_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.rat_zero.clone(),
            );
            let e = b.mk_lam(tr_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.generalization_gap"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_rg_gen_bound(
        &mut self,
        c: &RobustnessGenConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_robustness_generalization_defs as defs;
        let ty = defs::build_gen_bound_type(c);
        // Value: fun (_ : Nat) (_ _ _ : Rat) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, _) = b.fresh_local(c.nat.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (m_id, _) = b.fresh_local(c.rat.clone());
            let (delta_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(
                delta_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.rat_zero.clone(),
            );
            let e = b.mk_lam(m_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.RobustnessGen.gen_bound"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
