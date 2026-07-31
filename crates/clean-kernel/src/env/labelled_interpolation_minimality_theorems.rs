// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for labelled interpolation minimality.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Labelled interpolant validity (any labelling yields a Craig interpolant)
//! - McMillan support minimality (Var(I_McM) subset Var(I_L) for all L)
//! - Complete lattice structure on extractable interpolants
//! - McMillan = lattice bottom (weakest interpolant)
//! - Reverse McMillan = lattice top (strongest interpolant)
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: D'Silva et al. (2010), "Propositional Interpolation and
//!            Abstract Interpretation", ESOP 2010;
//!            D'Silva et al. (2010), "Interpolant Strength", VMCAI 2010.

#[cfg(test)]
use super::labelled_interpolation_minimality::LabelledInterpolationConsts;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    // ====================================================================
    // Theorem 1: Labelled interpolant validity
    // ====================================================================

    /// Any valid labelling produces a formula satisfying Craig conditions.
    /// Generalizes McMillan's extraction to arbitrary labellings.
    #[cfg(test)]
    pub(super) fn register_labelled_interpolant_valid(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.LabelledInterpolation.labelled_interpolant_valid_helper";
        let thm_name = "ProofTheory.LabelledInterpolation.labelled_interpolant_valid";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (pi : Proof) -> (L : LabellingFunction) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (pi_id, _) = b.fresh_local(c.res_proof.clone());
                let (l_id, _) = b.fresh_local(c.labelling_fn.clone());
                let e = b.mk_pi(
                    l_id,
                    BinderInfo::Default,
                    c.labelling_fn.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, pi) = b.fresh_local(c.res_proof.clone());
            let (l_id, l) = b.fresh_local(c.labelling_fn.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), pi.clone(), l.clone()]);
            let e = b.mk_pi(l_id, BinderInfo::Default, c.labelling_fn.clone(), body);
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: McMillan support minimality (D'Silva ESOP 2010)
    // ====================================================================

    /// **Main theorem (D'Silva ESOP 2010).** Var(I_McM(pi)) subset Var(I_L(pi))
    /// for all valid labellings L. McMillan's disjunction rule on A-only
    /// pivots introduces no new variables; conjunction on others may.
    #[cfg(test)]
    pub(super) fn register_mcmillan_support_minimal(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.LabelledInterpolation.mcmillan_support_minimal_helper";
        let thm_name = "ProofTheory.LabelledInterpolation.mcmillan_support_minimal";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (pi_id, _) = b.fresh_local(c.res_proof.clone());
                let (l_id, _) = b.fresh_local(c.labelling_fn.clone());
                let e = b.mk_pi(
                    l_id,
                    BinderInfo::Default,
                    c.labelling_fn.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, pi) = b.fresh_local(c.res_proof.clone());
            let (l_id, l) = b.fresh_local(c.labelling_fn.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), pi.clone(), l.clone()]);
            let e = b.mk_pi(l_id, BinderInfo::Default, c.labelling_fn.clone(), body);
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Interpolant lattice completeness
    // ====================================================================

    /// Extractable interpolants form a complete lattice under |= for fixed
    /// (A, B, pi). Bottom = McMillan, top = reverse McMillan.
    #[cfg(test)]
    pub(super) fn register_interpolant_lattice_complete(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.LabelledInterpolation.interpolant_lattice_complete_helper";
        let thm_name = "ProofTheory.LabelledInterpolation.interpolant_lattice_complete";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (pi_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    pi_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, pi) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), pi.clone()]);
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: McMillan = lattice bottom
    // ====================================================================

    /// McMillan = lattice bottom: interpolant_implies(I_McM, I_L) for all L.
    /// The weakest (most general) extractable interpolant.
    #[cfg(test)]
    pub(super) fn register_mcmillan_is_lattice_bottom(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom_helper";
        let thm_name = "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (pi_id, _) = b.fresh_local(c.res_proof.clone());
                let (l_id, _) = b.fresh_local(c.labelling_fn.clone());
                let e = b.mk_pi(
                    l_id,
                    BinderInfo::Default,
                    c.labelling_fn.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, pi) = b.fresh_local(c.res_proof.clone());
            let (l_id, l) = b.fresh_local(c.labelling_fn.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), pi.clone(), l.clone()]);
            let e = b.mk_pi(l_id, BinderInfo::Default, c.labelling_fn.clone(), body);
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: Reverse McMillan = lattice top
    // ====================================================================

    /// Reverse McMillan = lattice top: interpolant_implies(I_L, I_RMcM) for all L.
    /// The strongest (most specific) extractable interpolant.
    #[cfg(test)]
    pub(super) fn register_reverse_mcmillan_is_lattice_top(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name =
            "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top_helper";
        let thm_name = "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (pi_id, _) = b.fresh_local(c.res_proof.clone());
                let (l_id, _) = b.fresh_local(c.labelling_fn.clone());
                let e = b.mk_pi(
                    l_id,
                    BinderInfo::Default,
                    c.labelling_fn.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, pi) = b.fresh_local(c.res_proof.clone());
            let (l_id, l) = b.fresh_local(c.labelling_fn.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), pi.clone(), l.clone()]);
            let e = b.mk_pi(l_id, BinderInfo::Default, c.labelling_fn.clone(), body);
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
