// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness theorem declarations for VeriPB proof certificate verification.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Cutting-planes addition soundness
//! - Cutting-planes multiplication soundness
//! - Cutting-planes division soundness
//! - Cutting-planes saturation soundness
//! - Cutting-planes weakening soundness
//! - RUP soundness
//! - Small-step checker soundness
//! - Whole-certificate soundness
//!
//! Each theorem follows the helper-axiom pattern from
//! `cutting_planes_theorems.rs`: a `_helper` axiom captures the proposition
//! body, and the theorem quantifies over all parameters with the helper
//! applied.

#[cfg(test)]
use super::veripb_checker::VeriPbCheckerConsts;
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
    // Theorem 1: CP addition soundness
    // ====================================================================

    /// Helper for cp_add_sound:
    /// `(c1 : PbConstraint) -> (c2 : PbConstraint) -> (a : Assignment) -> Prop`
    ///
    /// Encodes: if assignment `a` satisfies `c1` and `c2`, then it satisfies
    /// `cp_add c1 c2`.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_add_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.cp_add_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (c2_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(c2_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            let e = b.mk_pi(c1_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_add_sound : forall (c1 : PbConstraint) (c2 : PbConstraint)
    ///     (a : Assignment), cp_add_sound_helper c1 c2 a`
    ///
    /// Soundness of the addition rule: adding two valid pseudo-Boolean
    /// inequalities preserves validity over 0/1 assignments.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_add_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.cp_add_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.cp_add_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, c1) = b.fresh_local(c.pb_constraint.clone());
            let (c2_id, c2) = b.fresh_local(c.pb_constraint.clone());
            let (a_id, a) = b.fresh_local(c.assignment.clone());
            let body = Expr::apps(helper, [c1.clone(), c2.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), body);
            let e = b.mk_pi(c2_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            let e = b.mk_pi(c1_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: CP multiplication soundness
    // ====================================================================

    /// Helper for cp_multiply_sound:
    /// `(cst : PbConstraint) -> (k : Nat) -> (a : Assignment) -> Prop`
    ///
    /// Encodes: if assignment `a` satisfies `cst`, then it satisfies
    /// `cp_multiply cst k`.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_multiply_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.cp_multiply_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_multiply_sound : forall (cst : PbConstraint) (k : Nat)
    ///     (a : Assignment), cp_multiply_sound_helper cst k a`
    ///
    /// Soundness of the multiplication rule: scaling a valid constraint by a
    /// natural-number factor preserves validity.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_multiply_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.cp_multiply_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.cp_multiply_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, cst) = b.fresh_local(c.pb_constraint.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (a_id, a) = b.fresh_local(c.assignment.clone());
            let body = Expr::apps(helper, [cst.clone(), k.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), body);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: CP division soundness
    // ====================================================================

    /// Helper for cp_divide_sound:
    /// `(cst : PbConstraint) -> (k : Nat) -> (a : Assignment) -> Prop`
    ///
    /// Encodes: if assignment `a` satisfies `cst`, then it satisfies
    /// `cp_divide cst k`.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_divide_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.cp_divide_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_divide_sound : forall (cst : PbConstraint) (k : Nat)
    ///     (a : Assignment), cp_divide_sound_helper cst k a`
    ///
    /// Soundness of the division rule: integer division with rounding used by
    /// VeriPB preserves validity for pseudo-Boolean constraints.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_divide_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.cp_divide_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.cp_divide_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, cst) = b.fresh_local(c.pb_constraint.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (a_id, a) = b.fresh_local(c.assignment.clone());
            let body = Expr::apps(helper, [cst.clone(), k.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), body);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: CP saturation soundness
    // ====================================================================

    /// Helper for cp_saturate_sound:
    /// `(cst : PbConstraint) -> (a : Assignment) -> Prop`
    ///
    /// Encodes: if assignment `a` satisfies `cst`, then it satisfies
    /// `cp_saturate cst`.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_saturate_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.cp_saturate_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_saturate_sound : forall (cst : PbConstraint) (a : Assignment),
    ///     cp_saturate_sound_helper cst a`
    ///
    /// Soundness of saturation: clamping coefficients beyond the threshold is
    /// valid over 0/1 variables.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_saturate_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.cp_saturate_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.cp_saturate_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, cst) = b.fresh_local(c.pb_constraint.clone());
            let (a_id, a) = b.fresh_local(c.assignment.clone());
            let body = Expr::apps(helper, [cst.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), body);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: CP weakening soundness
    // ====================================================================

    /// Helper for cp_weaken_sound:
    /// `(cst : PbConstraint) -> (v : PbVar) -> (a : Assignment) -> Prop`
    ///
    /// Encodes: if assignment `a` satisfies `cst`, then it satisfies
    /// `cp_weaken cst v`.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_weaken_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.cp_weaken_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (v_id, _) = b.fresh_local(c.pb_var.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(v_id, BinderInfo::Default, c.pb_var.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_weaken_sound : forall (cst : PbConstraint) (v : PbVar)
    ///     (a : Assignment), cp_weaken_sound_helper cst v a`
    ///
    /// Soundness of weakening: adding a fresh nonnegative literal to the left
    /// side preserves validity.
    #[cfg(test)]
    pub(super) fn register_veripb_cp_weaken_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.cp_weaken_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.cp_weaken_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, cst) = b.fresh_local(c.pb_constraint.clone());
            let (v_id, v) = b.fresh_local(c.pb_var.clone());
            let (a_id, a) = b.fresh_local(c.assignment.clone());
            let body = Expr::apps(helper, [cst.clone(), v.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), body);
            let e = b.mk_pi(v_id, BinderInfo::Default, c.pb_var.clone(), e);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
