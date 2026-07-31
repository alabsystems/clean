// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for VeriPB proof certificate verification.
//!
//! Registers the foundational types and checker operations needed to state:
//! - Pseudo-Boolean variables, constraints, and assignments
//! - Cutting-planes style constraint transformers used by VeriPB
//! - VeriPB proof steps (polynomial reasoning, weakening, RUP, deletion)
//! - A small-step certificate executor and whole-certificate verifier
//!
//! This module only registers the declaration surface. Operational semantics
//! for the checker are left abstract at the kernel boundary.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants used across all VeriPB checker declarations.
#[cfg(test)]
pub(super) struct VeriPbCheckerConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// VeriPB.PbConstraint : Type
    pub(super) pb_constraint: Expr,
    /// VeriPB.Assignment : Type
    pub(super) assignment: Expr,
    /// VeriPB.ConstraintDb : Type
    pub(super) constraint_db: Expr,
    /// VeriPB.PbVar : Type
    pub(super) pb_var: Expr,
    /// List VeriPB.VeriPbStep
    pub(super) list_step: Expr,
    /// Bool : Type
    pub(super) bool_ty: Expr,
    /// VeriPB.VeriPbStep : Type
    pub(super) veripb_step: Expr,
}

#[cfg(test)]
impl VeriPbCheckerConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        let pb_var = Expr::const_(Name::from_string("VeriPB.PbVar"), vec![]);
        let pb_constraint = Expr::const_(Name::from_string("VeriPB.PbConstraint"), vec![]);
        let assignment = Expr::const_(Name::from_string("VeriPB.Assignment"), vec![]);
        let constraint_db = Expr::const_(Name::from_string("VeriPB.ConstraintDb"), vec![]);
        let veripb_step = Expr::const_(Name::from_string("VeriPB.VeriPbStep"), vec![]);
        let list = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            pb_constraint,
            assignment,
            constraint_db,
            pb_var,
            list_step: Expr::app(list, veripb_step.clone()),
            bool_ty: Expr::const_(Name::from_string("Bool"), vec![]),
            veripb_step,
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize VeriPB checker declarations.
    ///
    /// Depends on: `init_nat()`, `init_bool()`, `init_list()`,
    /// `init_cutting_planes()`.
    #[cfg(test)]
    pub(crate) fn init_veripb_checker(&mut self) -> Result<(), EnvError> {
        if self.veripb_checker_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_bool()?;
        self.init_list()?;
        self.init_cutting_planes()?;

        let c = VeriPbCheckerConsts::new();
        self.register_veripb_pb_var(&c)?;
        self.register_veripb_pb_constraint(&c)?;
        self.register_veripb_assignment(&c)?;
        self.register_veripb_satisfies_constraint(&c)?;
        self.register_veripb_constraint_db(&c)?;
        self.register_veripb_cp_add(&c)?;
        self.register_veripb_cp_multiply(&c)?;
        self.register_veripb_cp_divide(&c)?;
        self.register_veripb_cp_saturate(&c)?;
        self.register_veripb_cp_weaken(&c)?;
        self.register_veripb_step(&c)?;
        self.register_veripb_step_pol_add(&c)?;
        self.register_veripb_step_pol_mul(&c)?;
        self.register_veripb_step_pol_div(&c)?;
        self.register_veripb_step_pol_sat(&c)?;
        self.register_veripb_step_weaken(&c)?;
        self.register_veripb_step_rup(&c)?;
        self.register_veripb_step_del(&c)?;
        self.register_veripb_step_conclude(&c)?;
        self.register_veripb_execute_step(&c)?;
        self.register_veripb_verify_certificate(&c)?;
        self.register_veripb_rup_check(&c)?;
        // Theorem registrations (in veripb_checker_theorems.rs)
        self.register_veripb_cp_add_sound_helper(&c)?;
        self.register_veripb_cp_add_sound(&c)?;
        self.register_veripb_cp_multiply_sound_helper(&c)?;
        self.register_veripb_cp_multiply_sound(&c)?;
        self.register_veripb_cp_divide_sound_helper(&c)?;
        self.register_veripb_cp_divide_sound(&c)?;
        self.register_veripb_cp_saturate_sound_helper(&c)?;
        self.register_veripb_cp_saturate_sound(&c)?;
        self.register_veripb_cp_weaken_sound_helper(&c)?;
        self.register_veripb_cp_weaken_sound(&c)?;
        self.register_veripb_rup_sound_helper(&c)?;
        self.register_veripb_rup_sound(&c)?;
        self.register_veripb_step_sound_helper(&c)?;
        self.register_veripb_step_sound(&c)?;
        self.register_veripb_verify_sound_helper(&c)?;
        self.register_veripb_verify_sound(&c)?;

        self.veripb_checker_init = true;
        Ok(())
    }

    /// `VeriPB.PbVar : Type` -- pseudo-Boolean variable.
    #[cfg(test)]
    fn register_veripb_pb_var(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("VeriPB.PbVar")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.PbVar"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `VeriPB.PbConstraint : Type` -- pseudo-Boolean constraint.
    #[cfg(test)]
    fn register_veripb_pb_constraint(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.PbConstraint"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.PbConstraint"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `VeriPB.Assignment : Type := VeriPB.PbVar -> Bool`.
    #[cfg(test)]
    fn register_veripb_assignment(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.Assignment"))
            .is_some()
        {
            return Ok(());
        }
        let value = Expr::pi(BinderInfo::Default, c.pb_var.clone(), c.bool_ty.clone());
        self.add_decl(Declaration::Definition {
            name: Name::from_string("VeriPB.Assignment"),
            level_params: vec![],
            type_: c.type0.clone(),
            value,
            is_reducible: true,
        })
    }

    /// `VeriPB.satisfies_constraint :
    ///    Assignment -> PbConstraint -> Prop`.
    #[cfg(test)]
    fn register_veripb_satisfies_constraint(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.satisfies_constraint"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let e = b.mk_pi(
                cst_id,
                BinderInfo::Default,
                c.pb_constraint.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.satisfies_constraint"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.ConstraintDb : Type := List VeriPB.PbConstraint`.
    #[cfg(test)]
    fn register_veripb_constraint_db(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.ConstraintDb"))
            .is_some()
        {
            return Ok(());
        }
        let list_pb_constraint = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            c.pb_constraint.clone(),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string("VeriPB.ConstraintDb"),
            level_params: vec![],
            type_: c.type0.clone(),
            value: list_pb_constraint,
            is_reducible: true,
        })
    }

    /// `VeriPB.cp_add : PbConstraint -> PbConstraint -> PbConstraint`.
    #[cfg(test)]
    fn register_veripb_cp_add(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.cp_add"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (c2_id, _) = b.fresh_local(c.pb_constraint.clone());
            let e = b.mk_pi(
                c2_id,
                BinderInfo::Default,
                c.pb_constraint.clone(),
                c.pb_constraint.clone(),
            );
            let e = b.mk_pi(c1_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.cp_add"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.cp_multiply : PbConstraint -> Nat -> PbConstraint`.
    #[cfg(test)]
    fn register_veripb_cp_multiply(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.cp_multiply"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                n_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.pb_constraint.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.cp_multiply"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.cp_divide : PbConstraint -> Nat -> PbConstraint`.
    #[cfg(test)]
    fn register_veripb_cp_divide(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.cp_divide"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                n_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.pb_constraint.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.cp_divide"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.cp_saturate : PbConstraint -> PbConstraint`.
    #[cfg(test)]
    fn register_veripb_cp_saturate(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.cp_saturate"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.pb_constraint.clone(),
            c.pb_constraint.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.cp_saturate"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.cp_weaken : PbConstraint -> PbVar -> PbConstraint`.
    #[cfg(test)]
    fn register_veripb_cp_weaken(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.cp_weaken"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let (v_id, _) = b.fresh_local(c.pb_var.clone());
            let e = b.mk_pi(
                v_id,
                BinderInfo::Default,
                c.pb_var.clone(),
                c.pb_constraint.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.cp_weaken"),
            level_params: vec![],
            type_: ty,
        })
    }
}
