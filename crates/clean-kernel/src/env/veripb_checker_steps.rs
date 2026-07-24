// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VeriPB proof step constructors and verifier function declarations.
//!
//! Registers the VeriPbStep inductive type constructors and the
//! execute_step / verify_certificate / rup_check verifier surface.

use super::veripb_checker::VeriPbCheckerConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `VeriPB.VeriPbStep : Type` -- a single VeriPB proof step.
    pub(super) fn register_veripb_step(&mut self, c: &VeriPbCheckerConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `VeriPB.VeriPbStep.PolAdd :
    ///    PbConstraint -> PbConstraint -> VeriPbStep`.
    pub(super) fn register_veripb_step_pol_add(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.PolAdd"))
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
                c.veripb_step.clone(),
            );
            let e = b.mk_pi(c1_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.PolAdd"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.PolMul :
    ///    PbConstraint -> Nat -> VeriPbStep`.
    pub(super) fn register_veripb_step_pol_mul(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.PolMul"))
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
                c.veripb_step.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.PolMul"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.PolDiv :
    ///    PbConstraint -> Nat -> VeriPbStep`.
    pub(super) fn register_veripb_step_pol_div(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.PolDiv"))
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
                c.veripb_step.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.PolDiv"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.PolSat : PbConstraint -> VeriPbStep`.
    pub(super) fn register_veripb_step_pol_sat(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.PolSat"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.pb_constraint.clone(),
            c.veripb_step.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.PolSat"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.Weaken :
    ///    PbConstraint -> PbVar -> VeriPbStep`.
    pub(super) fn register_veripb_step_weaken(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.Weaken"))
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
                c.veripb_step.clone(),
            );
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.Weaken"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.Rup : PbConstraint -> VeriPbStep`.
    pub(super) fn register_veripb_step_rup(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.Rup"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.pb_constraint.clone(),
            c.veripb_step.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.Rup"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.Del : Nat -> VeriPbStep`.
    pub(super) fn register_veripb_step_del(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.Del"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.veripb_step.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.Del"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.VeriPbStep.Conclude : VeriPbStep`.
    pub(super) fn register_veripb_step_conclude(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.VeriPbStep.Conclude"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.VeriPbStep.Conclude"),
            level_params: vec![],
            type_: c.veripb_step.clone(),
        })
    }

    /// `VeriPB.execute_step :
    ///    ConstraintDb -> VeriPbStep -> ConstraintDb`.
    pub(super) fn register_veripb_execute_step(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.execute_step"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, _) = b.fresh_local(c.constraint_db.clone());
            let (step_id, _) = b.fresh_local(c.veripb_step.clone());
            let e = b.mk_pi(
                step_id,
                BinderInfo::Default,
                c.veripb_step.clone(),
                c.constraint_db.clone(),
            );
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.execute_step"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.verify_certificate :
    ///    ConstraintDb -> List VeriPbStep -> Bool`.
    pub(super) fn register_veripb_verify_certificate(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.verify_certificate"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, _) = b.fresh_local(c.constraint_db.clone());
            let (steps_id, _) = b.fresh_local(c.list_step.clone());
            let e = b.mk_pi(
                steps_id,
                BinderInfo::Default,
                c.list_step.clone(),
                c.bool_ty.clone(),
            );
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.verify_certificate"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `VeriPB.rup_check : ConstraintDb -> PbConstraint -> Bool`.
    pub(super) fn register_veripb_rup_check(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("VeriPB.rup_check"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, _) = b.fresh_local(c.constraint_db.clone());
            let (cst_id, _) = b.fresh_local(c.pb_constraint.clone());
            let e = b.mk_pi(
                cst_id,
                BinderInfo::Default,
                c.pb_constraint.clone(),
                c.bool_ty.clone(),
            );
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("VeriPB.rup_check"),
            level_params: vec![],
            type_: ty,
        })
    }
}
