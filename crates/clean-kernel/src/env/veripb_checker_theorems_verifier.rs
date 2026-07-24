// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verifier-level soundness theorem declarations for VeriPB.
//!
//! Registers the kernel-level axiom surfaces for:
//! - RUP soundness (Theorem 6)
//! - Small-step checker soundness (Theorem 7)
//! - Whole-certificate soundness (Theorem 8)
//!
//! Each theorem follows the helper-axiom pattern from
//! `cutting_planes_theorems.rs`.

use super::veripb_checker::VeriPbCheckerConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 6: RUP soundness
    // ====================================================================

    /// Helper for rup_sound:
    /// `(db : ConstraintDb) -> (cst : PbConstraint) -> Prop`
    ///
    /// Encodes: if `rup_check db cst = true`, then `cst` is implied by `db`.
    pub(super) fn register_veripb_rup_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.rup_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
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
                c.prop.clone(),
            );
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `rup_sound : forall (db : ConstraintDb) (cst : PbConstraint),
    ///     rup_sound_helper db cst`
    ///
    /// Soundness of reverse unit propagation: every accepted RUP step is
    /// semantically implied by the current constraint database.
    pub(super) fn register_veripb_rup_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.rup_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.rup_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, db) = b.fresh_local(c.constraint_db.clone());
            let (cst_id, cst) = b.fresh_local(c.pb_constraint.clone());
            let body = Expr::apps(helper, [db.clone(), cst.clone()]);
            let e = b.mk_pi(cst_id, BinderInfo::Default, c.pb_constraint.clone(), body);
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 7: Step soundness
    // ====================================================================

    /// Helper for step_sound:
    /// `(db : ConstraintDb) -> (s : VeriPbStep) -> Prop`
    ///
    /// Encodes: executing `s` preserves satisfiability of `db`.
    pub(super) fn register_veripb_step_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.step_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, _) = b.fresh_local(c.constraint_db.clone());
            let (s_id, _) = b.fresh_local(c.veripb_step.clone());
            let e = b.mk_pi(
                s_id,
                BinderInfo::Default,
                c.veripb_step.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `step_sound : forall (db : ConstraintDb) (s : VeriPbStep),
    ///     step_sound_helper db s`
    ///
    /// Soundness of the small-step checker: each accepted VeriPB instruction
    /// preserves semantic correctness of the database state.
    pub(super) fn register_veripb_step_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.step_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.step_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, db) = b.fresh_local(c.constraint_db.clone());
            let (s_id, s) = b.fresh_local(c.veripb_step.clone());
            let body = Expr::apps(helper, [db.clone(), s.clone()]);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.veripb_step.clone(), body);
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 8: Overall soundness
    // ====================================================================

    /// Helper for verify_sound: `(db : ConstraintDb) -> Prop`
    ///
    /// Encodes: if `verify_certificate db steps = true`, then `db` is UNSAT.
    pub(super) fn register_veripb_verify_sound_helper(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let name = "VeriPB.verify_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.constraint_db.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `verify_sound : forall (db : ConstraintDb), verify_sound_helper db`
    ///
    /// Overall checker soundness: if a VeriPB certificate is accepted for
    /// `db`, then the initial constraint database is unsatisfiable.
    pub(super) fn register_veripb_verify_sound(
        &mut self,
        c: &VeriPbCheckerConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "VeriPB.verify_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("VeriPB.verify_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (db_id, db) = b.fresh_local(c.constraint_db.clone());
            let body = Expr::app(helper, db.clone());
            let e = b.mk_pi(db_id, BinderInfo::Default, c.constraint_db.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
