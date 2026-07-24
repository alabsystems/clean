// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Always-on algebraic data type init entrypoints extracted from mixed `data_types.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::init_shared::{type0_expr, InitLevelParam};
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Option inductive type.
    pub fn init_option(&mut self) -> Result<(), EnvError> {
        if self.option_init {
            return Ok(());
        }

        let u = InitLevelParam::new("u");
        let type_u = u.type_();
        let option_type = Expr::pi(BinderInfo::Implicit, type_u.clone(), type_u.clone());
        let option_const = Expr::const_(Name::from_string("Option"), vec![u.level.clone()]);

        let option_none_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let body = Expr::app(option_const.clone(), alpha);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(e)
        };

        let option_some_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(option_const.clone(), alpha.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let option_decl = InductiveDecl {
            level_params: vec![u.name.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Option"),
                type_: option_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Option.none"),
                        type_: option_none_type,
                    },
                    Constructor {
                        name: Name::from_string("Option.some"),
                        type_: option_some_type,
                    },
                ],
            }],
        };

        self.add_inductive(option_decl)?;
        self.option_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_option(&self) -> bool {
        self.option_init
    }

    /// Initialize Sum disjoint union type.
    pub fn init_sum(&mut self) -> Result<(), EnvError> {
        if self.sum_init {
            return Ok(());
        }

        let u = InitLevelParam::new("u");
        let v = InitLevelParam::new("v");
        let type_u = u.type_();
        let type_v = v.type_();
        let result_sort = Expr::sort(Level::max(
            Level::succ(u.level.clone()),
            Level::succ(v.level.clone()),
        ));

        let sum_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v.clone(), result_sort),
        );

        let sum_const = Expr::const_(
            Name::from_string("Sum"),
            vec![u.level.clone(), v.level.clone()],
        );

        let sum_inl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(Expr::app(sum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sum_inr_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (val_id, _val) = b.fresh_local(beta.clone());
            let body = Expr::app(Expr::app(sum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, beta.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sum_decl = InductiveDecl {
            level_params: vec![u.name.clone(), v.name.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Sum"),
                type_: sum_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Sum.inl"),
                        type_: sum_inl_type,
                    },
                    Constructor {
                        name: Name::from_string("Sum.inr"),
                        type_: sum_inr_type,
                    },
                ],
            }],
        };

        self.add_inductive(sum_decl)?;
        self.sum_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_sum(&self) -> bool {
        self.sum_init
    }

    /// Initialize Empty type (uninhabited type at Type level).
    pub fn init_empty(&mut self) -> Result<(), EnvError> {
        if self.empty_init {
            return Ok(());
        }

        let empty_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Empty"),
                type_: type0_expr(),
                constructors: vec![],
            }],
        };

        self.add_inductive(empty_decl)?;

        let u = InitLevelParam::new("u");
        let empty_const = Expr::const_(Name::from_string("Empty"), vec![]);

        let empty_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(u.sort());
            let (e_id, _e) = b.fresh_local(empty_const.clone());
            let e = b.mk_pi(e_id, BinderInfo::Default, empty_const.clone(), c.clone());
            let e = b.mk_pi(c_id, BinderInfo::Implicit, u.sort(), e);
            b.finish(e)
        };

        let empty_rec_const = Expr::const_(Name::from_string("Empty.rec"), vec![u.level.clone()]);
        let empty_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let sort_u = u.sort();
            let (c_id, c) = b.fresh_local(sort_u.clone());
            let (e_id, e_var) = b.fresh_local(empty_const.clone());
            let (dummy_id, _dummy) = b.fresh_local(empty_const.clone());
            let motive = b.mk_lam(
                dummy_id,
                BinderInfo::Default,
                empty_const.clone(),
                c.clone(),
            );
            let body = Expr::app(Expr::app(empty_rec_const.clone(), motive), e_var);
            let e = b.mk_lam(e_id, BinderInfo::Default, empty_const.clone(), body);
            let e = b.mk_lam(c_id, BinderInfo::Implicit, sort_u, e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Empty.elim"),
            level_params: vec![u.name.clone()],
            type_: empty_elim_type,
            value: empty_elim_value,
            is_reducible: true,
        })?;

        self.empty_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_empty(&self) -> bool {
        self.empty_init
    }

    /// Initialize PEmpty type (universe-polymorphic uninhabited type).
    pub fn init_pempty(&mut self) -> Result<(), EnvError> {
        if self.pempty_init {
            return Ok(());
        }

        let u = InitLevelParam::new("u");
        let pempty_decl = InductiveDecl {
            level_params: vec![u.name.clone()],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("PEmpty"),
                type_: u.sort(),
                constructors: vec![],
            }],
        };

        self.add_inductive(pempty_decl)?;

        let v = InitLevelParam::new("v");
        let pempty_const = Expr::const_(Name::from_string("PEmpty"), vec![u.level.clone()]);

        let pempty_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(v.sort());
            let (e_id, _e) = b.fresh_local(pempty_const.clone());
            let e = b.mk_pi(e_id, BinderInfo::Default, pempty_const.clone(), c.clone());
            let e = b.mk_pi(c_id, BinderInfo::Implicit, v.sort(), e);
            b.finish(e)
        };

        // FIDELITY (v4.30 matcher compilation): Lean's value delta-unfolds to
        // `fun {C} a => False.elim (PEmpty.rec (fun _ => False) a)` (stuck head
        // False.rec, not PEmpty.rec) — see the live copy in
        // `data_types.rs::init_pempty` for the full rationale.
        let pempty_rec_prop_const = Expr::const_(
            Name::from_string("PEmpty.rec"),
            vec![Level::zero(), u.level.clone()],
        );
        let false_elim_const = Expr::const_(Name::from_string("False.elim"), vec![v.level.clone()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let pempty_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let sort_v = v.sort();
            let (c_id, c) = b.fresh_local(sort_v.clone());
            let (e_id, e_var) = b.fresh_local(pempty_const.clone());
            let (dummy_id, _dummy) = b.fresh_local(pempty_const.clone());
            let motive = b.mk_lam(
                dummy_id,
                BinderInfo::Default,
                pempty_const.clone(),
                false_const.clone(),
            );
            let absurd = Expr::app(Expr::app(pempty_rec_prop_const.clone(), motive), e_var);
            let body = Expr::app(Expr::app(false_elim_const.clone(), c.clone()), absurd);
            let e = b.mk_lam(e_id, BinderInfo::Default, pempty_const.clone(), body);
            let e = b.mk_lam(c_id, BinderInfo::Implicit, sort_v, e);
            b.finish(e)
        };

        // FIDELITY: Lean's `PEmpty.elim.{u_1, u_2} : {C : Sort u_1} → PEmpty.{u_2}
        // → C` orders level params [C-univ, PEmpty-univ] (first-appearance). Here
        // `v` is C's universe and `u.name` is PEmpty's, so the list is `[v, u]`.
        // See the live copy in `data_types.rs::init_pempty` for the full rationale.
        self.add_decl(Declaration::Definition {
            name: Name::from_string("PEmpty.elim"),
            level_params: vec![v.name.clone(), u.name.clone()],
            type_: pempty_elim_type,
            value: pempty_elim_value,
            is_reducible: true,
        })?;

        self.pempty_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_pempty(&self) -> bool {
        self.pempty_init
    }
}
