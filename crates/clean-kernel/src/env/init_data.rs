// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Always-on core data init entrypoints extracted from mixed `data.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::init_shared::{prop_expr, type0_expr, InitLevelParam};
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Unit type.
    pub fn init_unit(&mut self) -> Result<(), EnvError> {
        if self.unit_init {
            return Ok(());
        }

        let unit_type = type0_expr();
        let unit_const = Expr::const_(Name::from_string("Unit"), vec![]);

        let unit_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Unit"),
                type_: unit_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Unit.unit"),
                    type_: unit_const,
                }],
            }],
        };

        self.add_inductive(unit_decl)?;
        self.unit_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_unit(&self) -> bool {
        self.unit_init
    }

    /// Initialize PUnit (universe-polymorphic unit type).
    pub fn init_punit(&mut self) -> Result<(), EnvError> {
        if self.punit_init {
            return Ok(());
        }

        let u = InitLevelParam::new("u");
        let punit_const = Expr::const_(Name::from_string("PUnit"), vec![u.level.clone()]);

        let punit_decl = InductiveDecl {
            level_params: vec![u.name.clone()],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("PUnit"),
                type_: u.type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("PUnit.unit"),
                    type_: punit_const,
                }],
            }],
        };

        self.add_inductive(punit_decl)?;
        self.punit_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_punit(&self) -> bool {
        self.punit_init
    }

    /// Initialize the Fin type (bounded natural numbers).
    pub fn init_fin(&mut self) -> Result<(), EnvError> {
        if self.fin_init {
            return Ok(());
        }

        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let fin_const = Expr::const_(Name::from_string("Fin"), vec![]);
        let type_ = type0_expr();
        let prop = prop_expr();

        let fin_type = Expr::pi(BinderInfo::Default, nat_const.clone(), type_.clone());

        let fin_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (val_id, _val) = b.fresh_local(nat_const.clone());
            let (islt_id, _islt) = b.fresh_local(prop.clone());
            let r = Expr::app(fin_const.clone(), n);
            let r = b.mk_pi(islt_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_pi(val_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        let fin_decl = InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Fin"),
                type_: fin_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Fin.mk"),
                    type_: fin_mk_type,
                }],
            }],
        };

        self.add_inductive(fin_decl)?;
        self.register_structure_fields(
            Name::from_string("Fin"),
            vec![Name::from_string("val"), Name::from_string("isLt")],
        )?;

        let fin_rec = Expr::const_(
            Name::from_string("Fin.rec"),
            vec![Level::succ(Level::zero())],
        );
        let fin_val_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let fin_n = Expr::app(fin_const.clone(), n.clone());
            let (x_id, _x) = b.fresh_local(fin_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, fin_n, nat_const.clone());
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        let fin_val_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let fin_n = Expr::app(fin_const.clone(), n.clone());
            let (x_id, x) = b.fresh_local(fin_n.clone());

            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(fin_n.clone());
                let r = c.mk_lam(w_id, BinderInfo::Default, fin_n.clone(), nat_const.clone());
                c.finish_child(r)
            };

            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (val_id, val) = c.fresh_local(nat_const.clone());
                let (proof_id, _proof) = c.fresh_local(prop.clone());
                let r = c.mk_lam(proof_id, BinderInfo::Default, prop.clone(), val);
                let r = c.mk_lam(val_id, BinderInfo::Default, nat_const.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(fin_rec.clone(), n.clone()), motive),
                    mk_case,
                ),
                x,
            );
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n, body);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.val"),
            level_params: vec![],
            type_: fin_val_type,
            value: fin_val_value,
            is_reducible: true,
        })?;

        self.fin_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_fin(&self) -> bool {
        self.fin_init
    }

    /// Initialize the Array type.
    pub(crate) fn init_array(&mut self) -> Result<(), EnvError> {
        if self.array_init {
            return Ok(());
        }

        self.init_list()?;

        let u = InitLevelParam::new("u");
        let type_u = u.type_();
        let array_const = Expr::const_(Name::from_string("Array"), vec![u.level.clone()]);
        let list_const = Expr::const_(Name::from_string("List"), vec![u.level.clone()]);

        let array_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

        let array_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (d_id, _d) = b.fresh_local(list_alpha.clone());
            let r = Expr::app(array_const.clone(), alpha.clone());
            let r = b.mk_pi(d_id, BinderInfo::Default, list_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let array_decl = InductiveDecl {
            level_params: vec![u.name.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Array"),
                type_: array_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Array.mk"),
                    type_: array_mk_type,
                }],
            }],
        };

        self.add_inductive(array_decl)?;
        self.register_structure_fields(
            Name::from_string("Array"),
            vec![Name::from_string("data")],
        )?;

        let array_rec = Expr::const_(
            Name::from_string("Array.rec"),
            vec![Level::succ(u.level.clone()), u.level.clone()],
        );

        let array_data_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let array_alpha = Expr::app(array_const.clone(), alpha.clone());
            let (arr_id, _arr) = b.fresh_local(array_alpha.clone());
            let r = b.mk_pi(
                arr_id,
                BinderInfo::Default,
                array_alpha,
                Expr::app(list_const.clone(), alpha.clone()),
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let array_data_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let array_alpha = Expr::app(array_const.clone(), alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (arr_id, arr) = b.fresh_local(array_alpha.clone());

            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(array_alpha.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    array_alpha.clone(),
                    list_alpha.clone(),
                );
                c.finish_child(r)
            };

            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (d_id, d) = c.fresh_local(list_alpha.clone());
                let r = c.mk_lam(d_id, BinderInfo::Default, list_alpha.clone(), d);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(array_rec.clone(), alpha.clone()), motive),
                    mk_case,
                ),
                arr,
            );
            let r = b.mk_lam(arr_id, BinderInfo::Default, array_alpha, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Array.data"),
            level_params: vec![u.name.clone()],
            type_: array_data_type,
            value: array_data_value,
            is_reducible: true,
        })?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_length = Expr::const_(Name::from_string("List.length"), vec![u.level.clone()]);
        let array_data_const = Expr::const_(Name::from_string("Array.data"), vec![u.level.clone()]);

        let array_size_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let array_alpha = Expr::app(array_const.clone(), alpha.clone());
            let (arr_id, _arr) = b.fresh_local(array_alpha.clone());
            let r = b.mk_pi(arr_id, BinderInfo::Default, array_alpha, nat_const.clone());
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let array_size_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let array_alpha = Expr::app(array_const.clone(), alpha.clone());
            let (arr_id, arr) = b.fresh_local(array_alpha.clone());
            let body = Expr::app(
                Expr::app(list_length.clone(), alpha.clone()),
                Expr::app(array_data_const.clone(), arr),
            );
            let r = b.mk_lam(arr_id, BinderInfo::Default, array_alpha, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Array.size"),
            level_params: vec![u.name.clone()],
            type_: array_size_type,
            value: array_size_value,
            is_reducible: true,
        })?;

        self.array_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_array(&self) -> bool {
        self.array_init
    }
}
