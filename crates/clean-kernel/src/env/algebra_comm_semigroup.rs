// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CommSemigroup and AddCommSemigroup typeclass initialization
//!
//! Split from algebra_groups.rs (#307). Contains:
//! - CommSemigroupFlavor struct and mul/add flavor constants
//! - init_comm_semigroup_with_flavor shared implementation
//! - init_comm_semigroup, init_add_comm_semigroup public wrappers

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

#[derive(Clone, Copy)]
pub(crate) struct CommSemigroupFlavor {
    class_name: &'static str,
    ctor_name: &'static str,
    op_field_name: &'static str,
    assoc_field_name: &'static str,
    comm_field_name: &'static str,
    projection_name: &'static str,
}

const MUL_COMM_SEMIGROUP_FLAVOR: CommSemigroupFlavor = CommSemigroupFlavor {
    class_name: "CommSemigroup",
    ctor_name: "CommSemigroup.mk",
    op_field_name: "mul",
    assoc_field_name: "mul_assoc",
    comm_field_name: "mul_comm",
    projection_name: "CommSemigroup.mul",
};

const ADD_COMM_SEMIGROUP_FLAVOR: CommSemigroupFlavor = CommSemigroupFlavor {
    class_name: "AddCommSemigroup",
    ctor_name: "AddCommSemigroup.mk",
    op_field_name: "add",
    assoc_field_name: "add_assoc",
    comm_field_name: "add_comm",
    projection_name: "AddCommSemigroup.add",
};

impl Environment {
    /// Shared implementation for CommSemigroup and AddCommSemigroup.
    ///
    /// CommSemigroup extends Semigroup with commutativity:
    /// ```text
    /// class CommSemigroup (α : Type u) extends Semigroup α where
    ///   op_comm : ∀ a b : α, op a b = op b a
    /// ```
    fn init_comm_semigroup_with_flavor(
        &mut self,
        flavor: CommSemigroupFlavor,
    ) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string(flavor.class_name);
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Build constructor type: 3 fields (op, assoc, comm)
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // op : α → α → α
            let op_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (op_id, op) = b.fresh_local(op_type.clone());

            // assoc : ∀ a b c : α, op (op a b) c = op a (op b c)
            let assoc_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let op_a_b = Expr::app(Expr::app(op.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(op.clone(), op_a_b), c.clone());
                let op_b_c = Expr::app(Expr::app(op.clone(), bv), c);
                let rhs = Expr::app(Expr::app(op.clone(), a), op_b_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (assoc_id, _) = b.fresh_local(assoc_type.clone());

            // comm : ∀ a b : α, op a b = op b a
            let comm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(op.clone(), a.clone()), bv.clone());
                let rhs = Expr::app(Expr::app(op.clone(), bv), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (comm_id, _) = b.fresh_local(comm_type.clone());

            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(comm_id, BinderInfo::Default, comm_type, result);
            let r = b.mk_pi(assoc_id, BinderInfo::Default, assoc_type, r);
            let r = b.mk_pi(op_id, BinderInfo::Default, op_type.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string(flavor.ctor_name),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(ind)?;

        self.register_structure_fields(
            class_name.clone(),
            vec![
                Name::from_string(flavor.op_field_name),
                Name::from_string(flavor.assoc_field_name),
                Name::from_string(flavor.comm_field_name),
            ],
        )?;

        // op projection (field 0)
        let op_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let (x_id, _) = b.fresh_local(alpha.clone());
            let (y_id, _) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let op_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 0, inst);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string(flavor.projection_name),
            level_params: vec![u],
            type_: op_proj_type,
            value: op_proj_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the CommSemigroup typeclass
    pub(crate) fn init_comm_semigroup(&mut self) -> Result<(), EnvError> {
        if self.comm_semigroup_init {
            return Ok(());
        }
        self.init_semigroup()?;
        self.init_eq()?;
        self.init_comm_semigroup_with_flavor(MUL_COMM_SEMIGROUP_FLAVOR)?;
        self.comm_semigroup_init = true;
        Ok(())
    }

    /// Check if CommSemigroup typeclass has been initialized
    #[cfg(test)]
    pub(crate) fn has_comm_semigroup(&self) -> bool {
        self.comm_semigroup_init
    }

    /// Initialize the AddCommSemigroup typeclass
    pub(crate) fn init_add_comm_semigroup(&mut self) -> Result<(), EnvError> {
        if self.add_comm_semigroup_init {
            return Ok(());
        }
        self.init_add_semigroup()?;
        self.init_eq()?;
        self.init_comm_semigroup_with_flavor(ADD_COMM_SEMIGROUP_FLAVOR)?;
        self.add_comm_semigroup_init = true;
        Ok(())
    }

    /// Check if AddCommSemigroup typeclass has been initialized
    #[cfg(test)]
    pub(crate) fn has_add_comm_semigroup(&self) -> bool {
        self.add_comm_semigroup_init
    }
}
