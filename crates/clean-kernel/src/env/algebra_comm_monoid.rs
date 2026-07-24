// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CommMonoid and AddCommMonoid typeclass initialization
//!
//! Split from algebra_groups.rs (#307). Contains:
//! - CommMonoidFlavor struct and mul/add flavor constants
//! - init_comm_monoid_with_flavor shared implementation
//! - init_comm_monoid, init_add_comm_monoid public wrappers

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

#[derive(Clone, Copy)]
struct CommMonoidFlavor {
    class_name: &'static str,
    ctor_name: &'static str,
    op_field_name: &'static str,
    assoc_field_name: &'static str,
    identity_field_name: &'static str,
    identity_left_name: &'static str,
    identity_right_name: &'static str,
    comm_field_name: &'static str,
    op_projection_name: &'static str,
    identity_projection_name: &'static str,
}

const MUL_COMM_MONOID_FLAVOR: CommMonoidFlavor = CommMonoidFlavor {
    class_name: "CommMonoid",
    ctor_name: "CommMonoid.mk",
    op_field_name: "mul",
    assoc_field_name: "mul_assoc",
    identity_field_name: "one",
    identity_left_name: "one_mul",
    identity_right_name: "mul_one",
    comm_field_name: "mul_comm",
    op_projection_name: "CommMonoid.mul",
    identity_projection_name: "CommMonoid.one",
};

const ADD_COMM_MONOID_FLAVOR: CommMonoidFlavor = CommMonoidFlavor {
    class_name: "AddCommMonoid",
    ctor_name: "AddCommMonoid.mk",
    op_field_name: "add",
    assoc_field_name: "add_assoc",
    identity_field_name: "zero",
    identity_left_name: "zero_add",
    identity_right_name: "add_zero",
    comm_field_name: "add_comm",
    op_projection_name: "AddCommMonoid.add",
    identity_projection_name: "AddCommMonoid.zero",
};

impl Environment {
    /// Shared implementation for CommMonoid and AddCommMonoid.
    ///
    /// CommMonoid extends Monoid with commutativity:
    /// ```text
    /// class CommMonoid (α : Type u) extends Monoid α where
    ///   op_comm : ∀ a b : α, op a b = op b a
    /// ```
    ///
    /// Field order: op, assoc, identity, identity_left, identity_right, comm
    /// (comm is last to maintain compatibility with instance constructors)
    fn init_comm_monoid_with_flavor(&mut self, flavor: CommMonoidFlavor) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string(flavor.class_name);
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Build constructor type: 6 fields
        // Field order: op, assoc, identity, identity_left, identity_right, comm
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

            // identity : α
            let (identity_id, identity) = b.fresh_local(alpha.clone());

            // identity_left : ∀ a : α, op identity a = a
            let id_left_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(op.clone(), identity.clone()), a.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (id_left_id, _) = b.fresh_local(id_left_type.clone());

            // identity_right : ∀ a : α, op a identity = a
            let id_right_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(op.clone(), a.clone()), identity.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (id_right_id, _) = b.fresh_local(id_right_type.clone());

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
            let r = b.mk_pi(id_right_id, BinderInfo::Default, id_right_type, r);
            let r = b.mk_pi(id_left_id, BinderInfo::Default, id_left_type, r);
            let r = b.mk_pi(identity_id, BinderInfo::Default, alpha.clone(), r);
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
                Name::from_string(flavor.identity_field_name),
                Name::from_string(flavor.identity_left_name),
                Name::from_string(flavor.identity_right_name),
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
            name: Name::from_string(flavor.op_projection_name),
            level_params: vec![u.clone()],
            type_: op_proj_type,
            value: op_proj_value,
            is_reducible: true,
        })?;

        // identity projection (field 2)
        let id_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let r = alpha.clone();
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let id_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 2, inst);
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
            name: Name::from_string(flavor.identity_projection_name),
            level_params: vec![u],
            type_: id_proj_type,
            value: id_proj_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the CommMonoid typeclass
    pub(crate) fn init_comm_monoid(&mut self) -> Result<(), EnvError> {
        if self.comm_monoid_init {
            return Ok(());
        }
        self.init_comm_semigroup()?;
        self.init_eq()?;
        self.init_comm_monoid_with_flavor(MUL_COMM_MONOID_FLAVOR)?;
        self.comm_monoid_init = true;
        Ok(())
    }

    /// Check if CommMonoid typeclass has been initialized
    pub(crate) fn has_comm_monoid(&self) -> bool {
        self.comm_monoid_init
    }

    /// Initialize the AddCommMonoid typeclass
    pub(crate) fn init_add_comm_monoid(&mut self) -> Result<(), EnvError> {
        if self.add_comm_monoid_init {
            return Ok(());
        }
        self.init_add_comm_semigroup()?;
        self.init_eq()?;
        self.init_comm_monoid_with_flavor(ADD_COMM_MONOID_FLAVOR)?;
        self.add_comm_monoid_init = true;
        Ok(())
    }

    /// Check if AddCommMonoid typeclass has been initialized
    pub(crate) fn has_add_comm_monoid(&self) -> bool {
        self.add_comm_monoid_init
    }
}
