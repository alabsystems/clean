// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Group and AddGroup typeclass initialization
//!
//! Contains Group, AddGroup, and the Int AddGroup instance.
//! Commutative structures split to separate files (#307):
//! - algebra_comm_semigroup.rs: CommSemigroup, AddCommSemigroup
//! - algebra_comm_monoid.rs: CommMonoid, AddCommMonoid
//! - algebra_comm_group.rs: CommGroup, AddCommGroup
//! - algebra_group_instances.rs: Nat/Int instances for commutative structures

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Flavor struct for Group
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct GroupFlavor {
    class_name: &'static str,
    ctor_name: &'static str,
    op_field_name: &'static str,
    assoc_field_name: &'static str,
    identity_field_name: &'static str,
    identity_left_name: &'static str,
    identity_right_name: &'static str,
    inverse_field_name: &'static str,
    inverse_law_name: &'static str,
    op_projection_name: &'static str,
    identity_projection_name: &'static str,
    inverse_projection_name: &'static str,
}

const MUL_GROUP_FLAVOR: GroupFlavor = GroupFlavor {
    class_name: "Group",
    ctor_name: "Group.mk",
    op_field_name: "mul",
    assoc_field_name: "mul_assoc",
    identity_field_name: "one",
    identity_left_name: "one_mul",
    identity_right_name: "mul_one",
    inverse_field_name: "inv",
    inverse_law_name: "mul_left_inv",
    op_projection_name: "Group.mul",
    identity_projection_name: "Group.one",
    inverse_projection_name: "Group.inv",
};

#[cfg(test)]
const ADD_GROUP_FLAVOR: GroupFlavor = GroupFlavor {
    class_name: "AddGroup",
    ctor_name: "AddGroup.mk",
    op_field_name: "add",
    assoc_field_name: "add_assoc",
    identity_field_name: "zero",
    identity_left_name: "zero_add",
    identity_right_name: "add_zero",
    inverse_field_name: "neg",
    inverse_law_name: "add_left_neg",
    op_projection_name: "AddGroup.add",
    identity_projection_name: "AddGroup.zero",
    inverse_projection_name: "AddGroup.neg",
};

impl Environment {
    // -----------------------------------------------------------------------
    // Group / AddGroup
    // -----------------------------------------------------------------------

    /// Shared implementation for Group and AddGroup.
    ///
    /// Group extends Monoid with inverse and cancellation:
    /// ```text
    /// class Group (α : Type u) extends Monoid α where
    ///   inv : α → α
    ///   mul_left_inv : ∀ a : α, op (inv a) a = identity
    /// ```
    fn init_group_with_flavor(&mut self, flavor: GroupFlavor) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string(flavor.class_name);
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Build constructor type: 7 fields
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

            // inv : α → α
            let inv_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (inv_id, inv) = b.fresh_local(inv_type.clone());

            // inverse_law : ∀ a : α, op (inv a) a = identity
            let inv_law_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let inv_a = Expr::app(inv.clone(), a.clone());
                let lhs = Expr::app(Expr::app(op.clone(), inv_a), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    identity.clone(),
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (inv_law_id, _) = b.fresh_local(inv_law_type.clone());

            // Result: Class α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(inv_law_id, BinderInfo::Default, inv_law_type, result);
            let r = b.mk_pi(inv_id, BinderInfo::Default, inv_type.clone(), r);
            let r = b.mk_pi(id_right_id, BinderInfo::Default, id_right_type, r);
            let r = b.mk_pi(id_left_id, BinderInfo::Default, id_left_type, r);
            let r = b.mk_pi(identity_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(assoc_id, BinderInfo::Default, assoc_type, r);
            let r = b.mk_pi(op_id, BinderInfo::Default, op_type.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Inductive type
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
                Name::from_string(flavor.inverse_field_name),
                Name::from_string(flavor.inverse_law_name),
            ],
        )?;

        // op projection (field 0): {α : Type u} → [inst : Class α] → α → α → α
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

        // identity projection (field 2): {α : Type u} → [inst : Class α] → α
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
            level_params: vec![u.clone()],
            type_: id_proj_type,
            value: id_proj_value,
            is_reducible: true,
        })?;

        // inv projection (field 5): {α : Type u} → [inst : Class α] → α → α
        let inv_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let (x_id, _) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
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

        let inv_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 5, inst);
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
            name: Name::from_string(flavor.inverse_projection_name),
            level_params: vec![u],
            type_: inv_proj_type,
            value: inv_proj_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the Group typeclass
    pub fn init_group(&mut self) -> Result<(), EnvError> {
        if self.group_init {
            return Ok(());
        }
        self.init_monoid()?;
        self.init_eq()?;
        self.init_group_with_flavor(MUL_GROUP_FLAVOR)?;
        self.group_init = true;
        Ok(())
    }

    /// Check if Group typeclass has been initialized
    #[cfg(test)]
    pub(crate) fn has_group(&self) -> bool {
        self.group_init
    }

    /// Initialize the AddGroup typeclass
    #[cfg(test)]
    pub(crate) fn init_add_group(&mut self) -> Result<(), EnvError> {
        if self.add_group_init {
            return Ok(());
        }
        self.init_add_monoid()?;
        self.init_eq()?;
        self.init_group_with_flavor(ADD_GROUP_FLAVOR)?;
        self.add_group_init = true;
        Ok(())
    }

    /// Check if AddGroup typeclass has been initialized
    #[cfg(test)]
    pub(crate) fn has_add_group(&self) -> bool {
        self.add_group_init
    }

    // -----------------------------------------------------------------------
    // Int AddGroup instance
    // -----------------------------------------------------------------------

    /// Initialize the Int AddGroup instance
    ///
    /// Int forms an AddGroup with Int.add, Int.zero, Int.neg, Int.neg_add_self
    #[cfg(test)]
    pub(crate) fn init_int_add_group_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_group_inst_init {
            return Ok(());
        }

        self.init_add_group()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_zero_add = Expr::const_(Name::from_string("Int.zero_add"), vec![]);
        let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let int_neg_add_self = Expr::const_(Name::from_string("Int.neg_add_self"), vec![]);

        let add_group_mk = Expr::const_(Name::from_string("AddGroup.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddGroup"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(add_group_mk, int_const), int_add),
                                int_add_assoc,
                            ),
                            int_zero,
                        ),
                        int_zero_add,
                    ),
                    int_add_zero,
                ),
                int_neg,
            ),
            int_neg_add_self,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddGroupInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_group_inst_init = true;
        Ok(())
    }

    /// Check if Int AddGroup instance has been initialized
    #[cfg(test)]
    pub(crate) fn has_int_add_group_inst(&self) -> bool {
        self.int_add_group_inst_init
    }
}
