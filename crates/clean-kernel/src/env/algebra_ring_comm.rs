// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CommSemiring and CommRing typeclass initialization
//!
//! This module contains the commutative ring hierarchy typeclasses:
//! - CommSemiring (Semiring + multiplicative commutativity)
//! - CommRing (Ring + multiplicative commutativity)

use crate::env::algebra_ring_fields::RingBaseFields;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the CommSemiring typeclass
    ///
    /// CommSemiring extends Semiring with multiplicative commutativity.
    ///
    /// class CommSemiring (α : Type u) extends Semiring α where
    ///   mul_comm : ∀ a b : α, mul a b = mul b a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.comm_semiring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_comm_semiring(&mut self) -> Result<(), EnvError> {
        if self.comm_semiring_init {
            return Ok(());
        }

        self.init_semiring()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("CommSemiring");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // CommSemiring has 16 fields: 15 from Semiring + mul_comm
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // Field 1: add : α → α → α
            let add_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (add_id, add) = b.fresh_local(add_type.clone());

            // Field 2: add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
            let add_assoc_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let add_a_b = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(add.clone(), add_a_b), c.clone());
                let add_b_c = Expr::app(Expr::app(add.clone(), bv), c);
                let rhs = Expr::app(Expr::app(add.clone(), a), add_b_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (add_assoc_id, _) = b.fresh_local(add_assoc_type.clone());

            // Field 3: zero : α
            let (zero_id, zero) = b.fresh_local(alpha.clone());

            // Field 4: zero_add : ∀ a, add zero a = a
            let zero_add_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(add.clone(), zero.clone()), a.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (zero_add_id, _) = b.fresh_local(zero_add_type.clone());

            // Field 5: add_zero : ∀ a, add a zero = a
            let add_zero_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(add.clone(), a.clone()), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (add_zero_id, _) = b.fresh_local(add_zero_type.clone());

            // Field 6: add_comm : ∀ a b, add a b = add b a
            let add_comm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
                let rhs = Expr::app(Expr::app(add.clone(), bv), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (add_comm_id, _) = b.fresh_local(add_comm_type.clone());

            // Field 7: mul : α → α → α
            let mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_id, mul) = b.fresh_local(mul_type.clone());

            // Field 8: mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
            let mul_assoc_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let mul_a_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), mul_a_b), c.clone());
                let mul_b_c = Expr::app(Expr::app(mul.clone(), bv), c);
                let rhs = Expr::app(Expr::app(mul.clone(), a), mul_b_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_assoc_id, _) = b.fresh_local(mul_assoc_type.clone());

            // Field 9: one : α
            let (one_id, one) = b.fresh_local(alpha.clone());

            // Field 10: one_mul : ∀ a, mul one a = a
            let one_mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), one.clone()), a.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (one_mul_id, _) = b.fresh_local(one_mul_type.clone());

            // Field 11: mul_one : ∀ a, mul a one = a
            let mul_one_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), one.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (mul_one_id, _) = b.fresh_local(mul_one_type.clone());

            // Field 12: zero_mul : ∀ a, mul zero a = zero
            let zero_mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), zero.clone()), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (zero_mul_id, _) = b.fresh_local(zero_mul_type.clone());

            // Field 13: mul_zero : ∀ a, mul a zero = zero
            let mul_zero_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (mul_zero_id, _) = b.fresh_local(mul_zero_type.clone());

            // Field 14: left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
            let left_distrib_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let add_b_c = Expr::app(Expr::app(add.clone(), bv.clone()), c.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), add_b_c);
                let mul_a_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv);
                let mul_a_c = Expr::app(Expr::app(mul.clone(), a), c);
                let rhs = Expr::app(Expr::app(add.clone(), mul_a_b), mul_a_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (left_distrib_id, _) = b.fresh_local(left_distrib_type.clone());

            // Field 15: right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
            let right_distrib_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let add_a_b = Expr::app(Expr::app(add.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), add_a_b), c.clone());
                let mul_a_c = Expr::app(Expr::app(mul.clone(), a), c.clone());
                let mul_b_c = Expr::app(Expr::app(mul.clone(), bv), c);
                let rhs = Expr::app(Expr::app(add.clone(), mul_a_c), mul_b_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (right_distrib_id, _) = b.fresh_local(right_distrib_type.clone());

            // Field 16: mul_comm : ∀ a b, mul a b = mul b a
            let mul_comm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), bv.clone());
                let rhs = Expr::app(Expr::app(mul.clone(), bv), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Result: CommSemiring α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, result);
            let r = b.mk_pi(right_distrib_id, BinderInfo::Default, right_distrib_type, r);
            let r = b.mk_pi(left_distrib_id, BinderInfo::Default, left_distrib_type, r);
            let r = b.mk_pi(mul_zero_id, BinderInfo::Default, mul_zero_type, r);
            let r = b.mk_pi(zero_mul_id, BinderInfo::Default, zero_mul_type, r);
            let r = b.mk_pi(mul_one_id, BinderInfo::Default, mul_one_type, r);
            let r = b.mk_pi(one_mul_id, BinderInfo::Default, one_mul_type, r);
            let r = b.mk_pi(one_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(mul_assoc_id, BinderInfo::Default, mul_assoc_type, r);
            let r = b.mk_pi(mul_id, BinderInfo::Default, mul_type.clone(), r);
            let r = b.mk_pi(add_comm_id, BinderInfo::Default, add_comm_type, r);
            let r = b.mk_pi(add_zero_id, BinderInfo::Default, add_zero_type, r);
            let r = b.mk_pi(zero_add_id, BinderInfo::Default, zero_add_type, r);
            let r = b.mk_pi(zero_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(add_assoc_id, BinderInfo::Default, add_assoc_type, r);
            let r = b.mk_pi(add_id, BinderInfo::Default, add_type.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Inductive type: CommSemiring : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let comm_semiring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("CommSemiring.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(comm_semiring_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            class_name.clone(),
            vec![
                Name::from_string("add"),
                Name::from_string("add_assoc"),
                Name::from_string("zero"),
                Name::from_string("zero_add"),
                Name::from_string("add_zero"),
                Name::from_string("add_comm"),
                Name::from_string("mul"),
                Name::from_string("mul_assoc"),
                Name::from_string("one"),
                Name::from_string("one_mul"),
                Name::from_string("mul_one"),
                Name::from_string("zero_mul"),
                Name::from_string("mul_zero"),
                Name::from_string("left_distrib"),
                Name::from_string("right_distrib"),
                Name::from_string("mul_comm"),
            ],
        )?;

        // CommSemiring.add: {α : Type u} → [inst : CommSemiring α] → α → α → α
        let add_proj_type = {
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
        let add_proj_value = {
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
            name: Name::from_string("CommSemiring.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // CommSemiring.zero: {α : Type u} → [inst : CommSemiring α] → α
        let zero_proj_type = {
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
        let zero_proj_value = {
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
            name: Name::from_string("CommSemiring.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // CommSemiring.mul: {α : Type u} → [inst : CommSemiring α] → α → α → α
        let mul_proj_type = {
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
        let mul_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 6, inst);
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
            name: Name::from_string("CommSemiring.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // CommSemiring.one: {α : Type u} → [inst : CommSemiring α] → α
        let one_proj_type = {
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
        let one_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 8, inst);
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
            name: Name::from_string("CommSemiring.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        self.comm_semiring_init = true;
        Ok(())
    }

    /// Check if CommSemiring typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.comm_semiring_init == true`
    #[cfg(test)]
    pub(crate) fn has_comm_semiring(&self) -> bool {
        self.comm_semiring_init
    }

    /// Initialize the CommRing typeclass
    ///
    /// CommRing extends Ring with multiplicative commutativity.
    ///
    /// class CommRing (α : Type u) extends Ring α where
    ///   mul_comm : ∀ a b : α, mul a b = mul b a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.comm_ring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_comm_ring(&mut self) -> Result<(), EnvError> {
        if self.comm_ring_init {
            return Ok(());
        }

        self.init_ring()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("CommRing");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // CommRing has 18 fields: 17 from Ring + mul_comm
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let ring = RingBaseFields::build(&mut b, &type_u, &eq_const);

            // Field 17: mul_comm : ∀ a b, mul a b = mul b a
            let mul_comm_type = ring.build_mul_comm_type(&b, &eq_const);
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Result: CommRing α
            let result = Expr::app(class_const.clone(), ring.alpha.clone());
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, result);
            let r = ring.fold_pi(&b, &type_u, r);
            b.finish(r)
        };

        // Inductive type: CommRing : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let comm_ring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("CommRing.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(comm_ring_ind)?;

        // Register structure fields for Expr::proj support
        let mut field_names = RingBaseFields::field_names();
        field_names.push(Name::from_string("mul_comm"));
        self.register_structure_fields(class_name.clone(), field_names)?;

        // CommRing.add: {α : Type u} → [inst : CommRing α] → α → α → α
        let add_proj_type = {
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
        let add_proj_value = {
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
            name: Name::from_string("CommRing.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // CommRing.zero: {α : Type u} → [inst : CommRing α] → α
        let zero_proj_type = {
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
        let zero_proj_value = {
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
            name: Name::from_string("CommRing.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // CommRing.mul: {α : Type u} → [inst : CommRing α] → α → α → α
        let mul_proj_type = {
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
        let mul_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 6, inst);
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
            name: Name::from_string("CommRing.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // CommRing.one: {α : Type u} → [inst : CommRing α] → α
        let one_proj_type = {
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
        let one_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 8, inst);
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
            name: Name::from_string("CommRing.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        // CommRing.neg: {α : Type u} → [inst : CommRing α] → α → α
        let neg_proj_type = {
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
        let neg_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 15, inst);
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
            name: Name::from_string("CommRing.neg"),
            level_params: vec![u.clone()],
            type_: neg_proj_type,
            value: neg_proj_value,
            is_reducible: true,
        })?;

        // Register CommRing as a typeclass
        self.register_class(KernelClassInfo {
            name: Name::from_string("CommRing"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // CommRing.toRing : {α : Type u} → [CommRing α] → Ring α
        let ring_const = |u: Level| Expr::const_(Name::from_string("Ring"), vec![u]);
        let ring_mk = Expr::const_(Name::from_string("Ring.mk"), vec![u_level.clone()]);

        // Type: {α : Type u} → [CommRing α] → Ring α
        let to_ring_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let r = Expr::app(ring_const(u_level.clone()), alpha.clone());
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Value: λ {α} [inst] => Ring.mk α (inst.0) (inst.1) ... (inst.16)
        let comm_ring_name = Name::from_string("CommRing");
        let to_ring_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));

            // Ring.mk {α} field0 field1 ... field16
            let mut ring_body = Expr::app(ring_mk, alpha.clone());
            for field_idx in 0..17u32 {
                let proj = Expr::proj(comm_ring_name.clone(), field_idx, inst.clone());
                ring_body = Expr::app(ring_body, proj);
            }

            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                ring_body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("CommRing.toRing"),
            level_params: vec![u.clone()],
            type_: to_ring_type,
            value: to_ring_value,
            is_reducible: true,
        })?;

        // Register CommRing.toRing as an instance for Ring
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("CommRing.toRing"),
            class_name: Name::from_string("Ring"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.comm_ring_init = true;
        Ok(())
    }

    /// Check if CommRing typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.comm_ring_init == true`
    pub fn has_comm_ring(&self) -> bool {
        self.comm_ring_init
    }
}
