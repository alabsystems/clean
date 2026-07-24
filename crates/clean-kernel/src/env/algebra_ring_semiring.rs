// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semiring and Ring typeclass initialization
//!
//! This module contains the core ring hierarchy typeclasses:
//! - Semiring (additive commutative monoid + multiplicative monoid + distributivity)
//! - Ring (Semiring + additive inverses)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Semiring typeclass
    ///
    /// Semiring combines AddCommMonoid with Monoid (for multiplication) plus distributivity laws.
    ///
    /// class Semiring (α : Type u) where
    ///   add : α → α → α
    ///   add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
    ///   zero : α
    ///   zero_add : ∀ a, add zero a = a
    ///   add_zero : ∀ a, add a zero = a
    ///   add_comm : ∀ a b, add a b = add b a
    ///   mul : α → α → α
    ///   mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
    ///   one : α
    ///   one_mul : ∀ a, mul one a = a
    ///   mul_one : ∀ a, mul a one = a
    ///   zero_mul : ∀ a, mul zero a = zero
    ///   mul_zero : ∀ a, mul a zero = zero
    ///   left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
    ///   right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.semiring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_semiring(&mut self) -> Result<(), EnvError> {
        if self.semiring_init {
            return Ok(());
        }

        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("Semiring");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Build constructor type using EnvDeclBuilder
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // add : α → α → α
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

            // add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
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

            let (zero_id, zero) = b.fresh_local(alpha.clone()); // zero : α

            // zero_add : ∀ a, add zero a = a
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

            // add_zero : ∀ a, add a zero = a
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

            // add_comm : ∀ a b, add a b = add b a
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

            // mul : α → α → α
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

            // mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
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

            let (one_id, one) = b.fresh_local(alpha.clone()); // one : α

            // one_mul : ∀ a, mul one a = a
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

            // mul_one : ∀ a, mul a one = a
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

            // zero_mul : ∀ a, mul zero a = zero
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

            // mul_zero : ∀ a, mul a zero = zero
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

            // left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
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

            // right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
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

            // Result: Semiring α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(
                right_distrib_id,
                BinderInfo::Default,
                right_distrib_type,
                result,
            );
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

        // Inductive type: Semiring : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let semiring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Semiring.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(semiring_ind)?;

        // Register structure fields
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
            ],
        )?;

        // Semiring.add: {α : Type u} → [inst : Semiring α] → α → α → α
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
            name: Name::from_string("Semiring.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // Semiring.zero: {α : Type u} → [inst : Semiring α] → α
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
            name: Name::from_string("Semiring.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // Semiring.mul: {α : Type u} → [inst : Semiring α] → α → α → α
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
            name: Name::from_string("Semiring.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // Semiring.one: {α : Type u} → [inst : Semiring α] → α
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
            name: Name::from_string("Semiring.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        self.semiring_init = true;
        Ok(())
    }

    /// Check if Semiring typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.semiring_init == true`
    pub(crate) fn has_semiring(&self) -> bool {
        self.semiring_init
    }

    /// Initialize the Ring typeclass
    ///
    /// Ring extends Semiring with additive inverses (negation).
    ///
    /// class Ring (α : Type u) extends Semiring α where
    ///   neg : α → α
    ///   add_left_neg : ∀ a : α, add (neg a) a = zero
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ring(&mut self) -> Result<(), EnvError> {
        if self.ring_init {
            return Ok(());
        }

        self.init_semiring()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("Ring");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Ring has 17 fields: 15 from Semiring + neg + add_left_neg
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

            // Field 2: add_assoc
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

            // Field 4: zero_add
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

            // Field 5: add_zero
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

            // Field 6: add_comm
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

            // Field 8: mul_assoc
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

            // Field 10: one_mul
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

            // Field 11: mul_one
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

            // Field 12: zero_mul
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

            // Field 13: mul_zero
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

            // Field 14: left_distrib
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

            // Field 15: right_distrib
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

            // Field 16: neg : α → α
            let neg_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (neg_id, neg) = b.fresh_local(neg_type.clone());

            // Field 17: add_left_neg : ∀ a, add (neg a) a = zero
            let add_left_neg_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let neg_a = Expr::app(neg.clone(), a.clone());
                let lhs = Expr::app(Expr::app(add.clone(), neg_a), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (add_left_neg_id, _) = b.fresh_local(add_left_neg_type.clone());

            // Result: Ring α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(
                add_left_neg_id,
                BinderInfo::Default,
                add_left_neg_type,
                result,
            );
            let r = b.mk_pi(neg_id, BinderInfo::Default, neg_type.clone(), r);
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

        // Inductive type: Ring : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let ring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Ring.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(ring_ind)?;

        // Register structure fields
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
                Name::from_string("neg"),
                Name::from_string("add_left_neg"),
            ],
        )?;

        // Ring.add projection
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
            name: Name::from_string("Ring.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // Ring.zero projection
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
            name: Name::from_string("Ring.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // Ring.mul projection
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
            name: Name::from_string("Ring.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // Ring.one projection
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
            name: Name::from_string("Ring.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        // Ring.neg projection: {α : Type u} → [inst : Ring α] → α → α
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
            name: Name::from_string("Ring.neg"),
            level_params: vec![u.clone()],
            type_: neg_proj_type,
            value: neg_proj_value,
            is_reducible: true,
        })?;

        // Register Ring as a typeclass
        self.register_class(KernelClassInfo {
            name: Name::from_string("Ring"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        self.ring_init = true;
        Ok(())
    }

    /// Check if Ring typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ring_init == true`
    pub fn has_ring(&self) -> bool {
        self.ring_init
    }
}
