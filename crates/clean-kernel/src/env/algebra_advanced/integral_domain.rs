// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IntegralDomain typeclass initialization for Environment
//!
//! IntegralDomain extends CommRing with no_zero_divisors (19 total fields).

use crate::env::algebra_ring_fields::RingBaseFields;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the IntegralDomain typeclass
    ///
    /// IntegralDomain is a CommRing with no zero divisors:
    /// - All CommRing fields (18 fields)
    /// - no_zero_divisors : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0
    ///
    /// Total: 19 fields
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.integral_domain_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_integral_domain(&mut self) -> Result<(), EnvError> {
        if self.integral_domain_init {
            return Ok(());
        }

        // Dependencies
        self.init_comm_ring()?;
        // Ensure Or type is available for the no_zero_divisors property
        // Or is defined in init_classical()
        self.init_classical()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("IntegralDomain");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // IntegralDomain has 19 fields: 17 Ring base + mul_comm + no_zero_divisors
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let ring = RingBaseFields::build(&mut b, &type_u, &eq_const);

            // Field 17: mul_comm
            let mul_comm_type = ring.build_mul_comm_type(&b, &eq_const);
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Field 18: no_zero_divisors : ∀ a b, mul a b = zero → Or (a = zero) (b = zero)
            let no_zero_divisors_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(ring.alpha.clone());
                let (bv_id, bv) = s.fresh_local(ring.alpha.clone());
                let mul_a_b = Expr::app(Expr::app(ring.mul.clone(), a.clone()), bv.clone());
                let premise = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), ring.alpha.clone()), mul_a_b),
                    ring.zero.clone(),
                );
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (_hyp_id, _) = s2.fresh_local(premise.clone());
                let eq_a_zero = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), ring.alpha.clone()), a.clone()),
                    ring.zero.clone(),
                );
                let eq_b_zero = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), ring.alpha.clone()), bv.clone()),
                    ring.zero.clone(),
                );
                let conclusion = Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_a_zero),
                    eq_b_zero,
                );
                let r = s2.mk_pi(_hyp_id, BinderInfo::Default, premise, conclusion);
                let r = s2.finish_child(r);
                let r = s.mk_pi(bv_id, BinderInfo::Default, ring.alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, ring.alpha.clone(), r);
                s.finish_child(r)
            };
            let (no_zero_divisors_id, _) = b.fresh_local(no_zero_divisors_type.clone());

            // Result: IntegralDomain α
            let result = Expr::app(class_const.clone(), ring.alpha.clone());
            let r = b.mk_pi(
                no_zero_divisors_id,
                BinderInfo::Default,
                no_zero_divisors_type,
                result,
            );
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, r);
            let r = ring.fold_pi(&b, &type_u, r);
            b.finish(r)
        };

        // Inductive type: IntegralDomain : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let integral_domain_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("IntegralDomain.mk"),
                    type_: ctor_type,
                }],
            }],
        };

        self.add_inductive(integral_domain_ind)?;

        // Register structure fields for Expr::proj support
        let mut field_names = RingBaseFields::field_names();
        field_names.push(Name::from_string("mul_comm")); // 17
        field_names.push(Name::from_string("no_zero_divisors")); // 18
        self.register_structure_fields(class_name.clone(), field_names)?;

        // IntegralDomain.add: {α : Type u} → [inst : IntegralDomain α] → α → α → α
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
            name: Name::from_string("IntegralDomain.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // IntegralDomain.zero: {α : Type u} → [inst : IntegralDomain α] → α
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
            name: Name::from_string("IntegralDomain.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // IntegralDomain.mul: {α : Type u} → [inst : IntegralDomain α] → α → α → α
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
            name: Name::from_string("IntegralDomain.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // IntegralDomain.one: {α : Type u} → [inst : IntegralDomain α] → α
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
            name: Name::from_string("IntegralDomain.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        // IntegralDomain.neg: {α : Type u} → [inst : IntegralDomain α] → α → α
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
            name: Name::from_string("IntegralDomain.neg"),
            level_params: vec![u.clone()],
            type_: neg_proj_type,
            value: neg_proj_value,
            is_reducible: true,
        })?;

        self.integral_domain_init = true;
        Ok(())
    }

    /// Check if IntegralDomain typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.integral_domain_init == true`
    pub fn has_integral_domain(&self) -> bool {
        self.integral_domain_init
    }
}
