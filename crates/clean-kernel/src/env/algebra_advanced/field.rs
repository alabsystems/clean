// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Division ring and field structures for Environment
//!
//! Contains initialization for DivisionRing and Field typeclasses plus the
//! associated predicates.

use crate::env::algebra_ring_fields::RingBaseFields;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the DivisionRing typeclass
    ///
    /// DivisionRing extends Ring with multiplicative inverse.
    ///
    /// class DivisionRing (α : Type u) extends Ring α where
    ///   inv : α → α
    ///   mul_inv_cancel : ∀ a : α, a ≠ 0 → a * inv a = 1
    ///   inv_zero : inv 0 = 0  (by convention)
    ///
    /// DivisionRing has 20 fields: 17 from Ring + inv + mul_inv_cancel + inv_zero
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.division_ring_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_division_ring(&mut self) -> Result<(), EnvError> {
        if self.division_ring_init {
            return Ok(());
        }

        self.init_ring()?;
        self.init_true_false()?; // for Ne

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u

        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("DivisionRing");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // DivisionRing has 20 fields: 17 from Ring + inv + mul_inv_cancel + inv_zero
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let ring = RingBaseFields::build(&mut b, &type_u, &eq_const);

            // Alias ring fields for DivisionRing-specific fields below
            let alpha = ring.alpha.clone();
            let zero = ring.zero.clone();
            let one = ring.one.clone();
            let mul = ring.mul.clone();

            // Field 17: inv : α → α
            let inv_type = ring.neg_type.clone(); // same shape: α → α
            let (inv_id, inv) = b.fresh_local(inv_type.clone());

            // Field 18: mul_inv_cancel : ∀ a, Ne a zero → mul a (inv a) = one
            let mul_inv_cancel_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let ne_a_zero = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Ne"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        a.clone(),
                    ),
                    zero.clone(),
                );
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (hyp_id, _) = s2.fresh_local(ne_a_zero.clone());
                let inv_a = Expr::app(inv.clone(), a.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a), inv_a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    one.clone(),
                );
                let r = s2.mk_pi(hyp_id, BinderInfo::Default, ne_a_zero, eq);
                let r = s2.finish_child(r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_inv_cancel_id, _) = b.fresh_local(mul_inv_cancel_type.clone());

            // Field 19: inv_zero : inv zero = zero
            let inv_zero_type = {
                let s = EnvDeclBuilder::child_of(&b);
                let lhs = Expr::app(inv.clone(), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(eq)
            };
            let (inv_zero_id, _) = b.fresh_local(inv_zero_type.clone());

            // Result: DivisionRing α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(inv_zero_id, BinderInfo::Default, inv_zero_type, result);
            let r = b.mk_pi(
                mul_inv_cancel_id,
                BinderInfo::Default,
                mul_inv_cancel_type,
                r,
            );
            let r = b.mk_pi(inv_id, BinderInfo::Default, inv_type.clone(), r);
            let r = ring.fold_pi(&b, &type_u, r);
            b.finish(r)
        };

        // Inductive type: DivisionRing : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let division_ring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("DivisionRing.mk"),
                    type_: ctor_type,
                }],
            }],
        };

        self.add_inductive(division_ring_ind)?;

        // Register structure fields for Expr::proj support
        let mut field_names = RingBaseFields::field_names();
        field_names.push(Name::from_string("inv")); // 17
        field_names.push(Name::from_string("mul_inv_cancel")); // 18
        field_names.push(Name::from_string("inv_zero")); // 19
        self.register_structure_fields(class_name.clone(), field_names)?;

        // DivisionRing.add: {α : Type u} → [inst : DivisionRing α] → α → α → α
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
            name: Name::from_string("DivisionRing.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // DivisionRing.zero: {α : Type u} → [inst : DivisionRing α] → α
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
            name: Name::from_string("DivisionRing.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // DivisionRing.mul: {α : Type u} → [inst : DivisionRing α] → α → α → α
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
            name: Name::from_string("DivisionRing.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // DivisionRing.one: {α : Type u} → [inst : DivisionRing α] → α
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
            name: Name::from_string("DivisionRing.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        // DivisionRing.neg: {α : Type u} → [inst : DivisionRing α] → α → α
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
            name: Name::from_string("DivisionRing.neg"),
            level_params: vec![u.clone()],
            type_: neg_proj_type,
            value: neg_proj_value,
            is_reducible: true,
        })?;

        // DivisionRing.inv: {α : Type u} → [inst : DivisionRing α] → α → α
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
            let body = Expr::proj(class_name.clone(), 17, inst);
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
            name: Name::from_string("DivisionRing.inv"),
            level_params: vec![u.clone()],
            type_: inv_proj_type,
            value: inv_proj_value,
            is_reducible: true,
        })?;

        self.division_ring_init = true;
        Ok(())
    }

    /// Check if DivisionRing typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.division_ring_init == true`
    pub(crate) fn has_division_ring(&self) -> bool {
        self.division_ring_init
    }

    /// Initialize the Field typeclass
    ///
    /// Field extends DivisionRing with multiplicative commutativity.
    ///
    /// class Field (α : Type u) extends DivisionRing α where
    ///   mul_comm : ∀ a b : α, mul a b = mul b a
    ///
    /// Field has 21 fields: 20 from DivisionRing + mul_comm
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.field_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_field(&mut self) -> Result<(), EnvError> {
        if self.field_init {
            return Ok(());
        }

        self.init_division_ring()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u

        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("Field");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);

        // Field has 21 fields: 17 Ring base + inv + mul_inv_cancel + inv_zero + mul_comm
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let ring = RingBaseFields::build(&mut b, &type_u, &eq_const);

            // Alias ring fields for Field-specific fields below
            let alpha = ring.alpha.clone();
            let zero = ring.zero.clone();
            let one = ring.one.clone();
            let mul = ring.mul.clone();

            // Field 17: inv : α → α
            let inv_type = ring.neg_type.clone(); // same shape: α → α
            let (inv_id, inv) = b.fresh_local(inv_type.clone());

            // Field 18: mul_inv_cancel : ∀ a, Ne a zero → mul a (inv a) = one
            let mul_inv_cancel_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let ne_a_zero = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Ne"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        a.clone(),
                    ),
                    zero.clone(),
                );
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (hyp_id, _) = s2.fresh_local(ne_a_zero.clone());
                let inv_a = Expr::app(inv.clone(), a.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a), inv_a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    one.clone(),
                );
                let r = s2.mk_pi(hyp_id, BinderInfo::Default, ne_a_zero, eq);
                let r = s2.finish_child(r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_inv_cancel_id, _) = b.fresh_local(mul_inv_cancel_type.clone());

            // Field 19: inv_zero : inv zero = zero
            let inv_zero_type = {
                let s = EnvDeclBuilder::child_of(&b);
                let lhs = Expr::app(inv.clone(), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(eq)
            };
            let (inv_zero_id, _) = b.fresh_local(inv_zero_type.clone());

            // Field 20: mul_comm : ∀ a b, mul a b = mul b a
            let mul_comm_type = ring.build_mul_comm_type(&b, &eq_const);
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Result: Field α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, result);
            let r = b.mk_pi(inv_zero_id, BinderInfo::Default, inv_zero_type, r);
            let r = b.mk_pi(
                mul_inv_cancel_id,
                BinderInfo::Default,
                mul_inv_cancel_type,
                r,
            );
            let r = b.mk_pi(inv_id, BinderInfo::Default, inv_type.clone(), r);
            let r = ring.fold_pi(&b, &type_u, r);
            b.finish(r)
        };

        // Inductive type: Field : Type u → Type u
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let field_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Field.mk"),
                    type_: ctor_type,
                }],
            }],
        };

        self.add_inductive(field_ind)?;

        // Register structure fields for Expr::proj support
        let mut field_names = RingBaseFields::field_names();
        field_names.push(Name::from_string("inv")); // 17
        field_names.push(Name::from_string("mul_inv_cancel")); // 18
        field_names.push(Name::from_string("inv_zero")); // 19
        field_names.push(Name::from_string("mul_comm")); // 20
        self.register_structure_fields(class_name.clone(), field_names)?;

        // Field.add: {α : Type u} → [inst : Field α] → α → α → α
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
            name: Name::from_string("Field.add"),
            level_params: vec![u.clone()],
            type_: add_proj_type,
            value: add_proj_value,
            is_reducible: true,
        })?;

        // Field.zero: {α : Type u} → [inst : Field α] → α
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
            name: Name::from_string("Field.zero"),
            level_params: vec![u.clone()],
            type_: zero_proj_type,
            value: zero_proj_value,
            is_reducible: true,
        })?;

        // Field.mul: {α : Type u} → [inst : Field α] → α → α → α
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
            name: Name::from_string("Field.mul"),
            level_params: vec![u.clone()],
            type_: mul_proj_type,
            value: mul_proj_value,
            is_reducible: true,
        })?;

        // Field.one: {α : Type u} → [inst : Field α] → α
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
            name: Name::from_string("Field.one"),
            level_params: vec![u.clone()],
            type_: one_proj_type,
            value: one_proj_value,
            is_reducible: true,
        })?;

        // Field.neg: {α : Type u} → [inst : Field α] → α → α
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
            name: Name::from_string("Field.neg"),
            level_params: vec![u.clone()],
            type_: neg_proj_type,
            value: neg_proj_value,
            is_reducible: true,
        })?;

        // Field.inv: {α : Type u} → [inst : Field α] → α → α
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
            let body = Expr::proj(class_name.clone(), 17, inst);
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
            name: Name::from_string("Field.inv"),
            level_params: vec![u.clone()],
            type_: inv_proj_type,
            value: inv_proj_value,
            is_reducible: true,
        })?;

        self.field_init = true;
        Ok(())
    }

    /// Check if Field typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.field_init == true`
    pub fn has_field(&self) -> bool {
        self.field_init
    }
}
