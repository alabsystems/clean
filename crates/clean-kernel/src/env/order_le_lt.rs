// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LE, LT, GE, GT typeclasses for Environment
//!
//! This module contains the foundational comparison typeclasses:
//! - LE (less-than-or-equal) typeclass + Nat.le inductive + instLENat
//! - LT (less-than) typeclass + Nat.lt + instLTNat
//! - GE (greater-than-or-equal) definition + Nat.ge
//! - GT (greater-than) definition + Nat.gt

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the LE (less-than-or-equal) typeclass
    ///
    /// In Lean 4, LE is defined as:
    /// ```text
    /// class LE (α : Type u) where
    ///   le : α → α → Prop
    /// ```
    ///
    /// This adds:
    /// - LE : Type u → Type u (the typeclass)
    /// - LE.mk : {α : Type u} → (α → α → Prop) → LE α
    /// - LE.le : {α : Type u} → [inst : LE α] → α → α → Prop
    /// - Nat.le : Nat → Nat → Prop (inductive)
    /// - instLENat : LE Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.le_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_le(&mut self) -> Result<(), EnvError> {
        if self.le_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // LE : Type u → Type u
        let le_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(type_u.clone());
            let r = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let r = b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // LE.mk : {α : Type u} → (α → α → Prop) → LE α
        let le_const = Expr::const_(Name::from_string("LE"), vec![u_level.clone()]);
        let le_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone()); // α : Type u
            let rel_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let (y_id, _y) = c.fresh_local(alpha.clone());
                let r = prop.clone();
                let r = c.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (rel_id, _rel) = b.fresh_local(rel_ty.clone());
            let r = Expr::app(le_const.clone(), alpha.clone()); // LE α
            let r = b.mk_pi(rel_id, BinderInfo::Default, rel_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let le_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("LE"),
                type_: le_type,
                constructors: vec![Constructor {
                    name: Name::from_string("LE.mk"),
                    type_: le_mk_type,
                }],
            }],
        };

        self.add_inductive(le_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("LE"), vec![Name::from_string("le")])?;

        // Register LE as a type class
        self.register_class(KernelClassInfo {
            name: Name::from_string("LE"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // LE.le : {α : Type u} → [inst : LE α] → α → α → Prop
        let le_field_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(Expr::app(le_const.clone(), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(le_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // LE.le value = λ {α} [inst : LE α] (a b : α) =>
        //   (Expr::proj("LE", 0, inst)) a b
        let le_field_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(le_const.clone(), alpha.clone()));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b2_id, b2) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(Expr::proj(Name::from_string("LE"), 0, inst), a),
                b2,
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(le_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("LE.le"),
            level_params: vec![u.clone()],
            type_: le_field_type,
            value: le_field_value,
            is_reducible: true,
        })?;

        // Now add Nat.le as an inductive type
        // inductive Nat.le (n : Nat) : Nat → Prop where
        //   | refl : Nat.le n n
        //   | step {m} : Nat.le n m → Nat.le n (succ m)
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Type: Nat → Nat → Prop (n is param, m is index)
        let nat_le_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(), // n : Nat (parameter)
            Expr::pi(
                BinderInfo::Default,
                nat_const.clone(), // m : Nat (index)
                prop.clone(),
            ),
        );

        // Nat.le.refl : (n : Nat) → Nat.le n n
        let nat_le_c = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let r = Expr::app(Expr::app(nat_le_c.clone(), n.clone()), n);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        // Nat.le.step : {n m : Nat} → Nat.le n m → Nat.le n (Nat.succ m)
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_step_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let premise = Expr::app(Expr::app(nat_le_c.clone(), n.clone()), m.clone());
            let (h_id, _h) = b.fresh_local(premise.clone()); // h : Nat.le n m
            let conclusion = Expr::app(
                Expr::app(nat_le_c.clone(), n),
                Expr::app(nat_succ.clone(), m),
            );
            let r = b.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, nat_const.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), r);
            b.finish(r)
        };

        let nat_le_ind = InductiveDecl {
            level_params: vec![],
            num_params: 1, // n is the parameter
            types: vec![InductiveType {
                name: Name::from_string("Nat.le"),
                type_: nat_le_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Nat.le.refl"),
                        type_: nat_le_refl_type,
                    },
                    Constructor {
                        name: Name::from_string("Nat.le.step"),
                        type_: nat_le_step_type,
                    },
                ],
            }],
        };

        self.add_inductive(nat_le_ind)?;

        // instLENat : LE Nat := ⟨Nat.le⟩
        // Nat : Type 0, so LE.{0}
        let le_nat_type = Expr::app(
            Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
            nat_const.clone(),
        );
        let nat_le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let le_nat_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LE.mk"), vec![Level::zero()]),
                nat_const.clone(),
            ),
            nat_le_const,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLENat"),
            level_params: vec![],
            type_: le_nat_type,
            value: le_nat_value,
            is_reducible: true,
        })?;

        self.le_init = true;
        Ok(())
    }

    /// Check if LE typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.le_init == true`
    #[cfg(test)]
    pub(crate) fn has_le(&self) -> bool {
        self.le_init
    }

    /// Initialize the LT (less-than) typeclass
    ///
    /// In Lean 4, LT is defined as:
    /// ```text
    /// class LT (α : Type u) where
    ///   lt : α → α → Prop
    /// ```
    ///
    /// This adds:
    /// - LT : Type u → Type u (the typeclass)
    /// - LT.mk : {α : Type u} → (α → α → Prop) → LT α
    /// - LT.lt : {α : Type u} → [inst : LT α] → α → α → Prop
    /// - Nat.lt : Nat → Nat → Prop (defined as λ n m => Nat.le (Nat.succ n) m)
    /// - instLTNat : LT Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.lt_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_lt(&mut self) -> Result<(), EnvError> {
        if self.lt_init {
            return Ok(());
        }

        // Initialize dependencies (LE provides Nat.le)
        self.init_le()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // LT : Type u → Type u
        let lt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(type_u.clone());
            let r = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let r = b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // LT.mk : {α : Type u} → (α → α → Prop) → LT α
        let lt_const = Expr::const_(Name::from_string("LT"), vec![u_level.clone()]);
        let lt_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let rel_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let (y_id, _y) = c.fresh_local(alpha.clone());
                let r = prop.clone();
                let r = c.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (rel_id, _rel) = b.fresh_local(rel_ty.clone());
            let r = Expr::app(lt_const.clone(), alpha.clone());
            let r = b.mk_pi(rel_id, BinderInfo::Default, rel_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let lt_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("LT"),
                type_: lt_type,
                constructors: vec![Constructor {
                    name: Name::from_string("LT.mk"),
                    type_: lt_mk_type,
                }],
            }],
        };

        self.add_inductive(lt_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("LT"), vec![Name::from_string("lt")])?;

        // Register LT as a type class
        self.register_class(KernelClassInfo {
            name: Name::from_string("LT"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // LT.lt : {α : Type u} → [inst : LT α] → α → α → Prop
        let lt_field_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(Expr::app(lt_const.clone(), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(lt_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // LT.lt value = λ {α} [inst : LT α] (a b : α) =>
        //   (Expr::proj("LT", 0, inst)) a b
        let lt_field_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(lt_const.clone(), alpha.clone()));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b2_id, b2) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(Expr::proj(Name::from_string("LT"), 0, inst), a),
                b2,
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(lt_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("LT.lt"),
            level_params: vec![u.clone()],
            type_: lt_field_type,
            value: lt_field_value,
            is_reducible: true,
        })?;

        // Nat.lt : Nat → Nat → Prop := λ n m => Nat.le (Nat.succ n) m
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);

        let nat_lt_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
        );

        // Nat.lt n m := Nat.le (Nat.succ n) m
        let nat_lt_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let body = Expr::app(Expr::app(nat_le.clone(), Expr::app(nat_succ.clone(), n)), m);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.lt"),
            level_params: vec![],
            type_: nat_lt_type,
            value: nat_lt_value,
            is_reducible: true,
        })?;

        // instLTNat : LT Nat := ⟨Nat.lt⟩
        // Nat : Type 0, so LT.{0}
        let lt_nat_type = Expr::app(
            Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
            nat_const.clone(),
        );
        let nat_lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let lt_nat_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
                nat_const.clone(),
            ),
            nat_lt_const,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLTNat"),
            level_params: vec![],
            type_: lt_nat_type,
            value: lt_nat_value,
            is_reducible: true,
        })?;

        self.lt_init = true;
        Ok(())
    }

    /// Check if LT typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.lt_init == true`
    #[cfg(test)]
    pub(crate) fn has_lt(&self) -> bool {
        self.lt_init
    }

    /// Initialize GE (greater-than-or-equal) definitions
    ///
    /// In Lean 4, `a ≥ b` is defined as `LE.le b a`. This adds:
    /// - GE.ge : {α : Type u} → [inst : LE α] → α → α → Prop
    /// - Nat.ge : Nat → Nat → Prop (alias for Nat.le with arguments swapped)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ge_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ge(&mut self) -> Result<(), EnvError> {
        if self.ge_init {
            return Ok(());
        }

        // Ensure LE and Nat.le are available
        self.init_le()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // GE.ge : {α : Type u} → [LE α] → α → α → Prop
        let le_const = Expr::const_(Name::from_string("LE"), vec![u_level.clone()]);
        let ge_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(Expr::app(le_const.clone(), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(le_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // ge {α} [inst] a b := LE.le b a
        let ge_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(le_const.clone(), alpha.clone()));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b2_id, b2) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LE.le"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst,
                    ),
                    b2, // b (swapped: ge a b = le b a)
                ),
                a, // a
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(le_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("GE.ge"),
            level_params: vec![u.clone()],
            type_: ge_type,
            value: ge_value,
            is_reducible: true,
        })?;

        // Nat.ge : Nat → Nat → Prop := λ n m => Nat.le m n
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);

        let nat_ge_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let r = prop.clone();
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let nat_ge_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let body = Expr::app(Expr::app(nat_le.clone(), m), n); // Nat.le m n
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.ge"),
            level_params: vec![],
            type_: nat_ge_type,
            value: nat_ge_value,
            is_reducible: true,
        })?;

        self.ge_init = true;
        Ok(())
    }

    /// Check if GE definitions have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ge_init == true`
    #[cfg(test)]
    pub(crate) fn has_ge(&self) -> bool {
        self.ge_init
    }

    /// Initialize GT (greater-than) definitions
    ///
    /// In Lean 4, `a > b` is defined as `LT.lt b a`. This adds:
    /// - GT.gt : {α : Type u} → [inst : LT α] → α → α → Prop
    /// - Nat.gt : Nat → Nat → Prop (alias for Nat.lt with arguments swapped)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.gt_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_gt(&mut self) -> Result<(), EnvError> {
        if self.gt_init {
            return Ok(());
        }

        // Ensure LT (and its LE dependency) are available
        self.init_lt()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // GT.gt : {α : Type u} → [LT α] → α → α → Prop
        let lt_const = Expr::const_(Name::from_string("LT"), vec![u_level.clone()]);
        let gt_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(Expr::app(lt_const.clone(), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(lt_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // gt {α} [inst] a b := LT.lt b a
        let gt_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(lt_const.clone(), alpha.clone()));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b2_id, b2) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LT.lt"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst,
                    ),
                    b2, // b (swapped: gt a b = lt b a)
                ),
                a, // a
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(lt_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("GT.gt"),
            level_params: vec![u.clone()],
            type_: gt_type,
            value: gt_value,
            is_reducible: true,
        })?;

        // Nat.gt : Nat → Nat → Prop := λ n m => Nat.lt m n
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);

        let nat_gt_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let r = prop.clone();
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let nat_gt_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let body = Expr::app(Expr::app(nat_lt.clone(), m), n); // Nat.lt m n
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.gt"),
            level_params: vec![],
            type_: nat_gt_type,
            value: nat_gt_value,
            is_reducible: true,
        })?;

        self.gt_init = true;
        Ok(())
    }

    /// Check if GT definitions have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.gt_init == true`
    #[cfg(test)]
    pub(crate) fn has_gt(&self) -> bool {
        self.gt_init
    }
}
