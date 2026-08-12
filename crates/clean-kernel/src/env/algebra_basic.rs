// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic algebraic typeclasses for Environment
//!
//! This module contains typeclass definitions:
//! - Zero, One, Add, Mul, Neg, Sub typeclasses
//!
//! Nat/Int instances are in algebra_basic_instances.rs.
//! OfNat typeclass and instances are in algebra_basic_ofnat.rs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ========================================================================
    // Algebraic Typeclasses: Zero, One, Add, Mul, Neg, Sub
    // ========================================================================

    /// Initialize the Zero typeclass
    ///
    /// Zero is a typeclass with a single field `zero`:
    /// ```text
    /// class Zero (α : Type u) where
    ///   zero : α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.zero_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_zero(&mut self) -> Result<(), EnvError> {
        if self.zero_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        // Zero : Type u → Type u
        // Represented as a structure with one field
        let zero_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Zero.mk : {α : Type u} → α → Zero α
        let zero_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("Zero"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let zero_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Zero"),
                type_: zero_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Zero.mk"),
                    type_: zero_mk_type,
                }],
            }],
        };

        self.add_inductive(zero_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("Zero"), vec![Name::from_string("zero")])?;

        // Add Zero.zero : {α : Type u} → [inst : Zero α] → α
        let zero_const = |u: Level| Expr::const_(Name::from_string("Zero"), vec![u]);

        let zero_zero_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(zero_const(u_level.clone()), alpha.clone()));
            let e = alpha.clone();
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(zero_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Zero.zero value = λ {α} [inst : Zero α] => Expr.proj("Zero", 0, inst)
        let zero_zero_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(zero_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("Zero"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(zero_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Zero.zero"),
            level_params: vec![u],
            type_: zero_zero_type,
            value: zero_zero_value,
            is_reducible: true,
        })?;

        self.zero_init = true;
        Ok(())
    }

    /// Check if Zero typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.zero_init == true`
    #[cfg(test)]
    pub(crate) fn has_zero(&self) -> bool {
        self.zero_init
    }

    /// Initialize the One typeclass
    ///
    /// One is a typeclass with a single field `one`:
    /// ```text
    /// class One (α : Type u) where
    ///   one : α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.one_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_one(&mut self) -> Result<(), EnvError> {
        if self.one_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        // One : Type u → Type u
        let one_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // One.mk : {α : Type u} → α → One α
        let one_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("One"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let one_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("One"),
                type_: one_type,
                constructors: vec![Constructor {
                    name: Name::from_string("One.mk"),
                    type_: one_mk_type,
                }],
            }],
        };

        self.add_inductive(one_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("One"), vec![Name::from_string("one")])?;

        // Add One.one : {α : Type u} → [inst : One α] → α
        let one_const = |u: Level| Expr::const_(Name::from_string("One"), vec![u]);

        let one_one_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(one_const(u_level.clone()), alpha.clone()));
            let e = alpha.clone();
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(one_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // One.one value = λ {α} [inst : One α] => Expr.proj("One", 0, inst)
        let one_one_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(one_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("One"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(one_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("One.one"),
            level_params: vec![u],
            type_: one_one_type,
            value: one_one_value,
            is_reducible: true,
        })?;

        self.one_init = true;
        Ok(())
    }

    /// Check if One typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_one` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_one(&self) -> bool {
        self.one_init
    }

    /// Initialize the Add typeclass
    ///
    /// Add is a typeclass with a single field `add`:
    /// ```text
    /// class Add (α : Type u) where
    ///   add : α → α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.add_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_add(&mut self) -> Result<(), EnvError> {
        if self.add_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        // Add : Type u → Type u
        // The constructor takes an (α → α → α) function
        let add_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Default, type_u.clone(), e);
            b.finish(e)
        };

        // Add.mk : {α : Type u} → (α → α → α) → Add α
        let add_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // The field type: α → α → α
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let field_body = alpha.clone();
            let field_type = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), field_body);
            let field_type = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), field_type);
            let (field_id, _field) = b.fresh_local(field_type.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("Add"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(field_id, BinderInfo::Default, field_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let add_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Add"),
                type_: add_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Add.mk"),
                    type_: add_mk_type,
                }],
            }],
        };

        self.add_inductive(add_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("Add"), vec![Name::from_string("add")])?;

        // Add Add.add : {α : Type u} → [inst : Add α] → α → α → α
        let add_const = |u: Level| Expr::const_(Name::from_string("Add"), vec![u]);

        // Type: {α : Type u} → [Add α] → α → α → α
        let add_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(add_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b_id, _b) = b.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(add_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Add.add value = λ {α} [inst : Add α] => Expr.proj("Add", 0, inst)
        let add_add_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(add_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("Add"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(add_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Add.add"),
            level_params: vec![u],
            type_: add_add_type,
            value: add_add_value,
            is_reducible: true,
        })?;

        self.add_init = true;
        Ok(())
    }

    /// Check if Add typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_add` has completed successfully
    /// ENSURES: Pure - no side effects
    pub fn has_add(&self) -> bool {
        self.add_init
    }

    /// Initialize the Mul typeclass
    ///
    /// Mul is a typeclass with a single field `mul`:
    /// ```text
    /// class Mul (α : Type u) where
    ///   mul : α → α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.mul_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_mul(&mut self) -> Result<(), EnvError> {
        if self.mul_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        let mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Default, type_u.clone(), e);
            b.finish(e)
        };

        // Mul.mk : {α : Type u} → (α → α → α) → Mul α
        let mul_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // The field type: α → α → α
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let field_body = alpha.clone();
            let field_type = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), field_body);
            let field_type = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), field_type);
            let (field_id, _field) = b.fresh_local(field_type.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("Mul"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(field_id, BinderInfo::Default, field_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let mul_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Mul"),
                type_: mul_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Mul.mk"),
                    type_: mul_mk_type,
                }],
            }],
        };

        self.add_inductive(mul_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("Mul"), vec![Name::from_string("mul")])?;

        // Add Mul.mul : {α : Type u} → [inst : Mul α] → α → α → α
        let mul_const = |u: Level| Expr::const_(Name::from_string("Mul"), vec![u]);

        let mul_mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(mul_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b_id, _b) = b.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(mul_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Mul.mul value = λ {α} [inst : Mul α] => Expr.proj("Mul", 0, inst)
        let mul_mul_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(mul_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("Mul"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(mul_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Mul.mul"),
            level_params: vec![u],
            type_: mul_mul_type,
            value: mul_mul_value,
            is_reducible: true,
        })?;

        self.mul_init = true;
        Ok(())
    }

    /// Check if Mul typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_mul` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_mul(&self) -> bool {
        self.mul_init
    }

    /// Initialize the Neg typeclass
    ///
    /// Neg is a typeclass with a single field `neg`:
    /// ```text
    /// class Neg (α : Type u) where
    ///   neg : α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.neg_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_neg(&mut self) -> Result<(), EnvError> {
        if self.neg_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        let neg_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Neg.mk : {α : Type u} → (α → α) → Neg α
        let neg_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // The field type: α → α
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let field_body = alpha.clone();
            let field_type = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), field_body);
            let (field_id, _field) = b.fresh_local(field_type.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("Neg"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(field_id, BinderInfo::Default, field_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let neg_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Neg"),
                type_: neg_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Neg.mk"),
                    type_: neg_mk_type,
                }],
            }],
        };

        self.add_inductive(neg_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("Neg"), vec![Name::from_string("neg")])?;

        // Register `Neg` as a type class so the elaborator's instance resolution
        // (`resolve_instance`) recognises `Neg α` goals. Prefix `-` desugars to
        // `Neg.neg` (see clean-parser expr_operators.rs), whose `[inst : Neg α]`
        // argument is filled by instance synthesis; without `Neg` in the class
        // registry the goal `Neg Int`/`Neg Float` was never even searched and the
        // instance argument leaked as a fresh metavariable ("contains free
        // variables"). One param, no out-params (homogeneous). (Track EF)
        self.register_class(KernelClassInfo {
            name: Name::from_string("Neg"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Add Neg.neg : {α : Type u} → [inst : Neg α] → α → α
        let neg_const = |u: Level| Expr::const_(Name::from_string("Neg"), vec![u]);

        let neg_neg_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(neg_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(neg_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Neg.neg value = λ {α} [inst : Neg α] => Expr.proj("Neg", 0, inst)
        let neg_neg_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(neg_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("Neg"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(neg_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Neg.neg"),
            level_params: vec![u],
            type_: neg_neg_type,
            value: neg_neg_value,
            is_reducible: true,
        })?;

        self.neg_init = true;
        Ok(())
    }

    /// Check if Neg typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_neg` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_neg(&self) -> bool {
        self.neg_init
    }

    /// Initialize the Sub typeclass
    ///
    /// Sub is a typeclass with a single field `sub`:
    /// ```text
    /// class Sub (α : Type u) where
    ///   sub : α → α → α
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.sub_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_sub(&mut self) -> Result<(), EnvError> {
        if self.sub_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        let sub_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Default, type_u.clone(), e);
            b.finish(e)
        };

        // Sub.mk : {α : Type u} → (α → α → α) → Sub α
        let sub_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // The field type: α → α → α
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let field_body = alpha.clone();
            let field_type = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), field_body);
            let field_type = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), field_type);
            let (field_id, _field) = b.fresh_local(field_type.clone());
            let e = Expr::app(
                Expr::const_(Name::from_string("Sub"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(field_id, BinderInfo::Default, field_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sub_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Sub"),
                type_: sub_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Sub.mk"),
                    type_: sub_mk_type,
                }],
            }],
        };

        self.add_inductive(sub_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(Name::from_string("Sub"), vec![Name::from_string("sub")])?;

        // Add Sub.sub : {α : Type u} → [inst : Sub α] → α → α → α
        let sub_const = |u: Level| Expr::const_(Name::from_string("Sub"), vec![u]);

        let sub_sub_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(sub_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b_id, _b) = b.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(sub_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Sub.sub value = λ {α} [inst : Sub α] => Expr.proj("Sub", 0, inst)
        let sub_sub_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(sub_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("Sub"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(sub_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Sub.sub"),
            level_params: vec![u],
            type_: sub_sub_type,
            value: sub_sub_value,
            is_reducible: true,
        })?;

        self.sub_init = true;
        Ok(())
    }

    /// Check if Sub typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_sub` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_sub(&self) -> bool {
        self.sub_init
    }
}
