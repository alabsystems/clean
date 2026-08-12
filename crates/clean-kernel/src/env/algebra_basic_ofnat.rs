// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OfNat typeclass and Nat numeric literal instance
//!
//! This module contains:
//! - OfNat typeclass definition (polymorphic numeric literals)
//! - OfNat instance for Nat (identity)
//!
//! UInt OfNat instances are in algebra_basic_ofnat_uint.rs.
//! Split from algebra_basic.rs for #307.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType,
    KernelInstanceInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ========================================================================
    // OfNat Typeclass: Polymorphic numeric literals
    // ========================================================================

    /// Initialize the OfNat typeclass
    ///
    /// OfNat enables polymorphic numeric literals. From Lean 4:
    /// ```text
    /// class OfNat.{u} (α : Type u) (n : Nat) : Type u where
    ///   ofNat : α
    /// ```
    ///
    /// Key characteristics:
    /// - Universe polymorphic: `α : Type u`
    /// - Indexed by concrete Nat value (second parameter)
    /// - Single method `ofNat : α`
    ///
    /// This enables `0` to elaborate as `@OfNat.ofNat ?α 0 ?inst` with the type
    /// inferred from context.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat(&mut self) -> Result<(), EnvError> {
        if self.ofnat_init {
            return Ok(());
        }

        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // OfNat : Type u → Nat → Type u
        // This is a 2-parameter typeclass (α and n)
        //
        // As an inductive:
        // inductive OfNat.{u} : Type u → Nat → Type u where
        //   | mk : {α : Type u} → {n : Nat} → α → OfNat α n
        let ofnat_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let e = type_u.clone();
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Default, type_u.clone(), e);
            b.finish(e)
        };

        // OfNat.mk : {α : Type u} → {n : Nat} → α → OfNat α n
        let ofnat_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let e = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("OfNat"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                n.clone(),
            );
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let ofnat_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("OfNat"),
                type_: ofnat_type,
                constructors: vec![Constructor {
                    name: Name::from_string("OfNat.mk"),
                    type_: ofnat_mk_type,
                }],
            }],
        };

        self.add_inductive(ofnat_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("OfNat"),
            vec![Name::from_string("ofNat")],
        )?;

        let ofnat_const = |u: Level| Expr::const_(Name::from_string("OfNat"), vec![u]);

        // OfNat.ofNat : {α : Type u} → {n : Nat} → [inst : OfNat α n] → α
        let ofnat_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (inst_id, _inst) = b.fresh_local(Expr::app(
                Expr::app(ofnat_const(u_level.clone()), alpha.clone()),
                n.clone(),
            ));
            let e = alpha.clone();
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(
                    Expr::app(ofnat_const(u_level.clone()), alpha.clone()),
                    n.clone(),
                ),
                e,
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // OfNat.ofNat value = λ {α} {n} [inst : OfNat α n] => Expr.proj("OfNat", 0, inst)
        let ofnat_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(
                Expr::app(ofnat_const(u_level.clone()), alpha.clone()),
                n.clone(),
            ));
            let body = Expr::proj(Name::from_string("OfNat"), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(
                    Expr::app(ofnat_const(u_level.clone()), alpha.clone()),
                    n.clone(),
                ),
                body,
            );
            let e = b.mk_lam(n_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("OfNat.ofNat"),
            level_params: vec![u],
            type_: ofnat_proj_type,
            value: ofnat_proj_value,
            is_reducible: true,
        })?;

        self.ofnat_init = true;
        Ok(())
    }

    /// Check if OfNat typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_ofnat` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_ofnat(&self) -> bool {
        self.ofnat_init
    }

    /// Initialize OfNat instance for Nat
    ///
    /// ```text
    /// instance (n : Nat) : OfNat Nat n where
    ///   ofNat := n
    /// ```
    ///
    /// This is the identity instance - for Nat, the literal IS the value.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_nat_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ofnat_nat(&mut self) -> Result<(), EnvError> {
        if self.ofnat_nat_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);

        // instOfNatNat : (n : Nat) → OfNat Nat n
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(Expr::app(ofnat_const.clone(), nat_const.clone()), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // value: λ n : Nat => OfNat.mk Nat n n
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), nat_const.clone()), n.clone()),
                n.clone(),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instOfNatNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        // Lean's INSTANCE priority for `instOfNatNat` is the unannotated
        // default, 1000 — verified two ways: `Init/Prelude.lean` declares
        // `@[default_instance 100] instance instOfNatNat (n : Nat) : OfNat Nat n`
        // (no `(priority := …)` on the `instance`), and the shipped
        // `Init/Prelude.olean` serializes it into `Lean.Meta.instanceExtension`
        // as `priority: 1000`.
        //
        // Do NOT read the `100` off that `@[default_instance 100]`: those are
        // two different tables. `default_instance` priority orders TYPE
        // DEFAULTING for an unresolved numeric literal; instance priority
        // orders `synthInstance` candidates. Clean tracks defaulting separately
        // (`ElabCtx::default_instances`, fed by the `@[default_instance]`
        // handler), so this field is only the latter.
        //
        // Registering 100 here (Lean's `low`) inverted Lean's candidate order
        // against `Zero.toOfNat0`, which `Init/Data/Zero.lean:17` declares at
        // `(priority := 300)`. Priority dominates candidate ordering, so
        // `(0 : Nat)` elaborated to `Zero.toOfNat0` where Lean produces
        // `instOfNatNat 0`. Both are definitionally equal, so nothing was
        // rejected — but `simp only [Nat.add_zero]` could no longer match its
        // own imported statement, because syntactic matching sees the two
        // shapes as different.
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatNat"),
            class_name: Name::from_string("OfNat"),
            priority: 1000,
            type_: None,
            value: None,
        });

        self.ofnat_nat_inst_init = true;
        Ok(())
    }

    /// Check if OfNat Nat instance has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_ofnat_nat` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn has_ofnat_nat(&self) -> bool {
        self.ofnat_nat_inst_init
    }
}
