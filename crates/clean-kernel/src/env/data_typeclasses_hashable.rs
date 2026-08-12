// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hashable typeclass initialization for Environment
//!
//! This module contains:
//! - Hashable typeclass and instances (Nat, Bool)

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Hashable typeclass
    ///
    /// class Hashable (α : Type u) where
    ///   hash : α → UInt64
    ///
    /// Provides a hash function for a type.
    /// Note: We use Nat instead of UInt64 since we don't have UInt64 yet.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.hashable_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_hashable(&mut self) -> Result<(), EnvError> {
        if self.hashable_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // Hashable : Type u → Type u
        let hashable_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        );

        // Hashable.mk : {α : Type u} → (α → Nat) → Hashable α
        let hashable_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let hash_fn_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = nat_const.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(hash_fn_ty.clone());
            let r = Expr::app(
                Expr::const_(Name::from_string("Hashable"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let r = b.mk_pi(f_id, BinderInfo::Default, hash_fn_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let hashable_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Hashable"),
                type_: hashable_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Hashable.mk"),
                    type_: hashable_mk_type,
                }],
            }],
        };

        self.add_inductive(hashable_ind)?;

        // Register `Hashable` as a one-field structure / typeclass so instance
        // synthesis can recognize it and resolve `[Hashable T]` (Task NN — the
        // prelude now wires `init_hashable`, so these registrations are required
        // for `deriving Hashable` and explicit `Hashable` instances to resolve).
        self.register_structure_fields(
            Name::from_string("Hashable"),
            vec![Name::from_string("hash")],
        )?;
        self.register_class(KernelClassInfo {
            name: Name::from_string("Hashable"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Hashable.hash : {α : Type u} → [inst : Hashable α] → α → Nat
        let hash_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let hashable_alpha = Expr::app(
                Expr::const_(Name::from_string("Hashable"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(hashable_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let r = nat_const.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, hashable_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Value uses Hashable.rec to extract the hash field
        let hashable_rec =
            |u1: Level, u2: Level| Expr::const_(Name::from_string("Hashable.rec"), vec![u1, u2]);

        let hash_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let hashable_alpha = Expr::app(
                Expr::const_(Name::from_string("Hashable"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(hashable_alpha.clone());
            // Motive: λ _ : Hashable α => α → Nat
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(hashable_alpha.clone());
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _x) = d.fresh_local(alpha.clone());
                    let r = nat_const.clone();
                    let r = d.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                    d.finish_child(r)
                };
                let r = c.mk_lam(w_id, BinderInfo::Default, hashable_alpha.clone(), inner);
                c.finish_child(r)
            };
            // Minor: λ f : (α → Nat) => f (just return the hash function)
            let alpha_to_nat = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = nat_const.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (f_id, f) = c.fresh_local(alpha_to_nat.clone());
                let r = c.mk_lam(f_id, BinderInfo::Default, alpha_to_nat, f);
                c.finish_child(r)
            };
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                hashable_rec(Level::succ(u_level.clone()), u_level.clone()),
                                alpha.clone(),
                            ),
                            motive,
                        ),
                        minor,
                    ),
                    inst,
                ),
                a,
            );
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, hashable_alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Hashable.hash"),
            level_params: vec![u.clone()],
            type_: hash_type,
            value: hash_value,
            is_reducible: true,
        })?;

        // instHashableNat : Hashable Nat := ⟨id⟩ (identity function - hash n = n)
        let hashable_nat_type = Expr::app(
            Expr::const_(Name::from_string("Hashable"), vec![Level::zero()]),
            nat_const.clone(),
        );
        // λ n : Nat => n (identity)
        let id_nat = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), n);
            b.finish(r)
        };
        let hashable_nat_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Hashable.mk"), vec![Level::zero()]),
                nat_const.clone(),
            ),
            id_nat,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHashableNat"),
            level_params: vec![],
            type_: hashable_nat_type,
            value: hashable_nat_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHashableNat"),
            class_name: Name::from_string("Hashable"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // instHashableBool : Hashable Bool
        // hash true = 1, hash false = 0
        self.init_bool()?;
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero.clone(),
        );

        // Bool.hash : Bool → Nat
        // hash b := Bool.rec 0 1 b (false -> 0, true -> 1)
        let bool_hash_type = Expr::pi(BinderInfo::Default, bool_const.clone(), nat_const.clone());
        let bool_motive = Expr::lam(BinderInfo::Default, bool_const.clone(), nat_const.clone());
        let bool_hash_value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(bool_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(bool_rec.clone(), bool_motive), nat_zero.clone()),
                    nat_one.clone(),
                ),
                bv,
            );
            let r = b.mk_lam(bv_id, BinderInfo::Default, bool_const.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Bool.hash"),
            level_params: vec![],
            type_: bool_hash_type,
            value: bool_hash_value,
            is_reducible: true,
        })?;

        // instHashableBool : Hashable Bool := ⟨Bool.hash⟩
        let hashable_bool_type = Expr::app(
            Expr::const_(Name::from_string("Hashable"), vec![Level::zero()]),
            bool_const.clone(),
        );
        let hashable_bool_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Hashable.mk"), vec![Level::zero()]),
                bool_const.clone(),
            ),
            Expr::const_(Name::from_string("Bool.hash"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instHashableBool"),
            level_params: vec![],
            type_: hashable_bool_type,
            value: hashable_bool_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instHashableBool"),
            class_name: Name::from_string("Hashable"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.hashable_init = true;
        Ok(())
    }

    /// Check if Hashable typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_hashable` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_hashable(&self) -> bool {
        self.hashable_init
    }
}
