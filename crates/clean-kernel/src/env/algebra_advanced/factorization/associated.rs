// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Associated relation for integral domains.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Associated relation for integral domains
    ///
    /// Associated {α : Type u} [Monoid α] (a b : α) : Prop
    /// Two elements are associated if they differ by a unit:
    /// Associated a b ↔ ∃ u : αˣ, a = u * b (or equivalently, a ∣ b ∧ b ∣ a)
    ///
    /// For Nat: Associated a b ↔ a = b (since only units are 1)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.associated_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_associated(&mut self) -> Result<(), EnvError> {
        if self.associated_init {
            return Ok(());
        }

        // Dependencies
        self.init_irreducible()?;
        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Associated : {α : Type u} → [IntegralDomain α] → α → α → Prop
        let associated_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _) = b.fresh_local(inst_ty.clone());
            let (a_id, _) = b.fresh_local(alpha.clone());
            let (bv_id, _) = b.fresh_local(alpha.clone());
            let r = b.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), prop.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Associated"),
            level_params: vec![u.clone()],
            type_: associated_type,
        })?;

        // Associated.refl : ∀ {α} [IntegralDomain α] (a : α), Associated a a
        let associated_refl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let assoc_a_a = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Associated"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst,
                    ),
                    a.clone(),
                ),
                a,
            );
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), assoc_a_a);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Associated.refl"),
            level_params: vec![u.clone()],
            type_: associated_refl_type,
        })?;

        // Associated.symm : ∀ {α} [IntegralDomain α] {a b : α}, Associated a b → Associated b a
        let associated_symm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (bv_id, bv) = b.fresh_local(alpha.clone());
            let assoc_ab = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Associated"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst.clone(),
                    ),
                    a.clone(),
                ),
                bv.clone(),
            );
            let assoc_ba = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Associated"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst,
                    ),
                    bv,
                ),
                a,
            );
            let (h_id, _) = b.fresh_local(assoc_ab.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, assoc_ab, assoc_ba);
            let r = b.mk_pi(bv_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Associated.symm"),
            level_params: vec![u.clone()],
            type_: associated_symm_type,
        })?;

        // Associated.trans : ∀ {α} [IntegralDomain α] {a b c : α},
        //   Associated a b → Associated b c → Associated a c
        let associated_trans_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (bv_id, bv) = b.fresh_local(alpha.clone());
            let (c_id, c) = b.fresh_local(alpha.clone());
            let mk_assoc = |x: Expr, y: Expr| -> Expr {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("Associated"),
                                    vec![u_level.clone()],
                                ),
                                alpha.clone(),
                            ),
                            inst.clone(),
                        ),
                        x,
                    ),
                    y,
                )
            };
            let assoc_ab = mk_assoc(a.clone(), bv.clone());
            let assoc_bc = mk_assoc(bv, c.clone());
            let assoc_ac = mk_assoc(a, c);
            let (h2_id, _) = b.fresh_local(assoc_bc.clone());
            let (h1_id, _) = b.fresh_local(assoc_ab.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, assoc_bc, assoc_ac);
            let r = b.mk_pi(h1_id, BinderInfo::Default, assoc_ab, r);
            let r = b.mk_pi(c_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(bv_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Associated.trans"),
            level_params: vec![u.clone()],
            type_: associated_trans_type,
        })?;

        // For Nat: Nat.Associated is just equality (since only unit is 1)
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.Associated : Nat → Nat → Prop (just Eq for Nat)
        let nat_assoc_type = Expr::pi(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::pi(BinderInfo::Default, nat_type.clone(), prop.clone()),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Associated"),
            level_params: vec![],
            type_: nat_assoc_type,
        })?;

        // Nat.Associated.eq : ∀ {a b}, Nat.Associated a b → Eq a b
        let nat_assoc_eq_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_type.clone());
            let (bv_id, bv) = b.fresh_local(nat_type.clone());
            let nat_assoc_ab = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.Associated"), vec![]),
                    a.clone(),
                ),
                bv.clone(),
            );
            let eq_ab = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    a,
                ),
                bv,
            );
            let (h_id, _) = b.fresh_local(nat_assoc_ab.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, nat_assoc_ab, eq_ab);
            let r = b.mk_pi(bv_id, BinderInfo::Implicit, nat_type.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Associated.eq"),
            level_params: vec![],
            type_: nat_assoc_eq_type,
        })?;

        // Nat.eq_iff_associated : ∀ {a b}, Eq a b ↔ Nat.Associated a b
        // (We state just one direction as axiom for simplicity)
        let eq_impl_assoc_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_type.clone());
            let (bv_id, bv) = b.fresh_local(nat_type.clone());
            let eq_ab = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    a.clone(),
                ),
                bv.clone(),
            );
            let nat_assoc_ab = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.Associated"), vec![]), a),
                bv,
            );
            let (h_id, _) = b.fresh_local(eq_ab.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, eq_ab, nat_assoc_ab);
            let r = b.mk_pi(bv_id, BinderInfo::Implicit, nat_type.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.eq_associated"),
            level_params: vec![],
            type_: eq_impl_assoc_type,
        })?;

        self.associated_init = true;
        Ok(())
    }

    /// Check if Associated has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.associated_init == true`
    pub fn has_associated(&self) -> bool {
        self.associated_init
    }
}
