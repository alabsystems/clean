// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Relation property typeclasses for Environment
//!
//! This module contains standalone relation property init_* and has_* functions:
//! - Reflexive
//! - Antisymm
//! - Irrefl
//! - Asymm
//!
//! Order hierarchy typeclasses (Trans, Preorder, PartialOrder, LinearOrder)
//! remain in order_structures.rs.
//!
//! Split from order_structures.rs for #307.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Reflexive typeclass
    ///
    /// Reflexive is a typeclass for reflexive relations:
    /// - Reflexive : {α : Sort u} → (α → α → Prop) → Prop
    /// - Reflexive.mk : {α : Sort u} → {r : α → α → Prop} →
    ///                  (∀ a : α, r a a) → Reflexive r
    /// - Reflexive.refl : {α : Sort u} → {r : α → α → Prop} → [Reflexive r] →
    ///                    ∀ a : α, r a a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.reflexive_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_reflexive(&mut self) -> Result<(), EnvError> {
        if self.reflexive_init {
            return Ok(());
        }

        // Initialize Eq for Prop
        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Helper: Reflexive.{u} α r
        let reflexive_const_app = |alpha: &Expr, r: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Reflexive"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            )
        };

        // Helper: relation type α → α → Prop
        let rel_type =
            |alpha: &Expr| Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), prop.clone()));

        // Reflexive : {α : Sort u} → (α → α → Prop) → Prop
        let reflexive_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (_r_id, _r) = b.fresh_local(rel_type(&alpha));
            let ty = prop.clone();
            let ty = b.mk_pi(_r_id, BinderInfo::Default, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        // Reflexive.mk : {α : Sort u} → {r : α → α → Prop} →
        //                (∀ a : α, r a a) → Reflexive r
        let reflexive_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));

            // refl_proof : ∀ a : α, r a a
            let refl_proof_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let body = Expr::app(Expr::app(r.clone(), a.clone()), a);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let (_proof_id, _proof) = b.fresh_local(refl_proof_type.clone());
            let result = reflexive_const_app(&alpha, &r);
            let ty = b.mk_pi(_proof_id, BinderInfo::Default, refl_proof_type, result);
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        let reflexive_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2, // α and r are parameters
            types: vec![InductiveType {
                name: Name::from_string("Reflexive"),
                type_: reflexive_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Reflexive.mk"),
                    type_: reflexive_mk_type,
                }],
            }],
        };

        self.add_inductive(reflexive_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Reflexive"),
            vec![Name::from_string("refl")],
        )?;

        // Add Reflexive.refl : {α : Sort u} → {r : α → α → Prop} → [Reflexive r] → ∀ a : α, r a a
        let (refl_type, refl_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));
            let (inst_id, _inst) = b.fresh_local(reflexive_const_app(&alpha, &r));

            // ∀ a : α, r a a
            let field_body = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let body = Expr::app(Expr::app(r.clone(), a.clone()), a);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                reflexive_const_app(&alpha, &r),
                field_body,
            );
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            let ty = b.finish(ty);

            // value: λ {α} {r} [inst] => proj("Reflexive", 0, inst)
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(sort_u.clone());
            let (vr_id, vr) = vb.fresh_local(rel_type(&va));
            let (vi_id, vi) = vb.fresh_local(reflexive_const_app(&va, &vr));
            let val = Expr::proj(Name::from_string("Reflexive"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                reflexive_const_app(&va, &vr),
                val,
            );
            let val = vb.mk_lam(vr_id, BinderInfo::Implicit, rel_type(&va), val);
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, sort_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Reflexive.refl"),
            level_params: vec![u.clone()],
            type_: refl_type,
            value: refl_value,
            is_reducible: true,
        })?;

        self.reflexive_init = true;
        Ok(())
    }

    /// Check if Reflexive typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.reflexive_init == true`
    pub(crate) fn has_reflexive(&self) -> bool {
        self.reflexive_init
    }

    /// Initialize Antisymm typeclass
    ///
    /// Antisymm is a typeclass for antisymmetric relations:
    /// - Antisymm : {α : Sort u} → (α → α → Prop) → Prop
    /// - Antisymm.mk : {α : Sort u} → {r : α → α → Prop} →
    ///                 (∀ a b : α, r a b → r b a → a = b) → Antisymm r
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.antisymm_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_antisymm(&mut self) -> Result<(), EnvError> {
        if self.antisymm_init {
            return Ok(());
        }

        // Initialize Eq
        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Helper: Antisymm.{u} α r
        let antisymm_const_app = |alpha: &Expr, r: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Antisymm"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            )
        };

        // Helper: relation type α → α → Prop
        let rel_type =
            |alpha: &Expr| Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), prop.clone()));

        // Helper: Eq.{u} α a b
        let eq_app = |alpha: &Expr, a: &Expr, b: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![u_level.clone()]),
                        alpha.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        // Antisymm : {α : Sort u} → (α → α → Prop) → Prop
        let antisymm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (_r_id, _r) = b.fresh_local(rel_type(&alpha));
            let ty = prop.clone();
            let ty = b.mk_pi(_r_id, BinderInfo::Default, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        // Antisymm.mk : {α : Sort u} → {r : α → α → Prop} →
        //               (∀ a b : α, r a b → r b a → a = b) → Antisymm r
        let antisymm_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));

            // antisymm_proof : ∀ a b : α, r a b → r b a → a = b
            let antisymm_proof_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (b_id, bv) = cb.fresh_local(alpha.clone());
                let (rab_id, _rab) =
                    cb.fresh_local(Expr::app(Expr::app(r.clone(), a.clone()), bv.clone()));
                let (rba_id, _rba) =
                    cb.fresh_local(Expr::app(Expr::app(r.clone(), bv.clone()), a.clone()));
                let conclusion = eq_app(&alpha, &a, &bv);
                let body = cb.mk_pi(
                    rba_id,
                    BinderInfo::Default,
                    Expr::app(Expr::app(r.clone(), bv.clone()), a.clone()),
                    conclusion,
                );
                let body = cb.mk_pi(
                    rab_id,
                    BinderInfo::Default,
                    Expr::app(Expr::app(r.clone(), a.clone()), bv.clone()),
                    body,
                );
                let body = cb.mk_pi(b_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let (_proof_id, _proof) = b.fresh_local(antisymm_proof_type.clone());
            let result = antisymm_const_app(&alpha, &r);
            let ty = b.mk_pi(_proof_id, BinderInfo::Default, antisymm_proof_type, result);
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        let antisymm_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2, // α and r are parameters
            types: vec![InductiveType {
                name: Name::from_string("Antisymm"),
                type_: antisymm_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Antisymm.mk"),
                    type_: antisymm_mk_type,
                }],
            }],
        };

        self.add_inductive(antisymm_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Antisymm"),
            vec![Name::from_string("antisymm")],
        )?;

        self.antisymm_init = true;
        Ok(())
    }

    /// Check if Antisymm typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.antisymm_init == true`
    pub(crate) fn has_antisymm(&self) -> bool {
        self.antisymm_init
    }

    /// Initialize Irrefl typeclass
    ///
    /// Irrefl is a typeclass for irreflexive relations:
    /// - Irrefl : {α : Sort u} → (α → α → Prop) → Prop
    /// - Irrefl.mk : {α : Sort u} → {r : α → α → Prop} →
    ///               (∀ a : α, ¬ r a a) → Irrefl r
    ///
    /// A relation r is irreflexive if ∀ a, ¬ r a a (no element is related to itself)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.irrefl_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_irrefl(&mut self) -> Result<(), EnvError> {
        if self.irrefl_init {
            return Ok(());
        }

        // Initialize Not (requires classical for negation)
        self.init_true_false()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // Helper: Irrefl.{u} α r
        let irrefl_const_app = |alpha: &Expr, r: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Irrefl"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            )
        };

        // Helper: relation type α → α → Prop
        let rel_type =
            |alpha: &Expr| Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), prop.clone()));

        // Irrefl : {α : Sort u} → (α → α → Prop) → Prop
        let irrefl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (_r_id, _r) = b.fresh_local(rel_type(&alpha));
            let ty = prop.clone();
            let ty = b.mk_pi(_r_id, BinderInfo::Default, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        // Irrefl.mk : {α : Sort u} → {r : α → α → Prop} →
        //             (∀ a : α, r a a → False) → Irrefl r
        let irrefl_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));

            // irrefl_proof : ∀ a : α, r a a → False
            let irrefl_proof_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let raa = Expr::app(Expr::app(r.clone(), a.clone()), a);
                let (raa_id, _raa) = cb.fresh_local(raa.clone());
                let body = false_const.clone();
                let body = cb.mk_pi(raa_id, BinderInfo::Default, raa, body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let (_proof_id, _proof) = b.fresh_local(irrefl_proof_type.clone());
            let result = irrefl_const_app(&alpha, &r);
            let ty = b.mk_pi(_proof_id, BinderInfo::Default, irrefl_proof_type, result);
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        let irrefl_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2, // α and r are parameters
            types: vec![InductiveType {
                name: Name::from_string("Irrefl"),
                type_: irrefl_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Irrefl.mk"),
                    type_: irrefl_mk_type,
                }],
            }],
        };

        self.add_inductive(irrefl_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Irrefl"),
            vec![Name::from_string("irrefl")],
        )?;

        // Add Irrefl.irrefl : {α : Sort u} → {r : α → α → Prop} → [Irrefl r] → ∀ a : α, r a a → False
        let (irrefl_field_type, irrefl_field_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));
            let (inst_id, _inst) = b.fresh_local(irrefl_const_app(&alpha, &r));

            // ∀ a : α, r a a → False
            let field_body = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let raa = Expr::app(Expr::app(r.clone(), a.clone()), a);
                let (raa_id, _raa) = cb.fresh_local(raa.clone());
                let body = false_const.clone();
                let body = cb.mk_pi(raa_id, BinderInfo::Default, raa, body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                irrefl_const_app(&alpha, &r),
                field_body,
            );
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            let ty = b.finish(ty);

            // value: λ {α} {r} [inst] => proj("Irrefl", 0, inst)
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(sort_u.clone());
            let (vr_id, vr) = vb.fresh_local(rel_type(&va));
            let (vi_id, vi) = vb.fresh_local(irrefl_const_app(&va, &vr));
            let val = Expr::proj(Name::from_string("Irrefl"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                irrefl_const_app(&va, &vr),
                val,
            );
            let val = vb.mk_lam(vr_id, BinderInfo::Implicit, rel_type(&va), val);
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, sort_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Irrefl.irrefl"),
            level_params: vec![u.clone()],
            type_: irrefl_field_type,
            value: irrefl_field_value,
            is_reducible: true,
        })?;

        self.irrefl_init = true;
        Ok(())
    }

    /// Check if Irrefl typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.irrefl_init == true`
    pub(crate) fn has_irrefl(&self) -> bool {
        self.irrefl_init
    }

    /// Initialize Asymm typeclass
    ///
    /// Asymm is a typeclass for asymmetric relations:
    /// - Asymm : {α : Sort u} → (α → α → Prop) → Prop
    /// - Asymm.mk : {α : Sort u} → {r : α → α → Prop} →
    ///              (∀ a b : α, r a b → ¬ r b a) → Asymm r
    ///
    /// A relation r is asymmetric if ∀ a b, r a b → ¬ r b a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.asymm_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_asymm(&mut self) -> Result<(), EnvError> {
        if self.asymm_init {
            return Ok(());
        }

        // Initialize False (for negation)
        self.init_true_false()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // Helper: Asymm.{u} α r
        let asymm_const_app = |alpha: &Expr, r: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Asymm"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            )
        };

        // Helper: relation type α → α → Prop
        let rel_type =
            |alpha: &Expr| Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), prop.clone()));

        // Asymm : {α : Sort u} → (α → α → Prop) → Prop
        let asymm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (_r_id, _r) = b.fresh_local(rel_type(&alpha));
            let ty = prop.clone();
            let ty = b.mk_pi(_r_id, BinderInfo::Default, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        // Asymm.mk : {α : Sort u} → {r : α → α → Prop} →
        //            (∀ a b : α, r a b → r b a → False) → Asymm r
        let asymm_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));

            // asymm_proof : ∀ a b : α, r a b → r b a → False
            let asymm_proof_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (b_id, bv) = cb.fresh_local(alpha.clone());
                let rab = Expr::app(Expr::app(r.clone(), a.clone()), bv.clone());
                let rba = Expr::app(Expr::app(r.clone(), bv.clone()), a.clone());
                let (rab_id, _rab) = cb.fresh_local(rab.clone());
                let (rba_id, _rba) = cb.fresh_local(rba.clone());
                let body = false_const.clone();
                let body = cb.mk_pi(rba_id, BinderInfo::Default, rba, body);
                let body = cb.mk_pi(rab_id, BinderInfo::Default, rab, body);
                let body = cb.mk_pi(b_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let (_proof_id, _proof) = b.fresh_local(asymm_proof_type.clone());
            let result = asymm_const_app(&alpha, &r);
            let ty = b.mk_pi(_proof_id, BinderInfo::Default, asymm_proof_type, result);
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            b.finish(ty)
        };

        let asymm_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2, // α and r are parameters
            types: vec![InductiveType {
                name: Name::from_string("Asymm"),
                type_: asymm_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Asymm.mk"),
                    type_: asymm_mk_type,
                }],
            }],
        };

        self.add_inductive(asymm_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Asymm"),
            vec![Name::from_string("asymm")],
        )?;

        // Add Asymm.asymm : {α : Sort u} → {r : α → α → Prop} → [Asymm r] →
        //                   ∀ a b : α, r a b → r b a → False
        let (asymm_field_type, asymm_field_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha));
            let (inst_id, _inst) = b.fresh_local(asymm_const_app(&alpha, &r));

            // ∀ a b : α, r a b → r b a → False
            let field_body = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (bv_id, bv) = cb.fresh_local(alpha.clone());
                let rab = Expr::app(Expr::app(r.clone(), a.clone()), bv.clone());
                let rba = Expr::app(Expr::app(r.clone(), bv.clone()), a.clone());
                let (rab_id, _rab) = cb.fresh_local(rab.clone());
                let (rba_id, _rba) = cb.fresh_local(rba.clone());
                let body = false_const.clone();
                let body = cb.mk_pi(rba_id, BinderInfo::Default, rba, body);
                let body = cb.mk_pi(rab_id, BinderInfo::Default, rab, body);
                let body = cb.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };

            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                asymm_const_app(&alpha, &r),
                field_body,
            );
            let ty = b.mk_pi(r_id, BinderInfo::Implicit, rel_type(&alpha), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), ty);
            let ty = b.finish(ty);

            // value: λ {α} {r} [inst] => proj("Asymm", 0, inst)
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(sort_u.clone());
            let (vr_id, vr) = vb.fresh_local(rel_type(&va));
            let (vi_id, vi) = vb.fresh_local(asymm_const_app(&va, &vr));
            let val = Expr::proj(Name::from_string("Asymm"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                asymm_const_app(&va, &vr),
                val,
            );
            let val = vb.mk_lam(vr_id, BinderInfo::Implicit, rel_type(&va), val);
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, sort_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Asymm.asymm"),
            level_params: vec![u.clone()],
            type_: asymm_field_type,
            value: asymm_field_value,
            is_reducible: true,
        })?;

        self.asymm_init = true;
        Ok(())
    }

    /// Check if Asymm typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.asymm_init == true`
    pub(crate) fn has_asymm(&self) -> bool {
        self.asymm_init
    }
}
