// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Function.comp` combinator (core function composition).
//!
//! Registers the Lean 4 core composition function as a real, fully-checked
//! `Declaration::Definition` (no axioms):
//!
//! ```text
//! @[reducible] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w}
//!     (f : β → δ) (g : α → β) : α → δ := fun x => f (g x)
//! ```
//!
//! Lean source: `Init/Prelude.lean` (toolchain `v4.30.0-rc2`).
//!
//! Clean already desugars the *notation* / partially-applied forms at the
//! surface level: `f ∘ g` (parsed as `Function.comp f g` with two args) and
//! `(f ∘ g) x` both rewrite to definitionally-equal lambdas in the elaborator
//! (`infer/mod.rs`). But those handlers are arity-specific, so the *fully
//! named, fully applied* forms — `Function.comp f g x`, or a bare
//! `Function.comp` referenced by name — fell through to `UnknownIdent`. This
//! constant closes that gap: every arity now resolves through ordinary
//! application and kernel reduction, matching Lean. The surface desugars still
//! fire first for the notation forms (they are defeq), so no existing behavior
//! changes — this registration is purely additive.
//!
//! Universe-polymorphic over three independent `Sort` universes exactly as Lean
//! core is, so `Function.comp` composes functions between `Prop`/`Type`s at any
//! levels.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register
    /// `Function.comp : {α : Sort u} → {β : Sort v} → {δ : Sort w} → (β → δ) → (α → β) → α → δ`
    /// `  := fun {α} {β} {δ} f g => fun x => f (g x)`.
    ///
    /// Lean fidelity: `Init/Prelude.lean`
    /// `@[reducible] def Function.comp {α β δ} (f : β → δ) (g : α → β) : α → δ := fun x => f (g x)`.
    /// Reducible (Clean's defeq-unfolding analog of Lean's `@[reducible]`),
    /// value is the composed lambda, no axioms.
    ///
    /// Skipped when a `Function.comp` constant is already present (e.g. restored
    /// from a real `.olean` import), so an imported definition always wins.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fun_comp_init == true`
    /// ENSURES: Idempotent — calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_fun_comp(&mut self) -> Result<(), EnvError> {
        if self.fun_comp_init {
            return Ok(());
        }

        // An imported `Function.comp` (real olean) takes precedence: never clobber.
        if self
            .get_const(&Name::from_string("Function.comp"))
            .is_none()
        {
            let u = Name::from_string("u");
            let v = Name::from_string("v");
            let w = Name::from_string("w");
            let sort_u = Expr::sort(Level::param(u.clone()));
            let sort_v = Expr::sort(Level::param(v.clone()));
            let sort_w = Expr::sort(Level::param(w.clone()));

            // Function.comp : {α : Sort u} → {β : Sort v} → {δ : Sort w}
            //               → (β → δ) → (α → β) → α → δ
            let comp_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (delta_id, delta) = b.fresh_local(sort_w.clone());
                // β → δ  (non-dependent arrow via a throwaway binder)
                let (bd_id, _) = b.fresh_local(beta.clone());
                let f_ty = b.mk_pi(bd_id, BinderInfo::Default, beta.clone(), delta.clone());
                // α → β
                let (ab_id, _) = b.fresh_local(alpha.clone());
                let g_ty = b.mk_pi(ab_id, BinderInfo::Default, alpha.clone(), beta.clone());
                // α → δ  (result)
                let (ad_id, _) = b.fresh_local(alpha.clone());
                let res_ty = b.mk_pi(ad_id, BinderInfo::Default, alpha.clone(), delta.clone());
                let (f_id, _f) = b.fresh_local(f_ty.clone());
                let (g_id, _g) = b.fresh_local(g_ty.clone());
                let r = res_ty;
                let r = b.mk_pi(g_id, BinderInfo::Default, g_ty.clone(), r);
                let r = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_pi(delta_id, BinderInfo::Implicit, sort_w.clone(), r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            // value: fun {α} {β} {δ} (f : β → δ) (g : α → β) => fun (x : α) => f (g x)
            let comp_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (delta_id, delta) = b.fresh_local(sort_w.clone());
                let (bd_id, _) = b.fresh_local(beta.clone());
                let f_ty = b.mk_pi(bd_id, BinderInfo::Default, beta.clone(), delta.clone());
                let (ab_id, _) = b.fresh_local(alpha.clone());
                let g_ty = b.mk_pi(ab_id, BinderInfo::Default, alpha.clone(), beta.clone());
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (g_id, g) = b.fresh_local(g_ty.clone());
                let (x_id, x) = b.fresh_local(alpha.clone());
                // f (g x)
                let g_x = Expr::app(g, x);
                let f_g_x = Expr::app(f, g_x);
                let r = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), f_g_x);
                let r = b.mk_lam(g_id, BinderInfo::Default, g_ty.clone(), r);
                let r = b.mk_lam(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_lam(delta_id, BinderInfo::Implicit, sort_w.clone(), r);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Function.comp"),
                level_params: vec![u, v, w],
                type_: comp_type,
                value: comp_value,
                is_reducible: true,
            })?;
        }

        self.fun_comp_init = true;
        Ok(())
    }
}
