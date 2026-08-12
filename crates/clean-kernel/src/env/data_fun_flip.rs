// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `flip` combinator (core argument-flipping composition).
//!
//! Registers the Lean core argument-flip function as a real, fully-checked
//! `Declaration::Definition` (no axioms):
//!
//! ```text
//! @[inline] def flip {α : Sort u} {β : Sort v} {φ : Sort w}
//!     (f : α → β → φ) : β → α → φ := fun b a => f a b
//! ```
//!
//! Lean source: `Init/Core.lean:65` (toolchain `v4.30.0-rc2`) — re-read from
//! the pinned toolchain 2026-07-30; the original citation here said
//! `Init/Prelude.lean` / `@[reducible]`, and both were wrong. Clean registers
//! the constant `is_reducible: true` while Lean marks it `@[inline]` (a
//! compiler hint, not a transparency setting), so Clean unfolds `flip` at
//! reducible transparency where Lean would not. That is a delta step either
//! way — sound, and only defeq *completeness* differs — but it is a
//! divergence, so do not cite this file as `@[reducible]` parity.
//!
//! Because the constant occupies the bare root name, a source file that writes
//! its own `def flip …` is a genuine duplicate declaration and is rejected —
//! which is also what `lean` does ("`flip` has already been declared").
//! Pinned by `clean-cli`'s
//! `tests::check_file_redefining_prelude_flip_is_a_loud_duplicate`.
//!
//! Like `Function.comp`, Clean already desugars the *partially applied* form at
//! the surface level: `flip g` (one argument) rewrites to the defeq
//! `fun a b => g b a` in the elaborator (`infer/mod.rs:1184`), and the applied
//! `(flip g) a b` form beta-reduces at `mod.rs:854`. But those handlers are
//! arity-specific, so the *fully named, fully applied* `flip f b a` (and a bare
//! `flip` referenced by name) fell through to `UnknownIdent`. This constant
//! closes that gap: every arity now resolves through ordinary application and
//! kernel reduction. The surface desugars still fire first for the partial
//! forms (they are defeq), so this registration is purely additive.
//!
//! Clean's surface parser spells this combinator `flip` (bare, per the
//! `func_qualified_name(func) == "flip"` desugar keys), so the constant is
//! registered under that name — matching what a source program writes and what
//! the elaborator looks up.
//!
//! Universe-polymorphic over three independent `Sort` universes exactly as Lean
//! core is.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register
    /// `flip : {α : Sort u} → {β : Sort v} → {γ : Sort w} → (α → β → γ) → β → α → γ`
    /// `  := fun {α} {β} {γ} f b a => f a b`.
    ///
    /// Lean fidelity: `Init/Core.lean:65`
    /// `@[inline] def flip {α β φ} (f : α → β → φ) : β → α → φ := fun b a => f a b`.
    /// Type and value match; the transparency does not (see the module header).
    /// Value is the argument-flipped application, no axioms.
    ///
    /// Skipped when a `flip` constant is already present (e.g. restored from a
    /// real `.olean` import), so an imported definition always wins.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fun_flip_init == true`
    /// ENSURES: Idempotent — calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_fun_flip(&mut self) -> Result<(), EnvError> {
        if self.fun_flip_init {
            return Ok(());
        }

        // An imported `flip` (real olean) takes precedence: never clobber.
        if self.get_const(&Name::from_string("flip")).is_none() {
            let u = Name::from_string("u");
            let v = Name::from_string("v");
            let w = Name::from_string("w");
            let sort_u = Expr::sort(Level::param(u.clone()));
            let sort_v = Expr::sort(Level::param(v.clone()));
            let sort_w = Expr::sort(Level::param(w.clone()));

            // flip : {α : Sort u} → {β : Sort v} → {γ : Sort w}
            //      → (α → β → γ) → β → α → γ
            let flip_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (gamma_id, gamma) = b.fresh_local(sort_w.clone());
                // f : α → β → γ  =  α → (β → γ), via nested throwaway binders
                let (bg_id, _) = b.fresh_local(beta.clone());
                let bg_arrow = b.mk_pi(bg_id, BinderInfo::Default, beta.clone(), gamma.clone());
                let (fa_id, _) = b.fresh_local(alpha.clone());
                let f_ty = b.mk_pi(fa_id, BinderInfo::Default, alpha.clone(), bg_arrow);
                let (f_id, _f) = b.fresh_local(f_ty.clone());
                let (b_id, _b) = b.fresh_local(beta.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let r = gamma.clone();
                let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                let r = b.mk_pi(b_id, BinderInfo::Default, beta.clone(), r);
                let r = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_pi(gamma_id, BinderInfo::Implicit, sort_w.clone(), r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            // value: fun {α} {β} {γ} (f : α → β → γ) (b : β) (a : α) => f a b
            let flip_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (gamma_id, gamma) = b.fresh_local(sort_w.clone());
                let (bg_id, _) = b.fresh_local(beta.clone());
                let bg_arrow = b.mk_pi(bg_id, BinderInfo::Default, beta.clone(), gamma.clone());
                let (fa_id, _) = b.fresh_local(alpha.clone());
                let f_ty = b.mk_pi(fa_id, BinderInfo::Default, alpha.clone(), bg_arrow);
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (b_id, bb) = b.fresh_local(beta.clone());
                let (a_id, aa) = b.fresh_local(alpha.clone());
                // f a b
                let f_a = Expr::app(f, aa);
                let f_a_b = Expr::app(f_a, bb);
                let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), f_a_b);
                let r = b.mk_lam(b_id, BinderInfo::Default, beta.clone(), r);
                let r = b.mk_lam(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_lam(gamma_id, BinderInfo::Implicit, sort_w.clone(), r);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("flip"),
                level_params: vec![u, v, w],
                type_: flip_type,
                value: flip_value,
                is_reducible: true,
            })?;
        }

        self.fun_flip_init = true;
        Ok(())
    }
}
