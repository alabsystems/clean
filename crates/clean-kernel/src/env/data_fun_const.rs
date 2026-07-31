// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Function.const` combinator (core constant function).
//!
//! Registers the Lean core constant-function combinator as a real,
//! fully-checked `Declaration::Definition` (no axioms):
//!
//! ```text
//! @[reducible] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
//!   fun _ => a
//! ```
//!
//! Lean source: `Init/Prelude.lean` (toolchain `v4.30.0-rc2`). Note `β` is an
//! **explicit** argument (the domain of the constant function) while `α` is
//! implicit (inferred from `a`).
//!
//! Like `Function.comp` and `flip`, Clean already desugars the partially
//! applied forms at the surface level: `Function.const β` and
//! `Function.const β a` rewrite to defeq lambdas in the elaborator
//! (`infer/mod.rs:1218`), and the applied `(Function.const β a) x` form
//! beta-reduces at `mod.rs:865`. But those handlers cover only one or two
//! arguments, so the *fully named, fully applied* `Function.const β a x` (and a
//! bare `Function.const` referenced by name) fell through to `UnknownIdent`.
//! This constant closes that gap: every arity now resolves through ordinary
//! application and kernel reduction. The surface desugars still fire first for
//! the one/two-argument forms (they are defeq), so this registration is purely
//! additive. Completes the core-combinator family `Function.comp` / `flip` /
//! `Function.const`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register
    /// `Function.const : {α : Sort u} → (β : Sort v) → α → β → α := fun {α} β a => fun _ => a`.
    ///
    /// Lean fidelity: `Init/Prelude.lean`
    /// `@[reducible] def Function.const {α} (β : Sort v) (a : α) : β → α := fun _ => a`.
    /// Reducible (Clean's defeq-unfolding analog of Lean's `@[reducible]`),
    /// value is the constant function ignoring its `β` argument, no axioms.
    ///
    /// Skipped when a `Function.const` constant is already present (e.g. restored
    /// from a real `.olean` import), so an imported definition always wins.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fun_const_init == true`
    /// ENSURES: Idempotent — calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_fun_const(&mut self) -> Result<(), EnvError> {
        if self.fun_const_init {
            return Ok(());
        }

        // An imported `Function.const` (real olean) takes precedence: never clobber.
        if self
            .get_const(&Name::from_string("Function.const"))
            .is_none()
        {
            let u = Name::from_string("u");
            let v = Name::from_string("v");
            let sort_u = Expr::sort(Level::param(u.clone()));
            let sort_v = Expr::sort(Level::param(v.clone()));

            // Function.const : {α : Sort u} → (β : Sort v) → α → β → α
            let const_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                // β is a *value* of type `Sort v` (i.e. a type), explicit.
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                // result: β → α  (non-dependent arrow via a throwaway binder)
                let (ig_id, _) = b.fresh_local(beta.clone());
                let res_ty = b.mk_pi(ig_id, BinderInfo::Default, beta.clone(), alpha.clone());
                let r = res_ty;
                let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                let r = b.mk_pi(beta_id, BinderInfo::Default, sort_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            // value: fun {α} (β : Sort v) (a : α) => fun (_ : β) => a
            let const_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (beta_id, beta) = b.fresh_local(sort_v.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (ig_id, _ig) = b.fresh_local(beta.clone());
                // fun (_ : β) => a   (the ignored argument; body is `a`)
                let r = b.mk_lam(ig_id, BinderInfo::Default, beta.clone(), a);
                let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                let r = b.mk_lam(beta_id, BinderInfo::Default, sort_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Function.const"),
                level_params: vec![u, v],
                type_: const_type,
                value: const_value,
                is_reducible: true,
            })?;
        }

        self.fun_const_init = true;
        Ok(())
    }
}
