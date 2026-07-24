// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `id` function combinator (Brick P1 — unregistered prelude heads).
//!
//! Registers the Lean 4 core identity function as a real, fully-checked
//! `Declaration::Definition` (no axioms):
//!
//! ```text
//! @[inline] def id {α : Sort u} (a : α) : α := a
//! ```
//!
//! Lean source: `Init/Prelude.lean:131` (toolchain `v4.30.0-rc2`).
//!
//! Without this constant, a bare `id 5` fell through to auto-implicit in the
//! elaborator (a fresh fvar typed `Sort u`), and applying the explicit
//! argument raised `TooManyArguments { func_type: "Sort(u)" }` — audit rows
//! e01–e03 in `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `id : {α : Sort u} → α → α := fun a => a`.
    ///
    /// Lean fidelity: `Init/Prelude.lean:131`
    /// `@[inline] def id {α : Sort u} (a : α) : α := a` — universe-polymorphic
    /// over `Sort u` (not just `Type u`), value is the identity lambda.
    /// Lean marks it `@[inline]` (a compiler hint); Clean's `is_reducible`
    /// flag is the defeq-unfolding analog used by every sibling registration.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fun_id_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_fun_id(&mut self) -> Result<(), EnvError> {
        if self.fun_id_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let sort_u = Expr::sort(Level::param(u.clone()));

        // id : {α : Sort u} → α → α
        let id_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // value: fun {α : Sort u} (a : α) => a
        let id_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), a);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("id"),
            level_params: vec![u],
            type_: id_type,
            value: id_value,
            is_reducible: true,
        })?;

        self.fun_id_init = true;
        Ok(())
    }
}
