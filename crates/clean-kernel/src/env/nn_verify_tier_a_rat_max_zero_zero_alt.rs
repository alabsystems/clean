// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 2:
//! `NNVerify.Rat.max_zero_zero_alt`.
//!
//! Alternative proof of `Rat.max 0 0 = 0` that routes through
//! `Rat.max_def'` instead of the `Rat.max_def` used by the original
//! `NNVerify.rat_max_zero_zero` / `NNVerify.Rat.max_zero_zero` theorems.
//!
//! Both `Rat.max_def` and `Rat.max_def'` are in `FOUNDATIONAL_AXIOMS`
//! (`axiom_audit.rs` lines 106-107) and express the two branches of
//! the `max` characterization. At the reflexive input `a = b = 0`
//! the two branches coincide, so this lemma has the same type as
//! `NNVerify.Rat.max_zero_zero` but a distinct proof term. Downstream
//! rewriters can pick either theorem, which avoids forcing callers
//! to carry a specific witness direction.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.max_zero_zero_alt
//!     : Eq Rat (Rat.max Rat.zero Rat.zero) Rat.zero`
//!
//!   Proof term: `@Rat.max_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
//!
//!   `Rat.max_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.max a b) a`.
//!   Specializing at `a = b = Rat.zero` with witness
//!   `Rat.le_refl Rat.zero` gives the desired equality.
//!
//!   Closure: `Rat.max_def'` (foundational axiom), `Rat.le_refl`
//!   (foundational axiom), `Rat.zero` (definition), `Eq`
//!   (foundational). Zero non-foundational axioms.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 2)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `max_zero_zero_alt` lemma (#3551 Batch 2).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_max_zero_zero_alt_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_max_zero_zero_alt(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_max_zero_zero_alt_init {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.le_refl
        self.init_rat_minmax()?; // Rat.max, Rat.max_def'

        self.register_rat_max_zero_zero_alt()?;

        self.nn_verify_tier_a_rat_max_zero_zero_alt_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.max_zero_zero_alt : Eq Rat (Rat.max 0 0) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`):
    /// `@Rat.max_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
    fn register_rat_max_zero_zero_alt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.max_zero_zero_alt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Eq Rat (Rat.max Rat.zero Rat.zero) Rat.zero
        let ty = {
            let max_zz = Expr::apps(rat_max.clone(), [rat_zero.clone(), rat_zero.clone()]);
            Expr::apps(eq, [rat, max_zz, rat_zero.clone()])
        };

        // Proof: @Rat.max_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero).
        let value = {
            let max_def_alt = Expr::const_(Name::from_string("Rat.max_def'"), vec![]);
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h = Expr::app(le_refl, rat_zero.clone());
            Expr::apps(max_def_alt, [rat_zero.clone(), rat_zero.clone(), h])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `max_zero_zero_alt` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_max_zero_zero_alt(&self) -> bool {
        self.nn_verify_tier_a_rat_max_zero_zero_alt_init
    }
}
