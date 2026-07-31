// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 2:
//! `NNVerify.Rat.min_zero_zero_alt`.
//!
//! Alternative proof of `Rat.min 0 0 = 0` that routes through
//! `Rat.min_def'` instead of the `Rat.min_def` used by the original
//! `NNVerify.Rat.min_zero_zero` theorem (batch 1).
//!
//! `Rat.min_def'` is in `FOUNDATIONAL_AXIOMS` (`axiom_audit.rs`
//! line 107), so the closure is empty. Same statement as batch-1's
//! `NNVerify.Rat.min_zero_zero` with a distinct proof term, giving
//! downstream rewriters both branches of the `min` characterization.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.min_zero_zero_alt
//!     : Eq Rat (Rat.min Rat.zero Rat.zero) Rat.zero`
//!
//!   Proof term: `@Rat.min_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
//!
//!   `Rat.min_def' : ∀ a b : Rat, Rat.le b a → Eq (Rat.min a b) b`.
//!   Specializing at `a = b = Rat.zero` with witness
//!   `Rat.le_refl Rat.zero` gives the desired equality.
//!
//!   Closure: `Rat.min_def'` (foundational axiom), `Rat.le_refl`
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
    /// Initialize the Tier A `min_zero_zero_alt` lemma (#3551 Batch 2).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_min_zero_zero_alt_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_min_zero_zero_alt(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_min_zero_zero_alt_init {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.le_refl
        self.init_rat_minmax()?; // Rat.min, Rat.min_def'

        self.register_rat_min_zero_zero_alt()?;

        self.nn_verify_tier_a_rat_min_zero_zero_alt_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.min_zero_zero_alt : Eq Rat (Rat.min 0 0) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`):
    /// `@Rat.min_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
    fn register_rat_min_zero_zero_alt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.min_zero_zero_alt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Eq Rat (Rat.min Rat.zero Rat.zero) Rat.zero
        let ty = {
            let min_zz = Expr::apps(rat_min.clone(), [rat_zero.clone(), rat_zero.clone()]);
            Expr::apps(eq, [rat, min_zz, rat_zero.clone()])
        };

        // Proof: @Rat.min_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero).
        let value = {
            let min_def_alt = Expr::const_(Name::from_string("Rat.min_def'"), vec![]);
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h = Expr::app(le_refl, rat_zero.clone());
            Expr::apps(min_def_alt, [rat_zero.clone(), rat_zero.clone(), h])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `min_zero_zero_alt` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_min_zero_zero_alt(&self) -> bool {
        self.nn_verify_tier_a_rat_min_zero_zero_alt_init
    }
}
