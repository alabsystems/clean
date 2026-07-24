// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 2:
//! `NNVerify.Rat.le_refl_min_zero_zero`.
//!
//! Reflexivity of `Rat.le` on `Rat.min Rat.zero Rat.zero`. Mirror of
//! `NNVerify.Rat.le_refl_max_zero_zero`. Supplies a ready witness for
//! downstream `Rat.le` / `Rat.min_def` / `Rat.min_def'` applications
//! over the `min 0 0` expression without forcing callers to rebuild
//! `Rat.le_refl` applications.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.le_refl_min_zero_zero
//!     : Rat.le (Rat.min Rat.zero Rat.zero) (Rat.min Rat.zero Rat.zero)`
//!
//!   Proof term: `Rat.le_refl (Rat.min Rat.zero Rat.zero)`.
//!
//!   Closure: `Rat.le_refl` (foundational axiom), `Rat.min`
//!   (foundational), `Rat.zero` (definition), `Rat.le` (definition).
//!   Zero non-foundational axioms.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 2)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `le_refl_min_zero_zero` lemma (#3551 Batch 2).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_le_refl_min_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_le_refl_min_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_le_refl_min_zero_zero_init {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.le_refl, Rat.le
        self.init_rat_minmax()?; // Rat.min

        self.register_rat_le_refl_min_zero_zero()?;

        self.nn_verify_tier_a_rat_le_refl_min_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.le_refl_min_zero_zero
    ///     : Rat.le (Rat.min Rat.zero Rat.zero) (Rat.min Rat.zero Rat.zero)`.
    ///
    /// Proof: `Rat.le_refl (Rat.min Rat.zero Rat.zero)`.
    fn register_rat_le_refl_min_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.le_refl_min_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        let min_zz = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);

        // Type: Rat.le (Rat.min 0 0) (Rat.min 0 0)
        let ty = Expr::apps(rat_le, [min_zz.clone(), min_zz.clone()]);

        // Proof: Rat.le_refl (Rat.min 0 0).
        let value = {
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            Expr::app(le_refl, min_zz)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `le_refl_min_zero_zero` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_le_refl_min_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_le_refl_min_zero_zero_init
    }
}
