// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 2: `NNVerify.Rat.min_eq_max_zero_zero`.
//!
//! Symmetric form of `NNVerify.Rat.max_eq_min_zero_zero` obtained by
//! applying `Eq.symm`. Completes the four-way chain
//! `max 0 0 ↔ min 0 0` in both directions.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.min_eq_max_zero_zero
//!     : Eq Rat (Rat.min Rat.zero Rat.zero) (Rat.max Rat.zero Rat.zero)`
//!
//!   Proof term:
//!   `@Eq.symm.{1} Rat (Rat.max Rat.zero Rat.zero) (Rat.min Rat.zero Rat.zero)
//!       NNVerify.Rat.max_eq_min_zero_zero`.
//!
//!   Closure: `Eq.symm` (foundational theorem),
//!   `NNVerify.Rat.max_eq_min_zero_zero` (existing Tier A theorem with
//!   empty domain-axiom closure). Zero non-foundational axioms.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 2)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `min_eq_max_zero_zero` lemma (#3551 Batch 2).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_min_eq_max_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_min_eq_max(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_min_eq_max_init {
            return Ok(());
        }
        self.init_nn_verify_tier_a_rat_max_eq_min()?; // batch-1 base
        self.init_eq()?; // Eq.symm

        self.register_rat_min_eq_max_zero_zero()?;

        self.nn_verify_tier_a_rat_min_eq_max_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.min_eq_max_zero_zero
    ///     : Eq Rat (Rat.min Rat.zero Rat.zero) (Rat.max Rat.zero Rat.zero)`.
    ///
    /// Proof:
    /// `@Eq.symm.{1} Rat (Rat.max 0 0) (Rat.min 0 0)
    ///     NNVerify.Rat.max_eq_min_zero_zero`.
    fn register_rat_min_eq_max_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.min_eq_max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let max_zz = Expr::apps(rat_max, [rat_zero.clone(), rat_zero.clone()]);
        let min_zz = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);

        // Type: Eq Rat (Rat.min 0 0) (Rat.max 0 0)
        let ty = Expr::apps(eq, [rat.clone(), min_zz.clone(), max_zz.clone()]);

        // Proof term:
        // @Eq.symm.{1} Rat (max 0 0) (min 0 0) NNVerify.Rat.max_eq_min_zero_zero.
        let value = {
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let base = Expr::const_(
                Name::from_string("NNVerify.Rat.max_eq_min_zero_zero"),
                vec![],
            );
            Expr::apps(eq_symm, [rat, max_zz, min_zz, base])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `min_eq_max_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_min_eq_max(&self) -> bool {
        self.nn_verify_tier_a_rat_min_eq_max_init
    }
}
