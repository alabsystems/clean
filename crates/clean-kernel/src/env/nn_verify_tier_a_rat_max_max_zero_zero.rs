// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 4:
//! `NNVerify.Rat.max_max_zero_zero` (max-idempotence at 0).
//!
//! Ground instance of `max`-idempotence: `max (max 0 0) (max 0 0) = 0`.
//! Established by composing the characterizing equation `Rat.max_def`
//! (applied at `a = b = max 0 0` with the reflexive witness
//! `le_refl_max_zero_zero`) with the existing `max_zero_zero`
//! equality via `Eq.trans`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.max_max_zero_zero
//!     : Eq Rat (Rat.max (Rat.max 0 0) (Rat.max 0 0)) Rat.zero`
//!
//!   Proof term:
//!   `@Eq.trans.{1} Rat
//!       (Rat.max (Rat.max 0 0) (Rat.max 0 0))
//!       (Rat.max Rat.zero Rat.zero)
//!       Rat.zero
//!       (@Rat.max_def (Rat.max 0 0) (Rat.max 0 0)
//!           NNVerify.Rat.le_refl_max_zero_zero)
//!       NNVerify.Rat.max_zero_zero`
//!
//!   Note: `Rat.max_def : ∀ a b, Rat.le a b → Eq (Rat.max a b) b`. At
//!   `a = b = max 0 0`, applying `max_def` yields
//!   `Eq (Rat.max (max 0 0) (max 0 0)) (max 0 0)`. Chaining with
//!   `max_zero_zero : Eq (max 0 0) 0` via `Eq.trans` gives the target.
//!
//!   Closure: `Rat.max_def` (foundational), `Eq.trans` (foundational),
//!   `NNVerify.Rat.le_refl_max_zero_zero` (constructive, empty closure),
//!   `NNVerify.Rat.max_zero_zero` (constructive, empty closure). Zero
//!   non-foundational axioms.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 4 min/max idempotence)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `max_max_zero_zero` lemma (#3551 Batch 4).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_max_max_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_max_max_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_max_max_zero_zero_init {
            return Ok(());
        }
        self.init_rat_minmax()?; // Rat.max, Rat.max_def
                                 // `init_nn_verify_ibp_width_zero` wires NNVerify.Rat.max_zero_zero.
        self.init_nn_verify_ibp_width_zero()?;
        self.init_nn_verify_tier_a_rat_le_refl_max_zero_zero()?; // witness
        self.init_eq()?; // Eq.trans

        self.register_rat_max_max_zero_zero()?;

        self.nn_verify_tier_a_rat_max_max_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.max_max_zero_zero
    ///     : Eq Rat (Rat.max (Rat.max 0 0) (Rat.max 0 0)) Rat.zero`.
    ///
    /// Proof: `Eq.trans` over `Rat.max_def` specialized at
    /// `a = b = max 0 0` with witness `le_refl_max_zero_zero`, chained
    /// with `max_zero_zero`.
    fn register_rat_max_max_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.max_max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let max_zz = Expr::apps(rat_max.clone(), [rat_zero.clone(), rat_zero.clone()]);
        let max_of_max = Expr::apps(rat_max, [max_zz.clone(), max_zz.clone()]);

        // Type: Eq Rat (max (max 0 0) (max 0 0)) Rat.zero
        let ty = Expr::apps(eq, [rat.clone(), max_of_max.clone(), rat_zero.clone()]);

        // Step 1: @Rat.max_def (max 0 0) (max 0 0) le_refl_max_zero_zero
        //   : Eq (max (max 0 0) (max 0 0)) (max 0 0)
        let step1 = {
            let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
            let le_refl_max = Expr::const_(
                Name::from_string("NNVerify.Rat.le_refl_max_zero_zero"),
                vec![],
            );
            Expr::apps(max_def, [max_zz.clone(), max_zz.clone(), le_refl_max])
        };

        // Step 2: NNVerify.Rat.max_zero_zero : Eq (max 0 0) Rat.zero
        let step2 = Expr::const_(Name::from_string("NNVerify.Rat.max_zero_zero"), vec![]);

        // Combine via Eq.trans.{1} α (max (max 0 0) (max 0 0)) (max 0 0) Rat.zero step1 step2
        let value = {
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            Expr::apps(eq_trans, [rat, max_of_max, max_zz, rat_zero, step1, step2])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `max_max_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_max_max_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_max_max_zero_zero_init
    }
}
