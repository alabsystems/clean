// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 4:
//! `NNVerify.Rat.min_min_zero_zero` (min-idempotence at 0).
//!
//! Ground instance of `min`-idempotence: `min (min 0 0) (min 0 0) = 0`.
//! Established by composing the characterizing equation `Rat.min_def`
//! (applied at `a = b = min 0 0` with the reflexive witness
//! `le_refl_min_zero_zero`) with the existing `min_zero_zero`
//! equality via `Eq.trans`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.min_min_zero_zero
//!     : Eq Rat (Rat.min (Rat.min 0 0) (Rat.min 0 0)) Rat.zero`
//!
//!   Proof term:
//!   `@Eq.trans.{1} Rat
//!       (Rat.min (Rat.min 0 0) (Rat.min 0 0))
//!       (Rat.min Rat.zero Rat.zero)
//!       Rat.zero
//!       (@Rat.min_def (Rat.min 0 0) (Rat.min 0 0)
//!           NNVerify.Rat.le_refl_min_zero_zero)
//!       NNVerify.Rat.min_zero_zero`
//!
//!   Note: `Rat.min_def : ∀ a b, Rat.le a b → Eq (Rat.min a b) a`. At
//!   `a = b = min 0 0`, applying `min_def` yields
//!   `Eq (Rat.min (min 0 0) (min 0 0)) (min 0 0)`. Chaining with
//!   `min_zero_zero : Eq (min 0 0) 0` via `Eq.trans` gives the target.
//!
//!   Closure: `Rat.min_def` (foundational), `Eq.trans` (foundational),
//!   `NNVerify.Rat.le_refl_min_zero_zero` (constructive, empty closure),
//!   `NNVerify.Rat.min_zero_zero` (constructive, empty closure). Zero
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
    /// Initialize the Tier A `min_min_zero_zero` lemma (#3551 Batch 4).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_min_min_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_min_min_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_min_min_zero_zero_init {
            return Ok(());
        }
        self.init_rat_minmax()?; // Rat.min, Rat.min_def
        self.init_nn_verify_tier_a_rat_min_zero()?; // NNVerify.Rat.min_zero_zero
        self.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()?; // witness
        self.init_eq()?; // Eq.trans

        self.register_rat_min_min_zero_zero()?;

        self.nn_verify_tier_a_rat_min_min_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.min_min_zero_zero
    ///     : Eq Rat (Rat.min (Rat.min 0 0) (Rat.min 0 0)) Rat.zero`.
    ///
    /// Proof: `Eq.trans` over `Rat.min_def` specialized at
    /// `a = b = min 0 0` with witness `le_refl_min_zero_zero`, chained
    /// with `min_zero_zero`.
    fn register_rat_min_min_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.min_min_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let min_zz = Expr::apps(rat_min.clone(), [rat_zero.clone(), rat_zero.clone()]);
        let min_of_min = Expr::apps(rat_min, [min_zz.clone(), min_zz.clone()]);

        // Type: Eq Rat (min (min 0 0) (min 0 0)) Rat.zero
        let ty = Expr::apps(eq, [rat.clone(), min_of_min.clone(), rat_zero.clone()]);

        // Step 1: @Rat.min_def (min 0 0) (min 0 0) le_refl_min_zero_zero
        //   : Eq (min (min 0 0) (min 0 0)) (min 0 0)
        let step1 = {
            let min_def = Expr::const_(Name::from_string("Rat.min_def"), vec![]);
            let le_refl_min = Expr::const_(
                Name::from_string("NNVerify.Rat.le_refl_min_zero_zero"),
                vec![],
            );
            Expr::apps(min_def, [min_zz.clone(), min_zz.clone(), le_refl_min])
        };

        // Step 2: NNVerify.Rat.min_zero_zero : Eq (min 0 0) Rat.zero
        let step2 = Expr::const_(Name::from_string("NNVerify.Rat.min_zero_zero"), vec![]);

        // Combine via Eq.trans.{1} α (min (min 0 0) (min 0 0)) (min 0 0) Rat.zero step1 step2
        let value = {
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            Expr::apps(eq_trans, [rat, min_of_min, min_zz, rat_zero, step1, step2])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `min_min_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_min_min_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_min_min_zero_zero_init
    }
}
