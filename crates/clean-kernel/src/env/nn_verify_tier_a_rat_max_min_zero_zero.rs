// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 4:
//! `NNVerify.Rat.max_min_zero_zero` (mixed max/min collapse to 0).
//!
//! Ground instance mixing `max` and `min`:
//! `max (min 0 0) (min 0 0) = 0`. Established by `Rat.max_def` applied at
//! `a = b = min 0 0` with witness `le_refl_min_zero_zero`, chained with
//! `min_zero_zero` via `Eq.trans`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.max_min_zero_zero
//!     : Eq Rat (Rat.max (Rat.min 0 0) (Rat.min 0 0)) Rat.zero`
//!
//!   Proof term:
//!   `@Eq.trans.{1} Rat
//!       (Rat.max (Rat.min 0 0) (Rat.min 0 0))
//!       (Rat.min Rat.zero Rat.zero)
//!       Rat.zero
//!       (@Rat.max_def (Rat.min 0 0) (Rat.min 0 0)
//!           NNVerify.Rat.le_refl_min_zero_zero)
//!       NNVerify.Rat.min_zero_zero`
//!
//!   Closure: `Rat.max_def` (foundational), `Eq.trans` (foundational),
//!   `NNVerify.Rat.le_refl_min_zero_zero` (constructive, empty closure),
//!   `NNVerify.Rat.min_zero_zero` (constructive, empty closure). Zero
//!   non-foundational axioms.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 4 min/max collapse)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `max_min_zero_zero` lemma (#3551 Batch 4).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_max_min_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_max_min_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_max_min_zero_zero_init {
            return Ok(());
        }
        self.init_rat_minmax()?; // Rat.max, Rat.min, Rat.max_def
        self.init_nn_verify_tier_a_rat_min_zero()?; // NNVerify.Rat.min_zero_zero
        self.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()?; // witness
        self.init_eq()?; // Eq.trans

        self.register_rat_max_min_zero_zero()?;

        self.nn_verify_tier_a_rat_max_min_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.max_min_zero_zero
    ///     : Eq Rat (Rat.max (min 0 0) (min 0 0)) Rat.zero`.
    ///
    /// Proof: `Eq.trans` over `Rat.max_def` specialized at
    /// `a = b = min 0 0` with witness `le_refl_min_zero_zero`, chained
    /// with `min_zero_zero`.
    fn register_rat_max_min_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.max_min_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let min_zz = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);
        let max_of_min = Expr::apps(rat_max, [min_zz.clone(), min_zz.clone()]);

        // Type: Eq Rat (max (min 0 0) (min 0 0)) Rat.zero
        let ty = Expr::apps(eq, [rat.clone(), max_of_min.clone(), rat_zero.clone()]);

        // Step 1: @Rat.max_def (min 0 0) (min 0 0) le_refl_min_zero_zero
        //   : Eq (max (min 0 0) (min 0 0)) (min 0 0)
        let step1 = {
            let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
            let le_refl_min = Expr::const_(
                Name::from_string("NNVerify.Rat.le_refl_min_zero_zero"),
                vec![],
            );
            Expr::apps(max_def, [min_zz.clone(), min_zz.clone(), le_refl_min])
        };

        // Step 2: NNVerify.Rat.min_zero_zero : Eq (min 0 0) Rat.zero
        let step2 = Expr::const_(Name::from_string("NNVerify.Rat.min_zero_zero"), vec![]);

        // Combine via Eq.trans.{1} α (max (min 0 0) (min 0 0)) (min 0 0) Rat.zero step1 step2
        let value = {
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            Expr::apps(eq_trans, [rat, max_of_min, min_zz, rat_zero, step1, step2])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `max_min_zero_zero` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_max_min_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_max_min_zero_zero_init
    }
}
