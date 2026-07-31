// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551) — Batch 4:
//! `NNVerify.Rat.min_le_max_zero_zero`.
//!
//! Connects `Rat.min` and `Rat.max` at the reflexive ground instance:
//! `Rat.le (Rat.min 0 0) (Rat.max 0 0)`. Established by LE-transport over
//! the existing `min_zero_zero` / `zero_eq_max_zero_zero` theorems and the
//! already-constructive `le_refl_zero` witness.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.min_le_max_zero_zero
//!     : Rat.le (Rat.min Rat.zero Rat.zero) (Rat.max Rat.zero Rat.zero)`
//!
//!   Proof term:
//!   `@NNVerify.le_of_eq_of_le (Rat.min 0 0) Rat.zero (Rat.max 0 0)
//!       NNVerify.Rat.min_zero_zero
//!       (@NNVerify.le_of_le_of_eq Rat.zero Rat.zero (Rat.max 0 0)
//!           NNVerify.Rat.le_refl_zero NNVerify.Rat.zero_eq_max_zero_zero)`.
//!
//!   Closure: `NNVerify.le_of_eq_of_le`, `NNVerify.le_of_le_of_eq`,
//!   `NNVerify.Rat.min_zero_zero`, `NNVerify.Rat.le_refl_zero`,
//!   `NNVerify.Rat.zero_eq_max_zero_zero` — all already constructive
//!   (`ProofQuality::Constructive`) with empty non-foundational axiom
//!   closure. Transitive closure over them is therefore also empty.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — Batch 4 min/max transitivity)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `min_le_max_zero_zero` lemma (#3551 Batch 4).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_min_le_max_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_min_le_max_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_min_le_max_zero_zero_init {
            return Ok(());
        }
        // Dependencies: existing constructive lemmas.
        self.init_nn_verify_ibp_width_zero()?; // NNVerify.Rat.max_zero_zero (used transitively via zero_eq_max)
        self.init_nn_verify_tier_a_rat_min_zero()?; // NNVerify.Rat.min_zero_zero
        self.init_nn_verify_tier_a_rat_le_refl_zero()?; // NNVerify.Rat.le_refl_zero
        self.init_nn_verify_tier_a_rat_zero_eq_max()?; // NNVerify.Rat.zero_eq_max_zero_zero
        self.init_nn_verify_ibp_linear()?; // NNVerify.le_of_eq_of_le, NNVerify.le_of_le_of_eq

        self.register_rat_min_le_max_zero_zero()?;

        self.nn_verify_tier_a_rat_min_le_max_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.min_le_max_zero_zero
    ///     : Rat.le (Rat.min 0 0) (Rat.max 0 0)`.
    ///
    /// Proof: LE-transport composition — see module docs.
    fn register_rat_min_le_max_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.min_le_max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        let min_zz = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);
        let max_zz = Expr::apps(rat_max, [rat_zero.clone(), rat_zero.clone()]);

        // Type: Rat.le (min 0 0) (max 0 0)
        let ty = Expr::apps(rat_le, [min_zz.clone(), max_zz.clone()]);

        // Inner: @NNVerify.le_of_le_of_eq 0 0 (max 0 0) le_refl_zero zero_eq_max
        //   : Rat.le 0 (max 0 0)
        let inner = {
            let le_of_le_of_eq = Expr::const_(Name::from_string("NNVerify.le_of_le_of_eq"), vec![]);
            let le_refl_zero = Expr::const_(Name::from_string("NNVerify.Rat.le_refl_zero"), vec![]);
            let zero_eq_max = Expr::const_(
                Name::from_string("NNVerify.Rat.zero_eq_max_zero_zero"),
                vec![],
            );
            Expr::apps(
                le_of_le_of_eq,
                [
                    rat_zero.clone(),
                    rat_zero.clone(),
                    max_zz.clone(),
                    le_refl_zero,
                    zero_eq_max,
                ],
            )
        };

        // Outer: @NNVerify.le_of_eq_of_le (min 0 0) 0 (max 0 0) min_zero_zero inner
        //   : Rat.le (min 0 0) (max 0 0)
        let value = {
            let le_of_eq_of_le = Expr::const_(Name::from_string("NNVerify.le_of_eq_of_le"), vec![]);
            let min_zz_eq_zero =
                Expr::const_(Name::from_string("NNVerify.Rat.min_zero_zero"), vec![]);
            Expr::apps(
                le_of_eq_of_le,
                [min_zz, rat_zero, max_zz, min_zz_eq_zero, inner],
            )
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `min_le_max_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_min_le_max_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_min_le_max_zero_zero_init
    }
}
