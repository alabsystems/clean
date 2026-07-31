// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.zero_eq_max_zero_zero`.
//!
//! Symmetric form of `NNVerify.Rat.max_zero_zero` obtained by applying
//! `Eq.symm` to the established max-zero-zero theorem. `Eq.symm` is a
//! kernel theorem (see `crates/clean-kernel/src/env/core_eq/basic.rs`)
//! derived from `Eq.rec`, so its transitive closure is purely
//! foundational. The resulting theorem closure is therefore empty.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.zero_eq_max_zero_zero
//!     : Eq Rat Rat.zero (Rat.max Rat.zero Rat.zero)`
//!
//!   Proof term:
//!   `@Eq.symm.{1} Rat (Rat.max Rat.zero Rat.zero) Rat.zero
//!       NNVerify.Rat.max_zero_zero`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `zero_eq_max_zero_zero` lemma (#3551).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_zero_eq_max_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_zero_eq_max(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_zero_eq_max_init {
            return Ok(());
        }
        self.init_nn_verify_ibp_width_zero()?; // NNVerify.Rat.max_zero_zero
        self.init_eq()?; // Eq.symm

        self.register_rat_zero_eq_max_zero_zero()?;

        self.nn_verify_tier_a_rat_zero_eq_max_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.zero_eq_max_zero_zero
    ///     : Eq Rat Rat.zero (Rat.max Rat.zero Rat.zero)`.
    ///
    /// Proof:
    /// `@Eq.symm.{1} Rat (Rat.max Rat.zero Rat.zero) Rat.zero
    ///     NNVerify.Rat.max_zero_zero`.
    ///
    /// Closure: `Eq.symm` (foundational theorem body, pulls only
    /// foundational `Eq.rec` / `Eq.refl`), `NNVerify.Rat.max_zero_zero`
    /// (existing Tier A theorem with empty closure). Zero
    /// non-foundational axioms.
    fn register_rat_zero_eq_max_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.zero_eq_max_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let max_zz = Expr::apps(rat_max, [rat_zero.clone(), rat_zero.clone()]);

        // Type: Eq Rat Rat.zero (Rat.max Rat.zero Rat.zero)
        let ty = Expr::apps(eq, [rat.clone(), rat_zero.clone(), max_zz.clone()]);

        // Proof term:
        // `@Eq.symm.{1} Rat (Rat.max Rat.zero Rat.zero) Rat.zero max_zero_zero`.
        let value = {
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let base = Expr::const_(Name::from_string("NNVerify.Rat.max_zero_zero"), vec![]);
            Expr::apps(eq_symm, [rat, max_zz, rat_zero, base])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `zero_eq_max_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_zero_eq_max(&self) -> bool {
        self.nn_verify_tier_a_rat_zero_eq_max_init
    }
}
