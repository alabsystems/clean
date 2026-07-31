// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.mul_zero_zero`.
//!
//! Instantiates `Rat.mul_zero : ∀ a : Rat, a * 0 = 0` at `a = Rat.zero`.
//! `Rat.mul_zero` is in `FOUNDATIONAL_AXIOMS`, so the transitive
//! non-foundational closure is empty and the theorem flows into the
//! clean-Native shard as `ProofQuality::Constructive`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.mul_zero_zero : Rat.mul Rat.zero Rat.zero = Rat.zero`
//!
//!   Proof term: `Rat.mul_zero Rat.zero`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage, Batch 3 — scalar lane)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.mul_zero_zero` lemma (#3551 Batch 3).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_mul_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_mul_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_mul_zero_zero_init {
            return Ok(());
        }
        self.init_rat_field_inst()?; // Rat.mul_zero (foundational axiom)
        self.init_eq()?;

        self.register_rat_mul_zero_zero()?;

        self.nn_verify_tier_a_rat_mul_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.mul_zero_zero : Rat.mul Rat.zero Rat.zero = Rat.zero`.
    ///
    /// Proof term: `Rat.mul_zero Rat.zero`. Transitive non-foundational
    /// axiom closure is empty — `Rat.mul_zero` is in `FOUNDATIONAL_AXIOMS`.
    fn register_rat_mul_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.mul_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Rat.mul Rat.zero Rat.zero = Rat.zero
        let lhs = Expr::apps(rat_mul, [rat_zero.clone(), rat_zero.clone()]);
        let ty = Expr::apps(eq, [rat, lhs, rat_zero.clone()]);

        // Proof term: Rat.mul_zero Rat.zero
        let mul_zero = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
        let value = Expr::app(mul_zero, rat_zero);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.mul_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_mul_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_mul_zero_zero_init
    }
}
