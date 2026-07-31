// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.mul_neg_zero_zero`.
//!
//! Instantiates `Rat.mul_neg : ∀ a b : Rat, a * (-b) = -(a * b)` at `a = b = Rat.zero`.
//! `Rat.mul_neg` is in `FOUNDATIONAL_AXIOMS`, so the transitive
//! non-foundational closure is empty and the theorem flows into the
//! clean-Native shard as `ProofQuality::Constructive`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.mul_neg_zero_zero :
//!       Rat.mul Rat.zero (Rat.neg Rat.zero) = Rat.neg (Rat.mul Rat.zero Rat.zero)`
//!
//!   Proof term: `Rat.mul_neg Rat.zero Rat.zero`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage, Batch 3 — scalar lane)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.mul_neg_zero_zero` lemma (#3551 Batch 3).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_mul_neg_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_mul_neg_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_mul_neg_zero_zero_init {
            return Ok(());
        }
        self.init_nn_verify_rat_ordering()?; // Rat.mul_neg (foundational axiom)
        self.init_eq()?;

        self.register_rat_mul_neg_zero_zero()?;

        self.nn_verify_tier_a_rat_mul_neg_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.mul_neg_zero_zero :
    ///     Rat.mul Rat.zero (Rat.neg Rat.zero) = Rat.neg (Rat.mul Rat.zero Rat.zero)`.
    ///
    /// Proof term: `Rat.mul_neg Rat.zero Rat.zero`. Transitive non-foundational
    /// axiom closure is empty — `Rat.mul_neg` is in `FOUNDATIONAL_AXIOMS`.
    fn register_rat_mul_neg_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.mul_neg_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Rat.mul Rat.zero (Rat.neg Rat.zero) = Rat.neg (Rat.mul Rat.zero Rat.zero)
        let neg_zero = Expr::app(rat_neg.clone(), rat_zero.clone());
        let lhs = Expr::apps(rat_mul.clone(), [rat_zero.clone(), neg_zero]);
        let inner_mul = Expr::apps(rat_mul, [rat_zero.clone(), rat_zero.clone()]);
        let rhs = Expr::app(rat_neg, inner_mul);
        let ty = Expr::apps(eq, [rat, lhs, rhs]);

        // Proof term: Rat.mul_neg Rat.zero Rat.zero
        let mul_neg = Expr::const_(Name::from_string("Rat.mul_neg"), vec![]);
        let value = Expr::apps(mul_neg, [rat_zero.clone(), rat_zero]);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.mul_neg_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_mul_neg_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_mul_neg_zero_zero_init
    }
}
