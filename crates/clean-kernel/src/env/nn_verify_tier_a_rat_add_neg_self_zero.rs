// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.add_neg_self_zero`.
//!
//! Instantiates `Rat.add_neg_self : ∀ a : Rat, a + (-a) = 0` at `a = Rat.zero`.
//! `Rat.add_neg_self` is in `FOUNDATIONAL_AXIOMS`, so the transitive
//! non-foundational closure is empty and the theorem flows into the
//! clean-Native shard as `ProofQuality::Constructive`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.add_neg_self_zero : Rat.add Rat.zero (Rat.neg Rat.zero) = Rat.zero`
//!
//!   Proof term: `Rat.add_neg_self Rat.zero`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage, Batch 3 — scalar lane)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.add_neg_self_zero` lemma (#3551 Batch 3).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_add_neg_self_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_add_neg_self_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_add_neg_self_zero_init {
            return Ok(());
        }
        self.init_nn_verify_rat_ordering()?; // Rat.add_neg_self (foundational axiom)
        self.init_eq()?;

        self.register_rat_add_neg_self_zero()?;

        self.nn_verify_tier_a_rat_add_neg_self_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.add_neg_self_zero : Rat.add Rat.zero (Rat.neg Rat.zero) = Rat.zero`.
    ///
    /// Proof term: `Rat.add_neg_self Rat.zero`. Transitive non-foundational
    /// axiom closure is empty — `Rat.add_neg_self` is in `FOUNDATIONAL_AXIOMS`.
    fn register_rat_add_neg_self_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.add_neg_self_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Rat.add Rat.zero (Rat.neg Rat.zero) = Rat.zero
        let neg_zero = Expr::app(rat_neg, rat_zero.clone());
        let lhs = Expr::apps(rat_add, [rat_zero.clone(), neg_zero]);
        let ty = Expr::apps(eq, [rat, lhs, rat_zero.clone()]);

        // Proof term: Rat.add_neg_self Rat.zero
        let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
        let value = Expr::app(add_neg_self, rat_zero);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.add_neg_self_zero` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_add_neg_self_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_add_neg_self_zero_init
    }
}
