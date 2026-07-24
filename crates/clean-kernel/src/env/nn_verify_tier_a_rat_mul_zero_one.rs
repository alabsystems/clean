// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.mul_zero_one`.
//!
//! Instantiates `Rat.zero_mul : ∀ a : Rat, 0 * a = 0` at `a = Rat.one`.
//! `Rat.zero_mul` is in `FOUNDATIONAL_AXIOMS`, so the transitive
//! non-foundational closure is empty and the theorem flows into the
//! clean-Native shard as `ProofQuality::Constructive`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.mul_zero_one : Rat.mul Rat.zero Rat.one = Rat.zero`
//!
//!   Proof term: `Rat.zero_mul Rat.one`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage, Batch 3 — scalar lane)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.mul_zero_one` lemma (#3551 Batch 3).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_mul_zero_one_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_mul_zero_one(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_mul_zero_one_init {
            return Ok(());
        }
        self.init_rat_field_inst()?; // Rat.zero_mul (foundational axiom)
        self.init_eq()?;

        self.register_rat_mul_zero_one()?;

        self.nn_verify_tier_a_rat_mul_zero_one_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.mul_zero_one : Rat.mul Rat.zero Rat.one = Rat.zero`.
    ///
    /// Proof term: `Rat.zero_mul Rat.one`. Transitive non-foundational
    /// axiom closure is empty — `Rat.zero_mul` is in `FOUNDATIONAL_AXIOMS`.
    fn register_rat_mul_zero_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.mul_zero_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Rat.mul Rat.zero Rat.one = Rat.zero
        let lhs = Expr::apps(rat_mul, [rat_zero.clone(), rat_one.clone()]);
        let ty = Expr::apps(eq, [rat, lhs, rat_zero]);

        // Proof term: Rat.zero_mul Rat.one
        let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
        let value = Expr::app(zero_mul, rat_one);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.mul_zero_one` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_mul_zero_one(&self) -> bool {
        self.nn_verify_tier_a_rat_mul_zero_one_init
    }
}
