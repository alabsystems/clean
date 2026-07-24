// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.le_refl_zero`.
//!
//! `Rat.le Rat.zero Rat.zero` — the zero-specialization of `Rat.le_refl`.
//! `Rat.le_refl` is already in `FOUNDATIONAL_AXIOMS` (#3490 T4
//! precedent; see `crates/clean-kernel/src/env/axiom_audit.rs`), so the
//! application at `Rat.zero` yields a theorem whose non-foundational
//! axiom closure is empty.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.le_refl_zero : Rat.le Rat.zero Rat.zero`
//!
//!   Proof term: `Rat.le_refl Rat.zero`.
//!
//!   `Rat.le_refl : ∀ a : Rat, Rat.le a a` (see
//!   `algebra_field.rs::init_rat_linear_order`). Instantiating at
//!   `Rat.zero` gives the desired proposition. This lemma is the
//!   witness consumed by `NNVerify.Rat.min_zero_zero` /
//!   `NNVerify.Rat.max_zero_zero` proofs and is useful on its own as a
//!   standalone kernel-typed fact about rational ordering at zero.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.le_refl_zero` lemma (#3551).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_le_refl_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_le_refl_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_le_refl_zero_init {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.le_refl + Rat.le

        self.register_rat_le_refl_zero()?;

        self.nn_verify_tier_a_rat_le_refl_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.le_refl_zero : Rat.le Rat.zero Rat.zero`.
    ///
    /// Proof: `Rat.le_refl Rat.zero`. Closure: `Rat.le_refl`
    /// (foundational axiom), `Rat.zero` (definition), `Rat.le`
    /// (definition). Zero non-foundational axioms.
    fn register_rat_le_refl_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.le_refl_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // Type: `Rat.le Rat.zero Rat.zero`.
        let ty = Expr::apps(rat_le, [rat_zero.clone(), rat_zero.clone()]);

        // Proof term: `Rat.le_refl Rat.zero`.
        let value = {
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            Expr::app(le_refl, rat_zero)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.le_refl_zero` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_le_refl_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_le_refl_zero_init
    }
}
