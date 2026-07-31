// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.min_zero_zero`.
//!
//! Mirrors the `NNVerify.Rat.max_zero_zero` pattern established in
//! `nn_verify_ibp_width_zero.rs` (#3490 T4). `Rat.min`, `Rat.min_def`, and
//! `Rat.le_refl` are all in `FOUNDATIONAL_AXIOMS` (see
//! `crates/clean-kernel/src/env/axiom_audit.rs`), so a theorem whose proof
//! term is `@Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)` has an
//! empty non-foundational axiom closure and flows into the
//! `clean-native.mathverse` shard as `ProofQuality::Constructive`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.min_zero_zero : Eq Rat (Rat.min Rat.zero Rat.zero) Rat.zero`
//!
//!   Proof term: `@Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
//!
//!   `Rat.min_def : ∀ a b, Rat.le a b → Eq (Rat.min a b) a` — specializing
//!   at `a = b = Rat.zero` with the witness `Rat.le_refl Rat.zero` gives
//!   the desired equality. Symmetric to `Rat.max_zero_zero` which uses
//!   `Rat.max_def : ∀ a b, Rat.le a b → Eq (Rat.max a b) b`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage)
//! - Mirrors #3490 T4 precedent

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.min_zero_zero` lemma (#3551).
    ///
    /// Registers `NNVerify.Rat.min_zero_zero` as a sorry-free
    /// `Declaration::Theorem` with proof term
    /// `@Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_min_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_min_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_min_zero_init {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.le_refl
        self.init_rat_minmax()?; // Rat.min, Rat.min_def

        self.register_rat_min_zero_zero()?;

        self.nn_verify_tier_a_rat_min_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.min_zero_zero : Eq Rat (Rat.min Rat.zero Rat.zero) Rat.zero`.
    ///
    /// Proof (sorry-free `Declaration::Theorem`):
    /// `@Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)`. Closure:
    /// `Rat.min_def` (foundational axiom), `Rat.le_refl` (foundational
    /// axiom), `Rat.zero` (definition), `Eq` (foundational). Zero
    /// non-foundational axioms.
    fn register_rat_min_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.min_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Type: Eq Rat (Rat.min Rat.zero Rat.zero) Rat.zero
        let ty = {
            let min_zz = Expr::apps(rat_min.clone(), [rat_zero.clone(), rat_zero.clone()]);
            Expr::apps(eq, [rat, min_zz, rat_zero.clone()])
        };

        // Proof term: @Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero).
        let value = {
            let min_def = Expr::const_(Name::from_string("Rat.min_def"), vec![]);
            let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
            let h = Expr::app(le_refl, rat_zero.clone());
            Expr::apps(min_def, [rat_zero.clone(), rat_zero.clone(), h])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.min_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_min_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_min_zero_init
    }
}
