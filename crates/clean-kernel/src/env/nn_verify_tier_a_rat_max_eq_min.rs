// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.max_eq_min_zero_zero`.
//!
//! Transitive combination of `max_zero_zero` and `zero_eq_min_zero_zero`.
//! Lets downstream rewriters collapse `max 0 0 = min 0 0` without routing
//! through explicit `Rat.zero`.
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.max_eq_min_zero_zero
//!     : Eq Rat (Rat.max Rat.zero Rat.zero) (Rat.min Rat.zero Rat.zero)`
//!
//!   Proof term:
//!   `@Eq.trans.{1} Rat (Rat.max Rat.zero Rat.zero) Rat.zero
//!       (Rat.min Rat.zero Rat.zero)
//!       NNVerify.Rat.max_zero_zero NNVerify.Rat.zero_eq_min_zero_zero`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `max_eq_min_zero_zero` lemma (#3551).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success,
    /// `self.nn_verify_tier_a_rat_max_eq_min_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_max_eq_min(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_max_eq_min_init {
            return Ok(());
        }
        self.init_nn_verify_ibp_width_zero()?; // NNVerify.Rat.max_zero_zero
        self.init_nn_verify_tier_a_rat_zero_eq_min()?; // NNVerify.Rat.zero_eq_min_zero_zero
        self.init_eq()?; // Eq.trans

        self.register_rat_max_eq_min_zero_zero()?;

        self.nn_verify_tier_a_rat_max_eq_min_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.max_eq_min_zero_zero
    ///     : Eq Rat (Rat.max Rat.zero Rat.zero) (Rat.min Rat.zero Rat.zero)`.
    ///
    /// Proof:
    /// `@Eq.trans.{1} Rat (Rat.max 0 0) Rat.zero (Rat.min 0 0)
    ///     NNVerify.Rat.max_zero_zero NNVerify.Rat.zero_eq_min_zero_zero`.
    fn register_rat_max_eq_min_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.max_eq_min_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
        let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let max_zz = Expr::apps(rat_max, [rat_zero.clone(), rat_zero.clone()]);
        let min_zz = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);

        // Type: Eq Rat (Rat.max 0 0) (Rat.min 0 0)
        let ty = Expr::apps(eq, [rat.clone(), max_zz.clone(), min_zz.clone()]);

        // Proof term:
        // @Eq.trans.{1} Rat (max 0 0) Rat.zero (min 0 0) max_zero_zero zero_eq_min.
        let value = {
            let eq_trans = Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            );
            let hab = Expr::const_(Name::from_string("NNVerify.Rat.max_zero_zero"), vec![]);
            let hbc = Expr::const_(
                Name::from_string("NNVerify.Rat.zero_eq_min_zero_zero"),
                vec![],
            );
            Expr::apps(eq_trans, [rat, max_zz, rat_zero, min_zz, hab, hbc])
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `max_eq_min_zero_zero` has been initialized.
    pub(crate) fn has_nn_verify_tier_a_rat_max_eq_min(&self) -> bool {
        self.nn_verify_tier_a_rat_max_eq_min_init
    }
}
