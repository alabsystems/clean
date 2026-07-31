// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A axiom-reject recovery (#3551): `NNVerify.Rat.neg_zero_zero`.
//!
//! Proves `Rat.neg Rat.zero = Rat.zero` constructively via kernel
//! reduction. `Rat.neg` is a reducible `Declaration::Definition` with
//! body `fun r => Rat.mk (Int.neg (Rat.num r)) (Rat.denom r)`
//! (algebra.rs line 271). `Rat.zero` is reducible
//! `Rat.mk Int.zero (Nat.succ Nat.zero)`. After δι reduction:
//!
//! ```text
//!   Rat.neg Rat.zero
//!     δ→ Rat.mk (Int.neg (Rat.num Rat.zero)) (Rat.denom Rat.zero)
//!     δι→ Rat.mk (Int.neg Int.zero) (Nat.succ Nat.zero)
//!     δι→ Rat.mk (Int.ofNat Nat.zero) (Nat.succ Nat.zero)
//!     (definitionally equal to)
//!   Rat.zero
//!     δ→ Rat.mk Int.zero (Nat.succ Nat.zero)
//!     δ→ Rat.mk (Int.ofNat Nat.zero) (Nat.succ Nat.zero)
//! ```
//!
//! Both sides share the same δι-normal form, so `Eq.refl Rat.zero`
//! inhabits `Rat.neg Rat.zero = Rat.zero`. No domain axioms are used;
//! only `Eq.refl` (foundational) plus the reducible definitions themselves
//! (`Rat.neg`, `Rat.num`, `Rat.denom`, `Rat.zero`, `Int.neg`, `Int.zero` —
//! none contribute axioms to the closure).
//!
//! ## Theorem (sorry-free `Declaration::Theorem`)
//!
//! - `NNVerify.Rat.neg_zero_zero : Rat.neg Rat.zero = Rat.zero`
//!
//!   Proof term: `@Eq.refl.{1} Rat Rat.zero`.
//!
//!   The kernel closes the equation by reducing both sides to the common
//!   δι-normal form `Rat.mk (Int.ofNat Nat.zero) (Nat.succ Nat.zero)`.
//!
//! ## Part of
//!
//! - #3551 (Tier A axiom-reject triage — zero-trio)

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Tier A `Rat.neg_zero_zero` lemma (#3551).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_rat_neg_zero_zero_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_rat_neg_zero_zero(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_rat_neg_zero_zero_init {
            return Ok(());
        }
        // Requires the reducible `Rat` carrier + `Rat.neg` + `Int.neg` +
        // `Rat.zero` definitions. `init_rat_arith` sets up Rat.neg / Rat.zero;
        // `init_int` brings in Int.neg / Int.zero. `init_eq` gives us Eq.refl.
        self.init_rat_arith()?;
        self.init_eq()?;

        self.register_rat_neg_zero_zero()?;

        self.nn_verify_tier_a_rat_neg_zero_zero_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.neg_zero_zero : Rat.neg Rat.zero = Rat.zero`.
    ///
    /// Proof term: `@Eq.refl.{1} Rat Rat.zero`.
    ///
    /// Closure: `Eq.refl` (foundational). Reducible definitions
    /// (`Rat.neg`, `Rat.num`, `Rat.denom`, `Rat.zero`, `Int.neg`, `Int.zero`)
    /// contribute zero axioms. Zero non-foundational axioms.
    fn register_rat_neg_zero_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.neg_zero_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let neg_zero = Expr::app(rat_neg, rat_zero.clone());

        // Type: Rat.neg Rat.zero = Rat.zero
        let ty = Expr::apps(eq, [rat.clone(), neg_zero, rat_zero.clone()]);

        // Proof: @Eq.refl.{1} Rat Rat.zero.  Kernel closes via δι reduction.
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let value = Expr::apps(eq_refl, [rat, rat_zero]);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Tier A `Rat.neg_zero_zero` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_rat_neg_zero_zero(&self) -> bool {
        self.nn_verify_tier_a_rat_neg_zero_zero_init
    }
}
