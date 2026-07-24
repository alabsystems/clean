// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eq (equality) type initialization for Environment.
//!
//! Registers the Eq inductive type and all derived declarations:
//! - Eq.rec, Eq.casesOn, Eq.recOn (recursor repair)
//! - rfl, Eq.symm, Eq.trans (basic lemmas)
//! - Eq.ndrec, Eq.ndrecOn, Eq.subst, cast, Eq.mp, Eq.mpr (transport)
//! - congrArg, congrFun, congrFun', congr (congruence)

mod basic;
mod congr;
mod congruence;
pub(crate) mod context;
mod recursors;
mod transport;

use super::EnvError;
use super::Environment;
use context::EqCtx;

impl Environment {
    /// Initialize the Eq (equality) inductive type and all derived declarations.
    ///
    /// Safe to call multiple times (subsequent calls are no-ops).
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_eq() == true`
    /// ENSURES: Idempotent
    pub fn init_eq(&mut self) -> Result<(), EnvError> {
        if self.eq_init {
            return Ok(());
        }

        let ctx = EqCtx::new();

        recursors::register(self, &ctx)?;
        basic::register(self, &ctx)?;
        transport::register(self, &ctx)?;
        congruence::register(self, &ctx)?;

        self.eq_init = true;

        // Inductives may legitimately have been initialized before equality in
        // a lightweight environment. Their generated `noConfusion{Type}` pair
        // mentions `Eq`, so the initial strict validation fails closed and
        // leaves `StructuralOnly` provenance. Now that the complete equality
        // surface exists, reconstruct every such kernel-generated pair and
        // fresh-check both exact declarations. The regeneration path upgrades
        // neither member unless both checks succeed.
        self.regenerate_missing_no_confusion();
        Ok(())
    }

    /// Check if Eq type has been initialized.
    #[allow(dead_code)] // Used by 60+ test assertions; dead in non-test builds
    pub(crate) fn has_eq(&self) -> bool {
        self.eq_init
    }
}
