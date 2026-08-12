// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural network verification foundation axioms for Environment
//!
//! This module provides the foundational types and axioms for
//! formalizing neural network verification:
//! - Interval arithmetic ([l, u] closed intervals)
//! - Affine layers (W*x + b)
//! - Linear networks (compositions of affine layers)
//! - Interval Bound Propagation (IBP)
//! - IBP soundness
//!
//! These axioms formalize the mathematical structures used in
//! bound propagation methods (CROWN, alpha-CROWN, beta-CROWN) as
//! implemented in gamma-crown.
//!
//! Reference: Xu et al., "Fast and Complete Verification of Neural
//! Networks" (alpha,beta-CROWN). Source: ~/alpha-beta-CROWN-ref/

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Interval arithmetic axiom names.
const INTERVAL_AXIOMS: &[&str] = &[
    "NNVerification.Interval",
    "NNVerification.interval_le",
    "NNVerification.interval_contains",
    "NNVerification.interval_add",
    "NNVerification.interval_smul",
    "NNVerification.interval_width",
    "NNVerification.interval_width_nonneg",
    "NNVerification.interval_add_width",
];

/// Affine layer axiom names.
const AFFINE_AXIOMS: &[&str] = &[
    "NNVerification.AffineLayer",
    "NNVerification.affine_apply",
    "NNVerification.affine_compose",
    "NNVerification.affine_compose_apply",
    "NNVerification.affine_compose_assoc",
    "NNVerification.affine_identity",
    "NNVerification.affine_identity_apply",
];

/// Linear network axiom names.
const LINEAR_NETWORK_AXIOMS: &[&str] = &[
    "NNVerification.LinearNetwork",
    "NNVerification.linear_network_apply",
    "NNVerification.linear_network_single",
    "NNVerification.linear_network_cons",
    "NNVerification.linear_network_to_affine",
    "NNVerification.linear_network_apply_eq_affine",
];

/// IBP (Interval Bound Propagation) axiom names.
const IBP_AXIOMS: &[&str] = &[
    "NNVerification.IBP",
    "NNVerification.ibp_affine",
    "NNVerification.ibp_soundness",
    "NNVerification.ibp_affine_width",
    "NNVerification.ibp_compose",
    "NNVerification.ibp_linear_network",
    "NNVerification.ibp_linear_network_soundness",
];

impl Environment {
    /// Initialize NNVerification foundation axioms.
    ///
    /// Provides the core mathematical structures for neural network
    /// verification via bound propagation. See module docs for details.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nn_verification_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verification(&mut self) -> Result<(), EnvError> {
        if self.nn_verification_init {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_field()?;
        self.init_algebra_linear()?;

        self.add_nn_verification_axioms()?;
        self.nn_verification_init = true;
        Ok(())
    }

    /// Register all NN verification foundation axioms.
    fn add_nn_verification_axioms(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        let all_axioms = INTERVAL_AXIOMS
            .iter()
            .chain(AFFINE_AXIOMS)
            .chain(LINEAR_NETWORK_AXIOMS)
            .chain(IBP_AXIOMS);

        for name in all_axioms {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }
        Ok(())
    }

    /// Check if NNVerification foundation has been initialized.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn has_nn_verification(&self) -> bool {
        self.nn_verification_init
    }
}
