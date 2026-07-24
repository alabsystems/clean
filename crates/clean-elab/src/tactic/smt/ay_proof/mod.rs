// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay tactics with proof certificates (DRAT/LRAT).
//!
//! These tactics accept proof certificates from Ay and verify them
//! before reconstructing kernel-checkable proof terms or recovering through the
//! shared bridge/superposition fallback lane.
//!
//! Module layout:
//! - `entrypoints`: public DRAT/LRAT certificate entrypoints and shared pipeline
//! - `selection`: certificate proof-selection and recovery policy

mod entrypoints;
mod selection;

pub use entrypoints::{ay_decide_with_lrat_proof, ay_decide_with_proof};

#[cfg(all(test, feature = "ay-smt"))]
pub(super) use selection::select_verified_certificate_proof_for_test;

use super::ay_types::AyConfig;
use crate::tactic::drat::CnfFormula;
use clean_auto::bridge::ay_contract::AyLogic;

/// Configuration for Ay tactics with proof certificates
#[derive(Debug, Clone)]
#[must_use]
pub struct AyProofConfig {
    /// Base Ay configuration
    base: AyConfig,
    /// Explicit logic used to classify strict-policy behavior for this
    /// certificate request.
    logic: AyLogic,
    /// The CNF formula (encoded goal)
    formula: CnfFormula,
}

impl AyProofConfig {
    /// Build a certificate request with an explicit logic classification.
    pub fn new(base: AyConfig, logic: AyLogic, formula: CnfFormula) -> Self {
        Self {
            base,
            logic,
            formula,
        }
    }

    pub fn base(&self) -> &AyConfig {
        &self.base
    }

    #[must_use]
    pub fn logic(&self) -> AyLogic {
        self.logic
    }

    #[must_use]
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }
}
