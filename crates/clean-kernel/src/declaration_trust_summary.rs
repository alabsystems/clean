// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};

/// Summary of trust-bearing terms within a declaration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DeclarationTrustSummary {
    /// Whether the declaration contains an explicit/non-synthetic sorry.
    pub has_explicit_sorry: bool,
    /// Whether the declaration contains a synthetic sorry.
    pub has_synthetic_sorry: bool,
    /// Number of embedded `trustedArith` references.
    pub trusted_arith_count: usize,
    /// Number of embedded `trustedAy` references.
    pub trusted_ay_count: usize,
}
