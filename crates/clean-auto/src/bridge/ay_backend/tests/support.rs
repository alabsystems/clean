// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for ay_backend tests.

use super::*;

pub(super) fn build_unsat_proof_backend(config: AyBackendConfig) -> AyProofBackend {
    let mut backend = AyProofBackend::with_config(config);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {} 0)", x));
    backend.assert_formula(&format!("(< {} 0)", x));
    backend
}
