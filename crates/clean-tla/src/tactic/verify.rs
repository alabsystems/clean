// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Descriptor-facing verification wrapper for `clean verify tla`.
//!
//! Split out of `tactic/mod.rs` so that file stays at its pre-existing size
//! (mod.rs is already over the 500-line budget; the no-growth check blocks
//! adding new functions to it). Added in Epic #3436 Phase 4 (#3452).

use super::{prove_tla_obligation, TlaAutoResult};
use crate::obligation::TlaObligation;

/// Verify a TLA+ obligation and surface the result as [`TlaAutoResult`].
///
/// Thin convenience wrapper over [`prove_tla_obligation`] that converts the
/// `ObligationResult` (used by TLAPS benchmark tooling) into the
/// `TlaAutoResult` shape expected by the `clean verify tla` CLI surface.
///
/// On success the `certificate` field (UTF-8 bytes of the kernel proof term)
/// is surfaced so callers can persist it; `tactics_tried` is propagated
/// verbatim so `--verbose` output reflects the exact dispatch path.
#[must_use]
pub fn verify_obligation(obligation: &TlaObligation) -> TlaAutoResult {
    let result = prove_tla_obligation(obligation);
    if result.proved {
        let certificate = result
            .certificate
            .map(String::into_bytes)
            .unwrap_or_default();
        TlaAutoResult::success(certificate, result.tactics_tried)
    } else {
        let error = result
            .error
            .unwrap_or_else(|| "proof search failed".to_string());
        TlaAutoResult::failure(&error, result.tactics_tried)
    }
}
