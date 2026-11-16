// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strength enforcement — the structural guard for honesty rail 6.
//!
//! Oracle/runtime evidence caps at [`AssuranceLevel::RuntimeObserved`], and a
//! `RuntimeObserved` strength can **never** satisfy a `Certified` requirement.
//! We do not reimplement any ordering: we call the real
//! [`ProofStrength::satisfies_requirement`] from `trust-ir-contract`.

use trust_ir_contract::{AssuranceLevel, ProofStrength, ReasoningKind};

/// A `RuntimeObserved` proof strength produced by runtime monitoring (the cap an
/// oracle/runtime pass can reach).
#[must_use]
pub fn runtime_observed_strength() -> ProofStrength {
    ProofStrength {
        reasoning: ReasoningKind::RuntimeMonitoring,
        assurance: AssuranceLevel::RuntimeObserved,
    }
}

/// True when `evidence` is strong enough to satisfy `required`, delegating to the
/// real `trust-ir-contract` [`ProofStrength::satisfies_requirement`]. No
/// ordering is reimplemented here.
#[must_use]
pub fn evidence_satisfies(evidence: &ProofStrength, required: &ProofStrength) -> bool {
    evidence.satisfies_requirement(required)
}

/// Honesty rail 6, asserted via the real method: a `RuntimeObserved` strength can
/// never satisfy a `Certified` requirement. Returns `true` when the invariant
/// holds (i.e. runtime-observed does NOT satisfy the certified requirement).
#[must_use]
pub fn runtime_never_satisfies_certified() -> bool {
    let runtime = runtime_observed_strength();
    let certified_required = ProofStrength::certified(ReasoningKind::RuntimeMonitoring);
    !runtime.satisfies_requirement(&certified_required)
}
