// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification phase — the temporal scope of a trust claim.
//!
//! Honesty rail 1 / rail 7: a *static-universal* claim is a proof that holds
//! for **every** execution within the modeled fragment, discharged to a formal
//! ISA (modulo named axioms). Any check that only observes a particular run —
//! including **every oracle pass** and every runtime/faithfulness observation —
//! is a [`Phase::RuntimeInstance`] check and must **never** masquerade as
//! [`Phase::StaticUniversal`]. The phase gate is the structural guard that keeps
//! a runtime-instance result from being relabeled as a universal proof.

use serde::{Deserialize, Serialize};

/// The temporal scope a verification result is allowed to claim.
///
/// `#[non_exhaustive]`: new phases may be added (e.g. distributed-replay) without
/// breaking downstream matches.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Phase {
    /// A proof that holds for every execution within the modeled fragment,
    /// discharged to the formal ISA modulo the named trusted models/axioms.
    /// Only this phase is eligible for a `RustCertifiedToBinary` label.
    StaticUniversal,
    /// A check that observed a particular execution (including every oracle pass
    /// and every faithfulness/runtime observation). Caps assurance at
    /// `RuntimeObserved`; can never be a static-universal proof.
    RuntimeInstance,
    /// A just-in-time certificate produced for a specific compiled instance.
    JitCert,
    /// A transitional check covering a patch/migration between two source states.
    PatchTransition,
}

impl Phase {
    /// True only for [`Phase::StaticUniversal`] — the sole phase eligible for a
    /// universal "certified to binary" claim. Every other phase is a
    /// per-instance / per-run observation.
    #[must_use]
    pub fn is_static_universal(self) -> bool {
        matches!(self, Self::StaticUniversal)
    }
}
