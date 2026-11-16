// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The inference meter — the **validated-never-proved** disclosure channel.
//!
//! Honesty rail 2 (the cardinal-error rule): the inference meter is reported
//! **side by side** with the proof-depth meter, and is **never fused** with it.
//! It counts spec/binding facts that were *inferred* (modeled here as
//! [`trust_ir_contract::TrustSpecVariableOrigin::Inferred`]) and carries a
//! standing **faithfulness obligation** (the obligation that the inferred facts
//! truly reflect source intent — a VALIDATION, not a proof).
//!
//! No number of oracle passes ever empties the meter: oracle/runtime evidence
//! caps at [`AssuranceLevel::RuntimeObserved`] (rail 6). Crucially, the meter is
//! **NEVER a gate** for a `*Certified*` label — it is pure disclosure. See
//! [`crate::badge::compute_badge`] for the gate (which omits the meter by design).

use trust_ir_contract::{AssuranceLevel, TrustSpecVariableOrigin};

/// Tracks inferred bindings and the standing faithfulness obligation.
///
/// Reported alongside (never combined with) the proof-depth meter.
#[derive(Debug, Clone, Default)]
pub struct InferenceMeter {
    /// Count of bindings whose origin was [`TrustSpecVariableOrigin::Inferred`].
    inferred: usize,
    /// Whether a standing faithfulness obligation is open. Validated, never
    /// proved; no oracle pass discharges it.
    faithfulness_obligation_open: bool,
}

impl InferenceMeter {
    /// A fresh meter: zero inferred bindings, faithfulness obligation closed.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one binding. Only [`TrustSpecVariableOrigin::Inferred`] origins
    /// increment the meter and open the standing faithfulness obligation;
    /// `Local`/`Quantified` origins are concrete and leave the meter untouched.
    pub fn record_inferred(&mut self, origin: &TrustSpecVariableOrigin) {
        if matches!(origin, TrustSpecVariableOrigin::Inferred) {
            // Saturating: the count is a meter, and a wrapped `usize` would read
            // as zero inferred bindings (`is_empty`) with the obligation open.
            self.inferred = self.inferred.saturating_add(1);
            self.faithfulness_obligation_open = true;
        }
    }

    /// Count of inferred bindings recorded.
    #[must_use]
    pub fn count(&self) -> usize {
        self.inferred
    }

    /// True when no inferred bindings have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inferred == 0
    }

    /// True when a standing faithfulness obligation is open (validated, never
    /// proved; not dischargeable by oracle passes).
    #[must_use]
    pub fn faithfulness_obligation_open(&self) -> bool {
        self.faithfulness_obligation_open
    }

    /// The assurance ceiling for inference/oracle evidence: it can never rise
    /// above [`AssuranceLevel::RuntimeObserved`] (rail 6). No number of oracle
    /// passes lifts this cap, and `RuntimeObserved` can never satisfy a
    /// `Certified` requirement.
    ///
    /// The cap is an INVARIANT of the meter, not a per-instance value, so it is an
    /// associated function (takes no `&self`).
    #[must_use]
    pub fn cap() -> AssuranceLevel {
        AssuranceLevel::RuntimeObserved
    }
}

#[cfg(test)]
mod saturation_tests {
    use super::InferenceMeter;
    use trust_ir_contract::TrustSpecVariableOrigin;

    /// Regression (Trust verified lane, 2026-10-02): `record_inferred` once did
    /// `inferred += 1`, which panics in a checked build and wraps to zero in an
    /// unchecked one -- after which `is_empty()` would report no inferred
    /// bindings while the faithfulness obligation stays open. It saturates now.
    #[test]
    fn record_inferred_saturates_instead_of_wrapping() {
        let mut m = InferenceMeter {
            inferred: usize::MAX,
            faithfulness_obligation_open: true,
        };
        m.record_inferred(&TrustSpecVariableOrigin::Inferred);
        assert_eq!(m.count(), usize::MAX);
        assert!(!m.is_empty());
        assert!(m.faithfulness_obligation_open());
    }
}
