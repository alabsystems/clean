// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Lane-agnostic verdict source** — the read-side contract the targeter (and a
//! future incremental-retry driver) needs from any import lane: *which items did
//! the kernel accept, and for the rest, why were they rejected?*
//!
//! # Why a trait
//!
//! The Isabelle lane persists verdicts in a replay SNAPSHOT (the v6 wire format,
//! whose `closure` keys are the accepted serials); the Coq lane persists them in
//! a `kernel-verified.json` [`KernelVerifiedManifest`] (accepted names) plus the
//! import report's `axiom_fallback_names` / `failures` (rejected names +
//! reasons). Both answer the same two questions, so the reusable infra takes a
//! [`VerdictSource`] and never hard-codes a wire format.
//!
//! The two questions are exactly what [`crate::replay_infra::targets`] consumes:
//! `accepted()` splits the corpus into accepted vs rejected, and
//! `reason(&id)` joins a diagnostic onto each ranked gatekeeper.
//!
//! # Scope of this extraction
//!
//! This module extracts only the *read* side (accepted set + reason join), which
//! is genuinely lane-agnostic and immediately drives the targeter for both lanes.
//! The *write* side of incremental retry — re-running the verifier over ONLY the
//! rejected subset and merging fresh verdicts — is lane-coupled (the Isabelle
//! streaming driver freezes/refreshes five translator registries; the Coq driver
//! runs `verify_corpus_incremental` over a merged library). That call stays in
//! each lane's driver; see `docs/analysis/replay-infra-lanes.md` for the exact
//! one-function contract the Coq lane adds when it opts in.

use std::collections::HashSet;
use std::hash::Hash;

/// The read-side verdict record of a completed import round, keyed by an opaque
/// item id (`i64` serial for Isabelle, `String` name for Coq).
pub trait VerdictSource {
    /// The item id type — `Eq + Hash + Clone` so the targeter can index it.
    type Id: Eq + Hash + Clone;

    /// The set of items the kernel ACCEPTED (`KernelVerified`). Everything else
    /// present in the corpus is REJECTED.
    fn accepted(&self) -> HashSet<Self::Id>;

    /// A human-readable rejection reason for `id`, when the record carries one
    /// (e.g. the kernel error joined from `axiom_fallback_names`). `None` when
    /// the item verified, or the record has no reason for it.
    fn reason(&self, id: &Self::Id) -> Option<String> {
        let _ = id;
        None
    }

    /// An optional short signature/bucket for `id` (e.g. an error-shape family
    /// used to group gatekeepers). `None` by default.
    fn signature(&self, id: &Self::Id) -> Option<String> {
        let _ = id;
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    struct Fixture {
        acc: HashSet<i64>,
        reasons: HashMap<i64, String>,
    }
    impl VerdictSource for Fixture {
        type Id = i64;
        fn accepted(&self) -> HashSet<i64> {
            self.acc.clone()
        }
        fn reason(&self, id: &i64) -> Option<String> {
            self.reasons.get(id).cloned()
        }
    }

    #[test]
    fn test_verdict_source_defaults_and_lookup() {
        let f = Fixture {
            acc: [1, 2].into_iter().collect(),
            reasons: [(9, "kernel-reject".to_string())].into_iter().collect(),
        };
        assert_eq!(f.accepted(), [1, 2].into_iter().collect());
        assert_eq!(f.reason(&9).as_deref(), Some("kernel-reject"));
        assert_eq!(f.reason(&1), None);
        assert_eq!(f.signature(&9), None, "default signature is None");
    }
}
