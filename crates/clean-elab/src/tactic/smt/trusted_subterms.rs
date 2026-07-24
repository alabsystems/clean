// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helpers for tracking embedded trusted sub-terms inside reconstructed proofs.
//!
//! When `ay-smt` is enabled, the canonical `count_embedded_trusted_ay_terms`
//! implementation is re-exported from `clean-auto::bridge::proof_trust` (the
//! bridge-level trust-accounting surface) so both crates count with identical
//! logic — the `debug_assert_eq` in `reconstruction_gate` is structurally
//! guaranteed rather than relying on duplicated visitor code.
//!
//! Without `ay-smt`, a local fallback keeps `record_embedded_trust_subterms_from_proof`
//! available for the DRAT/LRAT certificate path.

#[cfg(test)]
use crate::tactic::ProofState;
#[cfg(any(test, not(feature = "ay-smt")))]
use clean_kernel::Expr;

/// Re-export canonical implementation from clean-auto's bridge trust surface.
#[cfg(feature = "ay-smt")]
pub(crate) use clean_auto::bridge::proof_trust::count_embedded_trusted_ay_terms;

/// Fallback: standalone visitor for when ay-smt is not available.
#[cfg(not(feature = "ay-smt"))]
pub(crate) fn count_embedded_trusted_ay_terms(expr: &Expr) -> usize {
    use clean_kernel::{ExprVisitor, LevelVec, Name};

    struct TrustedAyConstCounter;

    impl ExprVisitor for TrustedAyConstCounter {
        type Result = usize;

        fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result {
            a + b
        }

        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
            if name.to_string() == "trustedAy" {
                1
            } else {
                0
            }
        }
    }

    let mut counter = TrustedAyConstCounter;
    counter.visit_expr(expr)
}

/// Mirror embedded `trustedAy` sub-terms from a proof term into the proof
/// state's trust ledger. Returns the number of recorded sub-terms.
#[cfg(test)]
pub(crate) fn record_embedded_trust_subterms_from_proof(
    state: &mut ProofState,
    proof: &Expr,
) -> usize {
    let trust_subterm_count = count_embedded_trusted_ay_terms(proof);
    if trust_subterm_count > 0 {
        let recorded_count = match u32::try_from(trust_subterm_count) {
            Ok(count) => count,
            Err(_) => {
                tracing::warn!(
                    trust_subterm_count,
                    "embedded trustedAy count exceeded u32 range; saturating proof-state accounting"
                );
                u32::MAX
            }
        };
        state.record_trusted_ay_unclassified(recorded_count);
    }
    if trust_subterm_count > 0 {
        tracing::info!(
            trust_subterm_count,
            "recorded embedded trustedAy sub-terms from reconstructed proof"
        );
    }
    trust_subterm_count
}
