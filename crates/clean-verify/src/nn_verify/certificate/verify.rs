// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic certificate verification framework for NN verification.
//!
//! Provides a method-agnostic API for verifying certificate chains,
//! checking bound containment via interval arithmetic, and producing
//! structured verification reports. Built on top of the per-layer
//! [`CertificateEntry`] and [`CertificateChain`] types from [`super::chain`].
//!
//! ## Proof obligations
//!
//! - C01: Chain continuity (each layer output matches next layer input)
//! - C02: Chain coverage (chain spans from network input to network output)
//! - C03: Bound soundness (claimed output bounds contain all reachable outputs)

use std::fmt;
use std::time::Duration;

use super::chain::{
    chain_trust_level, verify_chain_continuity, CertificateChain, CertificateEntry, ChainTrustLevel,
};
use crate::spec::ProofStatus;

/// Tolerance for floating-point comparisons.
const EPSILON: f64 = 1e-9;

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

/// C01: chain_continuity — every layer's output matches the next layer's input.
pub const C01_CHAIN_CONTINUITY: ProofStatus = ProofStatus::DerivedPending;

/// C02: chain_coverage — the chain spans from network input to network output.
pub const C02_CHAIN_COVERAGE: ProofStatus = ProofStatus::DerivedPending;

/// C03: bound_soundness — claimed output bounds contain all reachable outputs.
pub const C03_BOUND_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Overall status of a certificate verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificateStatus {
    /// Certificate is valid — all checks passed.
    Valid,
    /// Certificate is invalid — at least one check failed.
    Invalid { reason: String },
    /// Verification could not determine validity (e.g., missing data).
    Inconclusive,
}

impl fmt::Display for CertificateStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Valid => write!(f, "Valid"),
            Self::Invalid { reason } => write!(f, "Invalid: {reason}"),
            Self::Inconclusive => write!(f, "Inconclusive"),
        }
    }
}

/// A structured verification report for a certificate or certificate chain.
#[derive(Debug, Clone)]
#[must_use]
pub struct VerificationReport {
    /// Per-layer status (indexed by position in chain, not layer_index).
    pub layer_statuses: Vec<CertificateStatus>,
    /// Overall status of the chain.
    pub overall_status: CertificateStatus,
    /// Aggregated trust level (minimum across all layers).
    pub trust_level: ChainTrustLevel,
    /// Fraction of layers that verified as `Valid` (0.0..=1.0).
    pub coverage: f64,
    /// Wall-clock time spent verifying, if measured.
    pub elapsed: Option<Duration>,
    /// Human-readable notes accumulated during verification.
    pub notes: Vec<String>,
}

/// A simple classification specification: for all inputs in the certified
/// region, output dimension `dominant_class` exceeds output dimension
/// `other_class` by at least `margin`.
#[derive(Debug, Clone)]
pub struct ClassificationSpec {
    /// The output index that must dominate.
    pub dominant_class: usize,
    /// The output index that must be dominated.
    pub other_class: usize,
    /// Minimum required margin (dominant - other >= margin).
    pub margin: f64,
}

// ---------------------------------------------------------------------------
// Single-layer verification
// ---------------------------------------------------------------------------

/// Verify a single layer certificate entry.
///
/// Checks:
/// 1. Input and output bounds are well-formed (lower <= upper per dimension).
/// 2. Dimensions are non-zero.
/// 3. For `IBP` / `CROWN` / `AlphaCROWN`, bounds must be finite.
#[must_use]
pub fn verify_layer_certificate(entry: &CertificateEntry) -> CertificateStatus {
    if entry.input_bounds.is_empty() || entry.output_bounds.is_empty() {
        return CertificateStatus::Invalid {
            reason: "empty bounds".to_owned(),
        };
    }

    for (i, &(lo, hi)) in entry.input_bounds.iter().enumerate() {
        if lo > hi + EPSILON {
            return CertificateStatus::Invalid {
                reason: format!("input dim {i}: lower ({lo}) > upper ({hi})"),
            };
        }
        if !lo.is_finite() || !hi.is_finite() {
            return CertificateStatus::Invalid {
                reason: format!("input dim {i}: non-finite bound"),
            };
        }
    }

    for (i, &(lo, hi)) in entry.output_bounds.iter().enumerate() {
        if lo > hi + EPSILON {
            return CertificateStatus::Invalid {
                reason: format!("output dim {i}: lower ({lo}) > upper ({hi})"),
            };
        }
        if !lo.is_finite() || !hi.is_finite() {
            return CertificateStatus::Invalid {
                reason: format!("output dim {i}: non-finite bound"),
            };
        }
    }

    CertificateStatus::Valid
}

// ---------------------------------------------------------------------------
// Chain verification
// ---------------------------------------------------------------------------

/// Verify a full certificate chain.
///
/// Performs continuity, per-layer validation, and trust consistency checks.
/// Returns a [`VerificationReport`] with per-layer and overall status.
pub fn verify_chain_certificate(chain: &CertificateChain) -> VerificationReport {
    let start = std::time::Instant::now();
    let mut notes = Vec::new();

    if chain.entries.is_empty() {
        return VerificationReport {
            layer_statuses: Vec::new(),
            overall_status: CertificateStatus::Invalid {
                reason: "empty chain".to_owned(),
            },
            trust_level: ChainTrustLevel::Formal,
            coverage: 0.0,
            elapsed: Some(start.elapsed()),
            notes: vec!["chain has no entries".to_owned()],
        };
    }

    // Per-layer verification.
    let layer_statuses: Vec<CertificateStatus> =
        chain.entries.iter().map(verify_layer_certificate).collect();

    let valid_count = layer_statuses
        .iter()
        .filter(|s| matches!(s, CertificateStatus::Valid))
        .count();
    let total = layer_statuses.len();
    let coverage = valid_count as f64 / total as f64;

    // Continuity check.
    let continuous = verify_chain_continuity(chain);
    if !continuous {
        notes.push("chain is not continuous: layer bound mismatch".to_owned());
    }

    // Trust level.
    let trust_level = chain_trust_level(chain);

    // Overall status.
    let overall_status = if valid_count == total && continuous {
        CertificateStatus::Valid
    } else if valid_count == 0 {
        CertificateStatus::Invalid {
            reason: "all layers failed verification".to_owned(),
        }
    } else if !continuous {
        CertificateStatus::Invalid {
            reason: "chain continuity check failed".to_owned(),
        }
    } else {
        CertificateStatus::Invalid {
            reason: format!("{} of {total} layers failed", total - valid_count),
        }
    };

    VerificationReport {
        layer_statuses,
        overall_status,
        trust_level,
        coverage,
        elapsed: Some(start.elapsed()),
        notes,
    }
}

// ---------------------------------------------------------------------------
// Bound containment
// ---------------------------------------------------------------------------

/// Check that `inner` bounds are contained within `outer` bounds per dimension.
///
/// Uses interval arithmetic: for each dimension, `outer.lo <= inner.lo` and
/// `inner.hi <= outer.hi` (within tolerance).
///
/// Returns `true` if `inner` is fully contained in `outer`.
#[must_use]
pub fn verify_bound_containment(inner: &[(f64, f64)], outer: &[(f64, f64)]) -> bool {
    if inner.len() != outer.len() {
        return false;
    }
    inner
        .iter()
        .zip(outer.iter())
        .all(|(&(i_lo, i_hi), &(o_lo, o_hi))| o_lo <= i_lo + EPSILON && i_hi <= o_hi + EPSILON)
}

// ---------------------------------------------------------------------------
// Trust consistency
// ---------------------------------------------------------------------------

/// Verify that a claimed overall trust level is the minimum across all
/// layer trust levels in the chain.
///
/// Returns `true` when `claimed` equals the actual minimum trust.
#[must_use]
pub fn verify_trust_consistency(chain: &CertificateChain, claimed: ChainTrustLevel) -> bool {
    chain_trust_level(chain) == claimed
}

// ---------------------------------------------------------------------------
// Specification verification
// ---------------------------------------------------------------------------

/// Verify that the certificate proves a classification specification.
///
/// For the spec `dominant_class > other_class + margin`, we check the
/// worst-case bounds: the *minimum* of the dominant output must exceed the
/// *maximum* of the other output by at least `margin`.
///
/// The chain must have at least one entry and the last entry's output must
/// have sufficient dimensions.
#[must_use]
pub fn verify_specification(
    chain: &CertificateChain,
    spec: &ClassificationSpec,
) -> CertificateStatus {
    let last = match chain.entries.last() {
        Some(e) => e,
        None => {
            return CertificateStatus::Invalid {
                reason: "empty chain".to_owned(),
            }
        }
    };

    let out = &last.output_bounds;
    if spec.dominant_class >= out.len() || spec.other_class >= out.len() {
        return CertificateStatus::Invalid {
            reason: format!(
                "spec references output dims {}/{} but chain has {} outputs",
                spec.dominant_class,
                spec.other_class,
                out.len(),
            ),
        };
    }

    let dominant_min = out[spec.dominant_class].0; // worst-case low
    let other_max = out[spec.other_class].1; // worst-case high

    if dominant_min >= other_max + spec.margin - EPSILON {
        CertificateStatus::Valid
    } else {
        CertificateStatus::Invalid {
            reason: format!(
                "dominant min ({dominant_min}) < other max ({other_max}) + margin ({})",
                spec.margin,
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Report merging
// ---------------------------------------------------------------------------

/// Merge two verification reports (e.g., for sub-networks verified separately).
///
/// The merged report concatenates layer statuses, takes the minimum trust,
/// and combines coverage as a weighted average by layer count.
pub fn merge_reports(a: &VerificationReport, b: &VerificationReport) -> VerificationReport {
    let mut layer_statuses = a.layer_statuses.clone();
    layer_statuses.extend(b.layer_statuses.iter().cloned());

    let total_a = a.layer_statuses.len() as f64;
    let total_b = b.layer_statuses.len() as f64;
    let total = total_a + total_b;
    let coverage = if total > 0.0 {
        (a.coverage * total_a + b.coverage * total_b) / total
    } else {
        0.0
    };

    let trust_level = std::cmp::min(a.trust_level, b.trust_level);

    let overall_status = match (&a.overall_status, &b.overall_status) {
        (CertificateStatus::Valid, CertificateStatus::Valid) => CertificateStatus::Valid,
        (CertificateStatus::Invalid { reason }, _) => CertificateStatus::Invalid {
            reason: reason.clone(),
        },
        (_, CertificateStatus::Invalid { reason }) => CertificateStatus::Invalid {
            reason: reason.clone(),
        },
        _ => CertificateStatus::Inconclusive,
    };

    let elapsed = match (a.elapsed, b.elapsed) {
        (Some(da), Some(db)) => Some(da + db),
        (Some(d), None) | (None, Some(d)) => Some(d),
        (None, None) => None,
    };

    let mut notes = a.notes.clone();
    notes.extend(b.notes.iter().cloned());

    VerificationReport {
        layer_statuses,
        overall_status,
        trust_level,
        coverage,
        elapsed,
        notes,
    }
}

// ---------------------------------------------------------------------------
// Report summary
// ---------------------------------------------------------------------------

/// Generate a human-readable summary of a verification report.
#[must_use]
pub fn report_summary(report: &VerificationReport) -> String {
    let n = report.layer_statuses.len();
    let valid = report
        .layer_statuses
        .iter()
        .filter(|s| matches!(s, CertificateStatus::Valid))
        .count();
    let elapsed_str = report
        .elapsed
        .map_or_else(|| "N/A".to_owned(), |d| format!("{d:?}"));

    let mut s = format!(
        "VerificationReport: status={}, trust={}, layers={valid}/{n}, \
         coverage={:.1}%, elapsed={}",
        report.overall_status,
        report.trust_level,
        report.coverage * 100.0,
        elapsed_str,
    );

    for note in &report.notes {
        s.push_str(&format!("\n  note: {note}"));
    }

    s
}

// ---------------------------------------------------------------------------
// Certificate strength
// ---------------------------------------------------------------------------

/// Quantify the tightness of the output bounds relative to a bounding box.
///
/// For each dimension, the ratio is `(cert_hi - cert_lo) / (box_hi - box_lo)`.
/// The overall strength is `1.0 - mean(ratio)`, so `1.0` means the certificate
/// collapses every dimension to a point, and `0.0` means it is no tighter
/// than the bounding box.
///
/// Returns `None` if `bounding_box` has a zero-width dimension or the
/// dimensions do not match.
#[must_use]
pub fn certificate_strength(
    certified_bounds: &[(f64, f64)],
    bounding_box: &[(f64, f64)],
) -> Option<f64> {
    if certified_bounds.len() != bounding_box.len() || certified_bounds.is_empty() {
        return None;
    }

    let mut ratio_sum = 0.0;
    for (&(c_lo, c_hi), &(b_lo, b_hi)) in certified_bounds.iter().zip(bounding_box.iter()) {
        let box_width = b_hi - b_lo;
        if box_width < EPSILON {
            return None;
        }
        let cert_width = (c_hi - c_lo).max(0.0);
        ratio_sum += cert_width / box_width;
    }

    let mean_ratio = ratio_sum / certified_bounds.len() as f64;
    Some((1.0 - mean_ratio).clamp(0.0, 1.0))
}
