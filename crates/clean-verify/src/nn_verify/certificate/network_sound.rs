// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge from verify-side certificate chains to kernel theorem T71
//! (`network_cert_sound`).
//!
//! The kernel proof (in `clean-kernel/src/env/nn_verify_network_proof.rs`)
//! establishes that chaining per-layer interval-subset certificates via
//! `chainSubsetBetween` yields a whole-network subset proof. This module
//! provides Rust-side verification that a floating-point certificate chain
//! satisfies the preconditions required to invoke T71.
//!
//! Part of #3242.

use super::chain::{
    chain_trust_level, verify_chain_continuity, CertificateChain, CertificateEntry, ChainTrustLevel,
};
use crate::spec::ProofStatus;

const EPSILON: f64 = 1e-9;

/// Proof status for T71: `network_cert_sound`.
///
/// The kernel proof is fully constructed and type-checked in
/// `clean-kernel/src/env/nn_verify_network_proof.rs`. It is sorry-free
/// and uses structural induction on the intermediates list, applying T70
/// (`entailment_transitivity`) at each cons step.
pub(crate) const T71_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub(crate) struct NetworkSoundnessResult {
    pub(crate) valid: bool,
    pub(crate) chain_length: usize,
    pub(crate) trust_level: ChainTrustLevel,
    pub(crate) proof_status: ProofStatus,
    pub(crate) errors: Vec<String>,
}

/// Check whether a certificate chain discharges the Rust-side obligations
/// required to appeal to kernel theorem T71 (`network_cert_sound`).
pub(crate) fn verify_network_cert_sound(
    chain: &CertificateChain,
    input_bounds: &[(f64, f64)],
    output_bounds: &[(f64, f64)],
) -> NetworkSoundnessResult {
    let mut errors = Vec::new();

    if chain.entries.is_empty() {
        errors.push("certificate chain is empty".to_owned());
    }

    for entry in &chain.entries {
        errors.extend(entry_bounds_errors(entry));
    }

    if !verify_chain_continuity(chain) {
        errors.push("certificate chain continuity failed".to_owned());
    }

    match (chain.entries.first(), chain.entries.last()) {
        (Some(first), Some(last)) => {
            errors.extend(endpoint_coverage_errors(
                first,
                last,
                input_bounds,
                output_bounds,
            ));
        }
        _ => errors.push("certificate chain does not cover requested bounds".to_owned()),
    }

    let valid = errors.is_empty();
    NetworkSoundnessResult {
        valid,
        chain_length: chain.entries.len(),
        trust_level: chain_trust_level(chain),
        proof_status: if valid {
            T71_PROOF_STATUS
        } else {
            ProofStatus::DerivedPending
        },
        errors,
    }
}

#[must_use]
fn entry_bounds_errors(entry: &CertificateEntry) -> Vec<String> {
    let mut errors = Vec::new();
    errors.extend(bounds_errors(
        &entry.input_bounds,
        &format!("layer {} input", entry.layer_index),
    ));
    errors.extend(bounds_errors(
        &entry.output_bounds,
        &format!("layer {} output", entry.layer_index),
    ));
    errors
}

#[must_use]
fn endpoint_coverage_errors(
    first: &CertificateEntry,
    last: &CertificateEntry,
    input_bounds: &[(f64, f64)],
    output_bounds: &[(f64, f64)],
) -> Vec<String> {
    let mut errors = Vec::new();
    errors.extend(matching_bounds_errors(
        &first.input_bounds,
        input_bounds,
        "network input coverage failed",
    ));
    errors.extend(matching_bounds_errors(
        &last.output_bounds,
        output_bounds,
        "network output coverage failed",
    ));
    errors
}

#[must_use]
fn matching_bounds_errors(
    actual: &[(f64, f64)],
    expected: &[(f64, f64)],
    context: &str,
) -> Vec<String> {
    if actual.len() != expected.len() {
        return vec![format!(
            "{context}: dimension mismatch (expected {}, got {})",
            expected.len(),
            actual.len()
        )];
    }

    let mut errors = Vec::new();
    for (dim, (&(actual_lo, actual_hi), &(expected_lo, expected_hi))) in
        actual.iter().zip(expected.iter()).enumerate()
    {
        if (actual_lo - expected_lo).abs() > EPSILON || (actual_hi - expected_hi).abs() > EPSILON {
            errors.push(format!(
                "{context}: dim {dim} mismatch, expected [{expected_lo}, {expected_hi}], got [{actual_lo}, {actual_hi}]"
            ));
        }
    }
    errors
}

#[must_use]
fn bounds_errors(bounds: &[(f64, f64)], context: &str) -> Vec<String> {
    let mut errors = Vec::new();
    for (dim, &(lo, hi)) in bounds.iter().enumerate() {
        if lo > hi + EPSILON {
            errors.push(format!(
                "{context} bounds malformed at dim {dim}: lower {lo} exceeds upper {hi}"
            ));
        }
    }
    errors
}
