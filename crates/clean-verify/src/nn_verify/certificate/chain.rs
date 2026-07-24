// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate chain verification for composing layer-by-layer NN verification
//! results.
//!
//! This module provides a high-level abstraction over per-layer verification
//! certificates, enabling:
//! - Continuity verification (each layer's input matches the previous output)
//! - Coverage verification (chain spans from network input to output)
//! - Trust level aggregation (minimum trust across the chain)
//! - Chain merging (composing two compatible chains)
//!
//! Unlike the lower-level `compositional` module which works with Farkas
//! multipliers and constraint systems, this module operates on abstract
//! verification method certificates suitable for any bound propagation
//! technique (IBP, CROWN, alpha-CROWN, McCormick, Zonotope, or mixed).

use std::fmt;

/// Tolerance for floating-point bound comparisons.
const EPSILON: f64 = 1e-9;

/// Trust level of a verification method, ordered from highest to lowest.
///
/// Determines the soundness guarantee of a certificate entry.
/// When composing chains, the overall trust is the minimum across entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ChainTrustLevel {
    /// Formally verified with machine-checked proof.
    Formal,
    /// Numerically verified with floating-point bounds (sound up to FP error).
    Numerical,
    /// Heuristic bound (no soundness guarantee).
    Heuristic,
}

impl PartialOrd for ChainTrustLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ChainTrustLevel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank().cmp(&other.rank())
    }
}

impl ChainTrustLevel {
    /// Numeric rank: higher is more trustworthy.
    fn rank(self) -> u8 {
        match self {
            Self::Formal => 2,
            Self::Numerical => 1,
            Self::Heuristic => 0,
        }
    }
}

impl fmt::Display for ChainTrustLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Formal => write!(f, "Formal"),
            Self::Numerical => write!(f, "Numerical"),
            Self::Heuristic => write!(f, "Heuristic"),
        }
    }
}

/// Verification method used for a certificate entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationMethod {
    /// Interval Bound Propagation.
    IBP,
    /// Convex Relaxation using linear bounds (CROWN).
    CROWN,
    /// Alpha-CROWN with optimized relaxation slopes.
    AlphaCROWN,
    /// McCormick relaxation for nonlinear activations.
    McCormick,
    /// Zonotope abstract domain.
    Zonotope,
    /// Mixed strategy combining multiple methods.
    Mixed,
}

impl fmt::Display for VerificationMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IBP => write!(f, "IBP"),
            Self::CROWN => write!(f, "CROWN"),
            Self::AlphaCROWN => write!(f, "alpha-CROWN"),
            Self::McCormick => write!(f, "McCormick"),
            Self::Zonotope => write!(f, "Zonotope"),
            Self::Mixed => write!(f, "Mixed"),
        }
    }
}

/// A single entry in a certificate chain, representing one layer's
/// verification result.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct CertificateEntry {
    /// Layer index in the network (0-based).
    pub layer_index: usize,
    /// Verification method used for this layer.
    pub method: VerificationMethod,
    /// Per-dimension input bounds as (lower, upper) pairs.
    pub input_bounds: Vec<(f64, f64)>,
    /// Per-dimension output bounds as (lower, upper) pairs.
    pub output_bounds: Vec<(f64, f64)>,
    /// Trust level of this entry's verification.
    pub trust_level: ChainTrustLevel,
}

/// A chain of certificate entries covering a (sub-)network.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct CertificateChain {
    /// Ordered list of per-layer certificate entries.
    pub entries: Vec<CertificateEntry>,
    /// Property being verified (human-readable description).
    pub property: String,
    /// Identifier for the network this chain applies to.
    pub network_id: String,
}

/// Verify that each layer's input bounds match the previous layer's output
/// bounds (within floating-point tolerance).
///
/// An empty or single-entry chain is trivially continuous.
#[must_use]
pub fn verify_chain_continuity(chain: &CertificateChain) -> bool {
    if chain.entries.len() <= 1 {
        return true;
    }

    for window in chain.entries.windows(2) {
        let prev = &window[0];
        let next = &window[1];

        if prev.output_bounds.len() != next.input_bounds.len() {
            return false;
        }

        for (&(prev_lo, prev_hi), &(next_lo, next_hi)) in
            prev.output_bounds.iter().zip(next.input_bounds.iter())
        {
            if (prev_lo - next_lo).abs() > EPSILON || (prev_hi - next_hi).abs() > EPSILON {
                return false;
            }
        }
    }

    true
}

/// Verify that the chain covers the specified input-to-output bounds.
///
/// The first entry's input bounds must match `input_bounds`, and the last
/// entry's output bounds must match `output_bounds` (within tolerance).
///
/// Returns `false` for empty chains.
#[must_use]
pub fn verify_chain_coverage(
    chain: &CertificateChain,
    input_bounds: &[(f64, f64)],
    output_bounds: &[(f64, f64)],
) -> bool {
    let first = match chain.entries.first() {
        Some(e) => e,
        None => return false,
    };
    let last = match chain.entries.last() {
        Some(e) => e,
        None => return false,
    };

    if first.input_bounds.len() != input_bounds.len() {
        return false;
    }
    if last.output_bounds.len() != output_bounds.len() {
        return false;
    }

    let inputs_match =
        first
            .input_bounds
            .iter()
            .zip(input_bounds.iter())
            .all(|(&(a_lo, a_hi), &(b_lo, b_hi))| {
                (a_lo - b_lo).abs() <= EPSILON && (a_hi - b_hi).abs() <= EPSILON
            });

    let outputs_match = last.output_bounds.iter().zip(output_bounds.iter()).all(
        |(&(a_lo, a_hi), &(b_lo, b_hi))| {
            (a_lo - b_lo).abs() <= EPSILON && (a_hi - b_hi).abs() <= EPSILON
        },
    );

    inputs_match && outputs_match
}

/// Compute the minimum trust level across all entries in the chain.
///
/// Returns `Formal` for empty chains (vacuous truth).
#[must_use]
pub fn chain_trust_level(chain: &CertificateChain) -> ChainTrustLevel {
    chain
        .entries
        .iter()
        .map(|e| e.trust_level)
        .min()
        .unwrap_or(ChainTrustLevel::Formal)
}

/// Merge two certificate chains if they are compatible.
///
/// Chains are compatible when the last entry of `a` has output bounds
/// matching the first entry of `b`'s input bounds (within tolerance),
/// and both chains share the same `network_id`.
///
/// Returns `None` if the chains are incompatible.
#[must_use]
pub fn merge_chains(a: &CertificateChain, b: &CertificateChain) -> Option<CertificateChain> {
    if a.network_id != b.network_id {
        return None;
    }

    let a_last = a.entries.last()?;
    let b_first = b.entries.first()?;

    if a_last.output_bounds.len() != b_first.input_bounds.len() {
        return None;
    }

    let bounds_match = a_last
        .output_bounds
        .iter()
        .zip(b_first.input_bounds.iter())
        .all(|(&(a_lo, a_hi), &(b_lo, b_hi))| {
            (a_lo - b_lo).abs() <= EPSILON && (a_hi - b_hi).abs() <= EPSILON
        });

    if !bounds_match {
        return None;
    }

    let mut entries = a.entries.clone();
    entries.extend(b.entries.iter().cloned());

    let property = if a.property == b.property {
        a.property.clone()
    } else {
        format!("{} + {}", a.property, b.property)
    };

    Some(CertificateChain {
        entries,
        property,
        network_id: a.network_id.clone(),
    })
}

/// Format a human-readable summary of a certificate chain.
#[must_use]
pub fn format_chain_summary(chain: &CertificateChain) -> String {
    let num_entries = chain.entries.len();
    let trust = chain_trust_level(chain);
    let continuous = verify_chain_continuity(chain);

    let methods: Vec<String> = chain.entries.iter().map(|e| e.method.to_string()).collect();

    let unique_methods = {
        let mut seen = Vec::new();
        for m in &methods {
            if !seen.contains(m) {
                seen.push(m.clone());
            }
        }
        seen
    };

    let input_dim = chain.entries.first().map_or(0, |e| e.input_bounds.len());
    let output_dim = chain.entries.last().map_or(0, |e| e.output_bounds.len());

    format!(
        "CertificateChain(network={}, property={}, layers={}, \
         trust={}, continuous={}, methods=[{}], \
         input_dim={}, output_dim={})",
        chain.network_id,
        chain.property,
        num_entries,
        trust,
        continuous,
        unique_methods.join(", "),
        input_dim,
        output_dim,
    )
}
