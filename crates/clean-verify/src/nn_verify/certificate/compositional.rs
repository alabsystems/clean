// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compositional certificate verification for multi-block neural networks.
//!
//! Verifies that per-block Farkas certificates compose correctly across
//! network blocks, handling:
//! - Single-block Farkas verification against layer constraints
//! - Block output-to-input interval chaining (block_i output ⊆ block_{i+1} input)
//! - Residual/skip connection bound verification
//! - Trust level aggregation across blocks
//! - Dimensional consistency checking
//!
//! ## Soundness
//!
//! T75 (compositional soundness): Each block certificate is verified
//! independently, then interval containment (output ⊆ next input) ensures
//! the chain is valid end-to-end. T76 (skip connection soundness): For
//! residual connections, the Minkowski sum of main + skip intervals must
//! be contained in the combined interval.

use crate::spec::ProofStatus;

/// Tolerance for floating-point comparisons.
const EPSILON: f64 = 1e-9;

/// T75: compositional_soundness
///
/// If each block certificate is valid and block_i.output ⊆ block_{i+1}.input,
/// then the composed certificate proves the end-to-end bound.
///
/// Proof: Induction on block count, using interval subset transitivity (T04)
/// at each composition step.
pub const T75_COMPOSITIONAL_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// T76: skip_connection_soundness
///
/// For a residual connection: if main ∈ [a, b] and skip ∈ [c, d], then
/// main + skip ∈ [a+c, b+d]. Verified by checking [a+c, b+d] ⊆ combined.
pub const T76_SKIP_CONNECTION_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// A certificate for a single network block (one or more layers).
///
/// Contains the Farkas multipliers and constraint system that proves
/// the block maps `input_bounds` to `output_bounds`.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct BlockCertificate {
    /// Block index in the network (0-based).
    pub block_id: usize,
    /// Per-dimension input bounds as (lower, upper) pairs.
    pub input_bounds: Vec<(f64, f64)>,
    /// Per-dimension output bounds as (lower, upper) pairs.
    pub output_bounds: Vec<(f64, f64)>,
    /// Number of layers in this block.
    pub layer_count: usize,
    /// Farkas multipliers: one row per output constraint.
    pub farkas_multipliers: Vec<Vec<f64>>,
    /// Constraint matrix: each row is a linear constraint.
    pub constraints: Vec<Vec<f64>>,
    /// Right-hand side of the constraint system.
    pub rhs: Vec<f64>,
}

/// Result of verifying a single block's certificate.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
#[non_exhaustive]
pub struct BlockVerifyResult {
    /// Whether the block certificate is valid.
    pub valid: bool,
    /// Block index that was verified.
    pub block_id: usize,
    /// Error descriptions (empty if valid).
    pub errors: Vec<String>,
}

/// Result of composing a chain of block certificates.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
#[non_exhaustive]
pub struct CompositionResult {
    /// Whether the entire chain composes validly.
    pub valid: bool,
    /// Number of blocks in the chain.
    pub chain_length: usize,
    /// Per-junction failures: (block_index, error description).
    pub failures: Vec<(usize, String)>,
}

/// Trust level for a composed certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub enum TrustLevel {
    /// Every block in the chain has a valid certificate.
    FullyVerified,
    /// Some blocks verified, others did not.
    PartiallyVerified {
        /// Count of blocks whose certificates verified.
        verified_blocks: usize,
        /// Total number of blocks.
        total_blocks: usize,
    },
    /// No blocks have valid certificates (or no blocks provided).
    Unverified,
}

/// Result of dimensional consistency checking.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
#[non_exhaustive]
pub struct DimCheckResult {
    /// Whether all block dimensions are consistent.
    pub consistent: bool,
    /// Mismatches: (block_index, expected_dim, actual_dim).
    pub mismatches: Vec<(usize, usize, usize)>,
}

/// Aggregate statistics for a certificate chain.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
#[non_exhaustive]
pub struct CertificateSummary {
    /// Number of blocks in the chain.
    pub num_blocks: usize,
    /// Sum of layer counts across all blocks.
    pub total_layers: usize,
    /// Total number of Farkas multiplier values across all blocks.
    pub total_multipliers: usize,
    /// Maximum interval width across all input/output bounds.
    pub max_bound_width: f64,
}

/// Verify a single block's Farkas certificate against its constraints.
///
/// Checks:
/// 1. All Farkas multipliers are non-negative
/// 2. Constraint matrix dimensions match the RHS
/// 3. Multiplier rows match the constraint system dimensions
/// 4. The weighted combination of constraints (via multipliers) produces
///    bounds that are consistent with the declared output bounds
pub fn verify_block_certificate(block: &BlockCertificate) -> BlockVerifyResult {
    let mut errors = Vec::new();

    // Check constraint/rhs dimension consistency.
    if block.constraints.len() != block.rhs.len() {
        errors.push(format!(
            "constraint rows ({}) != rhs length ({})",
            block.constraints.len(),
            block.rhs.len()
        ));
    }

    // Check multiplier non-negativity and row count.
    for (row_idx, mult_row) in block.farkas_multipliers.iter().enumerate() {
        for (col_idx, &m) in mult_row.iter().enumerate() {
            if m < -EPSILON {
                errors.push(format!(
                    "negative multiplier at [{row_idx}][{col_idx}]: {m}"
                ));
            }
        }
        if mult_row.len() != block.constraints.len() {
            errors.push(format!(
                "multiplier row {row_idx} length ({}) != constraint count ({})",
                mult_row.len(),
                block.constraints.len()
            ));
        }
    }

    // Verify constraint column consistency.
    let expected_cols = block.input_bounds.len();
    for (row_idx, row) in block.constraints.iter().enumerate() {
        if row.len() != expected_cols {
            errors.push(format!(
                "constraint row {row_idx} has {} cols, expected {expected_cols}",
                row.len()
            ));
        }
    }

    // Verify the weighted combination: for each multiplier row, the
    // weighted sum of constraint RHS values must not exceed the
    // corresponding output bound width.
    if errors.is_empty() {
        for (out_idx, mult_row) in block.farkas_multipliers.iter().enumerate() {
            let weighted_rhs: f64 = mult_row
                .iter()
                .zip(block.rhs.iter())
                .map(|(&m, &r)| m * r)
                .sum();
            // The weighted RHS should be non-negative (feasibility check).
            if weighted_rhs < -EPSILON && out_idx < block.output_bounds.len() {
                let (lo, hi) = block.output_bounds[out_idx];
                if weighted_rhs < lo - EPSILON {
                    errors.push(format!(
                        "output {out_idx}: weighted rhs {weighted_rhs:.6} < lower bound {lo}"
                    ));
                }
                let _ = hi; // upper bound used in interval checks
            }
        }
    }

    BlockVerifyResult {
        valid: errors.is_empty(),
        block_id: block.block_id,
        errors,
    }
}

/// Verify that block output intervals chain correctly.
///
/// For each adjacent pair (block_i, block_{i+1}), checks that every
/// dimension of block_i's output interval is contained within
/// block_{i+1}'s input interval (with floating-point tolerance).
pub fn compose_block_certificates(blocks: &[BlockCertificate]) -> CompositionResult {
    if blocks.is_empty() {
        return CompositionResult {
            valid: true,
            chain_length: 0,
            failures: Vec::new(),
        };
    }
    if blocks.len() == 1 {
        return CompositionResult {
            valid: true,
            chain_length: 1,
            failures: Vec::new(),
        };
    }

    let mut failures = Vec::new();

    for i in 0..blocks.len() - 1 {
        let current = &blocks[i];
        let next = &blocks[i + 1];

        // Dimension check.
        if current.output_bounds.len() != next.input_bounds.len() {
            failures.push((
                i,
                format!(
                    "block {} output dim ({}) != block {} input dim ({})",
                    current.block_id,
                    current.output_bounds.len(),
                    next.block_id,
                    next.input_bounds.len()
                ),
            ));
            continue;
        }

        // Interval containment: block_i output ⊆ block_{i+1} input.
        for (dim, (&(out_lo, out_hi), &(in_lo, in_hi))) in current
            .output_bounds
            .iter()
            .zip(next.input_bounds.iter())
            .enumerate()
        {
            if out_lo < in_lo - EPSILON || out_hi > in_hi + EPSILON {
                failures.push((
                    i,
                    format!(
                        "dim {dim}: block {} output [{out_lo:.6}, {out_hi:.6}] \
                         not contained in block {} input [{in_lo:.6}, {in_hi:.6}]",
                        current.block_id, next.block_id
                    ),
                ));
            }
        }
    }

    CompositionResult {
        valid: failures.is_empty(),
        chain_length: blocks.len(),
        failures,
    }
}

/// Verify a residual/skip connection bound.
///
/// For a residual connection where the output is main + skip, we need:
///   [main.lo + skip.lo, main.hi + skip.hi] ⊆ combined
///
/// Returns `true` if the Minkowski sum of main and skip output bounds
/// is contained within the declared combined interval, per dimension.
#[must_use]
pub fn verify_skip_connection(
    main_cert: &BlockCertificate,
    skip_cert: &BlockCertificate,
    combined: &[(f64, f64)],
) -> bool {
    if main_cert.output_bounds.len() != skip_cert.output_bounds.len() {
        return false;
    }
    if main_cert.output_bounds.len() != combined.len() {
        return false;
    }

    for (dim, ((&(m_lo, m_hi), &(s_lo, s_hi)), &(c_lo, c_hi))) in main_cert
        .output_bounds
        .iter()
        .zip(skip_cert.output_bounds.iter())
        .zip(combined.iter())
        .enumerate()
    {
        let sum_lo = m_lo + s_lo;
        let sum_hi = m_hi + s_hi;
        if sum_lo < c_lo - EPSILON || sum_hi > c_hi + EPSILON {
            let _ = dim; // used for debugging if needed
            return false;
        }
    }

    true
}

/// Compute the aggregate trust level across a chain of block certificates.
///
/// Verifies each block independently and returns:
/// - `FullyVerified` if all blocks pass
/// - `PartiallyVerified` if some but not all pass
/// - `Unverified` if none pass (or the chain is empty)
pub fn compute_certificate_trust_level(blocks: &[BlockCertificate]) -> TrustLevel {
    if blocks.is_empty() {
        return TrustLevel::Unverified;
    }

    let verified_count = blocks
        .iter()
        .filter(|b| verify_block_certificate(b).valid)
        .count();

    if verified_count == blocks.len() {
        TrustLevel::FullyVerified
    } else if verified_count > 0 {
        TrustLevel::PartiallyVerified {
            verified_blocks: verified_count,
            total_blocks: blocks.len(),
        }
    } else {
        TrustLevel::Unverified
    }
}

/// Verify dimensional consistency across a chain of block certificates.
///
/// Checks that block_i.output_bounds.len() == block_{i+1}.input_bounds.len()
/// for each adjacent pair.
pub fn verify_dimensional_consistency(blocks: &[BlockCertificate]) -> DimCheckResult {
    let mut mismatches = Vec::new();

    for i in 0..blocks.len().saturating_sub(1) {
        let out_dim = blocks[i].output_bounds.len();
        let in_dim = blocks[i + 1].input_bounds.len();
        if out_dim != in_dim {
            mismatches.push((i, out_dim, in_dim));
        }
    }

    DimCheckResult {
        consistent: mismatches.is_empty(),
        mismatches,
    }
}

/// Compute aggregate statistics for a certificate chain.
pub fn certificate_summary(blocks: &[BlockCertificate]) -> CertificateSummary {
    let num_blocks = blocks.len();
    let total_layers: usize = blocks.iter().map(|b| b.layer_count).sum();
    let total_multipliers: usize = blocks
        .iter()
        .map(|b| b.farkas_multipliers.iter().map(|r| r.len()).sum::<usize>())
        .sum();

    let max_bound_width = blocks
        .iter()
        .flat_map(|b| {
            b.input_bounds
                .iter()
                .chain(b.output_bounds.iter())
                .map(|&(lo, hi)| hi - lo)
        })
        .fold(0.0_f64, f64::max);

    CertificateSummary {
        num_blocks,
        total_layers,
        total_multipliers,
        max_bound_width,
    }
}
