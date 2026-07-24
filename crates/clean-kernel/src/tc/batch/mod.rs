// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch Verification API for AI Workloads
//!
//! This module provides high-throughput batch verification optimized for AI agents
//! that generate millions of candidate proofs and need efficient filtering.
//!
//! # Design Principles
//!
//! 1. **Amortized setup costs** - Create one verifier, check many expressions
//! 2. **Early termination** - Stop as soon as a valid proof is found
//! 3. **Parallel execution** - Scale across CPU cores
//! 4. **Structured results** - Machine-readable output for AI consumption
//!
//! # Example
//!
//! ```no_run
//! use clean_kernel::{Environment, Expr, BatchVerifier};
//!
//! let env = Environment::new();
//! let verifier = BatchVerifier::new(&env);
//!
//! // AI generates candidate proofs
//! let candidates: Vec<Expr> = vec![Expr::prop(), Expr::type_()];
//!
//! // Find first valid proof (common pattern)
//! if let Some((expr, ty)) = verifier.find_first_valid(candidates.into_iter()) {
//!     // process valid proof of type `ty`
//! }
//! ```

mod arena;
mod verifier;

#[cfg(test)]
mod tests;

pub use arena::VerificationArena;
pub use verifier::BatchVerifier;

use crate::expr::Expr;
use crate::mode::CleanMode;

/// Result of batch verification for a single expression
#[derive(Debug, Clone)]
#[must_use = "batch check results should be inspected"]
pub struct BatchCheckResult {
    /// Whether the expression is well-typed
    pub valid: bool,
    /// The inferred type (if valid)
    pub inferred_type: Option<Expr>,
    /// Error message (if invalid)
    pub error: Option<String>,
    /// Time to verify in nanoseconds
    pub time_ns: u64,
}

impl BatchCheckResult {
    /// Create a successful batch check result
    ///
    /// # Contract
    ///
    /// ENSURES: `result.valid == true`
    /// ENSURES: `result.inferred_type == Some(ty)`
    /// ENSURES: `result.error.is_none()`
    /// ENSURES: `result.time_ns == time_ns`
    fn success(ty: Expr, time_ns: u64) -> Self {
        Self {
            valid: true,
            inferred_type: Some(ty),
            error: None,
            time_ns,
        }
    }

    /// Create a failed batch check result
    ///
    /// # Contract
    ///
    /// ENSURES: `result.valid == false`
    /// ENSURES: `result.inferred_type.is_none()`
    /// ENSURES: `result.error == Some(error)`
    /// ENSURES: `result.time_ns == time_ns`
    fn failure(error: String, time_ns: u64) -> Self {
        Self {
            valid: false,
            inferred_type: None,
            error: Some(error),
            time_ns,
        }
    }
}

/// Statistics for batch verification
#[derive(Debug, Clone, Default)]
pub struct BatchCheckStats {
    /// Total expressions checked
    pub total: usize,
    /// Number of valid expressions
    pub valid: usize,
    /// Number of invalid expressions
    pub invalid: usize,
    /// Total wall-clock time in nanoseconds (0 if not measured)
    pub wall_time_ns: u64,
    /// Average time per expression in nanoseconds
    pub avg_time_ns: u64,
    /// Minimum verification time in nanoseconds
    pub min_time_ns: u64,
    /// Maximum verification time in nanoseconds
    pub max_time_ns: u64,
}

/// Configuration for batch verification
#[derive(Debug, Clone)]
pub struct BatchConfig {
    /// Minimum batch size to trigger parallel execution
    pub parallel_threshold: usize,
    /// Number of threads (None = use rayon default)
    pub num_threads: Option<usize>,
    /// Type checking mode override (`None` inherits `env.mode()`)
    pub mode: Option<CleanMode>,
}

impl Default for BatchConfig {
    /// Create default batch configuration
    ///
    /// # Contract
    ///
    /// ENSURES: `result.parallel_threshold == 4`
    /// ENSURES: `result.num_threads.is_none()`
    /// ENSURES: `result.mode.is_none()`
    fn default() -> Self {
        Self {
            parallel_threshold: 4,
            num_threads: None,
            mode: None,
        }
    }
}

impl BatchConfig {
    /// Config optimized for latency (lower parallel threshold)
    ///
    /// # Contract
    ///
    /// ENSURES: `result.parallel_threshold == 2`
    /// ENSURES: `result.parallel_threshold < BatchConfig::default().parallel_threshold`
    /// ENSURES: `result.mode.is_none()`
    pub fn low_latency() -> Self {
        Self {
            parallel_threshold: 2,
            num_threads: None,
            mode: None,
        }
    }

    /// Config optimized for throughput (higher parallel threshold)
    ///
    /// # Contract
    ///
    /// ENSURES: `result.parallel_threshold == 16`
    /// ENSURES: `result.parallel_threshold > BatchConfig::default().parallel_threshold`
    /// ENSURES: `result.mode.is_none()`
    pub fn high_throughput() -> Self {
        Self {
            parallel_threshold: 16,
            num_threads: None,
            mode: None,
        }
    }
}

/// Compute statistics from batch results
///
/// # Contract
///
/// ENSURES: `result.total == results.len()`
/// ENSURES: `result.valid + result.invalid == result.total`
/// ENSURES: `result.wall_time_ns == wall_time_ns`
pub(super) fn compute_stats(results: &[BatchCheckResult], wall_time_ns: u64) -> BatchCheckStats {
    compute_stats_from_slice(&results.iter().collect::<Vec<_>>(), wall_time_ns)
}

/// Compute statistics from a slice of batch result references
///
/// # Contract
///
/// ENSURES: `result.total == results.len()`
/// ENSURES: `result.valid + result.invalid == result.total`
/// ENSURES: `result.wall_time_ns == wall_time_ns`
/// ENSURES: If `total > 0`: `result.min_time_ns <= result.avg_time_ns <= result.max_time_ns`
pub(super) fn compute_stats_from_slice(
    results: &[&BatchCheckResult],
    wall_time_ns: u64,
) -> BatchCheckStats {
    let total = results.len();
    if total == 0 {
        return BatchCheckStats::default();
    }

    let valid = results.iter().filter(|r| r.valid).count();
    let invalid = total - valid;
    let (min_time_ns, max_time_ns, sum_time_ns) =
        results
            .iter()
            .fold((u64::MAX, 0u64, 0u64), |(mn, mx, sum), r| {
                (
                    mn.min(r.time_ns),
                    mx.max(r.time_ns),
                    sum.saturating_add(r.time_ns),
                )
            });
    let min_time_ns = if total > 0 { min_time_ns } else { 0 };
    let avg_time_ns = if total > 0 {
        sum_time_ns / total as u64
    } else {
        0
    };

    BatchCheckStats {
        total,
        valid,
        invalid,
        wall_time_ns,
        avg_time_ns,
        min_time_ns,
        max_time_ns,
    }
}
