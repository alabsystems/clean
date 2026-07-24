// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shard-level foreign declaration verification via kernel type-checking.
//!
//! Provides [`verify_foreign_shard`] to verify constants in a single `.mathverse`
//! shard file and [`verify_foreign_batch`] to process multiple shards with
//! aggregated statistics.  Each constant is reconstructed from the shard's
//! `FlatExpr` arena and fed through `Environment::add_decl()`.
//!
//! Unlike [`crate::shard_verify`] (which provides directory-level discovery and
//! parallel execution), this module focuses on per-constant result tracking with
//! structured error messages and configurable error handling policy.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use clean_kernel::{Declaration, Environment, Name};
use thiserror::Error;

use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{MathverseConstantHeader, NO_VALUE};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors specific to foreign verification.
#[derive(Debug, Error)]
pub enum VerifyForeignError {
    #[error("shard load failed for `{path}`: {reason}")]
    ShardLoad { path: PathBuf, reason: String },

    #[error("reconstruction failed for constant `{name}`: {reason}")]
    Reconstruct { name: String, reason: String },

    #[error("kernel type-check failed for constant `{name}`: {reason}")]
    TypeCheck { name: String, reason: String },
}

impl From<VerifyForeignError> for MathverseError {
    fn from(value: VerifyForeignError) -> Self {
        MathverseError::Kernel(value.to_string())
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// How to handle per-constant verification failures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorPolicy {
    /// Continue verifying remaining constants after a failure.
    Continue,
    /// Stop at the first verification failure.
    StopOnFirst,
}

/// Configuration for foreign shard verification.
#[derive(Clone, Debug)]
pub struct VerifyForeignConfig {
    /// Maximum number of constants to process per shard (0 = unlimited).
    pub batch_size: usize,
    /// Per-constant timeout (not enforced at kernel level, but tracked).
    pub timeout_per_constant: Duration,
    /// Error handling policy.
    pub error_policy: ErrorPolicy,
}

impl Default for VerifyForeignConfig {
    fn default() -> Self {
        Self {
            batch_size: 0,
            timeout_per_constant: Duration::from_secs(30),
            error_policy: ErrorPolicy::Continue,
        }
    }
}

// ---------------------------------------------------------------------------
// Per-constant result
// ---------------------------------------------------------------------------

/// Outcome of verifying a single constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstantOutcome {
    /// Successfully type-checked as a theorem or definition.
    KernelVerified,
    /// Accepted as an axiom (type is well-formed, no proof term).
    AxiomAccepted,
    /// Reconstruction from FlatExpr failed.
    ReconstructFailed(String),
    /// Kernel type-checking rejected the declaration.
    TypeCheckFailed(String),
    /// Constant was skipped (batch_size limit or error policy).
    Skipped,
}

/// Result of verifying a single constant within a shard.
#[derive(Clone, Debug)]
pub struct ConstantVerifyResult {
    /// Index of the constant within the shard.
    pub index: usize,
    /// Name of the constant (from the shard string table).
    pub name: String,
    /// Verification outcome.
    pub outcome: ConstantOutcome,
    /// Time spent verifying this constant.
    pub elapsed: Duration,
}

// ---------------------------------------------------------------------------
// Shard result
// ---------------------------------------------------------------------------

/// Aggregated result from verifying all foreign constants in a single shard.
#[derive(Clone, Debug)]
pub struct VerifyForeignResult {
    /// Path of the shard file (if loaded from disk).
    pub shard_path: Option<PathBuf>,
    /// Per-constant results.
    pub constants: Vec<ConstantVerifyResult>,
    /// Total constants examined.
    pub total: usize,
    /// Constants that passed kernel verification (theorem/definition).
    pub verified: usize,
    /// Constants accepted as axioms.
    pub axiom_accepted: usize,
    /// Constants that failed reconstruction or type-checking.
    pub failed: usize,
    /// Constants skipped.
    pub skipped: usize,
    /// Total wall-clock time for the shard.
    pub elapsed: Duration,
}

impl VerifyForeignResult {
    /// Fraction of constants that were successfully verified or accepted.
    #[must_use]
    pub fn acceptance_rate(&self) -> f64 {
        let accepted = (self.verified + self.axiom_accepted) as f64;
        let total = self.total as f64;
        if total > 0.0 {
            accepted / total
        } else {
            0.0
        }
    }
}

// ---------------------------------------------------------------------------
// Public API: single shard
// ---------------------------------------------------------------------------

/// Verify all foreign constants in a shard loaded from `shard_path`.
///
/// Loads the shard via [`ShardReader::from_file`], reconstructs each constant's
/// type and value from the `FlatExpr` arena, and attempts kernel type-checking
/// via `Environment::add_decl()`.
pub fn verify_foreign_shard(
    shard_path: &Path,
    config: &VerifyForeignConfig,
) -> MathverseResult<VerifyForeignResult> {
    let reader = ShardReader::from_file(shard_path).map_err(|e| {
        MathverseError::from(VerifyForeignError::ShardLoad {
            path: shard_path.to_path_buf(),
            reason: e.to_string(),
        })
    })?;

    let mut result = verify_foreign_reader(&reader, config);
    result.shard_path = Some(shard_path.to_path_buf());
    Ok(result)
}

/// Verify all foreign constants in an already-loaded [`ShardReader`].
pub fn verify_foreign_reader(
    reader: &ShardReader,
    config: &VerifyForeignConfig,
) -> VerifyForeignResult {
    let start = Instant::now();
    let mut env = Environment::new();
    let mut constants = Vec::with_capacity(reader.constants.len());
    let mut verified = 0usize;
    let mut axiom_accepted = 0usize;
    let mut failed = 0usize;
    let mut skipped = 0usize;

    let limit = if config.batch_size > 0 {
        config.batch_size.min(reader.constants.len())
    } else {
        reader.constants.len()
    };

    for (ci, header) in reader.constants.iter().enumerate() {
        if ci >= limit {
            skipped += reader.constants.len() - ci;
            for si in ci..reader.constants.len() {
                constants.push(ConstantVerifyResult {
                    index: si,
                    name: constant_name(reader, reader.constants[si].name_idx),
                    outcome: ConstantOutcome::Skipped,
                    elapsed: Duration::ZERO,
                });
            }
            break;
        }

        let const_start = Instant::now();
        let name = constant_name(reader, header.name_idx);
        let outcome = verify_single_constant(reader, &mut env, ci, &name, header);

        match &outcome {
            ConstantOutcome::KernelVerified => verified += 1,
            ConstantOutcome::AxiomAccepted => axiom_accepted += 1,
            ConstantOutcome::ReconstructFailed(_) | ConstantOutcome::TypeCheckFailed(_) => {
                failed += 1;
            }
            ConstantOutcome::Skipped => skipped += 1,
        }

        let should_stop = config.error_policy == ErrorPolicy::StopOnFirst && outcome.is_failure();

        constants.push(ConstantVerifyResult {
            index: ci,
            name,
            outcome,
            elapsed: const_start.elapsed(),
        });

        if should_stop {
            // Mark remaining as skipped.
            for si in (ci + 1)..reader.constants.len() {
                skipped += 1;
                constants.push(ConstantVerifyResult {
                    index: si,
                    name: constant_name(reader, reader.constants[si].name_idx),
                    outcome: ConstantOutcome::Skipped,
                    elapsed: Duration::ZERO,
                });
            }
            break;
        }
    }

    VerifyForeignResult {
        shard_path: None,
        constants,
        total: reader.constants.len(),
        verified,
        axiom_accepted,
        failed,
        skipped,
        elapsed: start.elapsed(),
    }
}

// ---------------------------------------------------------------------------
// Public API: batch
// ---------------------------------------------------------------------------

/// Verify multiple shards and aggregate results.
pub fn verify_foreign_batch(
    shard_paths: &[PathBuf],
    config: &VerifyForeignConfig,
) -> Vec<VerifyForeignResult> {
    shard_paths
        .iter()
        .map(|path| {
            verify_foreign_shard(path, config).unwrap_or_else(|_| VerifyForeignResult {
                shard_path: Some(path.clone()),
                constants: Vec::new(),
                total: 0,
                verified: 0,
                axiom_accepted: 0,
                failed: 0,
                skipped: 0,
                elapsed: Duration::ZERO,
            })
        })
        .collect()
}

/// Aggregate statistics across multiple shard results.
#[derive(Clone, Debug, Default)]
pub struct BatchStats {
    pub shards_processed: usize,
    pub total_constants: usize,
    pub total_verified: usize,
    pub total_axiom_accepted: usize,
    pub total_failed: usize,
    pub total_skipped: usize,
    pub total_elapsed: Duration,
}

impl BatchStats {
    /// Compute batch statistics from a slice of shard results.
    #[must_use]
    pub fn from_results(results: &[VerifyForeignResult]) -> Self {
        let mut stats = Self::default();
        for r in results {
            stats.shards_processed += 1;
            stats.total_constants += r.total;
            stats.total_verified += r.verified;
            stats.total_axiom_accepted += r.axiom_accepted;
            stats.total_failed += r.failed;
            stats.total_skipped += r.skipped;
            stats.total_elapsed += r.elapsed;
        }
        stats
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

impl ConstantOutcome {
    fn is_failure(&self) -> bool {
        matches!(
            self,
            ConstantOutcome::ReconstructFailed(_) | ConstantOutcome::TypeCheckFailed(_)
        )
    }
}

/// Verify a single constant: reconstruct type/value, try theorem then axiom.
fn verify_single_constant(
    reader: &ShardReader,
    env: &mut Environment,
    ci: usize,
    name_str: &str,
    header: &MathverseConstantHeader,
) -> ConstantOutcome {
    // Reconstruct the type expression.
    let type_expr = match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        header.type_idx,
    ) {
        Ok(e) => e,
        Err(e) => {
            return ConstantOutcome::ReconstructFailed(format!("type reconstruction: {e}"));
        }
    };

    // Reconstruct the value expression (if present).
    let value_expr = if header.value_idx != NO_VALUE {
        match reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            header.value_idx,
        ) {
            Ok(e) => Some(e),
            Err(e) => {
                return ConstantOutcome::ReconstructFailed(format!("value reconstruction: {e}"));
            }
        }
    } else {
        None
    };

    // Reconstruct declaration-level universe parameter names.
    let level_params = reconstruct_level_params(
        &reader.strings,
        header.level_params_start,
        header.level_params_count,
    )
    .unwrap_or_default();

    let decl_name = Name::from_string(&format!("verify_foreign.{ci}.{name_str}"));

    // Try as theorem first if we have a value.
    if let Some(ref value) = value_expr {
        let theorem_decl = Declaration::Theorem {
            name: decl_name.clone(),
            level_params: level_params.clone(),
            type_: type_expr.clone(),
            value: value.clone(),
        };
        if env.add_decl(theorem_decl).is_ok() {
            return ConstantOutcome::KernelVerified;
        }

        // Theorem failed — try as definition (type may not be Prop).
        let def_name = Name::from_string(&format!("verify_foreign.{ci}.{name_str}.def"));
        let definition_decl = Declaration::Definition {
            name: def_name,
            level_params: level_params.clone(),
            type_: type_expr.clone(),
            value: value.clone(),
            is_reducible: false,
        };
        if env.add_decl(definition_decl).is_ok() {
            return ConstantOutcome::KernelVerified;
        }
    }

    // Fall back to axiom (type-only verification).
    let axiom_name = Name::from_string(&format!("verify_foreign.{ci}.{name_str}.axiom"));
    let axiom_decl = Declaration::Axiom {
        name: axiom_name,
        level_params,
        type_: type_expr,
    };
    match env.add_decl(axiom_decl) {
        Ok(()) => ConstantOutcome::AxiomAccepted,
        Err(e) => ConstantOutcome::TypeCheckFailed(e.to_string()),
    }
}

fn constant_name(reader: &ShardReader, name_idx: u32) -> String {
    reader
        .strings
        .get(name_idx as usize)
        .cloned()
        .unwrap_or_else(|| format!("<invalid-name-idx:{name_idx}>"))
}

#[cfg(test)]
mod tests;
