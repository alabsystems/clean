// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification-aware Lean 4 shard conversion.
//!
//! This bridges `clean-olean` kernel verification results with `.mathverse` shard
//! output so shard trust metadata reflects actual type-checking outcomes.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use clean_olean::verify_batch::{BatchSummary, ModuleResult};
use serde::Serialize;
use thiserror::Error;

use crate::error::{MathverseError, MathverseResult, MathverseResultExt};
use crate::lean4::olean::olean_bridge;
use crate::lean4::olean::verify;
use crate::shard::{ShardReader, ShardWriter};
use crate::types::{ImportConfidence, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
enum VerifyIntegrationError {
    #[error("Lean4 verification produced no summary for {path}")]
    MissingVerification { path: String },
    #[error("constant name index {idx} out of range (count: {count})")]
    InvalidNameIndex { idx: u32, count: usize },
}

impl From<VerifyIntegrationError> for MathverseError {
    fn from(value: VerifyIntegrationError) -> Self {
        match value {
            VerifyIntegrationError::MissingVerification { path } => {
                MathverseError::Kernel(format!("Lean4 verification produced no summary for {path}"))
            }
            VerifyIntegrationError::InvalidNameIndex { idx, count } => {
                MathverseError::StringOutOfRange {
                    idx,
                    count: saturating_usize_to_u32(count),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Config + reports
// ---------------------------------------------------------------------------

/// Configuration for verification-aware Lean 4 shard conversion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyOleanConfig {
    /// Reserved for future kernel-verification timeout enforcement.
    pub timeout_secs: u64,
    /// Reserved for future parallel verification/conversion orchestration.
    pub parallel: bool,
    /// Fallback trust level for declarations that do not kernel type-check.
    pub fallback_trust: TrustLevel,
}

impl Default for VerifyOleanConfig {
    fn default() -> Self {
        Self {
            timeout_secs: 300,
            parallel: false,
            fallback_trust: TrustLevel::TrustedOracle,
        }
    }
}

/// Per-module verification result emitted for a single source directory.
#[derive(Clone, Debug, Serialize)]
pub struct ModuleVerifyReport {
    pub module_name: String,
    pub total: usize,
    pub kernel_verified: usize,
    pub trusted_oracle: usize,
    pub errors: BTreeMap<String, String>,
}

/// Verification result for one converted Lean 4 directory.
#[derive(Clone, Debug, Serialize)]
pub struct VerificationReport {
    pub source_dir: String,
    pub total_constants: usize,
    pub kernel_verified: usize,
    /// Legacy field name retained for the summary schema; counts declarations
    /// downgraded away from `KernelVerified` in the written shard.
    pub trusted_oracle: usize,
    pub failed_load: usize,
    pub elapsed_secs: f64,
    pub per_module: Vec<ModuleVerifyReport>,
}

/// Aggregate verification summary across all source directories.
#[derive(Clone, Debug, Serialize)]
pub struct VerificationSummary {
    pub total_declarations: usize,
    pub total_kernel_verified: usize,
    pub total_trusted_oracle: usize,
    pub kernel_verified_pct: f64,
    pub per_source: Vec<VerificationReport>,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Verify a Lean 4 `.olean` directory, convert it to an `.mathverse` shard,
/// rewrite trust metadata based on kernel results, and return a report.
pub fn verify_and_convert_lean4_shard(
    olean_dir: &Path,
    output_dir: &Path,
    config: &VerifyOleanConfig,
) -> MathverseResult<VerificationReport> {
    let tc_results = verify::verify_lean4_dir(olean_dir).ok_or_else(|| {
        VerifyIntegrationError::MissingVerification {
            path: olean_dir.display().to_string(),
        }
    })?;

    fs::create_dir_all(output_dir)?;
    let output_path = shard_output_path(olean_dir, output_dir);

    olean_bridge::convert_olean_dir_to_mathverse(olean_dir, &output_path, None)
        .map_err_context("converting Lean4 directory to mathverse shard")?;

    let shard_bytes = fs::read(&output_path)
        .map_err(MathverseError::from)
        .map_err_context("reading generated mathverse shard")?;
    let upgraded_bytes = if config.fallback_trust == TrustLevel::TrustedOracle {
        upgrade_shard_trust_levels(&shard_bytes, &tc_results)?
    } else {
        upgrade_shard_trust_levels_with_confidence(
            &shard_bytes,
            &tc_results,
            confidence_for_fallback_trust(config.fallback_trust),
        )?
    };

    fs::write(&output_path, &upgraded_bytes)
        .map_err(MathverseError::from)
        .map_err_context("writing upgraded mathverse shard")?;

    let reader = ShardReader::from_bytes(&upgraded_bytes)
        .map_err_context("reading upgraded mathverse shard")?;
    build_verification_report(&reader, &tc_results)
}

/// Upgrade shard trust levels using the default TrustedOracle fallback.
pub(crate) fn upgrade_shard_trust_levels(
    shard_bytes: &[u8],
    tc_results: &BatchSummary,
) -> MathverseResult<Vec<u8>> {
    upgrade_shard_trust_levels_with_confidence(
        shard_bytes,
        tc_results,
        ImportConfidence::Axiomatized,
    )
}

/// Build the set of constant names that failed type-checking.
pub(crate) fn build_tc_error_set(tc_results: &BatchSummary) -> HashSet<String> {
    tc_results
        .modules
        .iter()
        .flat_map(|module| module.tc_errors.keys().cloned())
        .collect()
}

/// Aggregate per-directory verification reports into one summary.
pub fn aggregate_verification_reports(reports: &[VerificationReport]) -> VerificationSummary {
    let total_declarations = reports.iter().map(|r| r.total_constants).sum();
    let total_kernel_verified = reports.iter().map(|r| r.kernel_verified).sum();
    let total_trusted_oracle = reports.iter().map(|r| r.trusted_oracle).sum();
    let kernel_verified_pct = if total_declarations > 0 {
        total_kernel_verified as f64 / total_declarations as f64 * 100.0
    } else {
        0.0
    };

    VerificationSummary {
        total_declarations,
        total_kernel_verified,
        total_trusted_oracle,
        kernel_verified_pct,
        per_source: reports.to_vec(),
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn build_verification_report(
    reader: &ShardReader,
    tc_results: &BatchSummary,
) -> MathverseResult<VerificationReport> {
    let per_module_counts = count_shard_results_by_module(reader, &tc_results.modules)?;

    let mut total_constants = 0usize;
    let mut kernel_verified = 0usize;
    for constant in &reader.constants {
        total_constants += 1;
        // Count both KernelVerified and SourceVerified as "verified" for
        // the legacy report schema.  Downstream consumers that need the
        // distinction should inspect the raw shard headers.
        if constant.import_confidence == ImportConfidence::KernelVerified as u8
            || constant.import_confidence == ImportConfidence::SourceVerified as u8
        {
            kernel_verified += 1;
        }
    }

    let per_module = tc_results
        .modules
        .iter()
        .map(|module| {
            let counts = per_module_counts
                .get(&module.module_name)
                .copied()
                .unwrap_or_default();
            let total = if counts.total > 0 {
                counts.total
            } else {
                module.constants_added
            };
            let verified = counts.kernel_verified.min(total);
            ModuleVerifyReport {
                module_name: module.module_name.clone(),
                total,
                kernel_verified: verified,
                trusted_oracle: total.saturating_sub(verified),
                errors: build_module_errors(module),
            }
        })
        .collect();

    Ok(VerificationReport {
        source_dir: tc_results.root_dir.clone(),
        total_constants,
        kernel_verified,
        trusted_oracle: total_constants.saturating_sub(kernel_verified),
        failed_load: tc_results.load_failure,
        elapsed_secs: tc_results.total_elapsed_secs,
        per_module,
    })
}

fn build_module_errors(module: &ModuleResult) -> BTreeMap<String, String> {
    let mut errors = module.tc_errors.clone();
    if let Some(load_error) = &module.load_error {
        errors.insert("<load>".to_string(), load_error.clone());
    }
    errors
}

fn upgrade_shard_trust_levels_with_confidence(
    shard_bytes: &[u8],
    tc_results: &BatchSummary,
    fallback_confidence: ImportConfidence,
) -> MathverseResult<Vec<u8>> {
    let reader =
        ShardReader::from_bytes(shard_bytes).map_err_context("reading shard for trust upgrade")?;
    let tc_error_set = build_tc_error_set(tc_results);
    let failed_modules = build_failed_module_set(tc_results);

    let mut writer = ShardWriter::new();
    for value in &reader.strings {
        writer.add_string(value);
    }
    for level in &reader.levels {
        writer.add_level(*level);
    }
    for expr in &reader.exprs {
        writer.add_expr(*expr);
    }

    for mut constant in reader.constants.iter().copied() {
        let name = constant_name(&reader, constant.name_idx)?;
        let failed_module = failed_modules
            .iter()
            .any(|module| module_matches_name(module, name));

        constant.import_confidence = if tc_error_set.contains(name) || failed_module {
            fallback_confidence as u8
        } else {
            // Name-match upgrade: the *source* .olean passed TC, but the
            // reconstructed mathverse representation may be lossy (placeholder
            // Sort(0), missing universe levels).  Use SourceVerified — not
            // KernelVerified — to avoid trust inflation.  Only constants
            // independently verified from shard reconstruction should receive
            // KernelVerified.
            ImportConfidence::SourceVerified as u8
        };
        writer.add_constant(constant);
    }

    writer.set_provenance(reader.provenance.clone());

    let mut upgraded = Vec::new();
    writer.write(&mut upgraded)?;
    Ok(upgraded)
}

fn count_shard_results_by_module(
    reader: &ShardReader,
    modules: &[ModuleResult],
) -> MathverseResult<HashMap<String, ModuleShardCounts>> {
    let mut ordered_modules: Vec<&str> = modules
        .iter()
        .map(|module| module.module_name.as_str())
        .collect();
    ordered_modules.sort_by_key(|right| std::cmp::Reverse(right.len()));

    let mut counts = HashMap::with_capacity(modules.len());
    for module in modules {
        counts.insert(module.module_name.clone(), ModuleShardCounts::default());
    }

    for constant in &reader.constants {
        let name = constant_name(reader, constant.name_idx)?;
        if let Some(module_name) = ordered_modules
            .iter()
            .copied()
            .find(|module_name| module_matches_name(module_name, name))
        {
            let entry = counts.entry(module_name.to_string()).or_default();
            entry.total += 1;
            if constant.import_confidence == ImportConfidence::KernelVerified as u8
                || constant.import_confidence == ImportConfidence::SourceVerified as u8
            {
                entry.kernel_verified += 1;
            }
        }
    }

    Ok(counts)
}

fn build_failed_module_set(tc_results: &BatchSummary) -> HashSet<String> {
    tc_results
        .modules
        .iter()
        .filter(|module| !module.load_ok)
        .map(|module| module.module_name.clone())
        .collect()
}

fn constant_name(reader: &ShardReader, idx: u32) -> MathverseResult<&str> {
    let idx = idx as usize;
    reader
        .strings
        .get(idx)
        .map(|name| name.as_str())
        .ok_or_else(|| {
            VerifyIntegrationError::InvalidNameIndex {
                idx: saturating_usize_to_u32(idx),
                count: reader.strings.len(),
            }
            .into()
        })
}

fn module_matches_name(module_name: &str, constant_name: &str) -> bool {
    constant_name == module_name
        || constant_name
            .strip_prefix(module_name)
            .is_some_and(|suffix| suffix.starts_with('.'))
}

fn confidence_for_fallback_trust(trust: TrustLevel) -> ImportConfidence {
    match trust {
        TrustLevel::KernelVerified => ImportConfidence::KernelVerified,
        TrustLevel::CertificateReplayed => ImportConfidence::Translated,
        TrustLevel::AxiomDependent
        | TrustLevel::PartiallyAxiomatized
        | TrustLevel::TrustedOracle => ImportConfidence::Axiomatized,
    }
}

fn shard_output_path(olean_dir: &Path, output_dir: &Path) -> PathBuf {
    let base = olean_dir
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| "lean4".to_string());
    output_dir.join(format!("{base}.mathverse"))
}

fn saturating_usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

#[derive(Clone, Copy, Debug, Default)]
struct ModuleShardCounts {
    total: usize,
    kernel_verified: usize,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[path = "integration_tests.rs"]
mod tests;
