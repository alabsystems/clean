// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch kernel verification of constants stored in `.mathverse` shard files.
//!
//! For each constant, reconstructs the type (and optionally value) expression
//! from the shard's FlatExpr arena, then attempts kernel type-checking via
//! `Environment::add_decl()`. Returns structured statistics without side effects.

pub mod cake_gate;
mod constant_verify;
pub mod native_gate;
mod native_gate_helpers;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;
use thiserror::Error;

use constant_verify::verify_shard_file;

pub use cake_gate::{
    verify_cake_shard, verify_cake_shard_dir, CakeGateError, CakeGateReport, CakeGateViolation,
};
pub use native_gate::{
    verify_native_shard, verify_native_shard_dir, NativeGateError, NativeGateReport,
    NativeGateViolation,
};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Configuration for shard-directory verification.
#[derive(Debug, Clone)]
pub struct VerifyConfig {
    pub parallel: bool,
    pub max_threads: Option<usize>,
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            parallel: true,
            max_threads: None,
        }
    }
}

/// Result of batch-verifying all `.mathverse` shards in a directory.
#[derive(Debug, Default)]
pub struct VerifyStats {
    pub shards_processed: u64,
    pub shards_skipped: u64,
    pub total_constants: u64,
    pub kernel_verified: u64,
    pub translated: u64,
    pub reconstruct_failed: u64,
    pub type_check_failed: u64,
    pub elapsed_secs: f64,
}

/// Per-source-system breakdown.
#[derive(Debug)]
pub struct SystemStats {
    pub source_system: u8,
    pub total: u64,
    pub kernel_verified: u64,
    pub translated: u64,
    pub failed: u64,
}

/// Result of verifying a single shard file.
#[derive(Debug)]
pub struct ShardResult {
    pub path: PathBuf,
    pub num_constants: usize,
    pub verified: u64,
    pub translated: u64,
    pub failed: u64,
    pub elapsed_secs: f64,
    pub error: Option<String>,
}

/// Full verification report for a shard directory.
#[derive(Debug)]
pub struct VerifyReport {
    pub stats: VerifyStats,
    pub per_system: HashMap<u8, SystemStats>,
    pub shard_results: Vec<ShardResult>,
}

/// Errors returned when writing verification JSON output.
#[derive(Debug, Error)]
pub enum WriteResultsJsonError {
    #[error("JSON serialization failed: {0}")]
    Serialize(#[from] serde_json::Error),
    #[error("failed to write {path}: {source}")]
    Write {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Verify all `.mathverse` shards listed in `mathverse_files`.
///
/// Pure computation -- does not print output. Callers use the returned
/// `VerifyReport` to display results or write JSON.
pub fn verify_shard_dir(mathverse_files: &[PathBuf], config: VerifyConfig) -> VerifyReport {
    let start = Instant::now();
    let mut report = if config.parallel {
        verify_shard_dir_parallel(mathverse_files, &config)
    } else {
        verify_shard_dir_sequential(mathverse_files)
    };
    report.stats.elapsed_secs = start.elapsed().as_secs_f64();
    report
}

/// Verify all `.mathverse` shards using the default configuration.
pub fn verify_shard_dir_default(mathverse_files: &[PathBuf]) -> VerifyReport {
    verify_shard_dir(mathverse_files, VerifyConfig::default())
}

/// Map source-system ID to display name.
pub fn source_system_name(id: u8) -> &'static str {
    match id {
        0 => "Lean4",
        1 => "Coq",
        2 => "Agda",
        3 => "Idris2",
        4 => "FStar",
        5 => "Cedille",
        6 => "Isabelle",
        7 => "HOLLight",
        8 => "HOL4",
        9 => "Metamath",
        10 => "Mizar",
        11 => "Dafny",
        12 => "Why3",
        27 => "clean",
        69 => "Cake",
        _ => "Other",
    }
}

/// Serialize a `VerifyReport` to JSON and write to `output_path`.
pub fn write_results_json(
    report: &VerifyReport,
    output_path: &Path,
) -> Result<(), WriteResultsJsonError> {
    let mut systems: Vec<_> = report.per_system.values().collect();
    systems.sort_by_key(|b| std::cmp::Reverse(b.total));

    let results = serde_json::json!({
        "shards_processed": report.stats.shards_processed,
        "shards_skipped": report.stats.shards_skipped,
        "total_constants": report.stats.total_constants,
        "kernel_verified": report.stats.kernel_verified,
        "translated": report.stats.translated,
        "reconstruct_failed": report.stats.reconstruct_failed,
        "type_check_failed": report.stats.type_check_failed,
        "elapsed_secs": report.stats.elapsed_secs,
        "constants_per_sec": constants_per_sec(&report.stats),
        "per_system": systems.iter().map(|s| serde_json::json!({
            "system": source_system_name(s.source_system),
            "total": s.total,
            "kernel_verified": s.kernel_verified,
            "translated": s.translated,
            "failed": s.failed,
        })).collect::<Vec<_>>(),
    });

    let json_str = serde_json::to_string_pretty(&results)?;
    fs::write(output_path, json_str).map_err(|source| WriteResultsJsonError::Write {
        path: output_path.to_path_buf(),
        source,
    })
}

/// Discover all `.mathverse` shard files in a directory tree (recursive).
pub fn discover_mathverse_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_mathverse_files_recursive(dir, &mut files);
    files.sort();
    files
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn verify_shard_dir_sequential(mathverse_files: &[PathBuf]) -> VerifyReport {
    let mut per_system: HashMap<u8, SystemStats> = HashMap::new();
    let mut stats = VerifyStats::default();
    let mut shard_results = Vec::with_capacity(mathverse_files.len());

    for path in mathverse_files {
        let shard = verify_shard_file(path);
        merge_verify_stats(&mut stats, &shard.stats);
        merge_system_stats(&mut per_system, shard.per_system);
        shard_results.push(shard.result);
    }

    VerifyReport {
        stats,
        per_system,
        shard_results,
    }
}

fn verify_shard_dir_parallel(mathverse_files: &[PathBuf], config: &VerifyConfig) -> VerifyReport {
    let run = || -> Vec<constant_verify::ShardVerification> {
        mathverse_files
            .par_iter()
            .map(|path| verify_shard_file(path))
            .collect()
    };

    let shard_verifications = if let Some(n) = config.max_threads.filter(|n| *n > 0) {
        match ThreadPoolBuilder::new().num_threads(n).build() {
            Ok(pool) => pool.install(run),
            Err(_) => run(),
        }
    } else {
        run()
    };

    let mut stats = VerifyStats::default();
    let mut per_system = HashMap::new();
    let mut shard_results = Vec::with_capacity(shard_verifications.len());

    for shard in shard_verifications {
        merge_verify_stats(&mut stats, &shard.stats);
        merge_system_stats(&mut per_system, shard.per_system);
        shard_results.push(shard.result);
    }

    VerifyReport {
        stats,
        per_system,
        shard_results,
    }
}

fn merge_verify_stats(dst: &mut VerifyStats, src: &VerifyStats) {
    dst.shards_processed += src.shards_processed;
    dst.shards_skipped += src.shards_skipped;
    dst.total_constants += src.total_constants;
    dst.kernel_verified += src.kernel_verified;
    dst.translated += src.translated;
    dst.reconstruct_failed += src.reconstruct_failed;
    dst.type_check_failed += src.type_check_failed;
}

fn merge_system_stats(dst: &mut HashMap<u8, SystemStats>, src: HashMap<u8, SystemStats>) {
    for (source_system, stats) in src {
        let entry = dst.entry(source_system).or_insert_with(|| SystemStats {
            source_system,
            total: 0,
            kernel_verified: 0,
            translated: 0,
            failed: 0,
        });
        entry.total += stats.total;
        entry.kernel_verified += stats.kernel_verified;
        entry.translated += stats.translated;
        entry.failed += stats.failed;
    }
}

fn constants_per_sec(stats: &VerifyStats) -> f64 {
    if stats.elapsed_secs > 0.0 {
        stats.total_constants as f64 / stats.elapsed_secs
    } else {
        0.0
    }
}

fn collect_mathverse_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_mathverse_files_recursive(&path, out);
            } else if path.extension().is_some_and(|e| e == "mathverse") {
                out.push(path);
            }
        }
    }
}

#[cfg(test)]
mod tests;
