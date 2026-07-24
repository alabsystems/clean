// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathlib-to-Mathverse build pipeline.
//!
//! Discovers all `.olean` roots for a full Mathlib ecosystem build
//! (Lean toolchain Init/Std, lake packages, Mathlib itself), then
//! delegates to [`crate::build_library::build_lean4_library`] per-root
//! and merges results into `.mathverse` shards.

use std::path::{Path, PathBuf};
use std::time::Instant;

use tracing::{info, warn};

use crate::build_library::{build_lean4_library, BuildConfig, BuildResult};
use crate::error::{MathverseError, MathverseResult};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Default Mathlib .olean root (after `setup_mathlib_oleans.sh`).
pub const DEFAULT_MATHLIB_OLEAN_ROOT: &str = "data/raw/mathlib4/.lake/build/lib";

/// Default lake packages root.
pub const DEFAULT_PACKAGES_ROOT: &str = "data/raw/mathlib4/.lake/packages";

/// Default output directory for Mathlib mathverse shards.
pub const DEFAULT_OUTPUT_DIR: &str = "data/mathverse-library/mathlib";

/// Default shard size (larger than Init's 5,000).
const DEFAULT_SHARD_SIZE: usize = 10_000;

/// Default max .olean file size (2.5 MB).
const DEFAULT_MAX_FILE_SIZE: u64 = 2_500_000;

// ---------------------------------------------------------------------------
// MathlibBuildConfig
// ---------------------------------------------------------------------------

/// Configuration for building the full Mathlib Mathverse Library.
#[derive(Clone, Debug)]
pub struct MathlibBuildConfig {
    /// Root directory containing Mathlib .olean files.
    pub mathlib_olean_root: PathBuf,
    /// Root directory for lake packages (batteries, aesop, Qq, etc.).
    pub packages_root: PathBuf,
    /// Lean 4 toolchain library. `None` = auto-detect.
    pub toolchain_lib: Option<PathBuf>,
    /// Output directory for .mathverse shards and manifest.
    pub output_dir: PathBuf,
    /// Maximum constants per shard before splitting.
    pub shard_size_limit: usize,
    /// Maximum .olean file size in bytes (0 = no limit).
    pub max_file_size: u64,
    /// Limit total .olean files processed (0 = no limit).
    pub file_limit: usize,
    /// Print progress information.
    pub verbose: bool,
}

impl Default for MathlibBuildConfig {
    fn default() -> Self {
        Self {
            mathlib_olean_root: PathBuf::from(DEFAULT_MATHLIB_OLEAN_ROOT),
            packages_root: PathBuf::from(DEFAULT_PACKAGES_ROOT),
            toolchain_lib: None,
            output_dir: PathBuf::from(DEFAULT_OUTPUT_DIR),
            shard_size_limit: DEFAULT_SHARD_SIZE,
            max_file_size: DEFAULT_MAX_FILE_SIZE,
            file_limit: 0,
            verbose: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// Result from a single .olean root directory.
#[derive(Clone, Debug)]
pub struct RootBuildResult {
    /// Label (e.g., "toolchain", "pkg:batteries", "mathlib").
    pub label: String,
    /// Path to the root directory.
    pub root_dir: PathBuf,
    /// Build result for this root.
    pub result: BuildResult,
}

/// Aggregate result of the full Mathlib build.
#[derive(Clone, Debug, Default)]
pub struct MathlibBuildResult {
    /// Per-root results, in processing order.
    pub root_results: Vec<RootBuildResult>,
    /// Total constants across all roots.
    pub total_constants: usize,
    /// Total shards written.
    pub total_shards: usize,
    /// Total files parsed.
    pub total_files_parsed: usize,
    /// Total files failed.
    pub total_files_failed: usize,
    /// Wall-clock elapsed time in milliseconds.
    pub elapsed_ms: u64,
}

// ---------------------------------------------------------------------------
// Root discovery
// ---------------------------------------------------------------------------

/// Discover all .olean root directories for a Mathlib build.
///
/// Returns `(label, path)` pairs for each existing root:
/// - Lean toolchain (Init, Std, Lean, Lake)
/// - Lake packages (batteries, aesop, Qq, proofwidgets)
/// - Mathlib itself
pub fn discover_olean_roots(config: &MathlibBuildConfig) -> Vec<(String, PathBuf)> {
    let mut roots = Vec::new();
    discover_toolchain_root(config, &mut roots);
    discover_package_roots(config, &mut roots);
    discover_mathlib_root(config, &mut roots);
    roots
}

fn discover_toolchain_root(config: &MathlibBuildConfig, roots: &mut Vec<(String, PathBuf)>) {
    if let Some(ref tc) = config.toolchain_lib {
        if tc.exists() {
            roots.push(("toolchain".to_string(), tc.clone()));
        } else {
            warn!(
                path = %tc.display(),
                "SKIP toolchain root: configured toolchain_lib does not exist — fix the \
                 path or set toolchain_lib=None to auto-detect ~/.elan/toolchains"
            );
        }
    } else if let Some(tc) = auto_detect_toolchain() {
        roots.push(("toolchain".to_string(), tc));
    } else {
        warn!(
            "SKIP toolchain root: no leanprover toolchain found under ~/.elan/toolchains — \
             install one via elan, or set MathlibBuildConfig.toolchain_lib explicitly"
        );
    }
}

fn discover_package_roots(config: &MathlibBuildConfig, roots: &mut Vec<(String, PathBuf)>) {
    if !config.packages_root.exists() {
        warn!(
            path = %config.packages_root.display(),
            "SKIP lake package roots: packages_root does not exist — run \
             scripts/setup_mathlib_oleans.sh or point MathlibBuildConfig.packages_root at \
             <mathlib4>/.lake/packages"
        );
        return;
    }
    let Ok(entries) = std::fs::read_dir(&config.packages_root) else {
        warn!(
            path = %config.packages_root.display(),
            "SKIP lake package roots: packages_root exists but cannot be read (check \
             permissions)"
        );
        return;
    };
    let mut pkg_entries: Vec<_> = entries
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .collect();
    pkg_entries.sort_by_key(|e| e.file_name());

    for entry in pkg_entries {
        let name = entry.file_name().to_string_lossy().to_string();
        let pkg = entry.path();
        let candidates = [
            pkg.join("lib").join("lean"),
            pkg.join("build").join("lib"),
            pkg.join(".lake").join("build").join("lib"),
        ];
        for candidate in &candidates {
            if candidate.exists() {
                roots.push((format!("pkg:{name}"), candidate.clone()));
                break;
            }
        }
    }
}

fn discover_mathlib_root(config: &MathlibBuildConfig, roots: &mut Vec<(String, PathBuf)>) {
    if config.mathlib_olean_root.exists() {
        roots.push(("mathlib".to_string(), config.mathlib_olean_root.clone()));
    } else {
        // Loud by design: a "Mathlib build" that silently drops Mathlib itself
        // is a success-shaped failure (toolchain/package roots still build).
        warn!(
            path = %config.mathlib_olean_root.display(),
            "SKIP mathlib root: mathlib_olean_root does not exist — the build will \
             proceed WITHOUT Mathlib itself; run scripts/setup_mathlib_oleans.sh or point \
             MathlibBuildConfig.mathlib_olean_root at <mathlib4>/.lake/build/lib"
        );
    }
}

/// Auto-detect the newest Lean 4 toolchain under `~/.elan/toolchains/`.
fn auto_detect_toolchain() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let tc_dir = Path::new(&home).join(".elan").join("toolchains");
    if !tc_dir.exists() {
        return None;
    }
    let entries = std::fs::read_dir(&tc_dir).ok()?;
    let mut best: Option<PathBuf> = None;
    for entry in entries.filter_map(|e| e.ok()) {
        let name = entry.file_name().to_string_lossy().to_string();
        if name.starts_with("leanprover") {
            let lib = entry.path().join("lib").join("lean");
            if lib.exists() {
                best = Some(lib);
            }
        }
    }
    best
}

// ---------------------------------------------------------------------------
// Build pipeline
// ---------------------------------------------------------------------------

/// Build an Mathverse Library from the full Mathlib ecosystem.
///
/// Discovers all .olean roots, processes each via
/// `build_lean4_library`, and aggregates results.
pub fn build_mathlib_library(config: &MathlibBuildConfig) -> MathverseResult<MathlibBuildResult> {
    let start = Instant::now();
    let roots = discover_olean_roots(config);

    if roots.is_empty() {
        return Err(MathverseError::ImportFailed {
            system: "Mathlib".to_string(),
            reason: format!(
                "no .olean roots found: mathlib_olean_root `{}` and packages_root `{}` do \
                 not exist, and no Lean toolchain was {} — run \
                 scripts/setup_mathlib_oleans.sh to populate them, or set the \
                 MathlibBuildConfig paths explicitly",
                config.mathlib_olean_root.display(),
                config.packages_root.display(),
                match &config.toolchain_lib {
                    Some(tc) => format!("found at the configured `{}`", tc.display()),
                    None => "auto-detected under ~/.elan/toolchains".to_string(),
                }
            ),
        });
    }

    log_discovered_roots(&roots, config.verbose);

    let mut result = MathlibBuildResult::default();
    for (label, root_path) in &roots {
        let root_result = build_single_root(label, root_path, config)?;
        accumulate_result(&mut result, &root_result);
        result.root_results.push(root_result);
    }

    result.elapsed_ms = start.elapsed().as_millis() as u64;
    log_final_summary(&result, config.verbose);
    Ok(result)
}

fn build_single_root(
    label: &str,
    root_path: &Path,
    config: &MathlibBuildConfig,
) -> MathverseResult<RootBuildResult> {
    let build_config = BuildConfig {
        lean_lib_dir: root_path.to_path_buf(),
        output_dir: config.output_dir.clone(),
        modules: vec![],
        shard_size_limit: config.shard_size_limit,
        max_file_size: config.max_file_size,
        verbose: config.verbose,
    };

    info!(label, path = %root_path.display(), "building root");
    let br = build_lean4_library(&build_config)?;

    if config.verbose {
        info!(
            label,
            files_parsed = br.files_parsed,
            constants = br.total_constants,
            shards = br.shards_written,
            "root complete"
        );
    }

    Ok(RootBuildResult {
        label: label.to_string(),
        root_dir: root_path.to_path_buf(),
        result: br,
    })
}

fn accumulate_result(agg: &mut MathlibBuildResult, rr: &RootBuildResult) {
    agg.total_constants += rr.result.total_constants;
    agg.total_shards += rr.result.shards_written;
    agg.total_files_parsed += rr.result.files_parsed;
    agg.total_files_failed += rr.result.files_failed;
}

fn log_discovered_roots(roots: &[(String, PathBuf)], verbose: bool) {
    if !verbose {
        return;
    }
    info!(count = roots.len(), "discovered .olean roots");
    for (label, path) in roots {
        info!(label, path = %path.display(), "root");
    }
}

fn log_final_summary(result: &MathlibBuildResult, verbose: bool) {
    if !verbose {
        return;
    }
    info!(
        roots = result.root_results.len(),
        constants = result.total_constants,
        shards = result.total_shards,
        files_parsed = result.total_files_parsed,
        files_failed = result.total_files_failed,
        elapsed_ms = result.elapsed_ms,
        "mathlib build complete"
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
