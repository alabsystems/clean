// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch import pipeline for loading multiple Lean 4 `.olean` files into
//! `.mathverse` shards.
//!
//! Walks a directory tree, discovers `.olean` files, parses each one via
//! `clean-olean`, runs the per-module importer from [`crate::lean4`], and
//! splits the output into shards respecting a configurable maximum constant
//! count per shard.

use std::path::{Path, PathBuf};

use clean_olean::parse_module_file;

use crate::error::{MathverseError, MathverseResult};
use crate::lean4::olean::alpha::{import_module, ImportStats};
use crate::shard::ShardWriter;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for batch importing Lean 4 `.olean` files.
#[derive(Clone, Debug)]
pub struct Lean4BatchConfig {
    /// Root directory to search for `.olean` files.
    pub olean_root: PathBuf,
    /// Maximum constants per shard (split into multiple shards if exceeded).
    pub max_constants_per_shard: u32,
    /// Whether to extract dependencies from expressions.
    pub extract_deps: bool,
    /// Module filter (if `Some`, only import modules matching these prefixes).
    pub module_filter: Option<Vec<String>>,
}

impl Lean4BatchConfig {
    /// Create a new configuration with sensible defaults.
    pub fn new(root: PathBuf) -> Self {
        Self {
            olean_root: root,
            max_constants_per_shard: 50_000,
            extract_deps: false,
            module_filter: None,
        }
    }

    /// Set the maximum number of constants per shard.
    pub fn with_max_per_shard(mut self, max: u32) -> Self {
        self.max_constants_per_shard = max;
        self
    }

    /// Enable dependency extraction.
    pub fn with_deps(mut self) -> Self {
        self.extract_deps = true;
        self
    }

    /// Set the module filter prefixes.
    pub fn with_filter(mut self, prefixes: Vec<String>) -> Self {
        self.module_filter = Some(prefixes);
        self
    }
}

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// Aggregate result of a batch import operation.
#[derive(Clone, Debug, Default)]
pub struct BatchImportResult {
    /// Paths to shard files written.
    pub shards_written: Vec<PathBuf>,
    /// Total `.olean` files discovered (before filtering).
    pub total_files: u32,
    /// Total constants imported across all shards.
    pub total_constants: u32,
    /// Total kernel-verified constants.
    pub total_kernel_verified: u32,
    /// Total axiomatized constants.
    pub total_axiomatized: u32,
    /// Total skipped constants.
    pub total_skipped: u32,
    /// Files that failed to parse (path, error message).
    pub files_failed: Vec<(PathBuf, String)>,
}

impl BatchImportResult {
    /// Merge per-file `ImportStats` into aggregate totals.
    fn accum(&mut self, stats: &ImportStats) {
        self.total_constants += stats.total;
        self.total_kernel_verified += stats.kernel_verified;
        self.total_axiomatized += stats.axiomatized;
        self.total_skipped += stats.skipped;
    }
}

// ---------------------------------------------------------------------------
// Path helpers
// ---------------------------------------------------------------------------

/// Convert an `.olean` file path to a Lean 4 module name.
///
/// Strips the `root` prefix and the `.olean` extension, then replaces
/// path separators with dots.
///
/// # Examples
///
/// ```text
/// root  = "./.elan/lib/lean"
/// path  = "./.elan/lib/lean/Init/Data/Nat/Basic.olean"
/// result = "Init.Data.Nat.Basic"
/// ```
pub fn path_to_module_name(path: &Path, root: &Path) -> String {
    let relative = path.strip_prefix(root).unwrap_or(path);
    let stem = relative.with_extension("");
    stem.to_string_lossy()
        .replace([std::path::MAIN_SEPARATOR, '/'], ".")
}

// ---------------------------------------------------------------------------
// Batch importer
// ---------------------------------------------------------------------------

/// Batch importer for Lean 4 `.olean` files.
pub struct Lean4BatchImporter {
    config: Lean4BatchConfig,
}

impl Lean4BatchImporter {
    /// Create a new batch importer with the given configuration.
    pub fn new(config: Lean4BatchConfig) -> Self {
        Self { config }
    }

    /// Discover all `.olean` files under the configured root directory.
    ///
    /// Returns paths sorted lexicographically for deterministic shard
    /// assignment.
    pub fn discover_files(&self) -> MathverseResult<Vec<PathBuf>> {
        let root = &self.config.olean_root;
        if !root.exists() {
            return Err(MathverseError::Io(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("olean root not found: {}", root.display()),
            )));
        }

        let mut files = Vec::new();
        collect_olean_files(root, &mut files)?;
        files.sort();

        // Apply module filter if configured.
        if let Some(ref prefixes) = self.config.module_filter {
            let root = &self.config.olean_root;
            files.retain(|p| {
                let module = path_to_module_name(p, root);
                prefixes.iter().any(|pfx| module.starts_with(pfx))
            });
        }

        Ok(files)
    }

    /// Import a single `.olean` file into a `ShardWriter`.
    ///
    /// Returns the number of constants imported.
    pub fn import_file(
        &self,
        path: &Path,
        writer: &mut ShardWriter,
    ) -> MathverseResult<ImportStats> {
        let module = parse_module_file(path).map_err(|e| MathverseError::ImportFailed {
            system: "Lean4".to_string(),
            reason: format!("{}: {e}", path.display()),
        })?;
        import_module(&module, writer)
    }

    /// Batch import all discovered `.olean` files.
    ///
    /// Writes one or more `.mathverse` shard files to `output_dir`, splitting
    /// when the constant count exceeds `max_constants_per_shard`.
    pub fn import_all(&self, output_dir: &Path) -> MathverseResult<BatchImportResult> {
        std::fs::create_dir_all(output_dir)?;

        let files = self.discover_files()?;
        let mut result = BatchImportResult {
            total_files: files.len() as u32,
            ..BatchImportResult::default()
        };

        let mut writer = ShardWriter::new();
        let mut shard_constants: u32 = 0;
        let mut shard_idx: u32 = 0;

        for path in &files {
            match self.import_file(path, &mut writer) {
                Ok(stats) => {
                    shard_constants += stats.total;
                    result.accum(&stats);
                }
                Err(e) => {
                    result.files_failed.push((path.clone(), e.to_string()));
                    continue;
                }
            }

            // Split shard if we've exceeded the limit.
            if shard_constants >= self.config.max_constants_per_shard {
                let shard_path = output_dir.join(format!("shard_{shard_idx:04}.mathverse"));
                writer.write_to_file(&shard_path)?;
                result.shards_written.push(shard_path);
                writer = ShardWriter::new();
                shard_constants = 0;
                shard_idx += 1;
            }
        }

        // Flush remaining constants.
        if shard_constants > 0 {
            let shard_path = output_dir.join(format!("shard_{shard_idx:04}.mathverse"));
            writer.write_to_file(&shard_path)?;
            result.shards_written.push(shard_path);
        }

        Ok(result)
    }
}

// ---------------------------------------------------------------------------
// Directory walker
// ---------------------------------------------------------------------------

/// Recursively collect all `.olean` files under `dir`.
fn collect_olean_files(dir: &Path, out: &mut Vec<PathBuf>) -> MathverseResult<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        let path = entry.path();
        if ft.is_dir() {
            collect_olean_files(&path, out)?;
        } else if ft.is_file() {
            if let Some(ext) = path.extension() {
                if ext == "olean" {
                    out.push(path);
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_discover;
