// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Output directory support for `mathverse_convert`.
//!
//! When `--output-dir` is specified, `ConvertOutputWriter` creates a structured
//! output directory with per-system subdirectories containing `.mathverse` binary
//! shards and `.mathverse.json` metadata sidecars.
//!
//! Directory layout:
//! ```text
//! <output_dir>/
//!   mathverse_summary.json          -- aggregate summary
//!   lean4/
//!     Init.mathverse                -- binary shard
//!     Init.mathverse.json           -- metadata sidecar
//!     Std.mathverse
//!     Std.mathverse.json
//!   metamath/
//!     set.mathverse
//!     set.mathverse.json
//! ```

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};
use crate::shard_metadata::{self, ShardMetadata};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Output configuration for `convert_all`.
#[derive(Debug, Clone)]
pub struct ConvertOutputConfig {
    /// Root directory for structured output. If `None`, no persistent output.
    pub output_dir: Option<PathBuf>,

    /// Whether to copy/write binary `.mathverse` shards to the output directory.
    pub write_binary_shards: bool,

    /// Whether to write `.mathverse.json` metadata sidecars.
    pub write_metadata: bool,

    /// Whether to write only aggregate counts (no per-declaration metadata).
    pub write_counts_only: bool,
}

impl Default for ConvertOutputConfig {
    fn default() -> Self {
        Self {
            output_dir: None,
            write_binary_shards: true,
            write_metadata: true,
            write_counts_only: false,
        }
    }
}

impl ConvertOutputConfig {
    /// Create a config with an output directory and all output types enabled.
    #[must_use]
    pub fn with_output_dir(dir: impl Into<PathBuf>) -> Self {
        Self {
            output_dir: Some(dir.into()),
            ..Default::default()
        }
    }
}

// ---------------------------------------------------------------------------
// Writer
// ---------------------------------------------------------------------------

/// Writes conversion output to a structured directory.
///
/// Each system gets a subdirectory. The writer creates directories lazily
/// when the first file for a system is written.
pub struct ConvertOutputWriter {
    config: ConvertOutputConfig,
}

impl ConvertOutputWriter {
    /// Create a new writer. Creates the root output directory if needed.
    pub fn new(config: ConvertOutputConfig) -> MathverseResult<Self> {
        if let Some(ref dir) = config.output_dir {
            fs::create_dir_all(dir)?;
        }
        Ok(Self { config })
    }

    /// Whether this writer has a configured output directory.
    #[must_use]
    pub fn is_active(&self) -> bool {
        self.config.output_dir.is_some()
    }

    /// Get the system subdirectory path, creating it if needed.
    pub fn system_dir(&self, system_name: &str) -> MathverseResult<PathBuf> {
        let root = self.output_dir_or_err()?;
        let dir = root.join(sanitize_dirname(system_name));
        fs::create_dir_all(&dir)?;
        Ok(dir)
    }

    /// Write a binary shard file into the system subdirectory.
    ///
    /// Returns the path where the shard was written.
    pub fn write_shard(
        &self,
        system_name: &str,
        shard_name: &str,
        data: &[u8],
    ) -> MathverseResult<PathBuf> {
        if !self.config.write_binary_shards {
            return Err(MathverseError::ImportFailed {
                system: system_name.to_string(),
                reason: "binary shard writing is disabled".to_string(),
            });
        }
        let dir = self.system_dir(system_name)?;
        let path = dir.join(format!("{shard_name}.mathverse"));
        fs::write(&path, data)?;
        Ok(path)
    }

    /// Write a metadata sidecar for a shard in the system subdirectory.
    ///
    /// Returns the path where the metadata was written.
    pub fn write_shard_metadata(
        &self,
        system_name: &str,
        shard_name: &str,
        metadata: &ShardMetadata,
    ) -> MathverseResult<PathBuf> {
        if !self.config.write_metadata {
            return Err(MathverseError::ImportFailed {
                system: system_name.to_string(),
                reason: "metadata writing is disabled".to_string(),
            });
        }
        let dir = self.system_dir(system_name)?;
        let shard_path = dir.join(format!("{shard_name}.mathverse"));
        shard_metadata::write_metadata(&shard_path, metadata)?;
        Ok(shard_metadata::sidecar_path_for(&shard_path))
    }

    /// Write the aggregate summary JSON to the output directory root.
    pub fn write_summary(&self, summary: &OutputSummary) -> MathverseResult<PathBuf> {
        let root = self.output_dir_or_err()?;
        let path = root.join("mathverse_summary.json");
        let json = serde_json::to_string_pretty(summary)?;
        fs::write(&path, json)?;
        Ok(path)
    }

    fn output_dir_or_err(&self) -> MathverseResult<&Path> {
        self.config
            .output_dir
            .as_deref()
            .ok_or_else(|| MathverseError::ImportFailed {
                system: "convert_output".to_string(),
                reason: "no output directory configured".to_string(),
            })
    }
}

// ---------------------------------------------------------------------------
// Summary types
// ---------------------------------------------------------------------------

/// Aggregate summary written to `mathverse_summary.json` in the output directory.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct OutputSummary {
    /// Format version.
    pub version: String,

    /// Total declarations across all systems.
    pub total_declarations: usize,

    /// Total kernel-verified declarations.
    pub total_kernel_verified: usize,

    /// Kernel verification percentage.
    pub kernel_verified_pct: f64,

    /// Per-system summaries.
    pub systems: Vec<SystemSummary>,
}

impl OutputSummary {
    /// Create a new empty summary.
    #[must_use]
    pub fn new() -> Self {
        Self {
            version: "0.1.0".to_string(),
            ..Default::default()
        }
    }

    /// Recompute `kernel_verified_pct` from the current totals.
    pub fn recompute_pct(&mut self) {
        self.kernel_verified_pct = if self.total_declarations > 0 {
            self.total_kernel_verified as f64 / self.total_declarations as f64 * 100.0
        } else {
            0.0
        };
    }

    /// Add a system summary and update aggregate totals.
    pub fn add_system(&mut self, sys: SystemSummary) {
        self.total_declarations += sys.total_constants;
        self.total_kernel_verified += sys.kernel_verified;
        self.systems.push(sys);
        self.recompute_pct();
    }
}

/// Per-system summary within the aggregate output.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemSummary {
    /// System name (e.g. `"lean4"`, `"metamath"`).
    pub system: String,

    /// Source identifier (directory name, file name).
    pub source: String,

    /// Total constants in this system.
    pub total_constants: usize,

    /// Kernel-verified constant count.
    pub kernel_verified: usize,

    /// Number of shard files written for this system.
    pub shard_count: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Sanitize a system name for use as a directory name.
///
/// Lowercases and replaces non-alphanumeric characters with hyphens.
#[must_use]
pub(crate) fn sanitize_dirname(name: &str) -> String {
    name.to_lowercase()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize_dirname() {
        assert_eq!(sanitize_dirname("Lean4"), "lean4");
        assert_eq!(sanitize_dirname("HOL Light"), "hol-light");
        assert_eq!(sanitize_dirname("F*"), "f-");
        assert_eq!(sanitize_dirname("clean_native"), "clean_native");
    }

    #[test]
    fn test_convert_output_config_default() {
        let cfg = ConvertOutputConfig::default();
        assert!(cfg.output_dir.is_none());
        assert!(cfg.write_binary_shards);
        assert!(cfg.write_metadata);
        assert!(!cfg.write_counts_only);
    }

    #[test]
    fn test_convert_output_config_with_dir() {
        let cfg = ConvertOutputConfig::with_output_dir("/tmp/mathverse_out");
        assert_eq!(cfg.output_dir, Some(PathBuf::from("/tmp/mathverse_out")));
        assert!(cfg.write_binary_shards);
    }

    #[test]
    fn test_writer_inactive_when_no_dir() {
        let cfg = ConvertOutputConfig::default();
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");
        assert!(!writer.is_active());
    }

    #[test]
    fn test_writer_creates_output_dir() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig::with_output_dir(&out);
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");
        assert!(writer.is_active());
        assert!(out.exists());
    }

    #[test]
    fn test_writer_system_dir_creation() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig::with_output_dir(&out);
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");

        let sys_dir = writer.system_dir("Lean4").expect("create system dir");
        assert_eq!(sys_dir, out.join("lean4"));
        assert!(sys_dir.exists());
    }

    #[test]
    fn test_writer_write_shard() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig::with_output_dir(&out);
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");

        let data = b"fake mathverse shard data";
        let path = writer
            .write_shard("Lean4", "Init", data)
            .expect("write shard");

        assert_eq!(path, out.join("lean4").join("Init.mathverse"));
        assert_eq!(fs::read(&path).expect("read back"), data);
    }

    #[test]
    fn test_writer_write_metadata() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig::with_output_dir(&out);
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");

        let mut meta = ShardMetadata::new("Lean4");
        meta.push(shard_metadata::MetadataEntry {
            name: "Nat.zero".to_string(),
            kind: Some(shard_metadata::DeclKind::Definition),
            type_signature: Some("Nat".to_string()),
            source_file: None,
            line_number: None,
        });

        let path = writer
            .write_shard_metadata("Lean4", "Init", &meta)
            .expect("write metadata");

        assert_eq!(path, out.join("lean4").join("Init.mathverse.json"));
        assert!(path.exists());

        // Verify roundtrip through load_metadata
        let shard_path = out.join("lean4").join("Init.mathverse");
        // Create a dummy shard so the sidecar path is correct
        fs::write(&shard_path, b"dummy").expect("write dummy shard");
        let loaded = shard_metadata::load_metadata(&shard_path).expect("load");
        assert_eq!(loaded.system_name, "Lean4");
        assert_eq!(loaded.declaration_count, 1);
    }

    #[test]
    fn test_writer_write_summary() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig::with_output_dir(&out);
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");

        let mut summary = OutputSummary::new();
        summary.add_system(SystemSummary {
            system: "lean4".to_string(),
            source: "Init".to_string(),
            total_constants: 100,
            kernel_verified: 95,
            shard_count: 1,
        });

        let path = writer.write_summary(&summary).expect("write summary");
        assert_eq!(path, out.join("mathverse_summary.json"));
        assert!(path.exists());

        let contents = fs::read_to_string(&path).expect("read summary");
        let parsed: OutputSummary = serde_json::from_str(&contents).expect("parse summary");
        assert_eq!(parsed.total_declarations, 100);
        assert_eq!(parsed.total_kernel_verified, 95);
        assert_eq!(parsed.systems.len(), 1);
    }

    #[test]
    fn test_output_summary_recompute_pct() {
        let mut s = OutputSummary::new();
        s.total_declarations = 200;
        s.total_kernel_verified = 150;
        s.recompute_pct();
        assert!((s.kernel_verified_pct - 75.0).abs() < 0.01);
    }

    #[test]
    fn test_output_summary_empty_pct() {
        let mut s = OutputSummary::new();
        s.recompute_pct();
        assert!((s.kernel_verified_pct).abs() < 0.01);
    }

    #[test]
    fn test_writer_shard_disabled() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig {
            output_dir: Some(out),
            write_binary_shards: false,
            write_metadata: true,
            write_counts_only: false,
        };
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");
        let result = writer.write_shard("Lean4", "Init", b"data");
        assert!(result.is_err());
    }

    #[test]
    fn test_writer_metadata_disabled() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let out = dir.path().join("output");
        let cfg = ConvertOutputConfig {
            output_dir: Some(out),
            write_binary_shards: true,
            write_metadata: false,
            write_counts_only: false,
        };
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");

        let meta = ShardMetadata::new("Lean4");
        let result = writer.write_shard_metadata("Lean4", "Init", &meta);
        assert!(result.is_err());
    }

    #[test]
    fn test_no_output_dir_errors() {
        let cfg = ConvertOutputConfig::default();
        let writer = ConvertOutputWriter::new(cfg).expect("create writer");
        let result = writer.write_summary(&OutputSummary::new());
        assert!(result.is_err());
    }
}
