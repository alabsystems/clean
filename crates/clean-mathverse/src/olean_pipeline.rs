// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Olean binary pipeline for converting `.olean` files into `.mathverse` shards.
//!
//! This module provides [`OleanPipelineConfig`] and [`run_olean_pipeline`] to
//! discover `.olean` files under a directory, convert them to `.mathverse` shards
//! via [`olean_bridge::convert_olean_dir_to_mathverse`], and write the
//! results to a persistent output directory using [`ConvertOutputWriter`].
//!
//! The pipeline is wired into `convert_all` as the `.olean` binary conversion
//! phase, replacing the prior dead-code path.

use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::error::{MathverseError, MathverseResult};
use crate::export::convert_output::{ConvertOutputWriter, OutputSummary, SystemSummary};
use crate::lean4::olean::olean_bridge::{self, ConvertResult};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the `.olean` binary conversion pipeline.
#[derive(Clone, Debug)]
pub struct OleanPipelineConfig {
    /// Input directories containing `.olean` files.
    pub input_dirs: Vec<PathBuf>,
    /// Output directory for `.mathverse` shards.
    pub output_dir: PathBuf,
    /// Whether to verify reconstructed shards after conversion.
    pub verify_after_convert: bool,
    /// Module prefixes to include (empty = all modules).
    pub module_filter: Vec<String>,
}

impl OleanPipelineConfig {
    /// Create a config from a single input directory and an output directory.
    pub fn new(input_dir: &Path, output_dir: &Path) -> Self {
        Self {
            input_dirs: vec![input_dir.to_path_buf()],
            output_dir: output_dir.to_path_buf(),
            verify_after_convert: false,
            module_filter: Vec::new(),
        }
    }

    /// Create a config from multiple input directories.
    pub fn from_dirs(input_dirs: Vec<PathBuf>, output_dir: &Path) -> Self {
        Self {
            input_dirs,
            output_dir: output_dir.to_path_buf(),
            verify_after_convert: false,
            module_filter: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline result
// ---------------------------------------------------------------------------

/// Aggregate result from a pipeline run.
#[derive(Clone, Debug, Default)]
pub struct OleanPipelineResult {
    /// Number of input directories processed.
    pub dirs_processed: usize,
    /// Number of directories that failed entirely.
    pub dirs_failed: usize,
    /// Total constants across all shards.
    pub total_constants: u32,
    /// Total kernel-verified constants.
    pub kernel_verified: u32,
    /// Total axiomatized constants.
    pub axiomatized: u32,
    /// Number of shard files written.
    pub shards_written: usize,
    /// Per-directory results.
    pub per_dir: Vec<DirConvertResult>,
    /// Wall-clock elapsed milliseconds.
    pub elapsed_ms: u64,
}

/// Result for a single input directory.
#[derive(Clone, Debug)]
pub struct DirConvertResult {
    /// Directory path.
    pub dir: PathBuf,
    /// Shard output path (if successful).
    pub shard_path: Option<PathBuf>,
    /// Conversion result (if successful).
    pub result: Option<ConvertResult>,
    /// Error message (if failed).
    pub error: Option<String>,
}

// ---------------------------------------------------------------------------
// Pipeline execution
// ---------------------------------------------------------------------------

/// Run the `.olean` binary conversion pipeline.
///
/// For each input directory, discovers `.olean` files, converts them to an
/// `.mathverse` shard, and writes the shard to the output directory. Individual
/// directory failures are recorded but do not abort the pipeline.
pub fn run_olean_pipeline(config: &OleanPipelineConfig) -> MathverseResult<OleanPipelineResult> {
    let start = Instant::now();
    std::fs::create_dir_all(&config.output_dir)?;

    let mut result = OleanPipelineResult::default();
    let filter = if config.module_filter.is_empty() {
        None
    } else {
        Some(config.module_filter.as_slice())
    };

    for dir in &config.input_dirs {
        let dir_result = convert_single_dir(dir, &config.output_dir, filter);
        accumulate_dir_result(&mut result, dir_result);
    }

    result.elapsed_ms = start.elapsed().as_millis() as u64;
    Ok(result)
}

/// Convert a single `.olean` directory to a `.mathverse` shard.
fn convert_single_dir(
    dir: &Path,
    output_dir: &Path,
    filter: Option<&[String]>,
) -> DirConvertResult {
    let dir_name = dir
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let shard_name = sanitize_shard_name(&dir_name);
    let shard_path = output_dir.join(format!("{shard_name}.mathverse"));

    match olean_bridge::convert_olean_dir_to_mathverse(dir, &shard_path, filter) {
        Ok(conv) => DirConvertResult {
            dir: dir.to_path_buf(),
            shard_path: Some(shard_path),
            result: Some(conv),
            error: None,
        },
        Err(e) => DirConvertResult {
            dir: dir.to_path_buf(),
            shard_path: None,
            result: None,
            error: Some(e.to_string()),
        },
    }
}

/// Accumulate a single directory result into the aggregate pipeline result.
fn accumulate_dir_result(agg: &mut OleanPipelineResult, dir_result: DirConvertResult) {
    agg.dirs_processed += 1;
    if let Some(ref conv) = dir_result.result {
        agg.total_constants += conv.total_constants;
        agg.kernel_verified += conv.kernel_verified;
        agg.axiomatized += conv.axiomatized;
        agg.shards_written += 1;
    } else {
        agg.dirs_failed += 1;
    }
    agg.per_dir.push(dir_result);
}

// ---------------------------------------------------------------------------
// Output integration
// ---------------------------------------------------------------------------

/// Update an `OutputSummary` with olean pipeline results.
pub fn update_output_summary(summary: &mut OutputSummary, pipeline: &OleanPipelineResult) {
    for dir_result in &pipeline.per_dir {
        if let Some(ref conv) = dir_result.result {
            let dir_name = dir_result
                .dir
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();

            summary.add_system(SystemSummary {
                system: "lean4-olean".to_string(),
                source: dir_name,
                total_constants: conv.total_constants as usize,
                kernel_verified: conv.kernel_verified as usize,
                shard_count: 1,
            });
        }
    }
}

/// Write olean pipeline shards to a `ConvertOutputWriter`.
///
/// Copies each successful shard into the writer's system directory.
pub fn write_pipeline_shards(
    writer: &ConvertOutputWriter,
    pipeline: &OleanPipelineResult,
) -> MathverseResult<Vec<PathBuf>> {
    if !writer.is_active() {
        return Ok(Vec::new());
    }

    let mut written = Vec::new();
    for dir_result in &pipeline.per_dir {
        if let Some(ref shard_path) = dir_result.shard_path {
            let shard_name = dir_result
                .dir
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();

            let data = std::fs::read(shard_path).map_err(|source| {
                MathverseError::ShardFileUnreadable {
                    path: shard_path.display().to_string(),
                    source,
                }
            })?;
            let dest = writer.write_shard("lean4-olean", &shard_name, &data)?;
            written.push(dest);
        }
    }

    Ok(written)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Sanitize a directory name into a valid shard filename component.
fn sanitize_shard_name(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' {
                c
            } else {
                '_'
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
    use crate::export::convert_output::OutputSummary;

    #[test]
    fn test_olean_pipeline_config_new() {
        let cfg =
            OleanPipelineConfig::new(Path::new("/tmp/lean_lib"), Path::new("/tmp/mathverse_out"));
        assert_eq!(cfg.input_dirs.len(), 1);
        assert_eq!(cfg.output_dir, PathBuf::from("/tmp/mathverse_out"));
        assert!(!cfg.verify_after_convert);
        assert!(cfg.module_filter.is_empty());
    }

    #[test]
    fn test_olean_pipeline_config_from_dirs() {
        let cfg = OleanPipelineConfig::from_dirs(
            vec![PathBuf::from("/a"), PathBuf::from("/b")],
            Path::new("/out"),
        );
        assert_eq!(cfg.input_dirs.len(), 2);
    }

    #[test]
    fn test_sanitize_shard_name() {
        assert_eq!(sanitize_shard_name("Init"), "Init");
        assert_eq!(sanitize_shard_name("lean4-v4.13"), "lean4-v4.13");
        assert_eq!(sanitize_shard_name("path/to/dir"), "path_to_dir");
        assert_eq!(sanitize_shard_name("hello world"), "hello_world");
    }

    #[test]
    fn test_pipeline_empty_dirs() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let cfg = OleanPipelineConfig::from_dirs(Vec::new(), tmp.path());
        let result = run_olean_pipeline(&cfg).expect("run pipeline");
        assert_eq!(result.dirs_processed, 0);
        assert_eq!(result.shards_written, 0);
        assert_eq!(result.total_constants, 0);
    }

    #[test]
    fn test_pipeline_nonexistent_dir_records_failure() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let cfg = OleanPipelineConfig::from_dirs(
            vec![PathBuf::from("/nonexistent/olean/dir")],
            tmp.path(),
        );
        let result = run_olean_pipeline(&cfg).expect("run pipeline");
        assert_eq!(result.dirs_processed, 1);
        assert_eq!(result.dirs_failed, 1);
        assert_eq!(result.shards_written, 0);
        assert!(result.per_dir[0].error.is_some());
    }

    #[test]
    fn test_pipeline_empty_dir_records_zero_constants() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let input_dir = tmp.path().join("empty_lean");
        std::fs::create_dir_all(&input_dir).expect("mkdir");
        let output_dir = tmp.path().join("output");

        let cfg = OleanPipelineConfig::new(&input_dir, &output_dir);
        let result = run_olean_pipeline(&cfg).expect("run pipeline");

        // Empty dir should succeed but produce zero constants.
        assert_eq!(result.dirs_processed, 1);
        assert_eq!(result.total_constants, 0);
    }

    #[test]
    fn test_update_output_summary() {
        let mut summary = OutputSummary::new();
        let pipeline = OleanPipelineResult {
            dirs_processed: 1,
            dirs_failed: 0,
            total_constants: 100,
            kernel_verified: 80,
            axiomatized: 20,
            shards_written: 1,
            per_dir: vec![DirConvertResult {
                dir: PathBuf::from("/test/lean"),
                shard_path: Some(PathBuf::from("/out/lean.mathverse")),
                result: Some(ConvertResult {
                    total_constants: 100,
                    kernel_verified: 80,
                    kernel_verified_from_tc: 0,
                    axiomatized: 20,
                    skipped: 0,
                    provenance_records: 100,
                    modules: vec!["Init".to_string()],
                    failures: Vec::new(),
                }),
                error: None,
            }],
            elapsed_ms: 500,
        };

        update_output_summary(&mut summary, &pipeline);
        assert_eq!(summary.total_declarations, 100);
        assert_eq!(summary.total_kernel_verified, 80);
        assert_eq!(summary.systems.len(), 1);
        assert_eq!(summary.systems[0].system, "lean4-olean");
    }

    #[test]
    fn test_update_output_summary_skips_failures() {
        let mut summary = OutputSummary::new();
        let pipeline = OleanPipelineResult {
            dirs_processed: 1,
            dirs_failed: 1,
            per_dir: vec![DirConvertResult {
                dir: PathBuf::from("/bad"),
                shard_path: None,
                result: None,
                error: Some("not found".to_string()),
            }],
            ..Default::default()
        };

        update_output_summary(&mut summary, &pipeline);
        assert_eq!(summary.total_declarations, 0);
        assert!(summary.systems.is_empty());
    }

    #[test]
    fn test_convert_single_dir_nonexistent() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let result = convert_single_dir(Path::new("/nonexistent"), tmp.path(), None);
        assert!(result.error.is_some());
        assert!(result.result.is_none());
        assert!(result.shard_path.is_none());
    }

    #[test]
    fn test_accumulate_dir_result_success() {
        let mut agg = OleanPipelineResult::default();
        let dir_result = DirConvertResult {
            dir: PathBuf::from("/test"),
            shard_path: Some(PathBuf::from("/out/test.mathverse")),
            result: Some(ConvertResult {
                total_constants: 50,
                kernel_verified: 40,
                kernel_verified_from_tc: 0,
                axiomatized: 10,
                skipped: 0,
                provenance_records: 50,
                modules: vec!["Test".to_string()],
                failures: Vec::new(),
            }),
            error: None,
        };

        accumulate_dir_result(&mut agg, dir_result);
        assert_eq!(agg.dirs_processed, 1);
        assert_eq!(agg.dirs_failed, 0);
        assert_eq!(agg.total_constants, 50);
        assert_eq!(agg.kernel_verified, 40);
        assert_eq!(agg.shards_written, 1);
    }

    #[test]
    fn test_accumulate_dir_result_failure() {
        let mut agg = OleanPipelineResult::default();
        let dir_result = DirConvertResult {
            dir: PathBuf::from("/bad"),
            shard_path: None,
            result: None,
            error: Some("failed".to_string()),
        };

        accumulate_dir_result(&mut agg, dir_result);
        assert_eq!(agg.dirs_processed, 1);
        assert_eq!(agg.dirs_failed, 1);
        assert_eq!(agg.shards_written, 0);
    }
}
