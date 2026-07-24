// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scale pipeline for batch `.vo` file processing.
//!
//! Processes directories of Coq `.vo` files in parallel using rayon,
//! extracting declarations and producing aggregate statistics. Designed
//! to handle the Coq stdlib (~2700 .vo files) and MathComp (~600 .vo
//! files) at scale.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use rayon::prelude::*;

use super::vo_parser::{self, VoDeclKind, VoDeclaration, VoFile, VoParseError};

// ---------------------------------------------------------------------------
// Pipeline configuration
// ---------------------------------------------------------------------------

/// Configuration for the `.vo` processing pipeline.
#[derive(Clone, Debug)]
pub struct PipelineConfig {
    /// Maximum file size to process (skip files larger than this).
    pub max_file_size: usize,
    /// Whether to collect full declarations or just count them.
    pub collect_declarations: bool,
    /// File extensions to process (default: ["vo"]).
    pub extensions: Vec<String>,
    /// Library path prefixes to include (empty = include all).
    pub include_prefixes: Vec<String>,
    /// Library path prefixes to exclude.
    pub exclude_prefixes: Vec<String>,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            max_file_size: 256 * 1024 * 1024, // 256 MB
            collect_declarations: true,
            extensions: vec!["vo".to_string()],
            include_prefixes: Vec::new(),
            exclude_prefixes: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline statistics
// ---------------------------------------------------------------------------

/// Statistics from a pipeline run.
#[derive(Clone, Debug, Default)]
pub struct PipelineStats {
    /// Total .vo files found.
    pub files_found: usize,
    /// Files successfully parsed.
    pub files_parsed: usize,
    /// Files that failed to parse.
    pub files_failed: usize,
    /// Files skipped (too large, excluded prefix, etc.).
    pub files_skipped: usize,
    /// Total declarations extracted.
    pub total_declarations: usize,
    /// Constant declarations.
    pub constants: usize,
    /// Inductive type declarations.
    pub inductives: usize,
    /// Module declarations.
    pub modules: usize,
    /// Other/unknown declarations.
    pub other: usize,
    /// Opaque (proof-carrying) declarations.
    pub opaque_count: usize,
    /// Total bytes processed.
    pub bytes_processed: u64,
    /// Errors encountered (file path + error message).
    pub errors: Vec<(PathBuf, String)>,
}

impl PipelineStats {
    /// Merge another stats object into this one.
    pub fn merge(&mut self, other: &PipelineStats) {
        self.files_found += other.files_found;
        self.files_parsed += other.files_parsed;
        self.files_failed += other.files_failed;
        self.files_skipped += other.files_skipped;
        self.total_declarations += other.total_declarations;
        self.constants += other.constants;
        self.inductives += other.inductives;
        self.modules += other.modules;
        self.other += other.other;
        self.opaque_count += other.opaque_count;
        self.bytes_processed += other.bytes_processed;
        self.errors.extend(other.errors.iter().cloned());
    }

    /// Summary line for progress reporting.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{} files ({} ok, {} fail, {} skip), {} decls ({} const, {} ind, {} mod), {:.1} MB",
            self.files_found,
            self.files_parsed,
            self.files_failed,
            self.files_skipped,
            self.total_declarations,
            self.constants,
            self.inductives,
            self.modules,
            self.bytes_processed as f64 / (1024.0 * 1024.0),
        )
    }
}

// ---------------------------------------------------------------------------
// Pipeline
// ---------------------------------------------------------------------------

/// Result from processing a single .vo file.
#[derive(Clone, Debug)]
pub struct FileResult {
    /// Path to the .vo file.
    pub path: PathBuf,
    /// Parsed .vo file (if successful).
    pub vo_file: Option<VoFile>,
    /// Declarations extracted.
    pub declarations: Vec<VoDeclaration>,
    /// Error (if parsing failed).
    pub error: Option<String>,
}

/// Process all `.vo` files in a directory tree.
///
/// Uses rayon for parallel processing. Returns aggregate statistics and
/// optionally the full list of declarations.
///
/// # Errors
///
/// Returns `VoParseError::Io` if the directory cannot be read.
pub fn process_directory(
    dir: &Path,
    config: &PipelineConfig,
) -> Result<(PipelineStats, Vec<VoDeclaration>), VoParseError> {
    // Collect all .vo files.
    let mut files = Vec::new();
    collect_vo_files(dir, &config.extensions, &mut files);
    files.sort();

    let total_found = files.len();

    // Atomic counters for progress tracking.
    let parsed_count = AtomicUsize::new(0);
    let failed_count = AtomicUsize::new(0);
    let skipped_count = AtomicUsize::new(0);

    // Process files in parallel.
    let results: Vec<FileResult> = files
        .par_iter()
        .map(|path| process_single_file(path, config, &parsed_count, &failed_count, &skipped_count))
        .collect();

    // Aggregate statistics.
    let mut stats = PipelineStats {
        files_found: total_found,
        ..Default::default()
    };
    let mut all_decls = Vec::new();

    for result in &results {
        if let Some(err_msg) = &result.error {
            stats.files_failed += 1;
            stats.errors.push((result.path.clone(), err_msg.clone()));
        } else if result.vo_file.is_some() {
            stats.files_parsed += 1;
            if let Ok(meta) = std::fs::metadata(&result.path) {
                stats.bytes_processed += meta.len();
            }
        } else {
            stats.files_skipped += 1;
        }

        for decl in &result.declarations {
            stats.total_declarations += 1;
            match decl.kind {
                VoDeclKind::Constant => stats.constants += 1,
                VoDeclKind::Inductive => stats.inductives += 1,
                VoDeclKind::Module => stats.modules += 1,
                VoDeclKind::Universe | VoDeclKind::Other => stats.other += 1,
            }
            if decl.is_opaque {
                stats.opaque_count += 1;
            }
        }

        if config.collect_declarations {
            all_decls.extend(result.declarations.iter().cloned());
        }
    }

    Ok((stats, all_decls))
}

/// Process a single .vo file.
fn process_single_file(
    path: &Path,
    config: &PipelineConfig,
    _parsed: &AtomicUsize,
    _failed: &AtomicUsize,
    _skipped: &AtomicUsize,
) -> FileResult {
    // Check file size.
    let meta = match std::fs::metadata(path) {
        Ok(m) => m,
        Err(e) => {
            return FileResult {
                path: path.to_path_buf(),
                vo_file: None,
                declarations: Vec::new(),
                error: Some(format!("metadata error: {e}")),
            };
        }
    };

    if meta.len() as usize > config.max_file_size {
        _skipped.fetch_add(1, Ordering::Relaxed);
        return FileResult {
            path: path.to_path_buf(),
            vo_file: None,
            declarations: Vec::new(),
            error: None,
        };
    }

    // Check include/exclude prefixes against the file path.
    let path_str = path.display().to_string();
    if !config.include_prefixes.is_empty()
        && !config
            .include_prefixes
            .iter()
            .any(|p| path_str.contains(p.as_str()))
    {
        _skipped.fetch_add(1, Ordering::Relaxed);
        return FileResult {
            path: path.to_path_buf(),
            vo_file: None,
            declarations: Vec::new(),
            error: None,
        };
    }
    if config
        .exclude_prefixes
        .iter()
        .any(|p| path_str.contains(p.as_str()))
    {
        _skipped.fetch_add(1, Ordering::Relaxed);
        return FileResult {
            path: path.to_path_buf(),
            vo_file: None,
            declarations: Vec::new(),
            error: None,
        };
    }

    // Read and parse.
    let data = match std::fs::read(path) {
        Ok(d) => d,
        Err(e) => {
            _failed.fetch_add(1, Ordering::Relaxed);
            return FileResult {
                path: path.to_path_buf(),
                vo_file: None,
                declarations: Vec::new(),
                error: Some(format!("read error: {e}")),
            };
        }
    };

    match vo_parser::parse_vo_file(&data) {
        Ok(vo) => {
            _parsed.fetch_add(1, Ordering::Relaxed);
            let declarations = vo.declarations.clone();
            FileResult {
                path: path.to_path_buf(),
                vo_file: Some(vo),
                declarations,
                error: None,
            }
        }
        Err(e) => {
            _failed.fetch_add(1, Ordering::Relaxed);
            FileResult {
                path: path.to_path_buf(),
                vo_file: None,
                declarations: Vec::new(),
                error: Some(e.to_string()),
            }
        }
    }
}

/// Recursively collect files with matching extensions.
fn collect_vo_files(dir: &Path, extensions: &[String], out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(_) => return,
    };

    for entry in entries.filter_map(|e| e.ok()) {
        let path = entry.path();
        if path.is_dir() {
            collect_vo_files(&path, extensions, out);
        } else if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if extensions.iter().any(|x| x == ext) {
                out.push(path);
            }
        }
    }
}

/// Quick scan: count .vo files in a directory without parsing them.
#[must_use]
pub fn count_vo_files(dir: &Path) -> usize {
    let mut files = Vec::new();
    collect_vo_files(dir, &["vo".to_string()], &mut files);
    files.len()
}

/// Progress callback type for long-running pipeline operations.
pub type ProgressCallback = Box<dyn Fn(usize, usize) + Send + Sync>;

/// Process directory with progress reporting.
///
/// Calls `on_progress(files_done, files_total)` periodically during
/// processing.
pub fn process_directory_with_progress(
    dir: &Path,
    config: &PipelineConfig,
    on_progress: ProgressCallback,
) -> Result<(PipelineStats, Vec<VoDeclaration>), VoParseError> {
    let mut files = Vec::new();
    collect_vo_files(dir, &config.extensions, &mut files);
    files.sort();

    let total = files.len();
    let done = AtomicUsize::new(0);
    let parsed_count = AtomicUsize::new(0);
    let failed_count = AtomicUsize::new(0);
    let skipped_count = AtomicUsize::new(0);

    let all_decls = Mutex::new(Vec::new());
    let stats_mu = Mutex::new(PipelineStats {
        files_found: total,
        ..Default::default()
    });

    files.par_iter().for_each(|path| {
        let result =
            process_single_file(path, config, &parsed_count, &failed_count, &skipped_count);

        // Update stats under lock.
        {
            let mut stats = stats_mu.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(err_msg) = &result.error {
                stats.files_failed += 1;
                stats.errors.push((result.path.clone(), err_msg.clone()));
            } else if result.vo_file.is_some() {
                stats.files_parsed += 1;
                if let Ok(meta) = std::fs::metadata(&result.path) {
                    stats.bytes_processed += meta.len();
                }
            } else {
                stats.files_skipped += 1;
            }

            for decl in &result.declarations {
                stats.total_declarations += 1;
                match decl.kind {
                    VoDeclKind::Constant => stats.constants += 1,
                    VoDeclKind::Inductive => stats.inductives += 1,
                    VoDeclKind::Module => stats.modules += 1,
                    VoDeclKind::Universe | VoDeclKind::Other => stats.other += 1,
                }
                if decl.is_opaque {
                    stats.opaque_count += 1;
                }
            }
        }

        if config.collect_declarations {
            let mut decls = all_decls.lock().unwrap_or_else(|e| e.into_inner());
            decls.extend(result.declarations);
        }

        let current = done.fetch_add(1, Ordering::Relaxed) + 1;
        if current.is_multiple_of(50) || current == total {
            on_progress(current, total);
        }
    });

    let stats = stats_mu.into_inner().unwrap_or_else(|e| e.into_inner());
    let decls = all_decls.into_inner().unwrap_or_else(|e| e.into_inner());

    Ok((stats, decls))
}
