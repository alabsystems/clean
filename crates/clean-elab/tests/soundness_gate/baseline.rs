// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 baseline and manifest helpers for the file-level soundness gate.
//!
//! Issue: #2543

use crate::common::{corpus_root, manifest_path, GateVerdict, GateVerdictTag};
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

/// Relative path to the checked-in Lean 4 file baseline.
pub(crate) const FILE_BASELINE_PATH: &str = "lean4_file_baseline.json";
/// Current schema version for the file-level baseline JSON.
pub(crate) const FILE_BASELINE_SCHEMA_VERSION: u32 = 1;

/// Corpus manifest entry — path relative to corpus root.
#[derive(Debug, Clone)]
pub(crate) struct ManifestEntry {
    pub(crate) path: String,
    pub(crate) expected: GateVerdictTag,
}

/// Checked-in Lean 4 verdict baseline for the file-level soundness gate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct Lean4FileBaseline {
    pub(crate) schema_version: u32,
    pub(crate) generated_at: String,
    pub(crate) lean4_version: String,
    pub(crate) corpus_sha256: String,
    pub(crate) cases: Vec<FileBaselineCase>,
}

/// One file verdict in the checked-in baseline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FileBaselineCase {
    pub(crate) path: String,
    pub(crate) verdict: GateVerdictTag,
}

impl Lean4FileBaseline {
    pub(crate) fn generate(manifest: &[ManifestEntry], corpus_root: &Path) -> Result<Self> {
        let lean4_version = get_lean4_version()?;
        let cases = manifest
            .iter()
            .map(|entry| {
                let file_path = corpus_root.join(&entry.path);
                let source = std::fs::read_to_string(&file_path)
                    .with_context(|| format!("failed to read {}", file_path.display()))?;
                let verdict = run_lean4_file(&source)?.tag();
                Ok(FileBaselineCase {
                    path: entry.path.clone(),
                    verdict,
                })
            })
            .collect::<Result<Vec<_>>>()?;

        let generated_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| format!("unix:{}", d.as_secs()))
            .unwrap_or_else(|_| "unknown".to_string());

        Ok(Self {
            schema_version: FILE_BASELINE_SCHEMA_VERSION,
            generated_at,
            lean4_version,
            corpus_sha256: compute_corpus_sha256(manifest, corpus_root)?,
            cases,
        })
    }

    pub(crate) fn load(path: &Path) -> Result<Self> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read {}", path.display()))?;
        serde_json::from_str(&content).with_context(|| "failed to parse baseline JSON")
    }

    pub(crate) fn save(&self, path: &Path) -> Result<()> {
        let content = serde_json::to_string_pretty(self)?;
        std::fs::write(path, content)
            .with_context(|| format!("failed to write {}", path.display()))?;
        Ok(())
    }

    pub(crate) fn validate(&self, manifest: &[ManifestEntry], corpus_root: &Path) -> Result<()> {
        if self.schema_version != FILE_BASELINE_SCHEMA_VERSION {
            return Err(anyhow!(
                "baseline schema version mismatch: {} != {} (expected). Regenerate with REGEN_BASELINE=1 cargo test -p clean-elab --test soundness_gate",
                self.schema_version,
                FILE_BASELINE_SCHEMA_VERSION
            ));
        }

        let current_sha = compute_corpus_sha256(manifest, corpus_root)?;
        if self.corpus_sha256 != current_sha {
            return Err(anyhow!(
                "soundness gate corpus changed since the Lean 4 baseline was generated.\nBaseline SHA: {}\nCurrent SHA:  {}\nRegenerate with REGEN_BASELINE=1 cargo test -p clean-elab --test soundness_gate",
                self.corpus_sha256,
                current_sha
            ));
        }

        self.validate_case_coverage(manifest)?;
        self.validate_lane_alignment(manifest)?;
        Ok(())
    }

    pub(crate) fn verdict_for(&self, path: &str) -> Result<GateVerdictTag> {
        self.cases
            .iter()
            .find(|case| case.path == path)
            .map(|case| case.verdict)
            .ok_or_else(|| anyhow!("missing Lean 4 baseline verdict for {path}"))
    }

    pub(crate) fn case_path_set(&self) -> HashSet<String> {
        self.cases.iter().map(|case| case.path.clone()).collect()
    }

    fn validate_case_coverage(&self, manifest: &[ManifestEntry]) -> Result<()> {
        let manifest_paths = manifest_path_set(manifest);
        let baseline_paths = self.case_path_set();

        let duplicate_cases = duplicate_baseline_paths(&self.cases);
        if !duplicate_cases.is_empty() {
            return Err(anyhow!(
                "baseline contains duplicate paths: {}",
                duplicate_cases.join(", ")
            ));
        }

        let missing_from_baseline = sorted_difference(&manifest_paths, &baseline_paths);
        let stale_baseline_cases = sorted_difference(&baseline_paths, &manifest_paths);
        if missing_from_baseline.is_empty() && stale_baseline_cases.is_empty() {
            return Ok(());
        }

        let mut message = String::from("baseline coverage does not match manifest:\n");
        if !missing_from_baseline.is_empty() {
            message.push_str("  missing baseline verdicts:\n");
            for path in &missing_from_baseline {
                message.push_str(&format!("    {path}\n"));
            }
        }
        if !stale_baseline_cases.is_empty() {
            message.push_str("  stale baseline entries not present in manifest:\n");
            for path in &stale_baseline_cases {
                message.push_str(&format!("    {path}\n"));
            }
        }
        message.push_str(
            "Regenerate with REGEN_BASELINE=1 cargo test -p clean-elab --test soundness_gate",
        );
        Err(anyhow!(message))
    }

    fn validate_lane_alignment(&self, manifest: &[ManifestEntry]) -> Result<()> {
        let mut lane_mismatches = Vec::new();
        for entry in manifest {
            let baseline_verdict = self.verdict_for(&entry.path)?;
            if baseline_verdict != entry.expected {
                lane_mismatches.push(format!(
                    "{}: manifest lane {} does not match Lean 4 baseline verdict {}",
                    entry.path, entry.expected, baseline_verdict
                ));
            }
        }
        if lane_mismatches.is_empty() {
            Ok(())
        } else {
            Err(anyhow!(lane_mismatches.join("\n")))
        }
    }
}

/// Load the soundness gate manifest from `tests/soundness_gate/manifest.txt`.
///
/// Lines starting with `#` are comments. Blank lines are skipped.
/// Paths starting with `accept/` expect acceptance; `reject/` expect rejection.
pub(crate) fn load_manifest(manifest_path: &Path) -> Vec<ManifestEntry> {
    let content = std::fs::read_to_string(manifest_path).unwrap_or_else(|e| {
        panic!(
            "Failed to read manifest at {}: {e}",
            manifest_path.display()
        )
    });

    content
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                return None;
            }
            let expected = if trimmed.starts_with("accept/") {
                GateVerdictTag::Accept
            } else if trimmed.starts_with("reject/") {
                GateVerdictTag::Reject
            } else {
                panic!("Manifest entry must start with 'accept/' or 'reject/': {trimmed}");
            };
            Some(ManifestEntry {
                path: trimmed.to_string(),
                expected,
            })
        })
        .collect()
}

static BASELINE_IO_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

fn baseline_io_lock() -> &'static Mutex<()> {
    BASELINE_IO_LOCK.get_or_init(|| Mutex::new(()))
}

/// Try to find the Lean 4 binary in PATH or ~/.elan/bin.
pub(crate) fn find_lean_binary() -> Option<PathBuf> {
    if let Some(path_var) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path_var) {
            let candidate = dir.join("lean");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    let home = std::env::var_os("HOME")?;
    let fallback = PathBuf::from(home).join(".elan").join("bin").join("lean");
    if fallback.is_file() {
        return Some(fallback);
    }
    None
}

/// Run a Lean source file through Lean 4 and return accept/reject verdict.
pub(crate) fn run_lean4_file(source: &str) -> Result<GateVerdict> {
    let lean = find_lean_binary().ok_or_else(|| {
        anyhow!("Lean4 binary not found in PATH or ~/.elan/bin. Install Lean4 to regenerate.")
    })?;

    let tmp = tempfile::Builder::new()
        .suffix(".lean")
        .tempfile()
        .context("failed to create temp Lean file")?;
    std::fs::write(tmp.path(), source)
        .with_context(|| format!("failed to write temp file {}", tmp.path().display()))?;

    let output = Command::new(lean)
        .arg(tmp.path())
        .output()
        .context("failed to run Lean4 on temp file")?;

    if output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error") {
            Ok(GateVerdict::Reject(
                stderr.lines().next().unwrap_or("unknown error").to_string(),
            ))
        } else {
            Ok(GateVerdict::Accept)
        }
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        Ok(GateVerdict::Reject(
            stderr.lines().next().unwrap_or("unknown error").to_string(),
        ))
    }
}

fn baseline_path() -> PathBuf {
    corpus_root().join(FILE_BASELINE_PATH)
}

fn baseline_regen_requested() -> bool {
    matches!(std::env::var("REGEN_BASELINE").as_deref(), Ok("1"))
}

fn manifest_path_set(manifest: &[ManifestEntry]) -> HashSet<String> {
    manifest.iter().map(|entry| entry.path.clone()).collect()
}

fn duplicate_baseline_paths(cases: &[FileBaselineCase]) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut duplicates = Vec::new();
    for case in cases {
        if !seen.insert(case.path.clone()) {
            duplicates.push(case.path.clone());
        }
    }
    duplicates.sort();
    duplicates.dedup();
    duplicates
}

fn sorted_difference(left: &HashSet<String>, right: &HashSet<String>) -> Vec<String> {
    let mut diff: Vec<_> = left.difference(right).cloned().collect();
    diff.sort();
    diff
}

fn validate_manifest_entries(manifest: &[ManifestEntry], corpus_root: &Path) -> Result<()> {
    let mut seen = HashSet::new();
    let mut duplicates = Vec::new();
    let mut missing_files = Vec::new();

    for entry in manifest {
        if !seen.insert(entry.path.clone()) {
            duplicates.push(entry.path.clone());
        }
        let file_path = corpus_root.join(&entry.path);
        if !file_path.is_file() {
            missing_files.push(entry.path.clone());
        }
    }

    duplicates.sort();
    duplicates.dedup();
    missing_files.sort();

    if !duplicates.is_empty() || !missing_files.is_empty() {
        let mut message = String::from("invalid soundness gate manifest:\n");
        if !duplicates.is_empty() {
            message.push_str("  duplicate manifest entries:\n");
            for path in &duplicates {
                message.push_str(&format!("    {path}\n"));
            }
        }
        if !missing_files.is_empty() {
            message.push_str("  manifest entries missing from disk:\n");
            for path in &missing_files {
                message.push_str(&format!("    {path}\n"));
            }
        }
        return Err(anyhow!(message));
    }

    Ok(())
}

fn compute_corpus_sha256(manifest: &[ManifestEntry], corpus_root: &Path) -> Result<String> {
    let mut hasher = Sha256::new();
    for entry in manifest {
        let file_path = corpus_root.join(&entry.path);
        hasher.update(entry.path.as_bytes());
        hasher.update(b"\n");
        let content = std::fs::read(&file_path)
            .with_context(|| format!("failed to read {}", file_path.display()))?;
        hasher.update(&content);
        hasher.update(b"\n\0");
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>())
}

fn get_lean4_version() -> Result<String> {
    let lean = find_lean_binary().ok_or_else(|| {
        anyhow!("Lean4 binary not found in PATH or ~/.elan/bin. Install Lean4 to regenerate.")
    })?;
    let output = Command::new(lean)
        .arg("--version")
        .output()
        .context("failed to run `lean --version`")?;
    if !output.status.success() {
        return Err(anyhow!("lean --version failed"));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

pub(crate) fn load_checked_in_file_baseline(manifest: &[ManifestEntry]) -> Lean4FileBaseline {
    let corpus = corpus_root();
    let baseline_path = baseline_path();
    let _guard = baseline_io_lock()
        .lock()
        .expect("soundness gate baseline lock poisoned");

    if baseline_regen_requested() {
        eprintln!(
            "Regenerating Lean 4 soundness-gate baseline at {}",
            baseline_path.display()
        );
        let baseline = Lean4FileBaseline::generate(manifest, &corpus).unwrap_or_else(|e| {
            panic!(
                "Failed to generate Lean 4 soundness-gate baseline at {}: {e:#}",
                baseline_path.display()
            )
        });
        baseline.save(&baseline_path).unwrap_or_else(|e| {
            panic!(
                "Failed to write Lean 4 soundness-gate baseline at {}: {e:#}",
                baseline_path.display()
            )
        });
        return baseline;
    }

    Lean4FileBaseline::load(&baseline_path).unwrap_or_else(|e| {
        panic!(
            "Failed to load Lean 4 soundness-gate baseline at {}: {e:#}\nRegenerate with `REGEN_BASELINE=1 cargo test -p clean-elab --test soundness_gate`.",
            baseline_path.display()
        )
    })
}

pub(crate) fn load_gate_manifest_and_baseline() -> (Vec<ManifestEntry>, Lean4FileBaseline) {
    let manifest = load_manifest(&manifest_path());
    let corpus = corpus_root();
    validate_manifest_entries(&manifest, &corpus).unwrap_or_else(|e| {
        panic!("Soundness gate manifest is invalid: {e:#}");
    });
    let baseline = load_checked_in_file_baseline(&manifest);
    baseline.validate(&manifest, &corpus).unwrap_or_else(|e| {
        panic!("Lean 4 soundness-gate baseline is invalid: {e:#}");
    });
    (manifest, baseline)
}

pub(crate) fn collect_corpus_files(corpus_root: &Path) -> Result<Vec<String>> {
    let mut files = Vec::new();
    for lane in ["accept", "reject"] {
        let lane_dir = corpus_root.join(lane);
        let entries = std::fs::read_dir(&lane_dir)
            .with_context(|| format!("failed to read {}", lane_dir.display()))?;
        for entry in entries {
            let entry = entry.with_context(|| format!("failed to read {}", lane_dir.display()))?;
            let path = entry.path();
            if !path.is_file() || path.extension().and_then(|ext| ext.to_str()) != Some("lean") {
                continue;
            }
            let file_name = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| anyhow!("non-utf8 corpus file path {}", path.display()))?;
            files.push(format!("{lane}/{file_name}"));
        }
    }
    files.sort();
    Ok(files)
}
