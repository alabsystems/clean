// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse source refresh pipeline: staleness detection, incremental updates,
//! and version tracking for upstream formal math library sources.
//!
//! Reads `data/mathverse_sources.toml` to determine which upstream repositories
//! have new commits, fetches updates for stale sources, and records the
//! latest commit SHAs and timestamps.

use std::path::Path;
use std::process::Command;

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};

// ---------------------------------------------------------------------------
// Manifest types
// ---------------------------------------------------------------------------

/// Top-level TOML manifest containing all upstream sources.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SourceManifest {
    /// The list of upstream formal math library sources.
    #[serde(rename = "source")]
    pub sources: Vec<SourceEntry>,
}

/// A single upstream source repository entry.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SourceEntry {
    pub name: String,
    pub git_url: String,
    pub file_type: String,
    pub import_tier: u8,
    pub clone_path: String,
    pub last_fetched_sha: String,
    pub last_fetched_date: String,
}

// ---------------------------------------------------------------------------
// Refresh status types
// ---------------------------------------------------------------------------

/// Status of a single source after staleness check.
#[derive(Clone, Debug)]
pub struct SourceStatus {
    pub name: String,
    pub clone_exists: bool,
    pub local_sha: String,
    pub remote_sha: String,
    pub is_stale: bool,
    pub error: Option<String>,
}

/// Summary of a refresh operation across all sources.
#[derive(Clone, Debug)]
pub struct RefreshReport {
    pub statuses: Vec<SourceStatus>,
    pub stale_count: usize,
    pub up_to_date_count: usize,
    pub error_count: usize,
}

/// Result of fetching updates for a single source.
#[derive(Clone, Debug)]
pub struct FetchResult {
    pub name: String,
    pub success: bool,
    pub new_sha: String,
    pub old_sha: String,
    pub error: Option<String>,
}

// ---------------------------------------------------------------------------
// Core API
// ---------------------------------------------------------------------------

/// Load the source manifest from a TOML file.
pub fn load_manifest(path: &Path) -> MathverseResult<SourceManifest> {
    let text = std::fs::read_to_string(path).map_err(|e| {
        MathverseError::Io(std::io::Error::new(
            e.kind(),
            format!("reading manifest {}: {e}", path.display()),
        ))
    })?;
    parse_manifest(&text)
}

/// Parse a source manifest from TOML text.
pub fn parse_manifest(text: &str) -> MathverseResult<SourceManifest> {
    toml::from_str(text).map_err(|e| MathverseError::ImportFailed {
        system: "mathverse_sources".to_string(),
        reason: format!("TOML parse error: {e}"),
    })
}

/// Save the manifest back to a TOML file (for updating SHAs after fetch).
///
/// Preserves leading comment lines from the original file if it exists,
/// since `toml::to_string_pretty` strips comments.
pub fn save_manifest(manifest: &SourceManifest, path: &Path) -> MathverseResult<()> {
    let text = toml::to_string_pretty(manifest).map_err(|e| MathverseError::ImportFailed {
        system: "mathverse_sources".to_string(),
        reason: format!("TOML serialize error: {e}"),
    })?;

    // Preserve leading comment block from the existing file.
    let header = if path.exists() {
        let existing = std::fs::read_to_string(path).unwrap_or_default();
        let comment_lines: Vec<&str> = existing
            .lines()
            .take_while(|line| line.starts_with('#') || line.is_empty())
            .collect();
        if comment_lines.is_empty() {
            String::new()
        } else {
            let mut h = comment_lines.join("\n");
            h.push('\n');
            h
        }
    } else {
        String::new()
    };

    let output = if header.is_empty() {
        text
    } else {
        format!("{header}\n{text}")
    };
    std::fs::write(path, output)?;
    Ok(())
}

/// Check staleness of all sources in the manifest.
pub fn check_staleness(manifest: &SourceManifest) -> RefreshReport {
    let mut statuses = Vec::with_capacity(manifest.sources.len());
    let (mut stale, mut ok, mut err) = (0, 0, 0);

    for source in &manifest.sources {
        let status = check_source_staleness(source);
        match (&status.error, status.is_stale) {
            (Some(_), _) => err += 1,
            (None, true) => stale += 1,
            (None, false) => ok += 1,
        }
        statuses.push(status);
    }

    RefreshReport {
        statuses,
        stale_count: stale,
        up_to_date_count: ok,
        error_count: err,
    }
}

/// Check staleness for a single source.
fn check_source_staleness(source: &SourceEntry) -> SourceStatus {
    let clone_path = Path::new(&source.clone_path);
    let clone_exists = clone_path.join(".git").exists();
    let local_sha = if clone_exists {
        get_local_head(clone_path).unwrap_or_default()
    } else {
        String::new()
    };

    let remote_sha = match get_remote_head(&source.git_url) {
        Ok(sha) => sha,
        Err(e) => {
            return SourceStatus {
                name: source.name.clone(),
                clone_exists,
                local_sha,
                remote_sha: String::new(),
                is_stale: !clone_exists,
                error: Some(e.to_string()),
            };
        }
    };

    let is_stale = !clone_exists || local_sha != remote_sha;
    SourceStatus {
        name: source.name.clone(),
        clone_exists,
        local_sha,
        remote_sha,
        is_stale,
        error: None,
    }
}

/// Fetch updates for all stale sources. Updates manifest SHAs in place.
pub fn fetch_updates(manifest: &mut SourceManifest) -> Vec<FetchResult> {
    let mut results = Vec::with_capacity(manifest.sources.len());
    for source in &mut manifest.sources {
        let clone_exists = Path::new(&source.clone_path).join(".git").exists();
        let old_sha = if clone_exists {
            get_local_head(Path::new(&source.clone_path)).unwrap_or_default()
        } else {
            String::new()
        };
        let result = if clone_exists {
            fetch_existing(source, &old_sha)
        } else {
            clone_new(source)
        };
        if result.success {
            source.last_fetched_sha.clone_from(&result.new_sha);
            source.last_fetched_date = date_iso_today();
        }
        results.push(result);
    }
    results
}

fn fetch_existing(source: &SourceEntry, old_sha: &str) -> FetchResult {
    let r = Command::new("git")
        .args(["fetch", "--depth", "1", "origin"])
        .current_dir(&source.clone_path)
        .output();
    match r {
        Ok(out) if out.status.success() => {
            let _ = Command::new("git")
                .args(["reset", "--hard", "FETCH_HEAD"])
                .current_dir(&source.clone_path)
                .output();
            let new_sha = get_local_head(Path::new(&source.clone_path)).unwrap_or_default();
            FetchResult {
                name: source.name.clone(),
                success: true,
                new_sha,
                old_sha: old_sha.to_string(),
                error: None,
            }
        }
        Ok(out) => FetchResult {
            name: source.name.clone(),
            success: false,
            new_sha: String::new(),
            old_sha: old_sha.to_string(),
            error: Some(format!(
                "git fetch failed: {}",
                String::from_utf8_lossy(&out.stderr)
            )),
        },
        Err(e) => FetchResult {
            name: source.name.clone(),
            success: false,
            new_sha: String::new(),
            old_sha: old_sha.to_string(),
            error: Some(format!("git fetch error: {e}")),
        },
    }
}

fn clone_new(source: &SourceEntry) -> FetchResult {
    let r = Command::new("git")
        .args(["clone", "--depth", "1", &source.git_url, &source.clone_path])
        .output();
    match r {
        Ok(out) if out.status.success() => {
            let new_sha = get_local_head(Path::new(&source.clone_path)).unwrap_or_default();
            FetchResult {
                name: source.name.clone(),
                success: true,
                new_sha,
                old_sha: String::new(),
                error: None,
            }
        }
        Ok(out) => FetchResult {
            name: source.name.clone(),
            success: false,
            new_sha: String::new(),
            old_sha: String::new(),
            error: Some(format!(
                "git clone failed: {}",
                String::from_utf8_lossy(&out.stderr)
            )),
        },
        Err(e) => FetchResult {
            name: source.name.clone(),
            success: false,
            new_sha: String::new(),
            old_sha: String::new(),
            error: Some(format!("git clone error: {e}")),
        },
    }
}

// ---------------------------------------------------------------------------
// Git helpers
// ---------------------------------------------------------------------------

/// Get the HEAD commit SHA of a local git repository.
pub(crate) fn get_local_head(repo_path: &Path) -> MathverseResult<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo_path)
        .output()
        .map_err(MathverseError::Io)?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(MathverseError::ImportFailed {
            system: "git".to_string(),
            reason: format!("rev-parse HEAD failed in {}", repo_path.display()),
        })
    }
}

/// Get the remote HEAD commit SHA via `git ls-remote`.
pub(crate) fn get_remote_head(url: &str) -> MathverseResult<String> {
    let output = Command::new("git")
        .args(["ls-remote", "--exit-code", url, "HEAD"])
        .output()
        .map_err(MathverseError::Io)?;
    if output.status.success() {
        let line = String::from_utf8_lossy(&output.stdout);
        return Ok(line.split_whitespace().next().unwrap_or("").to_string());
    }
    // Fallback: scan for main/master branch.
    let output2 = Command::new("git")
        .args(["ls-remote", url])
        .output()
        .map_err(MathverseError::Io)?;
    if output2.status.success() {
        let stdout = String::from_utf8_lossy(&output2.stdout);
        for line in stdout.lines() {
            if line.contains("refs/heads/main") || line.contains("refs/heads/master") {
                return Ok(line.split_whitespace().next().unwrap_or("").to_string());
            }
        }
    }
    Err(MathverseError::ImportFailed {
        system: "git".to_string(),
        reason: format!("ls-remote failed for {url}"),
    })
}

fn date_iso_today() -> String {
    Command::new("date")
        .args(["+%Y-%m-%d"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// Display helpers
// ---------------------------------------------------------------------------

impl RefreshReport {
    /// Format a human-readable summary. Returns lines for the caller to print.
    pub fn format_summary(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let _ = writeln!(out, "=== Mathverse Source Refresh Status ===\n");
        let _ = writeln!(
            out,
            "  Total: {}, Stale: {}, Up-to-date: {}, Errors: {}\n",
            self.statuses.len(),
            self.stale_count,
            self.up_to_date_count,
            self.error_count
        );
        let _ = writeln!(
            out,
            "  {:<25} {:<8} {:<12} {:<12} Status",
            "Source", "Clone?", "Local SHA", "Remote SHA"
        );
        let _ = writeln!(out, "  {}", "-".repeat(75));
        for s in &self.statuses {
            let clone = if s.clone_exists { "yes" } else { "NO" };
            let local = short_sha(&s.local_sha);
            let remote = short_sha(&s.remote_sha);
            let tag = match (&s.error, s.is_stale) {
                (Some(e), _) => format!("ERROR: {e}"),
                (None, true) => "STALE".to_string(),
                (None, false) => "ok".to_string(),
            };
            let _ = writeln!(
                out,
                "  {:<25} {:<8} {:<12} {:<12} {}",
                &s.name[..25.min(s.name.len())],
                clone,
                local,
                remote,
                tag
            );
        }
        out
    }
}

fn short_sha(sha: &str) -> String {
    if sha.is_empty() {
        "-".to_string()
    } else {
        sha[..7.min(sha.len())].to_string()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
