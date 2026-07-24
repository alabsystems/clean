// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build script for the `clean` binary: embed the git SHA the binary was built
//! from and its build timestamp so `clean mathverse isabelle-doctor` can report
//! the running binary's identity and detect a STALE binary (the incident where a
//! chain script picked a 5-day-old binary via `ls | head -1`).
//!
//! Dependency-free by design (std + `git` only; no `vergen`). When `git` is
//! absent — e.g. a source tarball with no `.git` — the SHA falls back to
//! `"unknown"`, which the doctor reports as an un-verifiable build (a loud WARN,
//! never a silent pass).

use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn main() {
    // Build timestamp (seconds since the Unix epoch).
    let build_unix = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    println!("cargo:rustc-env=CLEAN_BUILD_UNIX={build_unix}");

    // Git SHA the binary is built from (fallback: "unknown").
    let sha = git(&["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown".to_string());
    println!("cargo:rustc-env=CLEAN_BUILD_GIT_SHA={sha}");

    // Re-run this script (and so re-capture the SHA) whenever HEAD or the
    // checked-out branch ref moves. `git rev-parse --git-path` resolves the real
    // locations even inside a linked worktree (where `.git` is a file).
    rerun_if_git_path_changes(&["--git-path", "HEAD"]);
    rerun_if_git_path_changes(&["--git-path", "packed-refs"]);
    if let Some(head_ref) = git(&["symbolic-ref", "-q", "HEAD"]) {
        rerun_if_git_path_changes(&["--git-path", &head_ref]);
    }
    println!("cargo:rerun-if-changed=build.rs");
}

/// Run `git <args>` and return trimmed stdout on a clean exit, else `None`.
fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

/// Emit `cargo:rerun-if-changed` for a `git rev-parse <args>`-resolved path when
/// that path exists.
fn rerun_if_git_path_changes(args: &[&str]) {
    let mut full = vec!["rev-parse"];
    full.extend_from_slice(args);
    if let Some(path) = git(&full) {
        if std::path::Path::new(&path).exists() {
            println!("cargo:rerun-if-changed={path}");
        }
    }
}
