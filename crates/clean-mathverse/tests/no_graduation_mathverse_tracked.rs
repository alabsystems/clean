// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed anti-recurrence guard for the graduation storage refactor
//! (`designs/2026-06-24-graduation-storage-and-distribution.md`).
//!
//! `CLAUDE.md` is explicit that `.mathverse` shard files are NOT in the git
//! tree (they ship as Release assets / live in the gitignored content-addressed
//! store). The graduation storage refactor extends that rule to the heavy
//! graduation artifacts under `data/graduation/`: the binary `.mathverse` shard
//! and the full-closure `.graduation.json` are relocated to the gitignored
//! `_mathverse-artifacts/graduations/` store and pinned by blake3 from the
//! COMPACT `*.record.json`. Git tracks only the lean, reviewable layer.
//!
//! This test asserts — via the authoritative tracked-set (`git ls-files`),
//! not a filesystem walk that could miss a staged-but-uncommitted add — that
//! NO `.mathverse` and NO `.graduation.json` is tracked under `data/graduation`,
//! so the anti-pattern the design fixes can never silently recur.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Repo root: `CARGO_MANIFEST_DIR` is `<root>/crates/clean-mathverse`.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root resolves from CARGO_MANIFEST_DIR")
}

/// The git-tracked paths under `data/graduation` (relative, repo-root-anchored).
///
/// Returns `None` when git is unavailable or the directory is not in a work
/// tree (the test then passes trivially — there is nothing to guard).
fn tracked_graduation_paths(root: &Path) -> Option<Vec<String>> {
    let output = Command::new("git")
        .current_dir(root)
        .args(["ls-files", "-z", "--", "data/graduation"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(
        output
            .stdout
            .split(|&b| b == 0)
            .filter(|s| !s.is_empty())
            .map(|s| String::from_utf8_lossy(s).into_owned())
            .collect(),
    )
}

#[test]
fn no_graduation_mathverse_tracked() {
    let root = repo_root();
    let Some(tracked) = tracked_graduation_paths(&root) else {
        // Not in a git work tree (e.g. a vendored source tarball). The
        // .gitignore enforcement is the live guard there; nothing to check.
        return;
    };

    let offending_shards: Vec<&String> = tracked
        .iter()
        .filter(|p| p.ends_with(".mathverse"))
        .collect();
    assert!(
        offending_shards.is_empty(),
        "graduation storage refactor violated: {} `.mathverse` shard(s) are git-tracked under \
         data/graduation. Shards must live in the gitignored content-addressed store \
         (_mathverse-artifacts/graduations/), pinned by blake3 from the compact *.record.json — \
         see designs/2026-06-24-graduation-storage-and-distribution.md and the .gitignore \
         `data/graduation/**/*.mathverse` rule. Offending:\n{}",
        offending_shards.len(),
        offending_shards
            .iter()
            .map(|p| format!("  {p}"))
            .collect::<Vec<_>>()
            .join("\n")
    );

    let offending_full: Vec<&String> = tracked
        .iter()
        .filter(|p| p.ends_with(".graduation.json"))
        .collect();
    assert!(
        offending_full.is_empty(),
        "graduation storage refactor violated: {} full-closure `.graduation.json` record(s) are \
         git-tracked under data/graduation. The full record (with the multi-MB carried-decl dump) \
         belongs in the gitignored store; git tracks only the compact *.record.json that pins it \
         — see designs/2026-06-24-graduation-storage-and-distribution.md and the .gitignore \
         `data/graduation/**/*.graduation.json` rule. Offending:\n{}",
        offending_full.len(),
        offending_full
            .iter()
            .map(|p| format!("  {p}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
