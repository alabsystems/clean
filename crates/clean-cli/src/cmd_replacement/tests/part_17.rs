// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 17): a row's evidence must exist for everyone, not just for
//! whoever generated it.
//!
//! `evidence_state_of` classifies an artifact by reading it off disk, so an
//! **untracked** file is indistinguishable from a committed one. That is
//! harmless while the row is non-Green and silently wrong the moment it is not:
//! the row reads `green` in the author's working tree and `pending_evidence` in
//! a clean clone, and the scorecard's whole point is that the second reader
//! sees the truth. Measured 2026-08-26: `reports/rust-first-tooling.json` and
//! `reports/lake-replacement-smoke.json` were both present and both untracked
//! (`git check-ignore` exit 1 — not ignored, just never added).
//!
//! The check lives here rather than inside `evidence_state_of` on purpose. The
//! CLI has to work outside a git checkout (a release tarball has no index), so
//! a runtime tracked-ness probe would have to fail *open* when git is missing —
//! precisely the wrong direction for a soundness question. Whether a file is
//! committed is a repo-hygiene invariant, so it is enforced where git is
//! guaranteed to exist: the harness that now also gates the `scorecard` row.

use crate::cmd_replacement::*;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn inside_work_tree() -> bool {
    Command::new("git")
        .current_dir(repo_root())
        .args(["rev-parse", "--is-inside-work-tree"])
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false)
}

fn is_tracked(path: &str) -> bool {
    Command::new("git")
        .current_dir(repo_root())
        .args(["ls-files", "--error-unmatch", "--", path])
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false)
}

#[test]
fn every_present_evidence_artifact_is_git_tracked() {
    if !inside_work_tree() {
        eprintln!("SKIP: not a git work tree, so tracked-ness is not a question here");
        return;
    }

    let mut untracked: Vec<(&str, &str)> = Vec::new();
    for row in replacement_rows() {
        // Rows may list several artifacts, semicolon-separated; schema-name
        // "evidence" carries no path separator and is not a file at all.
        for path in row.evidence_artifact.split(';') {
            let path = path.trim();
            if path.is_empty() || !path.contains('/') {
                continue;
            }
            // Only files that exist can be scored, so only those can lie.
            if !repo_artifact_path(path).exists() {
                continue;
            }
            if !is_tracked(path) {
                untracked.push((row.id, path));
            }
        }
    }

    assert!(
        untracked.is_empty(),
        "these evidence artifacts exist on disk but are not committed, so they score in the \
         author's tree and vanish in a clean clone: {untracked:?}"
    );
}

/// DIRECTION 2: the tracked-ness probe must be able to answer *no*.
///
/// The test above passes by finding nothing. A probe that always returns `true`
/// — `git ls-files` misspelled, run from the wrong directory, its exit code
/// ignored — passes it just as quietly, and this repo has already shipped
/// exactly that failure (`seal_driver.sh guard`, where an ABSENT verdict
/// passed). Both directions are pinned here, over paths that need no tree
/// mutation to be decisive.
#[test]
fn tracked_probe_answers_both_ways() {
    if !inside_work_tree() {
        eprintln!("SKIP: not a git work tree, so tracked-ness is not a question here");
        return;
    }
    assert!(
        is_tracked("Cargo.toml"),
        "the tracked-ness probe cannot recognise a file that is certainly committed, \
         so a green from it means nothing"
    );
    assert!(
        !is_tracked("reports/this-path-is-never-committed-9f3c1a.json"),
        "the tracked-ness probe answers yes for a path that does not exist, \
         so it can never refuse an untracked artifact"
    );
}
