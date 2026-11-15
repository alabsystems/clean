// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The build-provenance predicate behind `clean --version` and the doctor's
// `CLEAN_BUILD_GIT_SHA`.
//
// `include!`d by `build.rs` (which stamps the result into the binary) AND by
// `src/build_provenance_tests.rs` (which pins its refusals), so the predicate
// a binary's identity rests on is the one under test — a build script has no
// `cargo test` of its own.
//
// Why not `git rev-parse HEAD` alone (review of WS6.13, F-118): that answers
// "what is the HEAD of the nearest ENCLOSING repository", which is a
// different question from "which commit was this binary built from". A
// source tarball unpacked under a directory some OTHER repository owns — a
// dotfiles repository at `$HOME`, a vendor tree, a monorepo's scratch dir —
// would stamp that repository's commit into a binary it did not build, and
// `clean --version` would print `+g<sha>` for a commit that contains none of
// the sources: a false identity claim, which is exactly what F-118 exists to
// end. So the commit is reported only when the build script itself is
// TRACKED in the repository that `HEAD` belongs to (`git ls-files
// --error-unmatch`) AND that commit's own tree holds it at this very path
// (`<sha>:./<anchor>` is a blob); the reported commit then contains the file
// that reported it. The index alone does not say so: a tree `git add`-ed
// into a foreign repository but never committed is in the index while that
// repository's `HEAD` is still a commit containing none of it (measured in
// the second review of WS6.13 — the index-only predicate stamped the foreign
// commit). Everything else — no git, no repository, an untracked tree inside
// a foreign repository, sources staged but not committed, an index with no
// commit — is "no provenance", which `build.rs` spells out in words rather
// than minting a `+g…`.
//
// What this does NOT claim: that the tracked tree is unmodified. A dirty
// checkout still reports its HEAD (as the doctor always has); a working-tree
// diff is not something a build script can watch for re-runs, so a "dirty"
// marker could go stale in the dangerous direction (say clean when dirty).

use std::path::Path;
use std::process::Command;

/// Run `git -C <dir> <args>` and return trimmed stdout on a clean exit, else
/// `None` (git absent, not a repository, the command refused).
fn git_in(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()?;
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

/// The 40-hex commit whose repository TRACKS `anchor` (a path relative to
/// `dir`), or `None` when there is no such commit.
///
/// All three are required: `anchor` must be in the index of the repository
/// `dir` resolves to (so a foreign enclosing repository, or an untracked
/// unpack inside one, is refused); that repository must have a commit at
/// `HEAD` (so a fresh `git init && git add` is refused too); and that SAME
/// commit's tree must hold `anchor` as a blob at this path (so sources staged
/// into a foreign repository but never committed are refused — the index
/// tracks them, the commit does not). The tree lookup names the resolved sha,
/// not `HEAD` again, so both answers are about one commit.
pub(crate) fn tracked_head_sha(dir: &Path, anchor: &str) -> Option<String> {
    git_in(dir, &["ls-files", "--error-unmatch", "--", anchor])?;
    let sha = git_in(dir, &["rev-parse", "--verify", "HEAD^{commit}"])?;
    if sha.len() != 40 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    // `<rev>:./<path>` resolves `path` against `dir` (git's cwd under `-C`).
    let in_commit = format!("{sha}:./{anchor}");
    (git_in(dir, &["cat-file", "-t", &in_commit])? == "blob").then_some(sha)
}

/// The files to watch so that a commit, checkout or reset re-runs the build
/// script: `HEAD` (per worktree; a linked worktree's lives under
/// `.git/worktrees/<name>/`), `packed-refs` (shared), and the branch `HEAD`
/// names. Every path comes from `git rev-parse --git-path`, which resolves
/// the per-worktree and the shared parts of a linked worktree correctly.
///
/// A commit on a branch rewrites that branch's ref and nothing else among
/// these: the `HEAD` file only says `ref: refs/heads/<branch>`, and a commit
/// never rewrites `packed-refs`. When the branch ref is PACKED (`git gc` and
/// `git pack-refs` delete the loose file; measured 2026-10-17, `main` and 7 of
/// 14 worktree branches of this repository), there is no loose file to watch:
/// the next commit CREATES one, which a watch registered on nothing never
/// sees, so the binary kept the previous commit's sha. Cargo re-runs a script
/// on every build while a watched path is missing, so the absent file itself
/// cannot be watched either. The branch's reflog (`logs/<ref>`) is appended by
/// every move of that branch, packed or not, and is watched instead; with no
/// reflog, the nearest existing directory above the loose ref is (cargo scans
/// a directory recursively, so the new loose file is seen; other branches
/// beside it may re-run the script too, which costs a rebuild, never a stale
/// sha).
///
/// The reftable ref backend (`git init --ref-format=reftable`, Git 3.0's
/// default) has none of those files to move: `HEAD` is a fixed stub
/// (`ref: refs/heads/.invalid`), `refs/heads` is a plain file, and there are
/// no loose refs, `packed-refs` or reflog files. Every ref transaction
/// rewrites a table stack's `tables.list` instead, so both stacks are
/// watched: the per-worktree one (`--git-path reftable/tables.list`: HEAD)
/// and the shared one under `--git-common-dir` (branches, which another
/// worktree can move; measured 2026-10-22 on git 2.54).
///
/// Paths are absolute or relative to `dir`, as `rerun-if-changed` takes them.
pub(crate) fn head_watch_paths(dir: &Path) -> Vec<std::path::PathBuf> {
    let resolve = |git_path: &str| {
        git_in(dir, &["rev-parse", "--git-path", git_path]).map(|path| dir.join(path))
    };
    let mut paths: Vec<std::path::PathBuf> = ["HEAD", "packed-refs"]
        .into_iter()
        .filter_map(&resolve)
        .filter(|path| path.exists())
        .collect();
    let shared_stack = git_in(dir, &["rev-parse", "--git-common-dir"])
        .map(|common| dir.join(common).join("reftable").join("tables.list"));
    for stack in [resolve("reftable/tables.list"), shared_stack]
        .into_iter()
        .flatten()
    {
        if stack.exists() && !paths.contains(&stack) {
            paths.push(stack);
        }
    }
    let Some(head_ref) = git_in(dir, &["symbolic-ref", "-q", "HEAD"]) else {
        // Detached: the `HEAD` file holds the commit itself.
        return paths;
    };
    let Some(loose) = resolve(&head_ref) else {
        return paths;
    };
    if loose.exists() {
        paths.push(loose);
    } else if let Some(reflog) = resolve(&format!("logs/{head_ref}")).filter(|log| log.exists()) {
        paths.push(reflog);
    } else if let Some(ancestor) = loose.ancestors().skip(1).find(|dir| dir.is_dir()) {
        paths.push(ancestor.to_path_buf());
    }
    paths
}
