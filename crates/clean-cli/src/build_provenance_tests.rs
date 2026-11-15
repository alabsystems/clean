// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins the build-provenance predicate `build.rs` stamps `clean --version`
//! (`CLEAN_BUILD_VERSION`) and the doctor's `CLEAN_BUILD_GIT_SHA` with —
//! `build_support/provenance.rs`, `include!`d here so the code under test IS
//! the code the build script runs (two-language roadmap WS6.13 review,
//! F-118).
//!
//! The hole these guard: `git rev-parse HEAD` alone reports the HEAD of the
//! nearest ENCLOSING repository. A source tree that is not itself tracked —
//! a tarball unpacked under a dotfiles `$HOME`, a vendor directory, a
//! monorepo scratch dir — would then stamp a commit that contains none of
//! the sources into the binary, and `--version` would assert a build
//! identity that is simply false.

use std::process::Output;

include!("../build_support/provenance.rs");

fn git_ok(dir: &Path, args: &[&str]) -> Output {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        // A fresh repository needs an identity to commit; never touch the
        // developer's global config from a test.
        .args([
            "-c",
            "user.name=provenance-test",
            "-c",
            "user.email=provenance@test",
        ])
        .args(args)
        .output()
        .expect("spawn git");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

/// A repository with one commit, and inside it an UNTRACKED `vendor/clean-cli`
/// holding a `build.rs` — the tarball-under-a-foreign-repo shape.
fn foreign_repo_with_untracked_unpack() -> (tempfile::TempDir, std::path::PathBuf) {
    let repo = tempfile::tempdir().expect("tempdir");
    git_ok(repo.path(), &["init", "-q"]);
    std::fs::write(repo.path().join("README"), "not clean\n").expect("write");
    git_ok(repo.path(), &["add", "README"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "foreign"]);
    let unpack = repo.path().join("vendor").join("clean-cli");
    std::fs::create_dir_all(&unpack).expect("mkdir");
    std::fs::write(unpack.join("build.rs"), "fn main() {}\n").expect("write");
    (repo, unpack)
}

fn head_of(dir: &Path) -> String {
    String::from_utf8_lossy(&git_ok(dir, &["rev-parse", "HEAD"]).stdout)
        .trim()
        .to_owned()
}

/// ADVERSARIAL: the naive predicate WOULD have claimed the foreign commit —
/// `git rev-parse HEAD` from inside the unpack succeeds and names it — and
/// the tracked predicate refuses.
#[test]
fn foreign_enclosing_repository_head_is_not_claimed() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    let foreign_head = head_of(&unpack);
    assert_eq!(foreign_head, head_of(repo.path()));
    assert_eq!(
        foreign_head.len(),
        40,
        "the naive predicate had a sha to lie with"
    );
    assert_eq!(
        tracked_head_sha(&unpack, "build.rs"),
        None,
        "an untracked unpack inside a foreign repository has no provenance"
    );
}

/// The positive twin: once the same files ARE tracked at the repository's
/// HEAD, that HEAD is the provenance — a vendored, committed clean tree is
/// built from that commit.
#[test]
fn tracked_sources_report_the_repository_head() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    git_ok(repo.path(), &["add", "vendor/clean-cli/build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "vendor clean-cli"]);
    let head = head_of(repo.path());
    assert_eq!(
        tracked_head_sha(&unpack, "build.rs").as_deref(),
        Some(head.as_str())
    );
}

/// ADVERSARIAL (second review): sources `git add`-ed into a foreign
/// repository but never committed. The index tracks `build.rs` and the
/// repository has a HEAD, so the index-only predicate of the first review
/// stamped the FOREIGN commit — one that contains none of the sources. The
/// commit's own tree must hold the anchor.
#[test]
fn sources_staged_but_not_committed_in_a_foreign_repository_are_no_provenance() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    git_ok(repo.path(), &["add", "vendor/clean-cli/build.rs"]);
    // Both halves of the index-only predicate hold: it had a sha to lie with.
    git_ok(&unpack, &["ls-files", "--error-unmatch", "--", "build.rs"]);
    assert_eq!(head_of(&unpack).len(), 40);
    assert_eq!(
        tracked_head_sha(&unpack, "build.rs"),
        None,
        "a staged, uncommitted unpack is not in the commit HEAD names"
    );
}

/// ADVERSARIAL (second review): the foreign commit DOES hold a `build.rs` —
/// at the repository root, not at the unpack's path — and the unpack's own
/// `build.rs` is staged only. A root-relative `HEAD:build.rs` lookup would
/// find the wrong file and pass; the lookup is relative to `dir`.
#[test]
fn a_commit_holding_the_anchor_at_another_path_is_no_provenance() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    std::fs::write(repo.path().join("build.rs"), "fn main() {}\n").expect("write");
    git_ok(repo.path(), &["add", "build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "a root build.rs"]);
    git_ok(repo.path(), &["add", "vendor/clean-cli/build.rs"]);
    assert_eq!(
        tracked_head_sha(repo.path(), "build.rs"),
        Some(head_of(repo.path()))
    );
    assert_eq!(
        tracked_head_sha(&unpack, "build.rs"),
        None,
        "the commit's root build.rs is not the unpack's build.rs"
    );
}

/// ADVERSARIAL (second review): an anchor that the commit holds as a TREE
/// (a directory of tracked files) is not the build script; `ls-files
/// --error-unmatch` accepts a directory, the blob check does not.
#[test]
fn an_anchor_that_is_a_directory_in_the_commit_is_no_provenance() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    git_ok(repo.path(), &["add", "vendor/clean-cli/build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "vendor clean-cli"]);
    let vendor = repo.path().join("vendor");
    git_ok(&vendor, &["ls-files", "--error-unmatch", "--", "clean-cli"]);
    assert_eq!(tracked_head_sha(&vendor, "clean-cli"), None);
    // Its positive twin: the same commit, the file itself.
    assert_eq!(
        tracked_head_sha(&unpack, "build.rs"),
        Some(head_of(repo.path()))
    );
}

/// ADVERSARIAL (second review): the commit holds the anchor but the index no
/// longer tracks it (`git rm --cached`): the working-tree file is untracked,
/// so neither half alone decides and the predicate refuses.
#[test]
fn a_committed_anchor_removed_from_the_index_is_no_provenance() {
    let (repo, unpack) = foreign_repo_with_untracked_unpack();
    git_ok(repo.path(), &["add", "vendor/clean-cli/build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "vendor clean-cli"]);
    git_ok(
        repo.path(),
        &["rm", "-q", "--cached", "vendor/clean-cli/build.rs"],
    );
    assert!(unpack.join("build.rs").is_file());
    assert_eq!(tracked_head_sha(&unpack, "build.rs"), None);
}

/// An index without a commit (`git init && git add`) tracks the file but has
/// no HEAD to report: no provenance, not a panic and not an empty string.
#[test]
fn an_index_without_a_commit_is_no_provenance() {
    let repo = tempfile::tempdir().expect("tempdir");
    git_ok(repo.path(), &["init", "-q"]);
    std::fs::write(repo.path().join("build.rs"), "fn main() {}\n").expect("write");
    git_ok(repo.path(), &["add", "build.rs"]);
    assert_eq!(tracked_head_sha(repo.path(), "build.rs"), None);
}

/// A path that names no file (the anchor is wrong, or the tree is not a
/// repository at all) is no provenance.
#[test]
fn an_untracked_anchor_is_no_provenance() {
    let (_repo, unpack) = foreign_repo_with_untracked_unpack();
    assert_eq!(tracked_head_sha(&unpack, "no-such-file.rs"), None);
}

/// The predicate on THIS crate agrees with git about this checkout: the
/// build script is tracked here iff the checkout is a repository whose index
/// AND whose HEAD commit hold it, and then the reported sha is that
/// repository's HEAD. Not a skip when
/// the tree is a tarball — the expected answer is then `None`, exactly.
#[test]
fn this_crate_reports_its_own_checkout_head_iff_tracked() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tracked = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["ls-files", "--error-unmatch", "--", "build.rs"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    // The second half, spelled independently of the predicate: HEAD's own
    // tree holds this crate's build.rs as a blob.
    let committed = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["cat-file", "-t", "HEAD:./build.rs"])
        .output()
        .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).trim() == "blob")
        .unwrap_or(false);
    let expected = (tracked && committed).then(|| head_of(dir));
    let reported = tracked_head_sha(dir, "build.rs");
    assert_eq!(reported, expected);
    // Unconditional (no `if let` guard): whatever was reported is a full
    // 40-hex commit id, and a `None` is pinned exactly by the equality above,
    // so neither outcome skips an assertion.
    assert!(
        reported
            .iter()
            .all(|sha| sha.len() == 40 && sha.bytes().all(|b| b.is_ascii_hexdigit())),
        "a reported sha must be a full 40-hex commit id: {reported:?}"
    );
}

/// A one-commit repository whose branch is `main`, for the watch-path tests.
fn repo_with_one_commit() -> tempfile::TempDir {
    let repo = tempfile::tempdir().expect("tempdir");
    git_ok(repo.path(), &["init", "-q", "-b", "main"]);
    std::fs::write(repo.path().join("build.rs"), "fn main() {}\n").expect("write");
    git_ok(repo.path(), &["add", "build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "one"]);
    repo
}

/// Size and mtime of every watched path, so a test can say WHICH moved.
fn stamps(paths: &[std::path::PathBuf]) -> Vec<(std::path::PathBuf, u64, std::time::SystemTime)> {
    paths
        .iter()
        .map(|path| {
            let meta = std::fs::metadata(path).expect("a watched path exists");
            (path.clone(), meta.len(), meta.modified().expect("mtime"))
        })
        .collect()
}

/// Assert an empty commit in `dir` changes at least one watched path —
/// what cargo needs to re-run the build script and re-stamp the sha.
#[track_caller]
fn assert_a_commit_moves_a_watched_path(dir: &Path) {
    let watched = head_watch_paths(dir);
    let before = stamps(&watched);
    // mtimes on some filesystems have whole-second granularity.
    std::thread::sleep(std::time::Duration::from_millis(1100));
    git_ok(dir, &["commit", "-q", "--allow-empty", "-m", "next"]);
    let after = stamps(&watched);
    assert!(
        before
            .iter()
            .zip(&after)
            .any(|(b, a)| b.1 != a.1 || b.2 != a.2),
        "a commit moved none of the watched paths {watched:?}, so the build \
         script would keep the previous commit's sha"
    );
}

/// The branch ref is a loose file: it is watched, with `HEAD` and
/// `packed-refs` (when present), and a commit rewrites it.
#[test]
fn a_loose_branch_ref_is_watched() {
    let repo = repo_with_one_commit();
    let watched = head_watch_paths(repo.path());
    let loose = repo.path().join(".git/refs/heads/main");
    assert!(loose.exists(), "a fresh commit leaves a loose ref");
    let watched: Vec<_> = watched
        .iter()
        .map(|p| p.canonicalize().expect("canonicalize"))
        .collect();
    let head = repo.path().join(".git/HEAD");
    assert!(watched.contains(&head.canonicalize().expect("HEAD exists")));
    assert!(
        watched.contains(&loose.canonicalize().expect("loose ref exists")),
        "{watched:?}"
    );
    assert_a_commit_moves_a_watched_path(repo.path());
}

/// The failure this guards (2026-10-17): after `git pack-refs` the branch ref
/// has no loose file, a commit creates one, and a watch registered only on
/// `HEAD` and `packed-refs` sees neither move. The branch reflog is watched
/// instead, and the commit appends to it.
#[test]
fn a_packed_branch_ref_is_watched_through_its_reflog() {
    let repo = repo_with_one_commit();
    git_ok(repo.path(), &["pack-refs", "--all"]);
    let loose = repo.path().join(".git/refs/heads/main");
    assert!(!loose.exists(), "pack-refs --all removes the loose ref");
    let watched: Vec<_> = head_watch_paths(repo.path())
        .iter()
        .map(|p| p.canonicalize().expect("canonicalize"))
        .collect();
    let reflog = repo
        .path()
        .join(".git/logs/refs/heads/main")
        .canonicalize()
        .expect("a branch with a commit has a reflog");
    assert!(watched.contains(&reflog), "{watched:?}");
    assert_a_commit_moves_a_watched_path(repo.path());
}

/// In a linked worktree `HEAD` lives under `.git/worktrees/<name>/` and the
/// branch ref in the shared `.git/refs/`; both are found, and a commit made
/// in the worktree moves a watched path.
#[test]
fn a_linked_worktree_watches_its_own_head_and_branch() {
    let repo = repo_with_one_commit();
    let worktree = repo.path().join("wt");
    git_ok(
        repo.path(),
        &[
            "worktree",
            "add",
            "-q",
            "-b",
            "feature",
            worktree.to_str().expect("utf8"),
        ],
    );
    let watched: Vec<_> = head_watch_paths(&worktree)
        .iter()
        .map(|p| p.canonicalize().expect("canonicalize"))
        .collect();
    let own_head = repo
        .path()
        .join(".git/worktrees/wt/HEAD")
        .canonicalize()
        .expect("a linked worktree has its own HEAD");
    let branch = repo
        .path()
        .join(".git/refs/heads/feature")
        .canonicalize()
        .expect("worktree add -b writes a loose ref");
    assert!(watched.contains(&own_head), "{watched:?}");
    assert!(watched.contains(&branch), "{watched:?}");
    assert_a_commit_moves_a_watched_path(&worktree);
}

/// A detached `HEAD` holds the commit itself, so the `HEAD` file is what a
/// commit rewrites.
#[test]
fn a_detached_head_is_watched_through_the_head_file() {
    let repo = repo_with_one_commit();
    git_ok(repo.path(), &["checkout", "-q", "--detach"]);
    assert_a_commit_moves_a_watched_path(repo.path());
}

/// Assert that `op` changes at least one path `head_watch_paths(watch_dir)`
/// names (size or mtime), i.e. that cargo would re-run the build script.
#[track_caller]
fn assert_op_moves_a_watched_path(watch_dir: &Path, what: &str, op: impl FnOnce()) {
    let watched = head_watch_paths(watch_dir);
    let before = stamps(&watched);
    // mtimes on some filesystems have whole-second granularity.
    std::thread::sleep(std::time::Duration::from_millis(1100));
    op();
    let after = stamps(&watched);
    assert!(
        before
            .iter()
            .zip(&after)
            .any(|(b, a)| b.1 != a.1 || b.2 != a.2),
        "{what} moved none of the watched paths {watched:?}, so the build \
         script would keep the previous commit's sha"
    );
}

/// The reftable ref backend (`git init --ref-format=reftable`, Git 3.0's
/// default): `HEAD` is a fixed stub (`ref: refs/heads/.invalid`),
/// `refs/heads` is a plain file, and there are no loose refs, packed-refs or
/// reflog files. Every ref transaction rewrites a table stack's
/// `tables.list` instead — the per-worktree stack (HEAD) and the shared one
/// (branches) — so both are watched, and a commit, a detach, and a move of a
/// linked worktree's branch made from the main checkout each re-run the build
/// script (review C7, 2026-10-22, measured on git 2.54).
#[test]
fn a_reftable_repository_is_watched_through_its_table_stacks() {
    let repo = tempfile::tempdir().expect("tempdir");
    git_ok(
        repo.path(),
        &["init", "-q", "--ref-format=reftable", "-b", "main"],
    );
    std::fs::write(repo.path().join("build.rs"), "fn main() {}\n").expect("write");
    git_ok(repo.path(), &["add", "build.rs"]);
    git_ok(repo.path(), &["commit", "-q", "-m", "one"]);
    assert!(
        repo.path().join(".git/reftable").is_dir(),
        "the repository uses the reftable backend"
    );
    let dir = repo.path();
    assert_op_moves_a_watched_path(dir, "a commit on a branch", || {
        git_ok(dir, &["commit", "-q", "--allow-empty", "-m", "two"]);
    });
    assert_op_moves_a_watched_path(dir, "a detach", || {
        git_ok(dir, &["checkout", "-q", "--detach"]);
    });
    assert_op_moves_a_watched_path(dir, "a detached commit", || {
        git_ok(dir, &["commit", "-q", "--allow-empty", "-m", "three"]);
    });
    git_ok(dir, &["checkout", "-q", "main"]);
    let worktree = dir.join("wt");
    git_ok(
        dir,
        &[
            "worktree",
            "add",
            "-q",
            "-b",
            "feature",
            worktree.to_str().expect("utf8"),
        ],
    );
    assert_op_moves_a_watched_path(&worktree, "a commit in the linked worktree", || {
        git_ok(&worktree, &["commit", "-q", "--allow-empty", "-m", "wt"]);
    });
    assert_op_moves_a_watched_path(
        &worktree,
        "a move of the worktree's branch from the main checkout",
        || {
            git_ok(dir, &["update-ref", "refs/heads/feature", "main~1"]);
        },
    );
}
