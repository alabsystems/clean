// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `data/vendor_manifest.json` is bound to `Cargo.lock`, and `just ci` holds
//! the binding (R167).
//!
//! The binding's check, `scripts/gen_vendor_manifest.py --check`, ran only in
//! the opt-in pre-push hook and `scripts/local_gate.sh`. Neither is the landing
//! gate (`just ci`, AGENTS.md), so `86588a484` (R162) changed `Cargo.lock` (a
//! `clean-ck0` edge) without re-deriving the manifest and landed; the red
//! surfaced only when the R165 pin bump's `rederive_chain.py --check` refused.
//! This test puts the check in `test-fast` (`crates/clean` is a default member):
//!
//! * **control**: the committed manifest passes against the committed lock;
//! * **a lock changed without regenerating** (one byte appended, no crates.io
//!   package moved, the shape of `86588a484`) is refused as `STALE`;
//! * **a manifest missing one locked crate** (R165's 342-of-389 partial
//!   manifest, reduced to one removed row) is refused as `MISSING`;
//! * the generator's own `--self-test` arms are green, so a pass above is not a
//!   check that has stopped firing.
//!
//! There is no skip path: a missing `python3` is a failure, not a green.

#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn generator(args: &[&str]) -> Output {
    let root = workspace_root();
    Command::new("python3")
        .arg(root.join("scripts/gen_vendor_manifest.py"))
        .args(args)
        .current_dir(&root)
        .output()
        .unwrap_or_else(|e| panic!("python3 scripts/gen_vendor_manifest.py {args:?}: {e}"))
}

fn report(output: &Output) -> String {
    format!(
        "exit {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn committed(path: &str) -> String {
    let path = workspace_root().join(path);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

#[test]
fn generator_self_test_arms_fire() {
    let out = generator(&["--self-test"]);
    assert!(out.status.success(), "--self-test failed\n{}", report(&out));
}

#[test]
fn committed_manifest_matches_the_committed_lock() {
    let out = generator(&["--check"]);
    assert!(
        out.status.success(),
        "data/vendor_manifest.json does not match Cargo.lock; re-derive it:\n  \
         python3 scripts/gen_vendor_manifest.py --stage-third-party vendor --download\n  \
         python3 scripts/gen_vendor_manifest.py vendor\n{}",
        report(&out)
    );
}

#[test]
fn lock_changed_without_regenerating_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let lock = dir.path().join("Cargo.lock");
    fs::write(&lock, committed("Cargo.lock") + "\n").expect("write lock");
    let lock = lock.to_str().expect("utf-8 temp path");

    let out = generator(&["--check", "data/vendor_manifest.json", lock]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "a changed lock passed\n{}",
        report(&out)
    );
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("STALE:"),
        "refused for the wrong reason\n{}",
        report(&out)
    );
}

#[test]
fn manifest_missing_one_locked_crate_is_refused() {
    // Remove the first row object of `"crates": [` textually: the manifest is
    // written with `indent=2`, so each row opens on a line `    {` and closes
    // on `    },` (every row but the last).
    let manifest = committed("data/vendor_manifest.json");
    let crates = manifest
        .find("\"crates\": [\n")
        .expect("manifest has a crates list");
    let start = crates + manifest[crates..].find("    {\n").expect("a first row");
    let end =
        start + manifest[start..].find("\n    },\n").expect("a second row") + "\n    },\n".len();
    let removed = &manifest[start..end];
    let name = removed
        .split("\"name\": \"")
        .nth(1)
        .and_then(|rest| rest.split('"').next())
        .expect("the removed row has a name");
    let mutant = format!("{}{}", &manifest[..start], &manifest[end..]);

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("vendor_manifest.json");
    fs::write(&path, mutant).expect("write mutant");
    let path = path.to_str().expect("utf-8 temp path");

    let out = generator(&["--check", path, "Cargo.lock"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        out.status.code(),
        Some(1),
        "a manifest missing {name} passed\n{}",
        report(&out)
    );
    assert!(
        stderr.contains("MISSING: 1 of") && stderr.contains(&format!("    {name} ")),
        "refused for the wrong reason\n{}",
        report(&out)
    );
}
