// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build script for the `clean` binary: embed the git SHA the binary was built
//! from and its build timestamp so `clean mathverse isabelle-doctor` can report
//! the running binary's identity and detect a STALE binary (the incident where a
//! chain script picked a 5-day-old binary via `ls | head -1`).
//! Under SOURCE_DATE_EPOCH (a reproducible build) the timestamp is that time.
//!
//! The same SHA is what `clean --version` prints (`CLEAN_BUILD_VERSION`, the
//! crate version plus `+g<sha>` build metadata). Two-language roadmap WS6.13
//! (F-118): until then every `clean` printed only `clean 0.9.0`, so an
//! installed binary, a stage1 build and a source build of three different
//! commits were indistinguishable from the shell, and the atpkg seal's
//! provenance could not say which Clean it had packed.
//!
//! Dependency-free by design (std + `git` only; no `vergen`). The SHA is the
//! commit whose repository TRACKS this build script
//! (`build_support/provenance.rs`, shared with the tests that pin it): when
//! `git` is absent, the tree is no repository, or it is an untracked unpack
//! inside some OTHER repository (a dotfiles `$HOME`, a vendor tree — whose
//! `HEAD` is not this build's commit), the SHA falls back to `"unknown"`,
//! which the doctor reports as an un-verifiable build (a loud WARN, never a
//! silent pass) and `--version` spells out as such rather than minting a
//! `+gunknown` that a reader could mistake for a commit.

use std::time::{SystemTime, UNIX_EPOCH};

// Brings `Path`, `Command`, `git_in`, `tracked_head_sha` and `head_watch_paths`
// into scope.
include!("build_support/provenance.rs");

/// The `--version` spelling for a build whose git SHA could not be read.
/// Deliberately NOT valid SemVer build metadata: a version string that a
/// packer could parse as `<ver>+g<commit>` must only ever carry a real commit.
const UNKNOWN_BUILD_VERSION_SUFFIX: &str = " (git sha unknown: built without git provenance)";

fn main() {
    // Build timestamp (seconds since the Unix epoch). A build that sets
    // SOURCE_DATE_EPOCH (reproducible-builds.org) gets that time instead of the
    // wall clock, so two builds of one source produce the same bytes: Trust's
    // toolchain cut sets it to the commit's time and requires its double compile
    // to rebuild the toolchain byte for byte. Measured 2026-10-01, two builds of
    // one Trust commit differed in `bin/clean` by exactly this constant (in
    // clean_cli::cmd_mathverse). A malformed value stops the build rather than
    // quietly stamping the wall clock.
    println!("cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH");
    let build_unix = match std::env::var("SOURCE_DATE_EPOCH") {
        Ok(value) => value.trim().parse::<u64>().unwrap_or_else(|_| {
            panic!("SOURCE_DATE_EPOCH={value:?} is not a count of seconds since the Unix epoch")
        }),
        Err(_) => SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0),
    };
    println!("cargo:rustc-env=CLEAN_BUILD_UNIX={build_unix}");

    // Git SHA the binary is built from (fallback: "unknown"): the HEAD of the
    // repository that tracks THIS file, never merely the nearest enclosing one.
    // Qualified: `build_support/provenance.rs` (included above) names
    // `std::path::PathBuf` in full, so importing it here would make that an
    // unnecessary qualification.
    let manifest_dir = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"),
    );
    let sha = tracked_head_sha(&manifest_dir, "build.rs");
    println!(
        "cargo:rustc-env=CLEAN_BUILD_GIT_SHA={}",
        sha.as_deref().unwrap_or("unknown")
    );

    // `clean --version`: `<crate version>+g<sha>` — the `pub version --dev`
    // dev-build spelling (SemVer build metadata), with the FULL sha so the
    // string identifies exactly one commit.
    let pkg_version = std::env::var("CARGO_PKG_VERSION").unwrap_or_else(|_| "0.0.0".to_string());
    let build_version = match &sha {
        Some(sha) => format!("{pkg_version}+g{sha}"),
        None => format!("{pkg_version}{UNKNOWN_BUILD_VERSION_SUFFIX}"),
    };
    println!("cargo:rustc-env=CLEAN_BUILD_VERSION={build_version}");

    // Re-run this script (and so re-capture the SHA) whenever HEAD or the
    // checked-out branch moves, including a branch whose ref is packed
    // (`head_watch_paths`, in `build_support/provenance.rs` so its tests run
    // the same code). Only meaningful when the tree IS this build's
    // repository; a foreign enclosing repository's refs are not watched,
    // because its HEAD is not reported.
    if sha.is_some() {
        for path in head_watch_paths(&manifest_dir) {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=build_support/provenance.rs");
}
