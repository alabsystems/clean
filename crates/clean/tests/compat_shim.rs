// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the `clean-cli` deprecation compat shim (#3438).
//!
//! The shim at `crates/clean-cli/src/bin/clean_cli_compat.rs`:
//!   1. prints a one-line deprecation notice to stderr,
//!   2. exec's the canonical `clean` binary (this crate's `[[bin]]`) with
//!      the same argv,
//!   3. preserves the exit code.
//!
//! These tests live here (and not in `clean-cli`) because cargo sets
//! `CARGO_BIN_EXE_clean` only for the package that declares the `clean`
//! `[[bin]]`, namely this crate. The sibling `clean-cli` shim binary is
//! resolved relative to the canonical `clean` path and is expected to be
//! present because the `clean` package depends on `clean-cli`, so building
//! `clean`'s test harness also builds the shim.
//!
//! Part of Epic #3436 / #3438.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The exact deprecation prefix the shim prints on stderr. Keep in sync with
/// `DEPRECATION_NOTICE` in `crates/clean-cli/src/bin/clean_cli_compat.rs`.
const DEPRECATION_PREFIX: &str = "clean-cli is deprecated; use 'clean'";

/// Path to the canonical `clean` binary (set by cargo for this crate).
fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// Resolve the sibling `clean-cli` shim next to the canonical binary.
/// Returns `None` if the shim is missing (caller should skip rather than
/// fail, since the shim lives in a sister crate).
fn sibling_shim() -> Option<PathBuf> {
    let clean = clean_path();
    let dir = clean.parent()?;
    let candidate = dir.join(if cfg!(windows) {
        "clean-cli.exe"
    } else {
        "clean-cli"
    });
    if candidate.is_file() {
        Some(candidate)
    } else {
        None
    }
}

fn run(bin: &Path, args: &[&str]) -> Output {
    Command::new(bin)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn {bin:?}: {e}"))
}

#[test]
fn shim_prints_deprecation_notice_on_stderr() {
    let Some(shim) = sibling_shim() else {
        eprintln!(
            "test skipped: sibling `clean-cli` shim not built next to {:?}; \
             run `cargo build -p clean-cli --bin clean-cli` in the same target dir to enable.",
            clean_path()
        );
        return;
    };

    let out = run(&shim, &["--version"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains(DEPRECATION_PREFIX),
        "shim stderr must contain deprecation notice starting with \
         {DEPRECATION_PREFIX:?}; got stderr={stderr:?}",
    );
}

#[test]
fn shim_exit_code_matches_canonical_on_version_success() {
    let Some(shim) = sibling_shim() else {
        eprintln!("test skipped: sibling `clean-cli` shim not built");
        return;
    };

    let canonical = run(&clean_path(), &["--version"]);
    let shim_out = run(&shim, &["--version"]);

    assert_eq!(
        canonical.status.code(),
        shim_out.status.code(),
        "--version exit codes must match: canonical={:?} shim={:?}",
        canonical.status.code(),
        shim_out.status.code(),
    );
    assert_eq!(
        canonical.status.code(),
        Some(0),
        "`clean --version` must exit 0; got {:?}",
        canonical.status.code()
    );
}

#[test]
fn shim_stdout_matches_canonical_on_version() {
    let Some(shim) = sibling_shim() else {
        eprintln!("test skipped: sibling `clean-cli` shim not built");
        return;
    };

    let canonical = run(&clean_path(), &["--version"]);
    let shim_out = run(&shim, &["--version"]);

    assert_eq!(
        canonical.stdout, shim_out.stdout,
        "--version stdout must match byte-for-byte between canonical and shim",
    );
}

#[test]
fn shim_stdout_matches_canonical_on_features() {
    // `features` is a meta command that lists every registered feature. It is
    // a stable, deterministic surface that exercises full argv forwarding
    // without needing external file fixtures.
    let Some(shim) = sibling_shim() else {
        eprintln!("test skipped: sibling `clean-cli` shim not built");
        return;
    };

    let canonical = run(&clean_path(), &["features"]);
    let shim_out = run(&shim, &["features"]);

    assert_eq!(
        canonical.status.code(),
        shim_out.status.code(),
        "`features` exit codes must match",
    );
    assert_eq!(
        canonical.stdout, shim_out.stdout,
        "`features` stdout must match byte-for-byte between canonical and shim",
    );
}

#[test]
fn shim_first_stderr_line_is_the_deprecation_notice() {
    let Some(shim) = sibling_shim() else {
        eprintln!("test skipped: sibling `clean-cli` shim not built");
        return;
    };

    let shim_out = run(&shim, &["--version"]);
    let stderr = String::from_utf8_lossy(&shim_out.stderr);
    // The canonical `clean --version` path writes its banner to stdout, so
    // the first stderr line should be the deprecation notice.
    let first_line = stderr.lines().next().unwrap_or_default();
    assert!(
        first_line.starts_with(DEPRECATION_PREFIX),
        "first stderr line must be the deprecation notice; got {first_line:?}",
    );
}
