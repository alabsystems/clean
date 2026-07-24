// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-snapshot-preserve` — copy the current binary
//! into a durable, SHA-named location so a replay snapshot stays resumable.
//!
//! The real build identity (the git SHA the copy is named by) is injected by the
//! caller: `clean-cli` embeds it via `build.rs` and intercepts this verb (exactly
//! like `isabelle-doctor`); the library dispatch path passes
//! [`BuildIdentity::unknown`], which names the copy `clean-unknown` and warns.

use super::{IsabelleSnapshotPreserveArgs, MathverseCliError};
use crate::hol::isabelle_doctor::BuildIdentity;
use crate::hol::isabelle_snapshot_preserve::run_preserve;

/// Run the preserve helper with the (caller-provided) build identity, print the
/// copy + pairing report, and warn when no git SHA was embedded.
///
/// # Errors
/// [`MathverseCliError::IsabelleSnapshotPreserve`] on an I/O failure resolving or
/// copying the binary.
pub fn run_isabelle_snapshot_preserve(
    args: IsabelleSnapshotPreserveArgs,
    build: BuildIdentity,
) -> Result<(), MathverseCliError> {
    let report = run_preserve(&args.snapshot, &args.binaries_dir, &build)?;
    println!(
        "PRESERVED: {} -> {} (sha {})",
        report.source.display(),
        report.dest.display(),
        report.sha
    );
    println!("  {}", report.pairing);
    if report.sha == "unknown" {
        eprintln!(
            "WARNING: this binary has no embedded git SHA (built without git metadata, or a \
             test-harness binary) — the copy is named `clean-unknown`. Copy the real harness \
             binary manually if this is not the `clean` release binary."
        );
    }
    Ok(())
}
