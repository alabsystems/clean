// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean verify proof` subcommand into the `clean-verify`
//! crate's CLI module.
//!
//! The actual argument parsing, per-mode runners, and descriptor registration
//! live in [`clean_verify::cli`]. This wrapper propagates the runner's
//! contractual exit code (0 verified / 10 invalid / 1 error) up to the
//! top-level `clean-cli` binary via `std::process::exit` — the competition
//! judging scripts consume these bytes directly, so we cannot tunnel the
//! outcome through `anyhow::Result` without losing parity with the legacy
//! `proof_check` binary.
//!
//! Argument-level failures (e.g. bogus `--format <FMT>`) are surfaced as
//! `anyhow::Error` so they flow through the normal top-level error reporter
//! path, matching every other `clean verify <verb>`.
//!
//! Part of Epic #3436 (#3511).

use clean_verify::cli::{run as sat_verify_run, VerifyProofArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_verify_proof_command(args: VerifyProofArgs) -> anyhow::Result<()> {
    let exit = sat_verify_run(args).map_err(anyhow::Error::from)?;
    // Preserve the SAT-COMP / SMT-COMP exit-code contract exactly. Any other
    // mapping (e.g. Err for non-zero) would be consumed as a stderr message
    // by judging scripts and break parity.
    std::process::exit(exit);
}
