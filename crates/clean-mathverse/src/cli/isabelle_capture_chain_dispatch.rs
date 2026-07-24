// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-capture-chain` — the self-healing capture
//! chain driver. Loads the typed JSON spec, then runs (or resumes, or
//! dry-runs) the chain against the real [`SystemBuildRunner`] (which shells out
//! to `isabelle build`).

use super::{IsabelleCaptureChainArgs, MathverseCliError};
use crate::hol::isabelle_capture_chain::driver::{run_capture_chain, RunOptions};
use crate::hol::isabelle_capture_chain::runner::SystemBuildRunner;
use crate::hol::isabelle_capture_chain::spec::ChainSpec;
use crate::hol::isabelle_sessions::expand_tilde;

pub(super) fn cmd_isabelle_capture_chain(
    args: IsabelleCaptureChainArgs,
) -> Result<(), MathverseCliError> {
    let spec_path = expand_tilde(&args.spec);
    let mut spec = ChainSpec::load(&spec_path)?;
    if let Some(isabelle_home) = args.isabelle_home {
        spec.isabelle_home = isabelle_home;
    }
    let opts = RunOptions {
        work_dir: args.work_dir.clone(),
        resume: args.resume,
        dry: args.dry,
    };
    let runner = SystemBuildRunner;
    let summary = run_capture_chain(&spec, &opts, &runner)?;

    if args.dry {
        eprintln!(
            "dry run: {} segment(s) planned (no builds executed)",
            summary.total_segments
        );
    } else {
        eprintln!(
            "capture-chain done: {} segment(s) — {} ok, {} proofless, {} failed; \
             {} bisect(s), {} threads=1 retr(ies); {} capture file(s) collected",
            summary.total_segments,
            summary.ok,
            summary.proofless,
            summary.failed,
            summary.bisects,
            summary.retries_threads1,
            summary.captures_collected,
        );
    }
    Ok(())
}
