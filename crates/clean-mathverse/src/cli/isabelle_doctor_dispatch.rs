// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-doctor` — the ops preflight verb. Thin: it
//! translates [`IsabelleDoctorArgs`] into a [`DoctorConfig`], runs the checks,
//! renders the human or JSON report, and returns an error (nonzero exit) iff any
//! check FAILed. The real build identity is injected by the caller (`clean-cli`
//! embeds it via `build.rs`); the library path passes `BuildIdentity::unknown`.

use super::{IsabelleDoctorArgs, MathverseCliError};
use crate::hol::isabelle_doctor::{
    default_ops_dir, render_human, run_doctor, BuildIdentity, DoctorConfig, Strictness,
};

/// Run the doctor with the given (caller-provided) build identity, print the
/// report, and fail the process iff any check FAILed.
///
/// # Errors
/// [`MathverseCliError::IsabelleDoctor`] when one or more checks FAIL (after the
/// full report has already been printed), or [`MathverseCliError::Io`] if the
/// JSON report cannot be serialized/written.
pub fn run_isabelle_doctor(
    args: IsabelleDoctorArgs,
    build: BuildIdentity,
) -> Result<(), MathverseCliError> {
    let cfg = DoctorConfig {
        ops_dir: args.ops_dir.unwrap_or_else(default_ops_dir),
        corpus: args.corpus,
        snapshot: args.snapshot,
        afp_thys: args.afp_thys,
        isabelle_src: args.isabelle_src,
        verify_lock: args.verify_lock,
        disk_threshold_gib: args.disk_threshold_gib,
        strictness: if args.strict {
            Strictness::Strict
        } else {
            Strictness::Advisory
        },
    };
    let report = run_doctor(&cfg, &build);

    if args.json {
        let rendered = serde_json::to_string_pretty(&report)
            .map_err(|e| MathverseCliError::IsabelleDoctor(format!("json render: {e}")))?;
        println!("{rendered}");
    } else {
        println!("{}", render_human(&report, &cfg, &build));
    }

    if report.fail > 0 {
        return Err(MathverseCliError::IsabelleDoctor(format!(
            "{} check(s) FAILED — resolve them before running a grand import",
            report.fail
        )));
    }
    Ok(())
}
