// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse replay replacement evidence CLI commands.

use std::io::{self, Write};

use serde::Serialize;

use crate::cli::{MathverseCliError, ReplayCorpusArgs, ValidateReplayReportArgs};
use crate::replay_corpus::{build_replay_corpus_report, write_replay_corpus_report};
use crate::replay_report::validate_mathverse_replay_report;

#[derive(Debug, Serialize)]
struct ReplayCorpusCommandSummary {
    ok: bool,
    generated_by: &'static str,
    mode: &'static str,
    output: String,
    obligation_count: usize,
    native_gate_verified: usize,
    applied_through_strict_mathverse_use: usize,
    rejected: usize,
    unsupported: usize,
}

pub(crate) fn cmd_replay_corpus(args: ReplayCorpusArgs) -> Result<(), MathverseCliError> {
    if !args.production {
        return Err(MathverseCliError::ReplayCorpusMode(
            "`clean mathverse replay-corpus` currently supports the explicit `--production` mode"
                .to_owned(),
        ));
    }

    let report = build_replay_corpus_report(&args.root)?;
    write_replay_corpus_report(&report, &args.output)?;

    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        let summary = ReplayCorpusCommandSummary {
            ok: true,
            generated_by: "clean mathverse replay-corpus",
            mode: "production",
            output: args.output.display().to_string(),
            obligation_count: report.obligation_count,
            native_gate_verified: report.counts.native_gate_verified,
            applied_through_strict_mathverse_use: report
                .counts
                .applied_through_strict_mathverse_use,
            rejected: report.counts.rejected,
            unsupported: report.counts.unsupported,
        };
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        eprintln!(
            "wrote Mathverse replay production corpus: {} obligations -> {}",
            report.obligation_count,
            args.output.display()
        );
    }
    Ok(())
}

pub(crate) fn cmd_validate_replay_report(
    args: ValidateReplayReportArgs,
) -> Result<(), MathverseCliError> {
    let validation = validate_mathverse_replay_report(&args.root, &args.report, &args.corpus)?;
    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&validation)?)?;
    } else if validation.ok {
        println!(
            "mathverse replay report ok: {}/{} checks passed",
            validation.passed_count, validation.check_count
        );
    } else {
        eprintln!(
            "mathverse replay report invalid: {}/{} checks passed",
            validation.passed_count, validation.check_count
        );
        for error in &validation.errors {
            eprintln!("  - {error}");
        }
    }

    if validation.ok {
        Ok(())
    } else {
        Err(MathverseCliError::ReplayReportInvalid(
            validation.errors.join("; "),
        ))
    }
}
