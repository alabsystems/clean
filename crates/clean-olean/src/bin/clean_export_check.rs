// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean_export_check [--max-heartbeats N] [--json] <export.ndjson>`: the
//! NDJSON front door (`clean_olean::ndjson`, the engine of `clean olean replay
//! --from-export`) as a standalone checker.
//!
//! `--reference --permit <axiom>...` invokes the fenced reference
//! entry for the self-proof quorum (Q1; Q4 will orchestrate this command).
//! Permits default to empty and can only narrow the entry's Ax0 policy.
//! This mode prints its reference report with `--json` and exits 0 only for
//! acceptance; 1 for any refusal, an export the reader refuses or declines
//! and a read failure inside it included; 2 for a usage error (front-door
//! options are refused), an export it cannot open, or an entry that cannot run.
//!
//!
//! The export path is the one argument that is not a flag (Lake's external
//! kernels pass it last), and the exit code is the verdict, the contract of
//! Lake's external kernels and the Kernel Arena: 0 accepts, 1 rejects, 2
//! declines. A usage error exits 2 too: nothing was judged. `--json` prints the
//! report as one JSON line on stdout, with each declaration's structural axiom
//! closure; `--max-heartbeats N` bounds each declaration's check (`0`, the
//! default, is unlimited, as Lean's replay runs), and a declaration that runs
//! out declines the export unless another one is refused. A panic in the
//! replay exits 2 where panics unwind (a debug or test build); the release
//! profile is `panic = "abort"`, so there a panic aborts the process
//! (`SIGABRT`) and no exit code is written. The arena battery
//! (`tests/kernel_arena_battery.rs`) runs one process per test, so a timeout
//! or a crash in one test cannot take the battery with it, and records a
//! signal as its own ending, never as a verdict.

#[path = "clean_export_check/reference.rs"]
mod reference;

use std::path::PathBuf;
use std::process::ExitCode;

use clean_olean::ndjson::{check_export_path, ExportCheckOptions};

/// The replay's stack, as `clean olean replay` runs it.
const STACK_BYTES: usize = 1024 * 1024 * 1024;

const USAGE: &str = "usage: clean_export_check [--max-heartbeats N] [--json] <export.ndjson>";

fn parse(args: &[String]) -> Result<(PathBuf, ExportCheckOptions, bool), String> {
    let mut options = ExportCheckOptions::default();
    let mut json = false;
    let mut path = None;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--json" => json = true,
            "--max-heartbeats" => {
                let n = it.next().ok_or("--max-heartbeats needs a value")?;
                options.max_heartbeats = n
                    .parse()
                    .map_err(|e| format!("--max-heartbeats {n}: {e}"))?;
            }
            other if other.starts_with("--") => return Err(format!("unknown flag {other}")),
            other => {
                if path.replace(PathBuf::from(other)).is_some() {
                    return Err("exactly one export path".to_owned());
                }
            }
        }
    }
    options.axiom_closures = json;
    let path = path.ok_or("no export path")?;
    Ok((path, options, json))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|arg| arg == "--reference") {
        return reference::run(&args);
    }
    let (path, options, json) = match parse(&args) {
        Ok(parsed) => parsed,
        Err(problem) => {
            eprintln!("clean_export_check: {problem}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let worker = std::thread::Builder::new()
        .name("ndjson-replay".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || check_export_path(&path, options));
    let report = match worker.map(std::thread::JoinHandle::join) {
        Ok(Ok(report)) => report,
        Ok(Err(_)) => {
            eprintln!("clean_export_check: the replay thread panicked");
            return ExitCode::from(2);
        }
        Err(e) => {
            eprintln!("clean_export_check: cannot start the replay: {e}");
            return ExitCode::from(2);
        }
    };
    if json {
        match serde_json::to_string(&report) {
            Ok(line) => println!("{line}"),
            Err(e) => {
                eprintln!("clean_export_check: cannot render the report: {e}");
                return ExitCode::from(2);
            }
        }
    }
    if let Some(reader) = &report.reader_error {
        eprintln!("{} ({})", reader.message, reader.rule);
    } else if let Some(first) = &report.first_refusal {
        eprintln!(
            "while replaying declaration '{}': {}",
            first.name, first.reason
        );
    } else if let Some(reason) = &report.decline_reason {
        eprintln!("declined: {reason}");
    }
    ExitCode::from(report.exit_code)
}
