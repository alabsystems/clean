// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime for `clean olean replay`: resolve the modules the way
//! `leanchecker` does, replay each (`crate::replay_module`), and report.
//!
//! `leanchecker` (`src/lean/LeanChecker.lean`, v4.30.0-rc2) runs every module
//! as a task and, waiting on them in order, prints `leanchecker found a problem
//! in <m>` and exits 1 at the first failed one. This runner replays modules
//! one at a time (memory, not time, is what binds on this hardware), stops at
//! the first refused module unless `--keep-going` is given, and exits non-zero
//! whenever any module was refused or could not be loaded.

use std::collections::BTreeSet;

use crate::replay_module::{
    replay_module, replay_search_path, select_modules, ModuleReplayRecord, RefusalOutcome,
    ReplayMode, ReplayTargetError,
};

use super::OleanCliError;

/// `clean olean replay`'s arguments (the fields of `OleanCommands::Replay`,
/// documented there).
pub(super) struct ReplayOptions {
    pub(super) modules: Vec<String>,
    pub(super) fresh: bool,
    pub(super) exact: bool,
    pub(super) search_paths: Vec<std::path::PathBuf>,
    pub(super) max_heartbeats: u32,
    pub(super) keep_going: bool,
    pub(super) json: bool,
}

/// The replay thread's stack: the kernel's recursion is `stack_safe`, but the
/// loader and the replay schedule over a large closure are not all bounded,
/// and `clean olean verify-batch` runs on the same 1 GiB stack.
const REPLAY_STACK_BYTES: usize = 1024 * 1024 * 1024;

impl From<ReplayTargetError> for OleanCliError {
    fn from(error: ReplayTargetError) -> Self {
        OleanCliError::ReplayTargets(error.to_string())
    }
}

fn print_record(record: &ModuleReplayRecord, json: bool) -> Result<(), OleanCliError> {
    if json {
        let line = serde_json::to_string(record)
            .map_err(|error| OleanCliError::ReplayReport(error.to_string()))?;
        println!("{line}");
        return Ok(());
    }
    if let Some(error) = &record.load_error {
        eprintln!(
            "clean olean replay found a problem in {}: the .olean closure could not be loaded: {error}",
            record.module
        );
        return Ok(());
    }
    match &record.first_refusal {
        None => println!(
            "{}: {} declaration(s) replayed, all admitted ({} unsafe/partial left out; load {} ms, replay {} ms)",
            record.module,
            record.constants_checked,
            record.not_replayable,
            record.load_ms,
            record.replay_ms
        ),
        Some(first) => {
            // `leanchecker`'s wording is for a finding; a budget refusal is
            // none, so its headline says what happened instead.
            let headline = match first.outcome {
                RefusalOutcome::Refused => "found a problem in",
                RefusalOutcome::BudgetExhausted => "ran out of its --max-heartbeats budget in",
            };
            eprintln!(
                "clean olean replay {headline} {}\nwhile replaying declaration '{}':\n{}",
                record.module, first.constant, first.reason
            );
            eprintln!(
                "{}: {} of {} declaration(s) refused",
                record.module,
                record.refusals.len(),
                record.constants_checked
            );
            if record.budget_exhausted != 0 {
                eprintln!(
                    "{}: {} of those refusal(s) are budget exhausted, not findings: the \
                     --max-heartbeats budget ran out before the kernel decided (or every \
                     dependency refusing it was so left undecided); none is admitted",
                    record.module, record.budget_exhausted
                );
            }
        }
    }
    Ok(())
}

/// Replay every selected module; `Ok` only when every one was admitted.
fn replay_all(
    modules: &BTreeSet<String>,
    mode: ReplayMode,
    search_path: &[std::path::PathBuf],
    args: &ReplayOptions,
) -> Result<(), OleanCliError> {
    let mut replayed = 0usize;
    let mut refused = 0usize;
    let mut undecided = true;
    let mut first: Option<String> = None;
    for module in modules {
        let record = replay_module(module, mode, search_path, args.max_heartbeats);
        replayed += 1;
        print_record(&record, args.json)?;
        if !record.ok {
            refused += 1;
            // Undecided: loaded, refused, and every refusal the budget's.
            undecided &= record.load_error.is_none()
                && !record.refusals.is_empty()
                && record
                    .refusals
                    .iter()
                    .all(|r| r.outcome == RefusalOutcome::BudgetExhausted);
            if first.is_none() {
                first = Some(match (&record.load_error, &record.first_refusal) {
                    (Some(error), _) => format!("{module}: load error: {error}"),
                    (None, Some(r)) => format!("{module}: `{}`: {}", r.constant, r.reason),
                    (None, None) => format!("{module}: refused"),
                });
            }
            if !args.keep_going {
                break;
            }
        }
    }
    match first {
        None => Ok(()),
        Some(first) => Err(OleanCliError::ReplayRefused {
            refused,
            replayed,
            selected: modules.len(),
            first,
            undecided,
        }),
    }
}

/// `clean olean replay --from-export <FILE>`: the NDJSON front door
/// (`crate::ndjson`), on the replay's 1 GiB stack.
pub(super) fn run_from_export(
    path: &std::path::Path,
    max_heartbeats: u32,
    json: bool,
) -> Result<(), OleanCliError> {
    let owned = path.to_path_buf();
    let worker = std::thread::Builder::new()
        .name("ndjson-replay".to_owned())
        .stack_size(REPLAY_STACK_BYTES)
        .spawn(move || {
            crate::ndjson::check_export_path(
                &owned,
                crate::ndjson::ExportCheckOptions {
                    max_heartbeats,
                    axiom_closures: json,
                },
            )
        })
        .map_err(|error| {
            OleanCliError::ReplayReport(format!("cannot start the replay: {error}"))
        })?;
    let shown = path.display().to_string();
    // A panic judged nothing: exit 2, as `clean_export_check` exits. (A
    // release build aborts on a panic instead, `panic = "abort"`, and no exit
    // code is written at all.)
    let report = worker.join().map_err(|_| OleanCliError::ExportDeclined {
        path: shown.clone(),
        reason: "the replay thread panicked: nothing was judged".to_owned(),
    })?;
    if json {
        let line = serde_json::to_string(&report)
            .map_err(|error| OleanCliError::ReplayReport(error.to_string()))?;
        println!("{line}");
    }
    match report.exit {
        crate::ndjson::ExitClass::Accept => {
            if !json {
                println!(
                    "{shown}: {} declaration(s) replayed, all admitted ({} unsafe left out; load \
                     {} ms, replay {} ms)",
                    report.declarations, report.not_replayable, report.load_ms, report.replay_ms
                );
            }
            Ok(())
        }
        crate::ndjson::ExitClass::Reject => {
            let first = match (&report.reader_error, &report.first_refusal) {
                (Some(reader), _) => format!("{} ({})", reader.message, reader.rule),
                (None, Some(first)) => {
                    format!(
                        "while replaying declaration '{}': {}",
                        first.name, first.reason
                    )
                }
                (None, None) => "refused".to_owned(),
            };
            if !json {
                eprintln!(
                    "clean olean replay found a problem in {shown}: {first} ({} of {} \
                     declaration(s) refused)",
                    report.refused, report.declarations
                );
            }
            Err(OleanCliError::ExportRejected { path: shown, first })
        }
        crate::ndjson::ExitClass::Decline => {
            let reason = match (&report.reader_error, &report.decline_reason) {
                (Some(reader), _) => format!("{} ({})", reader.message, reader.rule),
                (None, Some(reason)) => reason.clone(),
                (None, None) => "declined".to_owned(),
            };
            if !json {
                eprintln!("clean olean replay declines {shown}: {reason}");
            }
            Err(OleanCliError::ExportDeclined {
                path: shown,
                reason,
            })
        }
    }
}

/// `clean olean replay <Module>...`.
pub(super) fn run_replay(args: ReplayOptions) -> Result<(), OleanCliError> {
    let lean_path = std::env::var_os("LEAN_PATH");
    let search_path = replay_search_path(
        &args.search_paths,
        lean_path.as_deref(),
        crate::pinned_lean_lib_path(),
    )?;
    let modules = select_modules(&args.modules, &search_path, args.exact, args.fresh)?;
    let mode = if args.fresh {
        ReplayMode::Fresh
    } else {
        ReplayMode::ImportsTrusted
    };
    let worker = std::thread::Builder::new()
        .name("olean-replay".to_owned())
        .stack_size(REPLAY_STACK_BYTES)
        .spawn(move || replay_all(&modules, mode, &search_path, &args))
        .map_err(|error| {
            OleanCliError::ReplayReport(format!("cannot start the replay: {error}"))
        })?;
    worker.join().unwrap_or_else(|_| {
        Err(OleanCliError::ReplayReport(
            "the replay thread panicked".to_owned(),
        ))
    })
}
