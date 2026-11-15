// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean olean <verb>` subcommand into the `clean-olean`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), overlay generation, batch
//! verification, and library access live in [`clean_olean::cli`]. This
//! wrapper exists only to convert the typed
//! [`OleanCliError`](clean_olean::cli::OleanCliError) into `anyhow` context
//! for the top-level CLI dispatcher (see `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436: absorbs the deprecated standalone `.olean` binaries
//! (`generate_namespace_overlay` per #3442, `verify_olean_batch` per #3441)
//! into the unified `clean` CLI surface via a single `OleanCommands` enum.

use clean_olean::cli::{run as olean_run, OleanArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_olean_command(args: OleanArgs) -> anyhow::Result<()> {
    olean_run(args).map_err(anyhow::Error::from)
}

/// The exit code a `clean olean` error asks for
/// ([`OleanCliError::exit_code`](clean_olean::cli::OleanCliError::exit_code)):
/// 2 when the verb declined to judge, 1 otherwise.
pub(crate) fn olean_exit_code(err: &anyhow::Error) -> Option<i32> {
    err.downcast_ref::<clean_olean::cli::OleanCliError>()
        .map(|e| i32::from(e.exit_code()))
}

#[cfg(test)]
mod tests {
    use super::olean_exit_code;
    use clean_olean::cli::OleanCliError;

    #[test]
    fn test_olean_exit_code_declined_export_exits_two() {
        let declined = anyhow::Error::from(OleanCliError::ExportDeclined {
            path: "x.ndjson".to_owned(),
            reason: "format version 4.0.0".to_owned(),
        });
        assert_eq!(olean_exit_code(&declined), Some(2));
        assert_eq!(crate::forwarded_exit_code(&declined), Some(2));
        let rejected = anyhow::Error::from(OleanCliError::ExportRejected {
            path: "x.ndjson".to_owned(),
            first: "duplicate object key".to_owned(),
        });
        assert_eq!(crate::forwarded_exit_code(&rejected), Some(1));
        let undecided = anyhow::Error::from(OleanCliError::ReplayRefused {
            refused: 1,
            replayed: 1,
            selected: 1,
            first: "budget".to_owned(),
            undecided: true,
        });
        assert_eq!(crate::forwarded_exit_code(&undecided), Some(2));
    }
}
