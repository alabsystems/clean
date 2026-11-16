// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compatibility shim for the legacy `tlaps-bench` binary.
//!
//! Part of Epic #3436 (Phase 3, #3448). The canonical entry point now lives
//! under `clean tlaps <verb>` in the unified `clean` CLI. This shim exists to
//! keep external scripts that still shell out to `tlaps-bench` working for
//! one release: it prints a deprecation notice on stderr and exec's
//! `clean tlaps <args…>` with the user's arguments forwarded verbatim.
//!
//! The legacy clap subcommands (`run` / `validate` / `show`) map to the new
//! verbs (`bench` / `validate` / `show`). Any bare argument set is forwarded
//! under `clean tlaps bench …` to preserve the old default behavior (#3448).

use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    eprintln!(
        "\
warning: `tlaps-bench` is deprecated — use `clean tlaps <verb>` instead. \
The legacy binary will be removed after the next release. See Epic #3436."
    );

    // argv[0] is the program name; skip it and translate the legacy verb if
    // present. Anything else is forwarded unchanged.
    let mut args = std::env::args().skip(1).peekable();
    let mut forwarded: Vec<String> = vec!["tlaps".to_owned()];

    match args.peek().map(String::as_str) {
        Some("run") => {
            let _ = args.next();
            forwarded.push("bench".to_owned());
        }
        Some("validate") => {
            let _ = args.next();
            forwarded.push("validate".to_owned());
        }
        Some("show") => {
            let _ = args.next();
            forwarded.push("show".to_owned());
        }
        // No verb or an unrecognized flag/path: default to `bench` so the
        // legacy default (`tlaps-bench` with no subcommand) keeps working.
        _ => forwarded.push("bench".to_owned()),
    }

    forwarded.extend(args);

    let clean_bin = std::env::var("CLEAN_BIN").unwrap_or_else(|_| "clean".to_owned());
    match Command::new(&clean_bin).args(&forwarded).status() {
        Ok(status) => ExitCode::from(status.code().unwrap_or(1) as u8),
        Err(e) => {
            eprintln!("error: failed to exec `{clean_bin}`: {e}");
            eprintln!(
                "hint: set CLEAN_BIN to the path of the unified `clean` binary, \
                 or run `cargo run -p clean -- tlaps <verb> …` directly."
            );
            ExitCode::from(127)
        }
    }
}
