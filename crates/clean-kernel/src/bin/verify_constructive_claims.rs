// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compatibility shim for the legacy `verify_constructive_claims` binary.
//!
//! The canonical entry point now lives under
//! `clean kernel verify-constructive-claims`. This shim preserves the old
//! binary name for one release window, prints a deprecation notice on stderr,
//! and execs the unified `clean` entry point with argv forwarded verbatim.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const DEPRECATION_NOTICE: &str =
    "warning: `verify_constructive_claims` is deprecated — use `clean kernel \
     verify-constructive-claims` instead. The legacy binary will be removed \
     after the next release. See Epic #3436 / #3510.";

fn resolve_clean_binary() -> PathBuf {
    if let Ok(explicit) = env::var("CLEAN_BIN") {
        return PathBuf::from(explicit);
    }
    if let Ok(current) = env::current_exe() {
        if let Some(dir) = current.parent() {
            let candidate = dir.join(if cfg!(windows) { "clean.exe" } else { "clean" });
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    PathBuf::from("clean")
}

fn forwarded_args<I>(args: I) -> Vec<String>
where
    I: IntoIterator<Item = String>,
{
    let mut forwarded = vec!["kernel".to_owned(), "verify-constructive-claims".to_owned()];
    forwarded.extend(args);
    forwarded
}

fn run() -> std::io::Result<i32> {
    eprintln!("{DEPRECATION_NOTICE}");

    let clean = resolve_clean_binary();
    let argv = forwarded_args(env::args().skip(1));

    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let err = Command::new(&clean).args(&argv).exec();
        Err(err)
    }

    #[cfg(not(unix))]
    {
        let status = Command::new(&clean).args(&argv).status()?;
        if let Some(code) = status.code() {
            Ok(code)
        } else {
            Ok(1)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
        Err(err) => {
            eprintln!("verify_constructive_claims: failed to exec 'clean': {err}");
            eprintln!(
                "hint: set CLEAN_BIN to the path of the unified `clean` binary, \
                 or run `cargo run -p clean --features math-overlays --bin clean -- \
                 kernel verify-constructive-claims <args...>` directly."
            );
            ExitCode::from(127)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::forwarded_args;

    #[test]
    fn forwarded_args_prefixes_the_unified_kernel_verb() {
        let args = forwarded_args(vec![
            "--conjecture".to_string(),
            "C008".to_string(),
            "--allow-empty".to_string(),
        ]);
        assert_eq!(
            args,
            vec![
                "kernel".to_string(),
                "verify-constructive-claims".to_string(),
                "--conjecture".to_string(),
                "C008".to_string(),
                "--allow-empty".to_string(),
            ]
        );
    }
}
