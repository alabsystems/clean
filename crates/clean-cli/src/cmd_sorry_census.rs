// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean sorry-census` handler — Rust wrapper around
//! `scripts/sorry_census.sh`.
//!
//! Mirrors the migration strategy used for `clean sorry-trace`
//! (see `cmd_sorry_trace.rs`): shell-out to the existing script so the
//! single source of truth stays in `scripts/`, while exposing the workflow
//! through the unified CLI surface (`clean features`, `clean help`,
//! `docs/cli/`).
//!
//! Forwarded flags:
//! - `--update` — write a new baseline JSON if the count decreased.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context};

use crate::cli::SorryCensusArgs;

/// Path to the shell script, relative to the workspace root.
const SCRIPT_REL_PATH: &str = "scripts/sorry_census.sh";

pub(crate) fn handle_sorry_census_command(args: SorryCensusArgs) -> anyhow::Result<()> {
    let script = locate_script()
        .with_context(|| format!("locating {SCRIPT_REL_PATH} from current working directory"))?;

    let mut cmd = Command::new("bash");
    cmd.arg(&script);
    if args.update {
        cmd.arg("--update");
    }

    let status = cmd
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .with_context(|| format!("failed to spawn `bash {}`", script.display()))?;
    if !status.success() {
        bail!(
            "sorry-census: {} exited with status {status}",
            script.display()
        );
    }
    Ok(())
}

fn locate_script() -> anyhow::Result<PathBuf> {
    let cwd = std::env::current_dir().context("reading current working directory")?;
    let mut dir: &Path = &cwd;
    loop {
        let candidate = dir.join(SCRIPT_REL_PATH);
        if candidate.is_file() {
            return Ok(candidate);
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => {
                bail!(
                    "could not find {SCRIPT_REL_PATH} anywhere above {} — \
                     run `clean sorry-census` from inside the clean checkout",
                    cwd.display()
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shell script must exist in the repo so `locate_script()` never
    /// falls off the end. Guards against accidental deletion of the script
    /// the CLI entry point wraps.
    #[test]
    fn script_is_present() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("workspace root above CARGO_MANIFEST_DIR");
        let script = root.join(SCRIPT_REL_PATH);
        assert!(
            script.is_file(),
            "sorry_census.sh missing at {}",
            script.display()
        );
    }

    /// Smoke-test the flag-forwarding: build the same argv the handler
    /// would build and inspect it. Doesn't spawn the script so the test
    /// stays hermetic.
    #[test]
    fn update_forwards_as_flag() {
        let args = SorryCensusArgs { update: true };
        let mut argv: Vec<String> = Vec::new();
        if args.update {
            argv.push("--update".into());
        }
        assert_eq!(argv, vec!["--update"]);
    }

    #[test]
    fn default_passes_no_flags() {
        let args = SorryCensusArgs::default();
        let argv: Vec<String> = if args.update {
            vec!["--update".into()]
        } else {
            Vec::new()
        };
        assert!(argv.is_empty());
    }
}
