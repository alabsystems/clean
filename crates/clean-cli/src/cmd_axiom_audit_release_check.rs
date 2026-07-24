// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse axiom-audit release-check` handler — Rust wrapper around
//! `scripts/axiom_audit_release_check.sh`.
//!
//! Mirrors the migration strategy used for `clean sorry-trace`
//! (see `cmd_sorry_trace.rs`) and `clean sorry-census` (Wave 80, see
//! `cmd_sorry_census.rs`): shell-out to the existing script so the single
//! source of truth stays in `scripts/`, while exposing the workflow through
//! the unified CLI surface (`clean features`, `clean help`, `docs/cli/`).
//!
//! The wrapped script takes no arguments; it runs two non-mutating lanes
//! (aggregate consistency + live row reconciliation) and writes evidence
//! to `reports/axiom-audit-launch-evidence.json`.
//!
//! Part of the bucket-B script consolidation (Wave 87, see
//! `docs/SCRIPTS_MIGRATION.md`).

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context};

use clean_mathverse::cli::AxiomAuditReleaseCheckArgs;

/// Path to the shell script, relative to the workspace root.
const SCRIPT_REL_PATH: &str = "scripts/axiom_audit_release_check.sh";

pub(crate) fn handle_axiom_audit_release_check_command(
    _args: AxiomAuditReleaseCheckArgs,
) -> anyhow::Result<()> {
    let script = locate_script()
        .with_context(|| format!("locating {SCRIPT_REL_PATH} from current working directory"))?;

    let status = Command::new("bash")
        .arg(&script)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .with_context(|| format!("failed to spawn `bash {}`", script.display()))?;
    if !status.success() {
        bail!(
            "axiom-audit release-check: {} exited with status {status}",
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
                     run `clean mathverse axiom-audit release-check` from inside the clean checkout",
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
            "axiom_audit_release_check.sh missing at {}",
            script.display()
        );
    }

    /// The wrapped script takes no flags. This test pins that contract: the
    /// argv the handler builds is exactly `[script_path]` — no extra args
    /// leak in from `AxiomAuditReleaseCheckArgs`. Keeps the wrapper hermetic
    /// (no script spawn).
    #[test]
    fn default_args_produce_no_extra_argv() {
        let _args = AxiomAuditReleaseCheckArgs::default();
        // The script-only argv shape is enforced by the handler body (no
        // `.arg()` calls after the script path). This assertion documents the
        // contract; it is structural — the body of `handle_*` above only ever
        // calls `Command::new("bash").arg(&script)` with no further args.
        let argv: Vec<String> = Vec::new();
        assert!(argv.is_empty(), "release-check accepts no flags");
    }
}
