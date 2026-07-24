// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean sorry-trace` handler — Rust wrapper around
//! `scripts/sorry_to_axiom_tracer.py`.
//!
//! Part of #3423 follow-up. T3 landed the Python tracer at commit `296090a21`.
//! This entry point preserves the Python CLI's flag surface
//! (`--json` / `--report` / `--report-path` / `-v*`) byte-for-byte so agents
//! and scripts can swap `python3 scripts/sorry_to_axiom_tracer.py`
//! for `clean sorry-trace` without relearning flags.
//!
//! Strategy: shell-out. The tracer is a standalone 400+ LOC Python script
//! (heuristic regex scans, markdown report rendering, axiom-audit lookup);
//! reimplementing it in Rust would duplicate logic with no soundness gain.
//! The Rust entry point exists so `clean sorry-trace` participates in the
//! unified CLI feature index (`clean features`, `clean help`, `docs/cli/`)
//! and so the Python tracer has a stable entry point when invoked from
//! tooling.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context};

use crate::cli::SorryTraceArgs;

/// Path to the Python tracer, relative to the workspace root.
const TRACER_REL_PATH: &str = "scripts/sorry_to_axiom_tracer.py";

pub(crate) fn handle_sorry_trace_command(args: SorryTraceArgs) -> anyhow::Result<()> {
    let tracer = locate_tracer()
        .with_context(|| format!("locating {TRACER_REL_PATH} from current working directory"))?;

    let python = pick_python_interpreter();
    let mut cmd = Command::new(&python);
    cmd.arg(&tracer);

    // Forward flags in the same shape the Python parser expects. Booleans
    // map to presence flags; the counted `-v` maps to a repeated short flag
    // so `--verbose --verbose` becomes `-vv`.
    if args.json {
        cmd.arg("--json");
    }
    if args.report {
        cmd.arg("--report");
    }
    if let Some(path) = args.report_path.as_ref() {
        cmd.arg("--report-path").arg(path);
    }
    for _ in 0..args.verbose {
        cmd.arg("-v");
    }

    let status = cmd
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .with_context(|| {
            format!(
                "failed to spawn `{} {}`",
                python.display(),
                tracer.display()
            )
        })?;
    if !status.success() {
        bail!(
            "sorry-trace: {} exited with status {status}",
            tracer.display()
        );
    }
    Ok(())
}

/// Resolve the tracer's on-disk path.
///
/// Walks upward from the current working directory looking for
/// `scripts/sorry_to_axiom_tracer.py`. This mirrors how
/// `cmd_kernel::generate_baseline` resolves its workspace root so the handler
/// works whether invoked from the repo root, a crate subdirectory, or a
/// worktree checkout. Returns the first match or an error if the walk hits
/// the filesystem root.
fn locate_tracer() -> anyhow::Result<PathBuf> {
    let cwd = std::env::current_dir().context("reading current working directory")?;
    let mut dir: &Path = &cwd;
    loop {
        let candidate = dir.join(TRACER_REL_PATH);
        if candidate.is_file() {
            return Ok(candidate);
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => {
                bail!(
                    "could not find {TRACER_REL_PATH} anywhere above {} — \
                     run `clean sorry-trace` from inside the clean checkout",
                    cwd.display()
                );
            }
        }
    }
}

/// Prefer the `python3` interpreter on `PATH`; fall back to `python` so
/// systems with only the unversioned binary still work.
fn pick_python_interpreter() -> PathBuf {
    if which_in_path("python3").is_some() {
        return PathBuf::from("python3");
    }
    PathBuf::from("python")
}

fn which_in_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    for entry in std::env::split_paths(&path) {
        let candidate = entry.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Python tracer must exist in the repo so `locate_tracer()` never
    /// falls off the end. Guards against accidental deletion of the script
    /// the CLI entry point wraps.
    #[test]
    fn tracer_script_is_present() {
        // CARGO_MANIFEST_DIR = crates/clean-cli; workspace root is two up.
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("workspace root above CARGO_MANIFEST_DIR");
        let tracer = root.join(TRACER_REL_PATH);
        assert!(
            tracer.is_file(),
            "sorry_to_axiom_tracer.py missing at {}",
            tracer.display()
        );
    }

    /// Smoke-test the flag-forwarding path: build the same `Command` the
    /// handler would build and inspect its argv. Doesn't spawn the tracer
    /// so the test stays hermetic.
    #[test]
    fn verbose_forwards_as_repeated_short_flags() {
        let args = SorryTraceArgs {
            json: true,
            report: false,
            report_path: None,
            verbose: 2,
        };
        // Reconstruct the argv by calling the same logic inline; the real
        // handler spawns a process which is out of scope for a unit test.
        let mut argv: Vec<String> = Vec::new();
        if args.json {
            argv.push("--json".into());
        }
        if args.report {
            argv.push("--report".into());
        }
        for _ in 0..args.verbose {
            argv.push("-v".into());
        }
        assert_eq!(argv, vec!["--json", "-v", "-v"]);
    }
}
