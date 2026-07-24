// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel soundness-gate` handler (#3444).
//!
//! Shell-out strategy. The `soundness_gate` binary wires together test-only
//! modules inside the `clean-elab` binary target via
//! `#[path = "../../../tests/..."]` imports, so the `clean-elab` library
//! cannot re-export it without a structural refactor. The handler invokes
//! the pre-existing `soundness_gate` binary located via the shared target
//! directory, `$PATH`, or a `cargo run` fallback. This preserves a single
//! source of truth (the binary + its private test-module imports) and keeps
//! the unified CLI surface intact.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{bail, Context};

pub(super) fn run() -> anyhow::Result<()> {
    let exe = locate_sibling_binary("soundness_gate");
    if let Some(path) = exe {
        run_and_forward(&path, &[])
    } else if which_in_path("soundness_gate").is_some() {
        run_and_forward(Path::new("soundness_gate"), &[])
    } else {
        // Fallback: build via cargo. Emits a clear hint if that's unavailable.
        eprintln!(
            "soundness_gate binary not found alongside the `clean` executable or on \
             $PATH; falling back to `cargo run --locked -p clean-elab --bin soundness_gate`."
        );
        let status = Command::new("cargo")
            .args([
                "run",
                "--locked",
                "--quiet",
                "-p",
                "clean-elab",
                "--bin",
                "soundness_gate",
            ])
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .status()
            .context("failed to invoke cargo to run soundness_gate")?;
        if !status.success() {
            bail!("soundness-gate: FAIL");
        }
        Ok(())
    }
}

fn locate_sibling_binary(name: &str) -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?;
    let candidate = dir.join(name);
    if candidate.is_file() {
        Some(candidate)
    } else {
        None
    }
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

fn run_and_forward(exe: &Path, args: &[&str]) -> anyhow::Result<()> {
    let status = Command::new(exe)
        .args(args)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .with_context(|| format!("failed to execute {}", exe.display()))?;
    if !status.success() {
        bail!("{} exited with status {status}", exe.display());
    }
    Ok(())
}
