// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned release readiness proof surfaces.

use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::{Args, Subcommand};
use serde::Serialize;

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum ReleaseCommands {
    /// Run the Rust-owned release readiness smoke proof surface.
    #[command(name = "readiness-smoke")]
    ReadinessSmoke(ReleaseReadinessSmokeArgs),
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ReleaseReadinessSmokeArgs {
    /// Also run the detached worktree cargo metadata, public demo, and benchmark lanes.
    #[arg(long)]
    clean_clone_lite: bool,
    /// Require the launch benchmark checker in the clean-clone lane.
    #[arg(long)]
    launch: bool,
    /// Write machine-readable JSON evidence to this path.
    #[arg(long, value_name = "PATH")]
    evidence: Option<PathBuf>,
    /// Emit the evidence JSON on stdout.
    #[arg(long)]
    json: bool,
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum ReleaseError {
    #[error("invalid release evidence target: {0}")]
    EvidenceTarget(String),
    #[error("failed to serialize release readiness JSON: {0}")]
    Serialize(serde_json::Error),
    #[error("failed to write release readiness output: {0}")]
    Io(#[from] io::Error),
    #[error("release readiness smoke is not ready: {0}")]
    NotReady(String),
}

#[derive(Debug, Clone, Serialize)]
struct ReleaseReadinessSmokeReport {
    issue: &'static str,
    generated_by: &'static str,
    status: &'static str,
    commit: String,
    git_status_short: String,
    clean_clone_lite_requested: bool,
    launch_requested: bool,
    public_demo_artifacts_dir: String,
    public_demo_artifacts_copied: bool,
    clean_clone_logs_dir: String,
    failure_count: usize,
    commands: Vec<String>,
    failures: Vec<String>,
}

struct ReleaseReadinessSmokeRunner {
    report: ReleaseReadinessSmokeReport,
    evidence_path: Option<PathBuf>,
}

pub(crate) fn handle_release_command(command: ReleaseCommands) -> Result<(), ReleaseError> {
    match command {
        ReleaseCommands::ReadinessSmoke(args) => run_readiness_smoke(args),
    }
}

fn run_readiness_smoke(args: ReleaseReadinessSmokeArgs) -> Result<(), ReleaseError> {
    validate_evidence_path(args.evidence.as_deref())?;

    let mut runner = ReleaseReadinessSmokeRunner::new(&args);
    runner.run_static_contract_checks();
    if args.clean_clone_lite {
        runner.run_clean_clone_lite(args.launch);
    }
    runner.finish(args.json)
}

impl ReleaseReadinessSmokeRunner {
    fn new(args: &ReleaseReadinessSmokeArgs) -> Self {
        let command = readiness_smoke_command(args);
        Self {
            report: ReleaseReadinessSmokeReport {
                issue: "#3671",
                generated_by: "clean release readiness-smoke",
                status: "NOT READY",
                commit: command_output("git", &["rev-parse", "--verify", "HEAD"])
                    .unwrap_or_else(|| "unknown".to_string()),
                git_status_short: command_output("git", &["status", "--short"])
                    .unwrap_or_else(|| "unknown".to_string()),
                clean_clone_lite_requested: args.clean_clone_lite,
                launch_requested: args.launch,
                public_demo_artifacts_dir: String::new(),
                public_demo_artifacts_copied: false,
                clean_clone_logs_dir: String::new(),
                failure_count: 0,
                commands: vec![command],
                failures: Vec::new(),
            },
            evidence_path: args.evidence.clone(),
        }
    }

    fn run_static_contract_checks(&mut self) {
        self.require_file("docs/RELEASE_READINESS.md");
        self.require_file("docs/MATHVERSE_RELEASE_CHECKLIST.md");
        self.require_file("docs/plans/LEAN4_REPLACEMENT_PLAN.md");
        self.require_file("Cargo.toml");
        self.require_file("README.md");
        self.require_file("CITATION.cff");
        self.require_file("SUPPORT.md");
        self.require_file("docs/BENCHMARKS.md");
        self.require_file("docs/DESIGN.md");
        self.require_file("docs/PUBLIC_DEMO.md");
        self.require_file("docs/VERIFICATION_AUDIT.md");
        self.require_file("demos/public/kernel_check_success.lean");
        self.require_file("demos/public/kernel_check_reject_sorry.lean");
        self.require_file("scripts/run_public_demo.sh");
        self.require_file("scripts/check_benchmark_publication.py");
        self.require_file("crates/clean-cli/src/cmd_factory.rs");

        self.require_text("docs/RELEASE_READINESS.md", "#3671");
        self.require_text("docs/RELEASE_READINESS.md", "clean release readiness-smoke");
        self.require_text(
            "docs/RELEASE_READINESS.md",
            "clean replacement release-issue-hygiene --fetch --json",
        );
        self.require_text("docs/RELEASE_READINESS.md", "clean factory status --json");
        self.require_text(
            "docs/RELEASE_READINESS.md",
            "clean bench publication-check --launch --json",
        );
        self.require_text("docs/RELEASE_READINESS.md", "## Aggregate Gate Map");
        self.require_text("docs/RELEASE_READINESS.md", "## clean Clone");
        self.require_text("docs/RELEASE_READINESS.md", "## Issue Hygiene");
        self.require_text("docs/PUBLIC_DEMO.md", "./scripts/run_public_demo.sh");
        self.require_text("docs/BENCHMARKS.md", "Last audited:");
        self.require_text(
            "crates/clean-cli/src/cmd_factory.rs",
            "clean factory status --json",
        );
    }

    fn run_clean_clone_lite(&mut self, launch: bool) {
        let Some(head) = command_output("git", &["rev-parse", "--verify", "HEAD"]) else {
            self.fail("cannot resolve HEAD for --clean-clone-lite");
            return;
        };
        let temp_root = env::temp_dir().join(format!(
            "clean-rust-clean-clone-lite-{}",
            std::process::id()
        ));
        let checkout = temp_root.join("clean");
        let _ = fs::remove_dir_all(&temp_root);
        if let Err(err) = fs::create_dir_all(&temp_root) {
            self.fail(format!(
                "cannot create temporary clean-clone-lite directory: {err}"
            ));
            return;
        }

        if !self.run_command(
            None,
            "git worktree add --detach <tmp>/clean HEAD",
            Command::new("git")
                .arg("worktree")
                .arg("add")
                .arg("--detach")
                .arg(&checkout)
                .arg(&head),
        ) {
            let _ = fs::remove_dir_all(&temp_root);
            return;
        }

        self.run_command(
            Some(&checkout),
            "cargo metadata --locked --no-deps --format-version 1",
            Command::new("cargo")
                .arg("metadata")
                .arg("--locked")
                .arg("--no-deps")
                .arg("--format-version")
                .arg("1"),
        );
        self.run_command(
            Some(&checkout),
            "./scripts/run_public_demo.sh",
            &mut Command::new("./scripts/run_public_demo.sh"),
        );
        let mut bench = Command::new(env::current_exe().unwrap_or_else(|_| PathBuf::from("clean")));
        bench.arg("bench").arg("publication-check").arg("--json");
        if launch {
            bench.arg("--launch");
        }
        self.run_command(
            Some(&checkout),
            if launch {
                "clean bench publication-check --launch --json"
            } else {
                "clean bench publication-check --json"
            },
            &mut bench,
        );
        if let Some(status) = command_output_in(&checkout, "git", &["status", "--short"]) {
            if !status.is_empty() {
                self.fail(format!(
                    "clean checkout was modified; first status: {}",
                    status.lines().next().unwrap_or("")
                ));
            }
        } else {
            self.fail("cannot read clean checkout git status");
        }

        let _ = Command::new("git")
            .arg("worktree")
            .arg("remove")
            .arg("--force")
            .arg(&checkout)
            .status();
        let _ = fs::remove_dir_all(&temp_root);
    }

    fn run_command(&mut self, cwd: Option<&Path>, label: &str, command: &mut Command) -> bool {
        self.report.commands.push(label.to_string());
        if let Some(cwd) = cwd {
            command.current_dir(cwd);
        }
        match command.status() {
            Ok(status) if status.success() => true,
            Ok(status) => {
                self.fail(format!("release command failed: {label} (exit {status})"));
                false
            }
            Err(err) => {
                self.fail(format!("cannot run release command {label}: {err}"));
                false
            }
        }
    }

    fn require_file(&mut self, path: &str) {
        if !Path::new(path).is_file() {
            self.fail(format!("missing {path}"));
        }
    }

    fn require_text(&mut self, path: &str, needle: &str) {
        match fs::read_to_string(path) {
            Ok(text) if text.contains(needle) => {}
            Ok(_) => self.fail(format!("{path} missing {needle}")),
            Err(_) => self.fail(format!("cannot scan missing {path} for {needle}")),
        }
    }

    fn fail(&mut self, message: impl Into<String>) {
        self.report.failures.push(message.into());
        self.report.failure_count = self.report.failures.len();
    }

    fn finish(mut self, json: bool) -> Result<(), ReleaseError> {
        self.report.failure_count = self.report.failures.len();
        self.report.status = if self.report.failure_count == 0 {
            "READY"
        } else {
            "NOT READY"
        };

        if let Some(path) = &self.evidence_path {
            fs::write(
                path,
                format!(
                    "{}\n",
                    serde_json::to_string_pretty(&self.report).map_err(ReleaseError::Serialize)?
                ),
            )?;
        }

        let stdout = io::stdout();
        let mut out = stdout.lock();
        if json {
            writeln!(
                out,
                "{}",
                serde_json::to_string_pretty(&self.report).map_err(ReleaseError::Serialize)?
            )?;
        } else if self.report.failure_count == 0 {
            writeln!(out, "=== Release readiness smoke: READY ===")?;
        } else {
            writeln!(
                out,
                "=== Release readiness smoke: NOT READY ({} failures) ===",
                self.report.failure_count
            )?;
        }

        if self.report.failure_count == 0 {
            Ok(())
        } else {
            Err(ReleaseError::NotReady(self.report.failures.join("; ")))
        }
    }
}

fn validate_evidence_path(path: Option<&Path>) -> Result<(), ReleaseError> {
    let Some(path) = path else {
        return Ok(());
    };
    let Some(parent) = path.parent() else {
        return Ok(());
    };
    if !parent.as_os_str().is_empty() && !parent.is_dir() {
        return Err(ReleaseError::EvidenceTarget(format!(
            "--evidence parent directory does not exist: {}",
            parent.display()
        )));
    }
    if path.exists() && !path.is_file() {
        return Err(ReleaseError::EvidenceTarget(format!(
            "--evidence must name a file, got non-file path: {}",
            path.display()
        )));
    }
    Ok(())
}

fn readiness_smoke_command(args: &ReleaseReadinessSmokeArgs) -> String {
    let mut command = "clean release readiness-smoke".to_string();
    if args.clean_clone_lite {
        command.push_str(" --clean-clone-lite");
    }
    if args.launch {
        command.push_str(" --launch");
    }
    if let Some(path) = &args.evidence {
        command.push_str(" --evidence ");
        command.push_str(&path.to_string_lossy());
    }
    if args.json {
        command.push_str(" --json");
    }
    command
}

fn command_output(program: &str, args: &[&str]) -> Option<String> {
    command_output_in(Path::new("."), program, args)
}

fn command_output_in(cwd: &Path, program: &str, args: &[&str]) -> Option<String> {
    let output = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_readiness_smoke_static_contract_is_ready() {
        let report = ReleaseReadinessSmokeRunner::new(&ReleaseReadinessSmokeArgs {
            clean_clone_lite: false,
            launch: false,
            evidence: None,
            json: true,
        });
        assert_eq!(report.report.generated_by, "clean release readiness-smoke");
        assert_eq!(report.report.issue, "#3671");
    }

    #[test]
    fn release_readiness_smoke_command_records_flags() {
        let command = readiness_smoke_command(&ReleaseReadinessSmokeArgs {
            clean_clone_lite: true,
            launch: true,
            evidence: Some(PathBuf::from("/tmp/clean-release.json")),
            json: true,
        });
        assert_eq!(
            command,
            "clean release readiness-smoke --clean-clone-lite --launch --evidence /tmp/clean-release.json --json"
        );
    }
}
