// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake replacement smoke evidence generator (#3707).
//!
//! `clean lake smoke` runs the governed init → build → test sequence in a
//! throwaway temp project (the `clean lake init` template: a `lean_lib` plus a
//! `lean_test` whose root defines the bounded native entrypoint
//! `def main : IO Unit := pure ()`), entirely through clean-owned in-process
//! Lake handlers, then writes the JSON evidence artifact the lake-workflow
//! replacement row names (`reports/lake-replacement-smoke.json` in
//! `cmd_replacement::rows`). Every step's pass/fail verdict and reproducing
//! command is recorded; the command exits non-zero when any step fails, after
//! still writing the honest per-step results (fail-closed, never
//! evidence-free).
//!
//! No-Lean4-delegation posture: this module never spawns Lean4's `lean` or
//! `lake` binaries — the steps call the same in-process handlers as
//! `clean lake init/build/test`, whose refusal to delegate is source-gated by
//! `crates/clean-cli/tests/lake_replacement_delegation.rs`.

use serde::Serialize;
use std::path::Path;
use std::time::Instant;

/// Schema version stamped into the generated artifact.
const LAKE_SMOKE_SCHEMA_VERSION: &str = "clean-lake-replacement-smoke-v1";

/// Replacement scorecard row this artifact backs (`cmd_replacement::rows`).
const LAKE_SMOKE_ROW_ID: &str = "lake-workflow";
const LAKE_SMOKE_ROW_ISSUE: u32 = 3707;

/// Temp project name. `clean lake init` derives package `replacement_smoke`,
/// lib module `ReplacementSmoke`, and test target `replacement_smoke_test`.
const SMOKE_PROJECT_NAME: &str = "replacement-smoke";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum SmokeStepStatus {
    Passed,
    Failed,
    NotRun,
}

#[derive(Debug, Serialize)]
struct SmokeStep {
    id: &'static str,
    /// The `clean lake` command this step is the in-process equivalent of,
    /// executed inside the throwaway temp project directory.
    command: &'static str,
    status: SmokeStepStatus,
    detail: String,
    duration_ms: u64,
}

#[derive(Debug, Serialize)]
struct SmokeReplacementRow {
    id: &'static str,
    issue: u32,
    expected_by_scorecard: bool,
    recommended_scorecard_status: &'static str,
}

#[derive(Debug, Serialize)]
struct SmokeDelegationEvidence {
    execution: &'static str,
    source_gate: &'static str,
    /// Whether a `lean` binary happens to be reachable on PATH when the smoke
    /// ran. Recorded as context only: the execution path above never invokes
    /// it either way.
    lean_binary_on_path: bool,
    note: &'static str,
}

#[derive(Debug, Serialize)]
struct LakeSmokeArtifact {
    schema_version: &'static str,
    generated_by: String,
    generated_at_commit: String,
    status: &'static str,
    passed: bool,
    replacement_row: SmokeReplacementRow,
    project_template: &'static str,
    steps: Vec<SmokeStep>,
    no_lean4_delegation: SmokeDelegationEvidence,
    non_claims: Vec<&'static str>,
}

/// Run the governed Lake replacement smoke and write its evidence artifact.
///
/// Fail-closed contract: the artifact is written whether or not the steps
/// pass (recording the honest per-step verdicts), and the process exits
/// non-zero when any step failed so the replacement gate command cannot go
/// green on a broken smoke.
pub(super) fn lake_smoke(report: &Path, verbose: bool) -> anyhow::Result<()> {
    let temp = tempfile::Builder::new()
        .prefix("clean-lake-replacement-smoke-")
        .tempdir()
        .map_err(|err| {
            anyhow::anyhow!("clean lake smoke could not create a temp project directory: {err}")
        })?;
    let project_dir = temp.path().join(SMOKE_PROJECT_NAME);

    let mut steps: Vec<SmokeStep> = Vec::new();
    let mut all_passed = true;

    run_step(
        &mut steps,
        &mut all_passed,
        "init",
        "clean lake init replacement-smoke",
        verbose,
        || {
            std::fs::create_dir_all(&project_dir)?;
            super::build::lake_init(
                Some(SMOKE_PROJECT_NAME.to_string()),
                Some(project_dir.clone()),
            )
        },
    );

    run_step(
        &mut steps,
        &mut all_passed,
        "build",
        "clean lake build",
        verbose,
        || {
            use clean_lake::{BuildContext, BuildOptions, Workspace};

            let config = super::load_project_config(&project_dir)?;
            let ws = Workspace::from_config(&project_dir, config);
            let mut ctx =
                BuildContext::new(ws).with_options(BuildOptions::new().with_verbose(verbose));
            let result = ctx.build_all()?;
            if !result.failed.is_empty() {
                let failures = result
                    .failed
                    .iter()
                    .map(|(module, err)| format!("{module}: {err}"))
                    .collect::<Vec<_>>()
                    .join("; ");
                anyhow::bail!(
                    "{} module(s) failed to build: {failures}",
                    result.failed.len()
                );
            }
            super::build::ensure_native_artifacts_for_executable_targets(ctx.workspace(), None)
        },
    );

    run_step(
        &mut steps,
        &mut all_passed,
        "test",
        "clean lake test",
        verbose,
        || super::run::lake_test_with_args(None, &[], verbose, 0, Some(project_dir.clone())),
    );

    let failed_steps = steps
        .iter()
        .filter(|step| step.status == SmokeStepStatus::Failed)
        .count();

    let artifact = LakeSmokeArtifact {
        schema_version: LAKE_SMOKE_SCHEMA_VERSION,
        generated_by: format!("clean lake smoke --report {}", report.display()),
        generated_at_commit: head_commit(),
        status: if all_passed { "passed" } else { "failed" },
        passed: all_passed,
        replacement_row: SmokeReplacementRow {
            id: LAKE_SMOKE_ROW_ID,
            issue: LAKE_SMOKE_ROW_ISSUE,
            expected_by_scorecard: true,
            recommended_scorecard_status: "in_progress",
        },
        project_template: "clean lake init template (lean_lib ReplacementSmoke + lean_test \
                           replacement_smoke_test with `def main : IO Unit := pure ()`), created \
                           in a throwaway temp directory and deleted after the run",
        steps,
        no_lean4_delegation: SmokeDelegationEvidence {
            execution: "every step ran in-process through clean's own Lake handlers \
                        (clean_cli::cmd_lake); this path never spawns Lean4's `lean` or `lake` \
                        binaries",
            source_gate: "crates/clean-cli/tests/lake_replacement_delegation.rs",
            lean_binary_on_path: lean_binary_on_path(),
            note: "the test executable is emitted by clean's native build engine and linked by \
                   the host C compiler; Lean4 is not consulted even when present on PATH",
        },
        non_claims: vec![
            "Covers only the bounded init/build/test template smoke; it does not claim full \
             Lake workflow parity (no transitive dependency resolution, no `lake serve`, no \
             facets/custom targets, no Mathlib cloud cache).",
            "A passing smoke does not by itself make the lake-workflow replacement row green; \
             scorecard status changes are reviewed against the fail-closed \
             `clean replacement status` gate.",
        ],
    };

    write_report(report, &artifact)?;

    println!(
        "Lake replacement smoke: {} ({}/{} step(s) passed); evidence written to {}",
        artifact.status,
        artifact
            .steps
            .iter()
            .filter(|step| step.status == SmokeStepStatus::Passed)
            .count(),
        artifact.steps.len(),
        report.display()
    );

    if !all_passed {
        anyhow::bail!(
            "clean lake smoke is fail-closed: {failed_steps} step(s) failed; per-step evidence \
             was still recorded at {}",
            report.display()
        );
    }
    Ok(())
}

/// Execute one smoke step, recording its verdict. Once any step has failed,
/// later steps are recorded as `not_run` instead of executing (fail-closed:
/// a broken `init` must not be masked by a vacuous `build`/`test`).
fn run_step(
    steps: &mut Vec<SmokeStep>,
    all_passed: &mut bool,
    id: &'static str,
    command: &'static str,
    verbose: bool,
    step: impl FnOnce() -> anyhow::Result<()>,
) {
    if !*all_passed {
        steps.push(SmokeStep {
            id,
            command,
            status: SmokeStepStatus::NotRun,
            detail: "not run: an earlier step failed (fail-closed)".to_owned(),
            duration_ms: 0,
        });
        return;
    }

    if verbose {
        println!("lake smoke step '{id}': {command}");
    }
    let start = Instant::now();
    let (status, detail) = match step() {
        Ok(()) => (SmokeStepStatus::Passed, "passed".to_owned()),
        Err(err) => {
            *all_passed = false;
            (SmokeStepStatus::Failed, format!("{err:#}"))
        }
    };
    steps.push(SmokeStep {
        id,
        command,
        status,
        detail,
        duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
    });
}

/// Write the artifact as pretty JSON (+ trailing newline, matching the other
/// generated `reports/` artifacts), creating the parent directory if needed.
fn write_report(report: &Path, artifact: &LakeSmokeArtifact) -> anyhow::Result<()> {
    if let Some(parent) = report.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).map_err(|err| {
                anyhow::anyhow!(
                    "could not create report directory {}: {err}",
                    parent.display()
                )
            })?;
        }
    }
    let rendered = serde_json::to_string_pretty(artifact)
        .map_err(|err| anyhow::anyhow!("could not serialize lake smoke artifact: {err}"))?
        + "\n";
    std::fs::write(report, rendered).map_err(|err| {
        anyhow::anyhow!(
            "could not write lake smoke artifact to {}: {err}",
            report.display()
        )
    })?;
    Ok(())
}

/// Best-effort `git rev-parse HEAD` so the artifact records which commit
/// generated it; `"unknown"` when git or the repo is unavailable (recorded
/// honestly, never fabricated).
fn head_commit() -> String {
    std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|stdout| stdout.trim().to_owned())
        .filter(|commit| !commit.is_empty())
        .unwrap_or_else(|| "unknown".to_owned())
}

/// Whether a `lean` binary is reachable on PATH (context evidence only; the
/// smoke's execution path never invokes it either way).
fn lean_binary_on_path() -> bool {
    let Some(path) = std::env::var_os("PATH") else {
        return false;
    };
    let file_name = if cfg!(windows) { "lean.exe" } else { "lean" };
    std::env::split_paths(&path).any(|dir| dir.join(file_name).is_file())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// End-to-end: the smoke runs the real in-process init/build/test sequence
    /// in a temp project and writes a schema-complete, non-stub artifact whose
    /// three steps all pass without any Lean4 delegation.
    #[test]
    fn lake_smoke_writes_schema_complete_passing_artifact() {
        let dir = tempfile::tempdir().expect("tempdir");
        let report = dir.path().join("lake-replacement-smoke.json");

        lake_smoke(&report, false).expect("smoke should pass on the clean lake init template");

        let raw = std::fs::read_to_string(&report).expect("smoke artifact should be written");
        let value: serde_json::Value =
            serde_json::from_str(&raw).expect("smoke artifact should be valid JSON");

        assert_eq!(
            value["schema_version"], LAKE_SMOKE_SCHEMA_VERSION,
            "artifact must carry the lake smoke schema version"
        );
        assert_eq!(value["replacement_row"]["id"], LAKE_SMOKE_ROW_ID);
        assert_eq!(value["replacement_row"]["issue"], LAKE_SMOKE_ROW_ISSUE);
        assert_eq!(
            value["replacement_row"]["recommended_scorecard_status"], "in_progress",
            "the smoke must not claim a green scorecard status on its own"
        );
        assert_eq!(value["status"], "passed");
        assert_eq!(value["passed"], true);
        assert!(
            value.get("stub").is_none(),
            "artifact must not be a stub placeholder"
        );

        let steps = value["steps"].as_array().expect("steps array");
        let ids: Vec<&str> = steps
            .iter()
            .map(|step| step["id"].as_str().expect("step id"))
            .collect();
        assert_eq!(
            ids,
            ["init", "build", "test"],
            "steps must cover the row's gate sequence"
        );
        for step in steps {
            assert_eq!(
                step["status"], "passed",
                "step {} should pass: {}",
                step["id"], step["detail"]
            );
            assert!(
                step["command"]
                    .as_str()
                    .expect("step command")
                    .starts_with("clean lake "),
                "each step must record its clean-owned reproducing command"
            );
        }

        assert_eq!(
            value["no_lean4_delegation"]["source_gate"],
            "crates/clean-cli/tests/lake_replacement_delegation.rs",
            "artifact must cite the source-level no-delegation gate"
        );
        assert!(
            !value["non_claims"]
                .as_array()
                .expect("non_claims array")
                .is_empty(),
            "artifact must record explicit non-claims"
        );
        assert!(
            value["generated_at_commit"].as_str().is_some(),
            "artifact must record the generating commit (or explicit unknown)"
        );
    }

    /// Fail-closed step accounting: after a failure, later steps are recorded
    /// as `not_run` rather than executed, and the failure flips the verdict.
    #[test]
    fn run_step_marks_later_steps_not_run_after_a_failure() {
        let mut steps = Vec::new();
        let mut all_passed = true;

        run_step(
            &mut steps,
            &mut all_passed,
            "init",
            "clean lake init x",
            false,
            || anyhow::bail!("boom"),
        );
        let mut executed_after_failure = false;
        run_step(
            &mut steps,
            &mut all_passed,
            "build",
            "clean lake build",
            false,
            || {
                executed_after_failure = true;
                Ok(())
            },
        );

        assert!(!all_passed, "a failed step must flip the overall verdict");
        assert!(
            !executed_after_failure,
            "steps after a failure must not execute"
        );
        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].status, SmokeStepStatus::Failed);
        assert!(steps[0].detail.contains("boom"));
        assert_eq!(steps[1].status, SmokeStepStatus::NotRun);
    }
}
