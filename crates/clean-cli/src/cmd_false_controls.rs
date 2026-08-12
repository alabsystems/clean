// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean false-controls` release-gate commands.
//!
//! The user-facing entry point for the false-control probe engine in
//! `clean_mathverse::false_control_suite`. Each probe feeds a backend an input
//! that is *known to be wrong* — a negative Farkas multiplier, a branch cover
//! with a hole, a swapped LLVM2 denotation, a direct proof of `False`, an
//! invalid QBF strategy — so the only healthy outcome is rejection.
//!
//! Fail-closed by construction, and the polarity matters: a control that
//! "passes" (its known-bad input was accepted) is a soundness alarm, not a
//! green test. `false-controls run` therefore exits NON-ZERO unless *every*
//! required control rejected its bad input exactly once. Pending and
//! probe-error rows block too — an unrun control is not evidence that bad input
//! would have been rejected.

use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::bail;
use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_mathverse::attempt_log::{
    prepare_replay_attempt, read_artifact, AttemptId, AttemptStatus, AuthorityReceipt,
    ReplayOptions, ReplayPlan,
};
use clean_mathverse::false_control_suite::{
    record_false_control_authority_gate_attempt, run_false_control_suite,
    validate_false_control_report_artifact, FalseControlReplaySummary, FalseControlReport,
    FalseControlStatus, FALSE_CONTROL_AUTHORITY_GATE, FALSE_CONTROL_REPORT_ARTIFACT_KIND,
    FALSE_CONTROL_REPORT_ARTIFACT_LOGICAL_NAME,
};
use serde::Serialize;

use crate::authority_source_guard::AuthoritySourceGuard;

/// The `clean-mathverse` crate owns the probe engine this surface drives.
/// `RefKind::Crate` (not `Doc`) because the authoritative description of the
/// contract is the module documentation on
/// `clean_mathverse::false_control_suite`, not a standalone markdown page.
const FALSE_CONTROL_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-mathverse (false-control probe engine)",
    target: "clean-mathverse",
};

pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["false-controls", "run"],
        summary: "Run known-bad proof false-control probes",
        description: "\
Runs the false-control suite: five probes that feed known-bad proof, solver, \
and translation inputs to their verifiers, where the only healthy outcome is \
rejection. A control whose bad input was accepted is a soundness alarm, so the \
command exits non-zero unless every required control rejected exactly once; \
pending-backend and probe-error rows block as well, because an unrun control \
is not evidence of rejection. `--record-attempt --root <project>` appends the \
run as a `false_controls` authority-gate proof attempt under \
`.mathverse/attempts` and refuses to record from a dirty git worktree. \
`--json` emits the structured report plus the authority receipt.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean false-controls run --json",
                what: "run the suite and emit the structured report",
            },
            Example {
                cmd: "clean false-controls run --record-attempt --root . --json",
                what: "run the suite and record the authority-gate result",
            },
        ],
        see_also: &["false-controls replay-attempt", "attempts list"],
        references: &[FALSE_CONTROL_CRATE_REF],
        domain_root: Some("false-controls"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["false-controls", "replay-attempt"],
        summary: "Validate a logged false-control gate attempt",
        description: "\
Checks that one persisted `.mathverse` proof attempt can serve as replayable \
false-control gate evidence. The stored report artifact is re-read, its \
content hash re-verified, and its summary recomputed from the control rows \
rather than believed; the recomputed verdict must match the attempt's status \
and failure mode or the command fails closed. `--allow-mismatch` permits \
validation under a different live environment and requires a non-empty \
`--mismatch-explanation`.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean false-controls replay-attempt attempt-1 --json",
                what: "validate one logged false-control attempt",
            },
            Example {
                cmd: "clean false-controls replay-attempt attempt-1 --root . --allow-mismatch --mismatch-explanation reviewed-host-change",
                what: "validate a logged attempt captured on a different host",
            },
        ],
        see_also: &["false-controls run", "attempts list"],
        references: &[FALSE_CONTROL_CRATE_REF],
        domain_root: Some("false-controls"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// False-control suite subcommands.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum FalseControlCommands {
    /// Run the aggregated false-control rejection suite.
    Run {
        /// Emit JSON instead of a human-readable table.
        #[arg(long)]
        json: bool,
        /// Append this run as a false-controls authority-gate attempt.
        #[arg(long)]
        record_attempt: bool,
        /// Repository or project root containing the `.mathverse` attempt log.
        #[arg(long, default_value = ".")]
        root: PathBuf,
    },
    /// Validate that one logged Mathverse attempt is replayable as gate evidence.
    ReplayAttempt {
        /// Attempt id from `.mathverse/attempts/*.jsonl`.
        attempt_id: String,
        /// Repository or project root containing the `.mathverse` attempt log.
        #[arg(long, default_value = ".")]
        root: PathBuf,
        /// Permit replay validation when the live environment differs.
        #[arg(long)]
        allow_mismatch: bool,
        /// Required explanation when `--allow-mismatch` is used and the environment differs.
        #[arg(long)]
        mismatch_explanation: Option<String>,
        /// Emit JSON instead of a human-readable report.
        #[arg(long)]
        json: bool,
    },
}

/// Dispatch entry point for `clean false-controls`.
pub(crate) fn handle_false_control_command(command: FalseControlCommands) -> anyhow::Result<()> {
    match command {
        FalseControlCommands::Run {
            json,
            record_attempt,
            root,
        } => run(json, record_attempt, &root),
        FalseControlCommands::ReplayAttempt {
            attempt_id,
            root,
            allow_mismatch,
            mismatch_explanation,
            json,
        } => replay_attempt(
            &root,
            AttemptId::from(attempt_id),
            ReplayOptions {
                allow_mismatch,
                mismatch_explanation,
            },
            json,
        ),
    }
}

fn run(json: bool, record_attempt: bool, root: &Path) -> anyhow::Result<()> {
    let started = Instant::now();
    let source_guard = if record_attempt {
        Some(AuthoritySourceGuard::capture_clean(
            root,
            "clean false-controls run --record-attempt",
        )?)
    } else {
        None
    };
    let report = run_false_control_suite();
    let wall_time_ms = elapsed_millis_saturating(started);
    let authority_receipt = if record_attempt {
        if let Some(source_guard) = source_guard.as_ref() {
            source_guard.ensure_unchanged("authority evidence write")?;
        }
        let attempt = record_false_control_authority_gate_attempt(root, &report, wall_time_ms)?;
        Some(AuthorityReceipt::from_attempt(&attempt))
    } else {
        None
    };

    if json {
        print_run_json(&report, authority_receipt.as_ref())?;
    } else {
        print_human_report(&report, authority_receipt.as_ref());
    }
    // Report first, then fail: the operator (and any recorded evidence) sees
    // exactly which lane failed to reject before the process exits non-zero.
    ensure_false_control_report_is_release_ready(&report)
}

fn elapsed_millis_saturating(started: Instant) -> u64 {
    started.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

/// Fail-closed exit-code path for `clean false-controls run`.
///
/// The probes are deliberately-wrong inputs the verifiers MUST reject, so a
/// control that did not reject means something false was accepted (or was never
/// tested). Never relax this into a warning: it is the only signal separating
/// "the verifier refused a falsehood" from "the verifier believed one".
fn ensure_false_control_report_is_release_ready(report: &FalseControlReport) -> anyhow::Result<()> {
    if report.all_controls_rejected() {
        return Ok(());
    }

    let summary = report.replay_summary();
    let non_rejected = summary.non_rejected_control_ids.join(", ");
    bail!(
        "false-control suite is not release-ready: {}/{} rejected, {} pending, {} accepted_bad_input, {} probe_errors; non_rejected=[{}]",
        summary.rejected,
        summary.total,
        summary.pending,
        summary.accepted_bad_input,
        summary.probe_errors,
        non_rejected
    );
}

fn replay_attempt(
    root: &Path,
    attempt_id: AttemptId,
    options: ReplayOptions,
    json: bool,
) -> anyhow::Result<()> {
    let report = validate_replay_attempt_with_options(root, attempt_id, options)?;
    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_replay_validation_report(&report);
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct FalseControlReplayValidationReport {
    schema_version: &'static str,
    attempt_id: String,
    root: String,
    replay_ready: bool,
    summary: FalseControlReplaySummary,
    plan: ReplayPlan,
}

fn validate_replay_attempt_with_options(
    root: &Path,
    attempt_id: AttemptId,
    options: ReplayOptions,
) -> anyhow::Result<FalseControlReplayValidationReport> {
    let plan = prepare_replay_attempt(root, &attempt_id, options)?;
    if plan.original.authority_gate.as_deref() != Some(FALSE_CONTROL_AUTHORITY_GATE) {
        bail!("attempt `{attempt_id}` is not a false-controls authority-gate attempt");
    }
    let artifact = plan.original.solver_artifact.as_ref().ok_or_else(|| {
        anyhow::anyhow!("attempt `{attempt_id}` is missing false-control report artifact")
    })?;
    if artifact.kind.as_deref() != Some(FALSE_CONTROL_REPORT_ARTIFACT_KIND)
        || artifact.logical_name.as_deref() != Some(FALSE_CONTROL_REPORT_ARTIFACT_LOGICAL_NAME)
    {
        bail!("attempt `{attempt_id}` does not reference a false-control report artifact");
    }
    let artifact_bytes = read_artifact(root, artifact)?;
    let artifact_validation = validate_false_control_report_artifact(&artifact_bytes)?;
    validate_attempt_status_matches_report(
        &attempt_id,
        &plan.original.status,
        plan.original.failure_mode.as_deref(),
        &artifact_validation.summary,
        artifact_validation.expected_failure_mode.as_deref(),
    )?;
    Ok(FalseControlReplayValidationReport {
        schema_version: "Clean-false-control-replay-validation-v1",
        attempt_id: attempt_id.to_string(),
        root: root.display().to_string(),
        replay_ready: artifact_validation.summary.replay_ready,
        summary: artifact_validation.summary,
        plan,
    })
}

/// Cross-check the recomputed report summary against the attempt's own status.
///
/// An attempt that claims `accepted` while its artifact's rows recompute to a
/// non-replay-ready summary is exactly the tampering this validation exists to
/// catch, so the mismatch is an error rather than a preference for either side.
fn validate_attempt_status_matches_report(
    attempt_id: &AttemptId,
    status: &AttemptStatus,
    failure_mode: Option<&str>,
    summary: &FalseControlReplaySummary,
    expected_failure_mode: Option<&str>,
) -> anyhow::Result<()> {
    match (summary.replay_ready, status) {
        (true, AttemptStatus::Accepted) if failure_mode.is_none() => Ok(()),
        (false, AttemptStatus::Rejected { .. }) if failure_mode == expected_failure_mode => Ok(()),
        _ => {
            let expected = if summary.replay_ready {
                "accepted with no failure_mode".to_owned()
            } else {
                format!(
                    "rejected with failure_mode={}",
                    expected_failure_mode.unwrap_or("none")
                )
            };
            bail!(
                "false-control report summary does not match attempt `{attempt_id}` status/failure_mode; expected {expected}"
            )
        }
    }
}

fn print_run_json(
    report: &FalseControlReport,
    authority_receipt: Option<&AuthorityReceipt>,
) -> anyhow::Result<()> {
    let mut value = serde_json::to_value(report)?;
    value["authority_receipt"] = match authority_receipt {
        Some(receipt) => serde_json::to_value(receipt)?,
        None => serde_json::Value::Null,
    };
    println!("{}", serde_json::to_string_pretty(&value)?);
    Ok(())
}

fn print_human_report(report: &FalseControlReport, authority_receipt: Option<&AuthorityReceipt>) {
    println!("False-control suite:");
    for control in &report.controls {
        let status = match control.status {
            FalseControlStatus::Rejected => "REJECTED",
            FalseControlStatus::AcceptedBadInput => "ACCEPTED_BAD_INPUT",
            FalseControlStatus::PendingBackend => "PENDING_BACKEND",
            FalseControlStatus::ProbeError => "PROBE_ERROR",
        };
        println!("  {status:20} {}", control.label);
        println!("    {}", control.detail);
        if let Some(todo) = control.todo {
            println!("    TODO: {todo}");
        }
    }
    if let Some(receipt) = authority_receipt {
        println!("  attempt_id: {}", receipt.attempt_id);
        if let Some(artifact) = &receipt.solver_artifact {
            println!("  solver_artifact: {}", artifact.blake3);
        }
    }
}

fn print_replay_validation_report(report: &FalseControlReplayValidationReport) {
    let original = &report.plan.original;
    println!("False-control replay validation:");
    println!("  attempt_id: {}", report.attempt_id);
    println!("  root: {}", report.root);
    println!("  status: {}", attempt_status_label(&original.status));
    println!("  env_matches: {}", report.plan.env_matches);
    println!("  artifact_refs: {}", original.artifact_refs().len());
    println!(
        "  summary: {}/{} rejected, {} pending, {} accepted_bad_input, {} probe_errors",
        report.summary.rejected,
        report.summary.total,
        report.summary.pending,
        report.summary.accepted_bad_input,
        report.summary.probe_errors
    );
    if let Some(explanation) = &report.plan.mismatch_explanation {
        println!("  mismatch_explanation: {explanation}");
    }
    println!("  replay_ready: {}", report.replay_ready);
}

fn attempt_status_label(status: &AttemptStatus) -> &'static str {
    match status {
        AttemptStatus::Accepted => "accepted",
        AttemptStatus::Rejected { .. } => "rejected",
        AttemptStatus::Timeout { .. } => "timeout",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::process::Command;

    use clean_mathverse::attempt_log::{
        append_to, artifact_path, iter_from, AttemptFilter, AttemptStatusFilter, ProofAttempt,
    };
    use clean_mathverse::false_control_suite::{FalseControlId, FalseControlResult};

    fn git(args: &[&str], root: &Path) {
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(args)
            .output()
            .expect("run git");
        assert!(
            output.status.success(),
            "git {:?} failed: {}",
            args,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn complete_rejected_controls() -> Vec<FalseControlResult> {
        vec![
            FalseControlResult {
                id: FalseControlId::InvalidFarkasMultiplier,
                label: "invalid Farkas multiplier",
                status: FalseControlStatus::Rejected,
                detail: "rejected".to_owned(),
                todo: None,
            },
            FalseControlResult {
                id: FalseControlId::BrokenBranchCover,
                label: "broken branch cover",
                status: FalseControlStatus::Rejected,
                detail: "rejected".to_owned(),
                todo: None,
            },
            FalseControlResult {
                id: FalseControlId::ChangedLlvm2Denotation,
                label: "changed LLVM2 denotation",
                status: FalseControlStatus::Rejected,
                detail: "rejected".to_owned(),
                todo: None,
            },
            FalseControlResult {
                id: FalseControlId::DirectFalseProof,
                label: "direct proof of False",
                status: FalseControlStatus::Rejected,
                detail: "rejected".to_owned(),
                todo: None,
            },
            FalseControlResult {
                id: FalseControlId::InvalidQbfStrategy,
                label: "invalid QBF strategy",
                status: FalseControlStatus::Rejected,
                detail: "rejected".to_owned(),
                todo: None,
            },
        ]
    }

    fn accepted_report() -> FalseControlReport {
        FalseControlReport {
            controls: complete_rejected_controls(),
        }
    }

    fn rejected_report() -> FalseControlReport {
        let mut controls = complete_rejected_controls();
        controls[2] = FalseControlResult {
            id: FalseControlId::ChangedLlvm2Denotation,
            label: "changed LLVM2 denotation",
            status: FalseControlStatus::AcceptedBadInput,
            detail: "swapped denotation was accepted".to_owned(),
            todo: None,
        };
        FalseControlReport { controls }
    }

    fn record_report_attempt(root: &Path, report: &FalseControlReport) -> ProofAttempt {
        record_false_control_authority_gate_attempt(root, report, 17)
            .expect("record false-control gate")
    }

    #[test]
    fn replay_attempt_validation_accepts_accepted_report_replay() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let attempt = record_report_attempt(root, &accepted_report());
        let attempt_id = attempt.attempt_id.clone();

        let report = validate_replay_attempt_with_options(
            root,
            attempt_id.clone(),
            ReplayOptions::default(),
        )
        .expect("validate replay attempt");

        assert_eq!(report.attempt_id, attempt_id.to_string());
        assert!(report.replay_ready);
        assert_eq!(report.summary.total, 5);
        assert_eq!(report.summary.rejected, 5);
        assert!(report.plan.env_matches);
        assert_eq!(report.plan.original.attempt_id, attempt_id);
        // Two artifacts for a fully-green run: the false-control report itself
        // plus the command-evidence artifact the engine attaches only when
        // every control rejected (see `false_control_command_evidence`).
        assert_eq!(report.plan.original.artifact_refs().len(), 2);
        assert!(report.plan.original.command_evidence.is_some());
    }

    #[test]
    fn replay_attempt_validation_accepts_rejected_report_replay() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let attempt = record_report_attempt(root, &rejected_report());
        let attempt_id = attempt.attempt_id.clone();

        let report = validate_replay_attempt_with_options(
            root,
            attempt_id.clone(),
            ReplayOptions::default(),
        )
        .expect("validate rejected report replay");

        assert_eq!(report.attempt_id, attempt_id.to_string());
        assert!(!report.replay_ready);
        assert_eq!(report.summary.accepted_bad_input, 1);
        assert_eq!(
            report.plan.original.failure_mode.as_deref(),
            Some("false_control_accepted_bad_input")
        );
    }

    #[test]
    fn run_records_false_control_authority_gate_attempt_when_requested() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        run(true, true, root).expect("run and record false-control authority gate");

        let attempts: Vec<_> = iter_from(
            root,
            AttemptFilter {
                authority_gate: Some(FALSE_CONTROL_AUTHORITY_GATE.to_owned()),
                status: Some(AttemptStatusFilter::Accepted),
                ..AttemptFilter::default()
            },
        )
        .expect("query recorded false-control attempt")
        .collect();

        assert_eq!(attempts.len(), 1);
        assert_eq!(
            attempts[0].authority_gate.as_deref(),
            Some(FALSE_CONTROL_AUTHORITY_GATE)
        );
        assert!(matches!(attempts[0].status, AttemptStatus::Accepted));
        assert!(attempts[0].solver_artifact.is_some());

        let receipt = AuthorityReceipt::from_attempt(&attempts[0]);
        let json = serde_json::to_value(&receipt).expect("receipt serializes");
        assert!(json["attempt_id"].as_str().is_some());
        assert_eq!(json["authority_gate"], FALSE_CONTROL_AUTHORITY_GATE);
        assert_eq!(json["status"], "accepted");
        assert!(json["goal_hash"].as_str().is_some());
        assert!(json["trust_audit_hash"].as_str().is_some());
        assert_eq!(json["solver_artifact"]["blake3"], json["trust_audit_hash"]);
    }

    #[test]
    fn run_record_attempt_rejects_dirty_git_source_root() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        git(&["init"], root);
        git(&["config", "user.email", "clean@example.invalid"], root);
        git(&["config", "user.name", "Clean Test"], root);
        fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.0.0\n")
            .expect("write toolchain");
        git(&["add", "lean-toolchain"], root);
        git(&["commit", "-m", "initial"], root);
        fs::write(root.join("dirty.lean"), "-- dirty\n").expect("write dirty file");

        let err = run(true, true, root).expect_err("dirty source must block recording");
        assert!(err.to_string().contains("dirty git worktree"));
    }

    #[test]
    fn replay_attempt_validation_rejects_tampered_or_missing_artifact() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let attempt = record_report_attempt(root, &accepted_report());
        let attempt_id = attempt.attempt_id.clone();
        let artifact = attempt
            .solver_artifact
            .as_ref()
            .expect("false-control report artifact");
        fs::write(artifact_path(root, artifact), b"{}").expect("tamper artifact");

        let err = validate_replay_attempt_with_options(root, attempt_id, ReplayOptions::default())
            .expect_err("tampered false-control report artifact should fail closed");
        assert!(err.to_string().contains("artifact hash mismatch"));

        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let attempt = record_report_attempt(root, &accepted_report());
        let attempt_id = attempt.attempt_id.clone();
        let artifact = attempt
            .solver_artifact
            .as_ref()
            .expect("false-control report artifact");
        fs::remove_file(artifact_path(root, artifact)).expect("remove artifact");

        validate_replay_attempt_with_options(root, attempt_id, ReplayOptions::default())
            .expect_err("missing false-control report artifact should fail closed");
    }

    #[test]
    fn replay_attempt_validation_rejects_status_mismatch() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let mut attempt = record_report_attempt(root, &rejected_report());
        attempt.attempt_id = AttemptId::from("status-mismatch");
        attempt.status = AttemptStatus::Accepted;
        attempt.failure_mode = None;
        let attempt_id = attempt.attempt_id.clone();
        append_to(root, &attempt).expect("append mismatched attempt");

        let err = validate_replay_attempt_with_options(root, attempt_id, ReplayOptions::default())
            .expect_err("accepted attempt with rejected report summary should fail closed");
        assert!(err.to_string().contains("summary does not match attempt"));
    }

    #[test]
    fn replay_attempt_validation_requires_mismatch_explanation() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let mut attempt = record_report_attempt(root, &accepted_report());
        attempt.attempt_id = AttemptId::from("env-mismatch");
        attempt.env.host_arch = "different-arch".to_owned();
        let attempt_id = attempt.attempt_id.clone();
        append_to(root, &attempt).expect("append attempt");

        let err = validate_replay_attempt_with_options(
            root,
            attempt_id.clone(),
            ReplayOptions {
                allow_mismatch: true,
                mismatch_explanation: None,
            },
        )
        .expect_err("mismatch without explanation should fail closed");
        assert!(err.to_string().contains("non-empty explanation"));

        let report = validate_replay_attempt_with_options(
            root,
            attempt_id,
            ReplayOptions {
                allow_mismatch: true,
                mismatch_explanation: Some("false-control regression replay".to_owned()),
            },
        )
        .expect("validate mismatch with explanation");
        assert!(!report.plan.env_matches);
        assert_eq!(
            report.plan.mismatch_explanation.as_deref(),
            Some("false-control regression replay")
        );
    }

    #[test]
    fn run_gate_blocks_pending_and_accepted_bad_input_controls() {
        let report = FalseControlReport {
            controls: vec![
                FalseControlResult {
                    id: FalseControlId::InvalidFarkasMultiplier,
                    label: "invalid Farkas multiplier",
                    status: FalseControlStatus::Rejected,
                    detail: "rejected".to_owned(),
                    todo: None,
                },
                FalseControlResult {
                    id: FalseControlId::BrokenBranchCover,
                    label: "broken branch cover",
                    status: FalseControlStatus::PendingBackend,
                    detail: "branch-cover verifier not wired".to_owned(),
                    todo: Some("wire branch-cover verifier"),
                },
                FalseControlResult {
                    id: FalseControlId::ChangedLlvm2Denotation,
                    label: "changed LLVM2 denotation",
                    status: FalseControlStatus::AcceptedBadInput,
                    detail: "swapped denotation was accepted".to_owned(),
                    todo: None,
                },
            ],
        };

        let err = ensure_false_control_report_is_release_ready(&report)
            .expect_err("pending or accepted-bad-input controls must block the run gate");
        let message = err.to_string();

        assert!(message.contains("1/3 rejected"));
        assert!(message.contains("1 pending"));
        assert!(message.contains("1 accepted_bad_input"));
        assert!(message.contains("broken_branch_cover"));
        assert!(message.contains("changed_llvm2_denotation"));
    }

    /// The live suite must be fully green: five probes, all rejecting. If this
    /// ever fails, a verifier accepted a deliberately-false input — treat it as
    /// a soundness alarm, not a flaky test.
    #[test]
    fn live_suite_rejects_every_known_bad_input() {
        let report = run_false_control_suite();

        assert_eq!(report.controls.len(), 5, "{:?}", report.controls);
        ensure_false_control_report_is_release_ready(&report)
            .expect("every false-control probe must reject its known-bad input");
    }
}
