// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 8) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn trust_core_evidence_reads_current_artifacts() {
    let Ok(report) = TrustCoreEvidenceReport::current() else {
        eprintln!("SKIP: trust-core evidence report artifacts not present");
        return;
    };
    let ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet");
    let axiom_audit = load_axiom_audit().expect("axiom audit artifact");

    assert!(!report.launch_ready);
    assert_eq!(report.overall_status, "pending_evidence");
    assert_eq!(report.kernel_differential.baseline_schema_version, 1);
    assert_eq!(report.kernel_differential.normalization_version, 2);
    assert_eq!(report.kernel_differential.baseline_cases, 2001);
    assert_eq!(report.kernel_differential.expression_count, 2001);
    assert!(report.kernel_differential.expressions_sha256_match);
    assert_eq!(
        report.kernel_differential.gate_command,
        KERNEL_SOUNDNESS_RUST_GATE_COMMAND
    );
    assert!(report.kernel_differential.gate_preflight_required);
    assert!(report
        .kernel_differential
        .gate_preflight_artifacts
        .contains(&TRUST_CORE_RUST_SOURCE_PATH));
    assert!(report
        .kernel_differential
        .gate_preflight_guards
        .contains(&"expressions_sha256 matches expressions.txt"));
    assert_eq!(
        report
            .fallback_denial
            .unchecked_decl_ratchet
            .add_decl_structural_count,
        ratchet.add_decl_structural_count
    );
    assert_eq!(
        report
            .fallback_denial
            .unchecked_decl_ratchet
            .add_decl_unchecked_count,
        ratchet.add_decl_unchecked_count
    );
    assert_eq!(
        report.fallback_denial.launch_evidence_path,
        DENY_SORRY_LAUNCH_EVIDENCE_PATH
    );
    assert!(matches!(
        report.fallback_denial.launch_evidence_status.as_str(),
        "passed" | "missing" | "stale"
    ));
    assert!(report
        .fallback_denial
        .launch_evidence_summary
        .contains(DENY_SORRY_LAUNCH_EVIDENCE_PATH));
    assert!(report
        .source_artifacts
        .contains(&UNCHECKED_DECL_RATCHET_PATH));
    assert!(report
        .source_artifacts
        .contains(&TRUST_CORE_RUST_SOURCE_PATH));
    assert!(report
        .source_artifacts
        .contains(&AXIOM_AUDIT_RUST_SOURCE_PATH));
    assert!(!report
        .source_artifacts
        .contains(&AXIOM_AUDIT_RELEASE_CHECK_PATH));
    assert!(report
        .source_artifacts
        .contains(&VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH));
    assert!(report
        .source_artifacts
        .contains(&PROOF_SYSTEM_CERTIFICATION_BLOCKER_REPORT_PATH));
    assert_eq!(report.zero_trust_gates.len(), 3);
    let gates_passed = report
        .zero_trust_gates
        .iter()
        .filter(|gate| gate.required_for_launch)
        .all(|gate| gate.status == ZeroTrustGateStatus::Passed);
    assert_eq!(
        report.proof_system_certification.zero_trust_gates_passed,
        gates_passed
    );
    // Never Green while any verification-audit lane or replay row blocks;
    // InProgress vs Blocked tracks the zero-trust gates.
    assert_eq!(
        report.proof_system_certification.status,
        if report.proof_system_certification.zero_trust_gates_passed
            && report
                .proof_system_certification
                .blocking_verification_audit_lanes
                == 0
            && report
                .proof_system_certification
                .blocking_replay_parity_rows
                == 0
        {
            ReplacementStatus::Green
        } else if report.proof_system_certification.zero_trust_gates_passed {
            ReplacementStatus::InProgress
        } else {
            ReplacementStatus::Blocked
        }
    );
    assert!(
        report
            .proof_system_certification
            .blocking_verification_audit_lanes
            >= 1,
        "verification-audit lanes should block until certification closes"
    );
    assert!(
        report
            .proof_system_certification
            .blocking_replay_parity_rows
            >= 1,
        "replay parity rows should block until replay lanes are Green"
    );
    assert!(report
        .proof_system_certification
        .replay_parity_rows
        .iter()
        .any(|row| row.row_id == "mathverse-replay" && row.blocks_certification));
    assert_eq!(
        report.axiom_audit.total_domain_axioms,
        axiom_audit.total_domain_axioms
    );
    assert_eq!(
        report.axiom_audit.total_all_axioms,
        axiom_audit.total_all_axioms
    );
    assert_eq!(
        report.axiom_audit.conjecture_rows,
        axiom_audit.conjectures.len()
    );
    let expected_nonzero_axiom_rows = axiom_audit
        .conjectures
        .values()
        .filter(|row| row.axioms > 0)
        .count();
    assert_eq!(
        report.axiom_audit.nonzero_axiom_rows,
        expected_nonzero_axiom_rows
    );
    assert!(report
        .axiom_audit
        .proof_mechanism_counts
        .contains_key("masquerade_demoted"));
}

#[test]
fn trust_core_evidence_rejects_stale_expression_count() {
    let baseline = Lean4BaselineArtifact {
        schema_version: 1,
        lean4_version: "test".to_string(),
        expressions_sha256: "abc".to_string(),
        normalization_version: 2,
        cases: vec![serde_json::json!({})],
    };

    let err = validate_kernel_differential_artifacts(&baseline, 2, "abc")
        .expect_err("stale expression count should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err.to_string().contains("has 1 cases"));
    assert!(err.to_string().contains("has 2 active expressions"));
}

#[test]
fn trust_core_evidence_rejects_stale_expression_hash() {
    let baseline = Lean4BaselineArtifact {
        schema_version: 1,
        lean4_version: "test".to_string(),
        expressions_sha256: "expected".to_string(),
        normalization_version: 2,
        cases: vec![serde_json::json!({})],
    };

    let err = validate_kernel_differential_artifacts(&baseline, 1, "actual")
        .expect_err("stale expression hash should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("expects expressions_sha256=expected"));
    assert!(err.to_string().contains("hashes to actual"));
}

#[test]
fn trust_core_evidence_rejects_kernel_gate_without_preflight_marker() {
    let source = KERNEL_GATE_PREFLIGHT_MARKERS
        .iter()
        .copied()
        .filter(|marker| *marker != "unset REGEN_BASELINE")
        .collect::<Vec<_>>()
        .join("\n");

    let err = validate_kernel_soundness_gate_preflight_source(&source)
        .expect_err("missing kernel gate preflight marker should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("missing hardened differential preflight marker `unset REGEN_BASELINE`"));
}

#[test]
fn kernel_soundness_launch_evidence_accepts_strict_current_artifact() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);

    validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect("current strict kernel soundness artifact should validate");
}

/// Canned libtest output for the parity lane, shaped like a real passing run.
const PARITY_LANE_PASSING_OUTPUT: &str = "running 1 test\n\
     test lean4_parity_check ... ok\n\n\
     test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n";
/// The elaborator gate logs its marker to stderr; the runner merges streams.
const ELAB_LANE_PASSING_OUTPUT: &str = " INFO soundness_gate: running reject lane\n\
     INFO soundness_gate: PASS\n";

fn passing_lane_runner(argv: &[&'static str]) -> Result<String, String> {
    if argv == KERNEL_LEAN4_PARITY_LANE_COMMAND {
        Ok(PARITY_LANE_PASSING_OUTPUT.to_string())
    } else if argv == ELAB_SOUNDNESS_GATE_LANE_COMMAND {
        Ok(ELAB_LANE_PASSING_OUTPUT.to_string())
    } else {
        Err(format!("unexpected lane command: {argv:?}"))
    }
}

#[test]
fn rust_kernel_soundness_generator_emits_strict_current_artifact() {
    let artifact = generate_kernel_soundness_launch_evidence_with(
        "2026-04-27T00:00:00Z",
        &passing_lane_runner,
    )
    .expect("kernel soundness artifact");

    assert_eq!(artifact.generated_by, KERNEL_SOUNDNESS_RUST_GATE_COMMAND);
    assert_eq!(artifact.gate_command, KERNEL_SOUNDNESS_RUST_GATE_COMMAND);
    assert!(artifact
        .source_sha256
        .contains_key(TRUST_CORE_RUST_SOURCE_PATH));
    assert!(!artifact
        .source_sha256
        .contains_key(KERNEL_SOUNDNESS_GATE_PATH));
    assert_eq!(artifact.lanes.len(), KERNEL_SOUNDNESS_EXPECTED_LANES.len());
    assert!(artifact.lanes.iter().all(|lane| lane.status == "passed"
        && lane.matched_expected_count
        && lane.matched_expected_output));
}

/// No row may be Green while the zero-trust gate that backs it is not passed.
#[test]
fn informational_row_cannot_outrank_its_own_zero_trust_gate() {
    let scorecard = InformationalScorecard::current();
    let backed: Vec<_> = scorecard
        .rows
        .iter()
        .filter(|row| row.zero_trust_gate.is_some())
        .collect();
    assert!(
        !backed.is_empty(),
        "expected at least one gate-backed row (kernel-differential, fallback-denial)"
    );

    for row in backed {
        match row.zero_trust_gate_status {
            // Unknown verdict: the trust-core report could not be built, which
            // this never-fail-closed view tolerates.
            None => {}
            Some(ZeroTrustGateStatus::Passed) => {}
            Some(_) => assert_ne!(
                row.effective_status,
                ReplacementStatus::Green,
                "row {} is Green while its gate {:?} reports {:?}",
                row.id,
                row.zero_trust_gate,
                row.zero_trust_gate_status
            ),
        }
    }
}

#[test]
fn gate_verdict_reconciliation_only_ever_downgrades() {
    use ReplacementStatus::{Blocked, Green, PendingEvidence};

    // An unknown or passing gate leaves the row alone.
    assert_eq!(reconcile_with_gate_verdict(Green, None), Green);
    assert_eq!(
        reconcile_with_gate_verdict(Green, Some(ZeroTrustGateStatus::Passed)),
        Green
    );
    // A red gate overrides a Green row -- the defect this fixes.
    assert_eq!(
        reconcile_with_gate_verdict(Green, Some(ZeroTrustGateStatus::Blocked)),
        Blocked
    );
    assert_eq!(
        reconcile_with_gate_verdict(Green, Some(ZeroTrustGateStatus::PendingEvidence)),
        PendingEvidence
    );
    // Never upgrades: a Blocked row stays Blocked under a weaker gate verdict.
    assert_eq!(
        reconcile_with_gate_verdict(Blocked, Some(ZeroTrustGateStatus::PendingEvidence)),
        Blocked
    );
}

/// A gate that reports `launch_ready: false` and exits 0 is not a gate --
/// `clean replacement status && echo READY` would print READY.
#[test]
fn fail_closed_status_exits_nonzero_while_launch_is_not_ready() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status artifacts not present");
        return;
    };

    let result = run_status(ReplacementStatusArgs {
        json: true,
        informational: false,
    });

    if report.launch_ready {
        assert!(
            result.is_ok(),
            "a ready gate must exit 0, got {:?}",
            result.err()
        );
        return;
    }

    let err = result.expect_err("a gate reporting launch_ready=false must not exit 0");
    assert!(
        matches!(err, ReplacementError::LaunchNotReady { .. }),
        "unexpected error: {err}"
    );
    // The error must name what is blocking, not just that something is.
    let rendered = err.to_string();
    for row in report
        .rows
        .iter()
        .filter(|row| row.effective_status != ReplacementStatus::Green)
    {
        assert!(
            rendered.contains(row.id),
            "blocking row {} missing from the error: {rendered}",
            row.id
        );
    }
}

/// The informational survey is explicitly the never-fail-closed view; scripts
/// and agents rely on it exiting 0 regardless of gate state.
#[test]
fn informational_status_stays_exit_zero_when_launch_is_not_ready() {
    if ReplacementStatusReport::current().is_err() {
        eprintln!("SKIP: replacement status artifacts not present");
        return;
    }

    run_status(ReplacementStatusArgs {
        json: true,
        informational: true,
    })
    .expect("informational status must never fail closed");
}

/// Launch evidence must not be writable by a binary built at another commit.
/// This is the exact failure that let an 11-day-stale binary "measure HEAD".
#[test]
fn build_provenance_accepts_only_a_binary_built_at_head() {
    let sha = "3a1d13dd5cba99cfd097654520e0642c927e49fb";
    build_provenance_verdict(Some(sha), Some(sha)).expect("matching commit must pass");

    let err = build_provenance_verdict(Some(sha), Some("7ab1c4caa32a36ad09cb0c032cacea6913ab5c3d"))
        .expect_err("a binary built at a different commit must refuse");
    assert!(err.contains("built at"), "unexpected: {err}");
    assert!(err.contains("but HEAD is"), "unexpected: {err}");
}

/// Every uncertain case fails closed rather than assuming the binary is fresh.
#[test]
fn build_provenance_fails_closed_on_unknown_inputs() {
    let sha = "3a1d13dd5cba99cfd097654520e0642c927e49fb";
    // No build stamp at all (built outside the build-script path).
    build_provenance_verdict(None, Some(sha)).expect_err("missing stamp must refuse");
    // build.rs could not reach git and recorded its documented fallback.
    build_provenance_verdict(Some("unknown"), Some(sha)).expect_err("unknown stamp must refuse");
    // git unavailable at run time, so HEAD cannot be confirmed.
    build_provenance_verdict(Some(sha), None).expect_err("unreadable HEAD must refuse");
}

/// The gate logic lives in `cmd_replacement/`, not in `cmd_replacement.rs`.
/// Evidence produced before a change to that logic must not read as fresh.
#[test]
fn kernel_soundness_launch_evidence_rejects_stale_module_tree_sha() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact.source_sha256.insert(
        TRUST_CORE_RUST_MODULE_TREE_KEY.to_string(),
        "stale".to_string(),
    );

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("evidence pinned to stale gate logic must not validate");

    assert!(
        err.contains(TRUST_CORE_RUST_MODULE_TREE_KEY),
        "unexpected error: {err}"
    );
}

#[test]
fn kernel_soundness_launch_evidence_rejects_missing_module_tree_sha() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact
        .source_sha256
        .remove(TRUST_CORE_RUST_MODULE_TREE_KEY);

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("evidence without a gate-logic pin must not validate");

    assert!(err.contains("missing"), "unexpected error: {err}");
}

/// Every lane except the in-process preflight must be executable. A lane with
/// no command could only ever be self-declared.
#[test]
fn every_executable_kernel_soundness_lane_declares_a_command() {
    for lane in KERNEL_SOUNDNESS_EXPECTED_LANES {
        if lane.id == "differential_artifact_preflight" {
            assert!(lane.command.is_none());
        } else {
            assert!(
                lane.command.is_some_and(|command| !command.is_empty()),
                "lane {} must declare a non-empty command",
                lane.id
            );
        }
    }
}

#[test]
fn kernel_soundness_generator_fails_closed_when_a_lane_command_fails() {
    let runner = |argv: &[&'static str]| -> Result<String, String> {
        if argv == KERNEL_LEAN4_PARITY_LANE_COMMAND {
            Err("exited with status: 101".to_string())
        } else {
            passing_lane_runner(argv)
        }
    };

    let err = generate_kernel_soundness_launch_evidence_with("2026-04-27T00:00:00Z", &runner)
        .expect_err("a failing lane must not yield a passing artifact");

    assert!(
        err.to_string().contains("kernel_lean4_parity"),
        "unexpected error: {err}"
    );
}

#[test]
fn kernel_soundness_generator_fails_closed_on_wrong_test_count() {
    let runner = |argv: &[&'static str]| -> Result<String, String> {
        if argv == KERNEL_LEAN4_PARITY_LANE_COMMAND {
            // Exit status 0, but zero tests actually ran — the exact shape a
            // filter typo produces, and the reason exit code alone is not
            // sufficient evidence.
            Ok("running 0 tests\n\ntest result: ok. 0 passed; 0 failed\n".to_string())
        } else {
            passing_lane_runner(argv)
        }
    };

    let err = generate_kernel_soundness_launch_evidence_with("2026-04-27T00:00:00Z", &runner)
        .expect_err("a zero-test run must not count as parity evidence");

    assert!(
        err.to_string().contains("matched_expected_count=false"),
        "unexpected error: {err}"
    );
}

#[test]
fn kernel_soundness_generator_fails_closed_on_missing_expected_output() {
    let runner = |argv: &[&'static str]| -> Result<String, String> {
        if argv == ELAB_SOUNDNESS_GATE_LANE_COMMAND {
            Ok(" INFO soundness_gate: running reject lane\n".to_string())
        } else {
            passing_lane_runner(argv)
        }
    };

    let err = generate_kernel_soundness_launch_evidence_with("2026-04-27T00:00:00Z", &runner)
        .expect_err("a missing PASS marker must not yield a passing artifact");

    assert!(
        err.to_string().contains("matched_expected_output=false"),
        "unexpected error: {err}"
    );
}

#[test]
fn kernel_soundness_launch_evidence_rejects_failed_status() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact.status = "failed".to_string();

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("failed kernel soundness evidence must not pass");

    assert!(err.contains("is not passed"));
}

#[test]
fn kernel_soundness_launch_evidence_rejects_wrong_command() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact.gate_command = "cargo test -p clean-kernel".to_string();

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("wrong kernel gate command must fail closed");

    assert!(err.contains("gate_command"));
}

#[test]
fn kernel_soundness_launch_evidence_rejects_stale_source_hash() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact
        .source_sha256
        .insert(TRUST_CORE_RUST_SOURCE_PATH.to_string(), "stale".to_string());

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("stale kernel gate source hash must fail closed");

    assert!(err.contains("source_sha256[crates/clean-cli/src/cmd_replacement.rs]"));
}

#[test]
fn kernel_soundness_launch_evidence_rejects_stale_differential_hash() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    artifact.kernel_differential.expressions_sha256 = "stale".to_string();

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("stale kernel differential hash must fail closed");

    assert!(err.contains("kernel_differential.expressions_sha256"));
}

#[test]
fn kernel_soundness_launch_evidence_rejects_wrong_lane_expectation() {
    let (baseline, expression_count, expressions_sha256) = current_kernel_soundness_inputs();
    let mut artifact =
        valid_kernel_soundness_launch_artifact(&baseline, expression_count, &expressions_sha256);
    let lane = artifact
        .lanes
        .iter_mut()
        .find(|lane| lane.id == "kernel_lean4_parity")
        .expect("kernel parity lane");
    lane.expected_tests = Some(2);

    let err = validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        expression_count,
        &expressions_sha256,
    )
    .expect_err("wrong kernel soundness lane expectation must fail closed");

    assert!(err.contains("kernel_lean4_parity expected_tests"));
}

#[test]
fn trust_core_evidence_rejects_stale_structural_ratchet_count() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 2,
        add_decl_unchecked_count: 1,
        add_decl_structural_production_sites: vec![],
        add_decl_unchecked_production_sites: vec![],
        files: vec![
            UncheckedDeclRatchetEntry {
                method: "add_decl_structural".to_string(),
                count: 1,
            },
            UncheckedDeclRatchetEntry {
                method: "add_decl_unchecked".to_string(),
                count: 1,
            },
        ],
        last_updated: "2026-04-16".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("stale structural ratchet count should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("declares add_decl_structural_count=2"));
    assert!(err
        .to_string()
        .contains("file rows + production sites sum to 1"));
}

#[test]
fn trust_core_evidence_rejects_stale_unchecked_ratchet_count() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 1,
        add_decl_unchecked_count: 2,
        add_decl_structural_production_sites: vec![],
        add_decl_unchecked_production_sites: vec![],
        files: vec![
            UncheckedDeclRatchetEntry {
                method: "add_decl_structural".to_string(),
                count: 1,
            },
            UncheckedDeclRatchetEntry {
                method: "add_decl_unchecked".to_string(),
                count: 1,
            },
        ],
        last_updated: "2026-04-16".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("stale unchecked ratchet count should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("declares add_decl_unchecked_count=2"));
    assert!(err
        .to_string()
        .contains("file rows + production sites sum to 1"));
}

#[test]
fn trust_core_evidence_rejects_unknown_unchecked_decl_method() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 1,
        add_decl_unchecked_count: 1,
        add_decl_structural_production_sites: vec![],
        add_decl_unchecked_production_sites: vec![],
        files: vec![
            UncheckedDeclRatchetEntry {
                method: "add_decl_structural".to_string(),
                count: 1,
            },
            UncheckedDeclRatchetEntry {
                method: "add_decl_unchecked".to_string(),
                count: 1,
            },
            UncheckedDeclRatchetEntry {
                method: "add_decl_uncheckd".to_string(),
                count: 1,
            },
        ],
        last_updated: "2026-04-16".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("unknown unchecked-decl method should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("unsupported unchecked-decl method `add_decl_uncheckd`"));
}
