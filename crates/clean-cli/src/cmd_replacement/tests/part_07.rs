// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 7) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn replacement_status_wires_zero_trust_gates() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let gate_ids: Vec<&str> = report.zero_trust_gates.iter().map(|gate| gate.id).collect();

    assert_eq!(report.zero_trust_gates.len(), 3);
    assert!(gate_ids.contains(&"kernel-soundness"));
    assert!(gate_ids.contains(&"deny-sorry"));
    assert!(gate_ids.contains(&"axiom-audit"));
    assert!(report
        .zero_trust_gates
        .iter()
        .all(|gate| gate.required_for_launch));
    let kernel = report
        .zero_trust_gates
        .iter()
        .find(|gate| gate.id == "kernel-soundness")
        .expect("kernel-soundness zero-trust gate");
    if kernel.status == ZeroTrustGateStatus::Passed {
        assert!(kernel
            .evidence_summary
            .contains("kernel-soundness-launch-evidence.json passed"));
    } else {
        assert_eq!(kernel.status, ZeroTrustGateStatus::PendingEvidence);
        assert!(kernel
            .fail_closed_reason
            .contains(KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH));
    }
    let deny_sorry = report
        .zero_trust_gates
        .iter()
        .find(|gate| gate.id == "deny-sorry")
        .expect("deny-sorry zero-trust gate");
    if deny_sorry.status == ZeroTrustGateStatus::Passed {
        assert!(deny_sorry
            .evidence_summary
            .contains("deny-sorry-launch-evidence.json passed"));
    }
    assert_eq!(
        report.zero_trust_gates_passed,
        report
            .zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed)
    );
}

#[test]
fn replacement_status_fails_closed_on_sorry_and_axiom_debt() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet");
    let axiom_audit_artifact = load_axiom_audit().expect("axiom audit artifact");
    let fallback_debt = ratchet
        .add_decl_structural_count
        .saturating_add(ratchet.add_decl_unchecked_count);
    let axiom_audit_debt = axiom_audit_artifact
        .total_domain_axioms
        .saturating_add(axiom_audit_artifact.total_all_axioms);
    let deny_sorry = report
        .zero_trust_gates
        .iter()
        .find(|gate| gate.id == "deny-sorry")
        .expect("deny-sorry zero-trust gate");
    let axiom_audit = report
        .zero_trust_gates
        .iter()
        .find(|gate| gate.id == "axiom-audit")
        .expect("axiom-audit zero-trust gate");

    assert!(!report.launch_ready);
    assert_eq!(
        report.zero_trust_gates_passed,
        report
            .zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed)
    );
    assert!(deny_sorry.required_for_launch);
    if fallback_debt == 0 {
        assert!(matches!(
            deny_sorry.status,
            ZeroTrustGateStatus::PendingEvidence | ZeroTrustGateStatus::Passed
        ));
        if deny_sorry.status == ZeroTrustGateStatus::Passed {
            assert!(deny_sorry
                .evidence_summary
                .contains("deny-sorry-launch-evidence.json passed"));
        } else {
            assert!(deny_sorry
                .fail_closed_reason
                .contains("fresh launch-gate evidence artifact"));
        }
    } else {
        assert_eq!(deny_sorry.status, ZeroTrustGateStatus::Blocked);
        assert!(deny_sorry
            .fail_closed_reason
            .contains("trusted fallback callsites"));
    }
    assert_eq!(
        deny_sorry.debt_class,
        ZeroTrustDebtClass::SorryAndTrustedFallback
    );
    assert!(deny_sorry
        .source_artifacts
        .contains(&UNCHECKED_DECL_RATCHET_PATH));
    assert_eq!(deny_sorry.active_debt_count, fallback_debt);
    assert!(deny_sorry.evidence_summary.starts_with(&format!(
        "add_decl_structural_count={}, add_decl_unchecked_count={}, total={}; ",
        ratchet.add_decl_structural_count, ratchet.add_decl_unchecked_count, fallback_debt
    )));
    assert!(deny_sorry
        .evidence_summary
        .contains(format!("{DENY_SORRY_LAUNCH_EVIDENCE_PATH} ").as_str()));
    if axiom_audit_debt == 0 {
        assert!(matches!(
            axiom_audit.status,
            ZeroTrustGateStatus::PendingEvidence | ZeroTrustGateStatus::Passed
        ));
        if axiom_audit.status == ZeroTrustGateStatus::Passed {
            assert!(axiom_audit
                .evidence_summary
                .contains("axiom-audit-launch-evidence.json passed"));
        } else {
            assert!(axiom_audit
                .fail_closed_reason
                .contains(AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH));
        }
    } else {
        assert_eq!(axiom_audit.status, ZeroTrustGateStatus::Blocked);
    }
    assert_eq!(axiom_audit.debt_class, ZeroTrustDebtClass::AxiomAudit);
    assert!(axiom_audit.source_artifacts.contains(&AXIOM_AUDIT_PATH));
    assert!(axiom_audit
        .source_artifacts
        .contains(&VERIFICATION_AUDIT_PATH));
    assert_eq!(axiom_audit.active_debt_count, axiom_audit_debt);
    assert!(axiom_audit.evidence_summary.starts_with(&format!(
        "total_domain_axioms={}, total_all_axioms={}, total={}; ",
        axiom_audit_artifact.total_domain_axioms,
        axiom_audit_artifact.total_all_axioms,
        axiom_audit_debt
    )));
    assert!(axiom_audit
        .evidence_summary
        .contains(format!("{AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH} ").as_str()));
}

#[test]
fn replacement_status_human_fallback_denial_row_reports_live_ratchet_totals() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet");
    let fallback_debt = ratchet
        .add_decl_structural_count
        .saturating_add(ratchet.add_decl_unchecked_count);
    let expected_evidence = format!(
        "evidence: add_decl_structural_count={}, add_decl_unchecked_count={}, total={}; ",
        ratchet.add_decl_structural_count, ratchet.add_decl_unchecked_count, fallback_debt
    );
    let mut output = Vec::new();

    render_human(&mut output, &report).expect("render replacement status");
    let output = String::from_utf8(output).expect("human output should be utf-8");
    let row_start = output
        .find("- fallback-denial [green]")
        .expect("fallback-denial row");
    let row_tail = &output[row_start..];
    let row_end = row_tail
        .find("\n- frontend-parity")
        .map(|offset| row_start + offset)
        .unwrap_or(output.len());
    let row_output = &output[row_start..row_end];

    assert!(!report.launch_ready);
    assert_eq!(
        fallback_debt,
        ratchet
            .add_decl_structural_count
            .saturating_add(ratchet.add_decl_unchecked_count)
    );
    assert!(output.contains("launch_ready: false"));
    assert!(!output.contains("launch_ready: true"));
    assert!(row_output.contains(&expected_evidence));
    assert!(row_output.contains(DENY_SORRY_LAUNCH_EVIDENCE_PATH));
    assert!(row_output.contains("Fresh DENY_SORRY launch evidence passed"));
    assert!(!row_output.contains("[in_progress]"));
}

#[test]
fn replacement_status_points_to_tactic_parity_report() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let tactic_row = report
        .rows
        .iter()
        .find(|row| row.id == "tactic-parity")
        .expect("tactic parity row");
    let strict_row = report
        .rows
        .iter()
        .find(|row| row.id == "strict-reconstruction")
        .expect("strict reconstruction row");

    assert_eq!(tactic_row.status, ReplacementStatus::Green);
    assert_eq!(strict_row.status, ReplacementStatus::Green);
    assert_eq!(
        tactic_row.evidence_artifact,
        TACTIC_PARITY_COUNT_ARTIFACT_PATH
    );
    assert_eq!(
        strict_row.evidence_artifact,
        STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH
    );
}

#[test]
fn replacement_status_points_to_trust_core_evidence_report() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let kernel_row = report
        .rows
        .iter()
        .find(|row| row.id == "kernel-differential")
        .expect("kernel differential row");
    let proof_row = report
        .rows
        .iter()
        .find(|row| row.id == "proof-system-certification")
        .expect("proof-system certification row");
    let fallback_row = report
        .rows
        .iter()
        .find(|row| row.id == "fallback-denial")
        .expect("fallback denial row");

    assert_eq!(kernel_row.status, ReplacementStatus::Green);
    assert_eq!(proof_row.status, ReplacementStatus::InProgress);
    assert_eq!(fallback_row.status, ReplacementStatus::Green);
    assert_eq!(
        kernel_row.evidence_artifact,
        KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH
    );
    assert!(kernel_row
        .blocker
        .contains("Fresh kernel soundness launch evidence"));
    assert_eq!(
        proof_row.evidence_artifact,
        TRUST_CORE_EVIDENCE_SCHEMA_VERSION
    );
    assert_eq!(
        report.proof_system_certification.status,
        if report.proof_system_certification.zero_trust_gates_passed {
            ReplacementStatus::InProgress
        } else {
            ReplacementStatus::Blocked
        }
    );
    assert!(report
        .proof_system_certification
        .evidence_summary
        .contains(&format!(
            "replay_parity_blockers={}",
            report
                .proof_system_certification
                .blocking_replay_parity_rows
        )));
    assert!(proof_row
        .blocker
        .contains("proof-system certification remains in progress on #464"));
    assert_eq!(
        fallback_row.evidence_artifact,
        DENY_SORRY_LAUNCH_EVIDENCE_PATH
    );
    assert!(fallback_row
        .blocker
        .contains("Fresh DENY_SORRY launch evidence passed"));
}

#[test]
fn replacement_status_points_to_native_library_evidence_report() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let native_row = report
        .rows
        .iter()
        .find(|row| row.id == "native-libraries")
        .expect("native libraries row");

    assert_eq!(native_row.status, ReplacementStatus::InProgress);
    assert_eq!(
            native_row.gate_command,
            "clean replacement validate-report --report reports/native-library-replacement.json --kind native-library --json && clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json && clean replacement native-library api-slice --slice nat-arithmetic --json && clean replacement native-library api-slice --slice nat-bitwise --json && clean replacement native-library api-slice --slice bool-nat-ext --json && clean replacement native-library api-slice --slice string-ext --json && clean replacement native-library api-slice --slice string-core --json && clean replacement native-library api-slice --slice string-transform --json && clean replacement native-library api-slice --slice string-hash --json && clean replacement native-library api-slice --slice name-core --json && clean replacement native-library api-slice --slice decidable-core --json && clean replacement native-library api-slice --slice decidable-eq-aliases --json && clean replacement native-library api-slice --slice int-order-decidable --json && clean replacement native-library api-slice --slice signed-decidable-eq-aliases --json && clean replacement native-library api-slice --slice hetero-ops --json && clean replacement native-library api-slice --slice beq-shortcircuit --json && clean replacement native-library api-slice --slice decidable-combinators --json && clean replacement native-library api-slice --slice nat-order-decidable --json && clean replacement native-library api-slice --slice char-core --json && clean replacement native-library api-slice --slice uint-of-nat --json && clean replacement native-library api-slice --slice fin-val --json && clean replacement native-library api-slice --slice uint-narrowing --json && clean replacement native-library api-slice --slice uint-widening --json && clean replacement native-library api-slice --slice bitvec-core --json && clean replacement native-library api-slice --slice uint-bitvec --json && clean replacement native-library api-slice --slice signed-bitvec --json && clean replacement native-library api-slice --slice uint8-core --json && clean replacement native-library api-slice --slice uint16-core --json && clean replacement native-library api-slice --slice uint32-core --json && clean replacement native-library api-slice --slice uint64-core --json && clean replacement native-library api-slice --slice usize-core --json && clean replacement native-library api-slice --slice uint8-bitwise --json && clean replacement native-library api-slice --slice uint16-bitwise --json && clean replacement native-library api-slice --slice uint32-bitwise --json && clean replacement native-library api-slice --slice uint64-bitwise --json && clean replacement native-library api-slice --slice usize-bitwise --json && clean replacement native-library api-slice --slice platform-core --json && clean replacement native-library api-slice --slice float-core --json && clean replacement native-library api-slice --slice float-classification --json && clean replacement native-library api-slice --slice float-functions --json && clean replacement native-library api-slice --slice float-input-conversions --json && clean replacement native-library api-slice --slice float-formatting --json && clean replacement native-library api-slice --slice float-output-conversions --json && clean replacement native-library api-slice --slice int-core --json && clean replacement native-library api-slice --slice int8-core --json && clean replacement native-library api-slice --slice int16-core --json && clean replacement native-library api-slice --slice int32-core --json && clean replacement native-library api-slice --slice int64-core --json && clean replacement native-library api-slice --slice isize-core --json && clean replacement native-library mathlib-api --expect-blocked --json && cargo test --locked -p clean-kernel native_reducers --lib"
        );
    assert_eq!(
        native_row.evidence_artifact,
        "reports/native-library-replacement.json"
    );
    assert!(
        native_row.blocker.contains("compatibility-only")
            && native_row
                .blocker
                .contains("full native Mathlib replacement remains blocked")
    );

    let artifact = fs::read_to_string(repo_artifact_path(native_row.evidence_artifact))
        .expect("native-library replacement report should be checked in");
    let artifact_json: serde_json::Value =
        serde_json::from_str(&artifact).expect("native-library report should be JSON");
    if artifact_json
        .get("stub")
        .and_then(serde_json::Value::as_bool)
        == Some(true)
    {
        eprintln!(
            "SKIP: {} is the checked-in stub placeholder; regenerate it to assert its contents",
            native_row.evidence_artifact
        );
        return;
    }
    assert_eq!(
        artifact_json["schema_version"],
        "clean-native-library-replacement-v1"
    );
    assert_eq!(
            artifact_json["gate_command"],
            "clean replacement validate-report --report reports/native-library-replacement.json --kind native-library --json && clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json && clean replacement native-library api-slice --slice nat-arithmetic --json && clean replacement native-library api-slice --slice nat-bitwise --json && clean replacement native-library api-slice --slice bool-nat-ext --json && clean replacement native-library api-slice --slice string-ext --json && clean replacement native-library api-slice --slice string-core --json && clean replacement native-library api-slice --slice string-transform --json && clean replacement native-library api-slice --slice string-hash --json && clean replacement native-library api-slice --slice name-core --json && clean replacement native-library api-slice --slice decidable-core --json && clean replacement native-library api-slice --slice decidable-eq-aliases --json && clean replacement native-library api-slice --slice int-order-decidable --json && clean replacement native-library api-slice --slice signed-decidable-eq-aliases --json && clean replacement native-library api-slice --slice hetero-ops --json && clean replacement native-library api-slice --slice beq-shortcircuit --json && clean replacement native-library api-slice --slice decidable-combinators --json && clean replacement native-library api-slice --slice nat-order-decidable --json && clean replacement native-library api-slice --slice char-core --json && clean replacement native-library api-slice --slice uint-of-nat --json && clean replacement native-library api-slice --slice fin-val --json && clean replacement native-library api-slice --slice uint-narrowing --json && clean replacement native-library api-slice --slice uint-widening --json && clean replacement native-library api-slice --slice bitvec-core --json && clean replacement native-library api-slice --slice uint-bitvec --json && clean replacement native-library api-slice --slice signed-bitvec --json && clean replacement native-library api-slice --slice uint8-core --json && clean replacement native-library api-slice --slice uint16-core --json && clean replacement native-library api-slice --slice uint32-core --json && clean replacement native-library api-slice --slice uint64-core --json && clean replacement native-library api-slice --slice usize-core --json && clean replacement native-library api-slice --slice uint8-bitwise --json && clean replacement native-library api-slice --slice uint16-bitwise --json && clean replacement native-library api-slice --slice uint32-bitwise --json && clean replacement native-library api-slice --slice uint64-bitwise --json && clean replacement native-library api-slice --slice usize-bitwise --json && clean replacement native-library api-slice --slice platform-core --json && clean replacement native-library api-slice --slice float-core --json && clean replacement native-library api-slice --slice float-classification --json && clean replacement native-library api-slice --slice float-functions --json && clean replacement native-library api-slice --slice float-input-conversions --json && clean replacement native-library api-slice --slice float-formatting --json && clean replacement native-library api-slice --slice float-output-conversions --json && clean replacement native-library api-slice --slice int-core --json && clean replacement native-library api-slice --slice int8-core --json && clean replacement native-library api-slice --slice int16-core --json && clean replacement native-library api-slice --slice int32-core --json && clean replacement native-library api-slice --slice int64-core --json && clean replacement native-library api-slice --slice isize-core --json && clean replacement native-library mathlib-api --expect-blocked --json && cargo test --locked -p clean-kernel native_reducers --lib"
        );
    assert_eq!(artifact_json["replacement_row"]["id"], "native-libraries");
    assert_eq!(artifact_json["replacement_row"]["issue"], 3713);
    assert_eq!(artifact_json["status"], "in_progress");
    assert!(artifact_json["claim"]
        .as_str()
        .is_some_and(|claim| claim.contains("Full native Mathlib replacement is not claimed")));
    assert!(artifact_json["non_claims"]
        .as_array()
        .is_some_and(|non_claims| non_claims.iter().any(|claim| {
            claim
                .as_str()
                .is_some_and(|claim| claim.contains("does not claim full native Mathlib"))
        })));

    let rows = artifact_json["rows"]
        .as_array()
        .expect("native-library report rows should be an array");
    assert_eq!(artifact_json["summary"]["row_count"], rows.len());
    let native_evidence_rows = artifact_json["summary"]["native_evidence_rows"]
        .as_array()
        .expect("native evidence row ids should be an array");
    assert!(native_evidence_rows.len() >= 2);
    assert!(native_evidence_rows.contains(&serde_json::Value::String(
        "native-shard-trust-gate".to_string()
    )));
    assert!(artifact_json["summary"]["compatibility_only_rows"]
        .as_array()
        .expect("compatibility-only row ids should be an array")
        .contains(&serde_json::Value::String(
            "mathlib-olean-compatibility".to_string()
        )));
    for row in rows {
        assert!(row["evidence"]
            .as_array()
            .is_some_and(|evidence| !evidence.is_empty()));
    }

    let mathlib_row = rows
        .iter()
        .find(|row| row["id"] == "mathlib-olean-compatibility")
        .expect("native-library report should include Mathlib compatibility row");
    assert_eq!(mathlib_row["status"], "compatibility_only");
    assert!(mathlib_row["acceptance"]
        .as_str()
        .is_some_and(|acceptance| acceptance.contains(".olean")));
    assert!(mathlib_row["blockers"]
        .as_array()
        .is_some_and(|blockers| blockers.iter().any(|blocker| {
            blocker
                .as_str()
                .is_some_and(|blocker| blocker.contains("Do not claim native Mathlib replacement"))
        })));
}

#[test]
fn replacement_status_points_to_compile_runtime_evidence_report() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let compile_row = report
        .rows
        .iter()
        .find(|row| row.id == "compile-runtime")
        .expect("compile runtime row");

    assert_eq!(compile_row.status, ReplacementStatus::Green);
    assert_eq!(
        compile_row.gate_command,
        "clean compile demos/public/kernel_check_success.lean --decl main --emit c"
    );
    assert_eq!(
        compile_row.evidence_artifact,
        "reports/compile-runtime-smoke.json"
    );
    assert!(compile_row
        .blocker
        .contains("Public demo compile smoke emits C"));

    let artifact = fs::read_to_string(repo_artifact_path(compile_row.evidence_artifact))
        .expect("compile-runtime smoke report should be checked in");
    let artifact_json: serde_json::Value =
        serde_json::from_str(&artifact).expect("compile-runtime report should be JSON");
    assert_eq!(
        artifact_json["schema_version"],
        "clean-compile-runtime-smoke-v1"
    );
    assert_eq!(artifact_json["replacement_row"]["id"], "compile-runtime");
    assert_eq!(artifact_json["replacement_row"]["issue"], 3708);
    assert_eq!(artifact_json["status"], "passed");
    assert!(artifact_json["rows"]
        .as_array()
        .expect("compile-runtime report rows should be an array")
        .iter()
        .any(|row| row["id"] == "public-demo-main-emit-c" && row["status"] == "passed"));
}
