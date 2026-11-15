// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 7) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

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
    // G6 (2026-08-26): the row's verdict is the ratchet's CLOSURE, not its
    // count. This asks the SAME validator the gate asks, so the two halves
    // cannot drift apart again — and a closed ratchet carrying a nonzero
    // sanctioned, capped occurrence count can never read `blocked`.
    match validate_unchecked_decl_ratchet_closed(&ratchet) {
        Err(message) => {
            assert_eq!(deny_sorry.status, ZeroTrustGateStatus::Blocked);
            assert!(
                deny_sorry.fail_closed_reason.contains("is not closed"),
                "blocked deny-sorry must print the closure branch, got: {}",
                deny_sorry.fail_closed_reason
            );
            assert!(
                deny_sorry.fail_closed_reason.contains(message.as_str()),
                "blocked deny-sorry must quote the closure failure, got: {}",
                deny_sorry.fail_closed_reason
            );
        }
        Ok(()) => {
            assert!(
                matches!(
                    deny_sorry.status,
                    ZeroTrustGateStatus::PendingEvidence | ZeroTrustGateStatus::Passed
                ),
                "a CLOSED ratchet must never leave deny-sorry blocked (status {:?}, reason {})",
                deny_sorry.status,
                deny_sorry.fail_closed_reason
            );
            assert!(
                deny_sorry.fail_closed_reason.contains("ratchet is closed"),
                "closed deny-sorry must print the closure branch, got: {}",
                deny_sorry.fail_closed_reason
            );
            if deny_sorry.status == ZeroTrustGateStatus::Passed {
                assert!(deny_sorry
                    .evidence_summary
                    .contains("deny-sorry-launch-evidence.json passed"));
            } else {
                assert!(deny_sorry
                    .fail_closed_reason
                    .contains("fresh launch-gate evidence artifact"));
            }
        }
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
    // Locate the row by its EFFECTIVE status. This assertion used to hard-code
    // `[green]`, which pinned the renderer's defect in place: the human view
    // printed the hand-declared `row.status` while the same output's
    // `readiness_accounting` line named `fallback-denial` a launch blocker.
    let fallback_row = report
        .rows
        .iter()
        .find(|row| row.id == "fallback-denial")
        .expect("fallback-denial row in report");
    let expected_header = format!(
        "- fallback-denial [{}]",
        fallback_row.effective_status.as_str()
    );

    render_human(&mut output, &report).expect("render replacement status");
    let output = String::from_utf8(output).expect("human output should be utf-8");
    let row_start = output.find(&expected_header).unwrap_or_else(|| {
        panic!(
            "fallback-denial row must print its effective status {:?}, not its declared {:?}",
            fallback_row.effective_status, fallback_row.status
        )
    });
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

/// A row must never outrank its own gate in the human view.
///
/// The `--json` view always emitted `effective_status`; the human view emitted
/// the hand-declared `status`, so `clean replacement status` could print
/// `- fallback-denial [green]` in the SAME output whose `readiness_accounting`
/// line and whose nonzero-exit message both named `fallback-denial` a launch
/// blocker. This checks the whole row set, not one row, because the defect is
/// in the renderer and lands on whichever row happens to disagree today.
#[test]
fn replacement_status_human_rows_print_effective_status_not_declared() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let mut output = Vec::new();
    render_human(&mut output, &report).expect("render replacement status");
    let output = String::from_utf8(output).expect("human output should be utf-8");

    // The blockers named by the readiness accounting are exactly the rows that
    // must not render green. Read them off the report so the two views are
    // compared against each other, not against a frozen expectation.
    let blocking = &report.readiness_accounting.launch_blocking_row_ids;

    let mut checked = 0usize;
    for row in &report.rows {
        let header = format!("- {} [{}]", row.id, row.effective_status.as_str());
        assert!(
            output.contains(&header),
            "row {} must render its effective status {:?} (declared {:?}); \
             human output disagreed with the --json view",
            row.id,
            row.effective_status,
            row.status
        );
        if row.effective_status != row.status {
            // The declared claim is still shown, but only as an annotation --
            // never as the row's headline label.
            assert!(
                !output.contains(&format!("- {} [{}]", row.id, row.status.as_str())),
                "row {} printed its declared {:?} as the headline label",
                row.id,
                row.status
            );
            checked += 1;
        }
        if blocking.contains(&row.id) {
            assert_ne!(
                row.effective_status,
                ReplacementStatus::Green,
                "row {} is named a launch blocker yet renders green",
                row.id
            );
        }
    }
    // Guard against the test going vacuous if every row ever agrees: the
    // accounting must still have named at least one blocker for this report to
    // be the fail-closed one we are checking.
    assert!(
        !blocking.is_empty() || checked > 0,
        "no blocking rows and no status disagreement: nothing was actually checked"
    );
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

/// The `compile-runtime` row is backed by the byte-exact differential battery,
/// not by the emit-C smoke that linked, ran and compared nothing (measured
/// 2026-09-25: it stayed Green while `clean run` printed wrong answers at exit
/// 0). The battery gates fail-closedness, not parity, so the row may not be
/// Green on it.
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

    assert_eq!(compile_row.status, ReplacementStatus::InProgress);
    assert_eq!(
        compile_row.gate_command,
        "cargo test --locked -p clean --test native_exec_battery"
    );
    assert_eq!(
        compile_row.evidence_artifact,
        "reports/native-exec-battery.json"
    );
    assert!(compile_row
        .blocker
        .contains("byte-exact differential battery"));

    let artifact = fs::read_to_string(repo_artifact_path(compile_row.evidence_artifact))
        .expect("the native execution battery report should be checked in");
    let artifact_json: serde_json::Value =
        serde_json::from_str(&artifact).expect("the battery report should be JSON");
    assert_eq!(
        artifact_json["schema_version"],
        "clean-native-exec-battery-v1"
    );
    assert_eq!(artifact_json["status"], "passed");
    assert_eq!(artifact_json["wrong_output_exit0"], 0);
    let programs = artifact_json["programs"]
        .as_array()
        .expect("the battery report lists its programs");
    assert!(
        !programs.is_empty(),
        "a battery of zero programs gates nothing"
    );
    for program in programs {
        let verdict = program["verdict"]
            .as_str()
            .expect("each program has a verdict");
        assert!(
            matches!(verdict, "BYTE_EQUAL" | "REFUSED_BUILD" | "REFUSED_RUNTIME"),
            "{} is {verdict}: neither byte-identical to Lean nor refused by name",
            program["name"]
        );
    }
}

// ---------------------------------------------------------------------------
// Exit discipline: a gate command must be able to say no.
//
// `run_status` has always failed closed. Three sibling handlers returned
// `Ok(())` unconditionally while printing a report that carried
// `launch_ready: false`, so `<gate> && echo GREEN` printed GREEN off a red
// report. Two of them are NAMED gate commands for scorecard rows:
//   * `clean replacement tactic-parity --json`     -> rows `tactic-parity`,
//                                                     `strict-reconstruction`
//   * `clean replacement trust-core-evidence --json` -> trailing `&&` conjunct
//     of `proof-system-certification`, `fallback-denial`, `kernel-differential`
//
// Each test states the same invariant -- the handler errs exactly when its own
// report is not launch-ready -- so it stays load-bearing in both directions
// rather than pinning today's colour.
// ---------------------------------------------------------------------------

#[test]
fn tactic_parity_gate_exit_status_tracks_its_own_launch_ready() {
    let report = TacticParityReport::current();
    let result = run_tactic_parity(TacticParityArgs {
        command: None,
        json: true,
    });

    assert_eq!(
        result.is_err(),
        !report.launch_ready,
        "tactic-parity exit status must be derived from its report \
         (launch_ready={}, err={:?}); this command is the named gate for the \
         `tactic-parity` and `strict-reconstruction` rows",
        report.launch_ready,
        result.err().map(|error| error.to_string()),
    );
}

#[test]
fn trust_core_evidence_gate_exit_status_tracks_its_own_launch_ready() {
    let Ok(report) = TrustCoreEvidenceReport::current() else {
        eprintln!("SKIP: trust-core evidence artifacts not present on this machine");
        return;
    };
    let result = run_trust_core_evidence(TrustCoreEvidenceArgs {
        json: true,
        kernel_soundness: false,
        deny_sorry: false,
        evidence: None,
        generated_at: "1970-01-01T00:00:00Z".to_string(),
    });

    assert_eq!(
        result.is_err(),
        !report.launch_ready,
        "trust-core-evidence exit status must be derived from its report \
         (launch_ready={}, overall_status={}, err={:?}); this command is the \
         trailing `&&` conjunct of three rows' gate commands",
        report.launch_ready,
        report.overall_status,
        result.err().map(|error| error.to_string()),
    );
}

/// Same invariant for the rust-first tooling inventory.
///
/// NOTE ON WHAT THIS PROVES TODAY: the inventory reads `launch_ready=true` at
/// this commit, so this assertion is currently satisfied by BOTH the fixed and
/// the unfixed handler -- it is not a mutation-sensitive proof right now. It is
/// here because the read path's exit was never *derived* from the verdict (only
/// the evidence WRITE was guarded, by `rust_first_tooling_write_refusal`), and
/// this makes the derivation explicit so a lane regressing to non-Rust-owned
/// cannot pass an `&&`-chained caller.
#[test]
fn rust_first_tooling_exit_status_tracks_its_own_launch_ready() {
    let artifact = RustFirstToolingEvidenceArtifact::current();
    let result = run_rust_first_tooling(RustFirstToolingEvidenceArgs {
        json: true,
        evidence: None,
    });

    assert_eq!(
        result.is_err(),
        !artifact.rust_first_tooling.launch_ready,
        "rust-first-tooling exit status must be derived from its inventory \
         (launch_ready={}, err={:?})",
        artifact.rust_first_tooling.launch_ready,
        result.err().map(|error| error.to_string()),
    );
    // The write-path refusal and the read-path exit must agree on the same
    // predicate, so the two halves cannot drift.
    assert_eq!(
        rust_first_tooling_write_refusal(&artifact.rust_first_tooling).is_err(),
        !artifact.rust_first_tooling.launch_ready,
    );
}

/// The whole family, stated once: no `clean replacement` gate surface may
/// return success while its own report declares itself not launch-ready.
///
/// Measured 2026-08-26 across every subcommand of the group. `status`,
/// `release-issue-hygiene`, `validate-report`, `axiom-audit`,
/// `tactic-parity validate-full-corpus`, `native-library coverage-matrix`,
/// `native-library api-slice` and `native-library mathlib-api` already derived
/// their exit from a verdict field; the three below did not.
#[test]
fn replacement_gate_commands_cannot_return_ok_on_a_red_report() {
    let tactic = TacticParityReport::current();
    if !tactic.launch_ready {
        assert!(
            run_tactic_parity(TacticParityArgs {
                command: None,
                json: true,
            })
            .is_err(),
            "tactic-parity returned Ok(()) on launch_ready=false"
        );
    }
    if let Ok(trust_core) = TrustCoreEvidenceReport::current() {
        if !trust_core.launch_ready {
            assert!(
                run_trust_core_evidence(TrustCoreEvidenceArgs {
                    json: true,
                    kernel_soundness: false,
                    deny_sorry: false,
                    evidence: None,
                    generated_at: "1970-01-01T00:00:00Z".to_string(),
                })
                .is_err(),
                "trust-core-evidence returned Ok(()) on launch_ready=false"
            );
        }
    }
    let rust_first = RustFirstToolingEvidenceArtifact::current();
    if !rust_first.rust_first_tooling.launch_ready {
        assert!(
            run_rust_first_tooling(RustFirstToolingEvidenceArgs {
                json: true,
                evidence: None,
            })
            .is_err(),
            "rust-first-tooling returned Ok(()) on launch_ready=false"
        );
    }
}
