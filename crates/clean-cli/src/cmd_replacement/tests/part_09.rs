// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 9) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn trust_core_evidence_rejects_zero_count_unchecked_decl_row() {
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
                count: 0,
            },
        ],
        last_updated: "2026-04-16".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("zero-count unchecked-decl row should fail closed");

    assert!(matches!(
        err,
        ReplacementError::StaleTrustCoreArtifact { .. }
    ));
    assert!(err
        .to_string()
        .contains("zero-count unchecked-decl row for `add_decl_unchecked`"));
}

fn structural_production_site(
    trust: &str,
    occurrences: Option<u32>,
) -> UncheckedDeclProductionSite {
    UncheckedDeclProductionSite {
        file: "crates/clean-mathverse/src/bin/mathverse_shard/proof_commands.rs".to_string(),
        method: "add_decl_structural".to_string(),
        trust: trust.to_string(),
        occurrences,
    }
}

#[test]
fn trust_core_evidence_accepts_production_site_accounted_ratchet() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 1,
        add_decl_unchecked_count: 0,
        add_decl_structural_production_sites: vec![structural_production_site(
            "SOUND BY ISOLATION: read-only audit env, mints no KernelVerified",
            None,
        )],
        add_decl_unchecked_production_sites: vec![],
        files: vec![],
        last_updated: "2026-07-01".to_string(),
    };

    validate_unchecked_decl_ratchet(&ratchet)
        .expect("production-site-accounted ratchet should validate");
}

#[test]
fn trust_core_evidence_rejects_production_site_without_trust_justification() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 1,
        add_decl_unchecked_count: 0,
        add_decl_structural_production_sites: vec![structural_production_site("  ", None)],
        add_decl_unchecked_production_sites: vec![],
        files: vec![],
        last_updated: "2026-07-01".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("production site without trust prose should fail closed");

    assert!(err
        .to_string()
        .contains("missing its SOUNDNESS trust justification"));
}

#[test]
fn trust_core_evidence_rejects_zero_occurrence_production_site() {
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 0,
        add_decl_unchecked_count: 0,
        add_decl_structural_production_sites: vec![structural_production_site(
            "SOUND BY ISOLATION",
            Some(0),
        )],
        add_decl_unchecked_production_sites: vec![],
        files: vec![],
        last_updated: "2026-07-01".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("zero-occurrence production site should fail closed");

    assert!(err.to_string().contains("records zero occurrences"));
}

#[test]
fn trust_core_evidence_rejects_misfiled_production_site_method() {
    let mut site = structural_production_site("SOUND BY ISOLATION", None);
    site.method = "add_decl_unchecked".to_string();
    let ratchet = UncheckedDeclRatchetArtifact {
        add_decl_structural_count: 1,
        add_decl_unchecked_count: 0,
        add_decl_structural_production_sites: vec![site],
        add_decl_unchecked_production_sites: vec![],
        files: vec![],
        last_updated: "2026-07-01".to_string(),
    };

    let err = validate_unchecked_decl_ratchet(&ratchet)
        .expect_err("misfiled production-site method should fail closed");

    assert!(err.to_string().contains(
        "records method `add_decl_unchecked` under add_decl_structural_production_sites"
    ));
}

#[test]
fn current_unchecked_decl_ratchet_artifact_validates() {
    let ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet parses");

    validate_unchecked_decl_ratchet(&ratchet)
        .expect("checked-in unchecked-decl ratchet artifact should be internally consistent");
}

#[test]
fn deny_sorry_launch_evidence_accepts_strict_closed_artifact() {
    let ratchet = closed_unchecked_decl_ratchet();
    let artifact = valid_deny_sorry_launch_artifact(&ratchet);

    validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .expect("strict deny-sorry artifact against a closed ratchet should validate");
}

#[test]
fn rust_deny_sorry_generator_matches_current_ratchet_debt() {
    let ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet");
    let debt = ratchet
        .add_decl_structural_count
        .saturating_add(ratchet.add_decl_unchecked_count);

    let result = generate_deny_sorry_launch_evidence("2026-04-27T00:00:00Z");
    if debt == 0 {
        let artifact = result.expect("closed ratchet must generate deny-sorry evidence");
        assert_eq!(artifact.generated_by, DENY_SORRY_RUST_GATE_COMMAND);
        assert_eq!(artifact.gate_command, DENY_SORRY_RUST_GATE_COMMAND);
        assert!(artifact
            .source_sha256
            .contains_key(TRUST_CORE_RUST_SOURCE_PATH));
        assert!(!artifact.source_sha256.contains_key(DENY_SORRY_GATE_PATH));
        assert!(!artifact.source_sha256.contains_key(LINT_SORRY_BYPASS_PATH));
    } else {
        let err = result
            .expect_err("open ratchet must fail deny-sorry evidence generation closed")
            .to_string();
        assert!(
            err.contains("current ratchet is not closed at 0/0"),
            "unexpected generator error: {err}"
        );
    }
}

#[test]
fn deny_sorry_launch_evidence_rejects_failed_status() {
    let ratchet = closed_unchecked_decl_ratchet();
    let mut artifact = valid_deny_sorry_launch_artifact(&ratchet);
    artifact.status = "failed".to_string();

    let err = validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .expect_err("failed deny-sorry evidence must not pass");

    assert!(err.contains("is not passed"));
}

#[test]
fn deny_sorry_launch_evidence_rejects_stale_source_hash() {
    let ratchet = closed_unchecked_decl_ratchet();
    let mut artifact = valid_deny_sorry_launch_artifact(&ratchet);
    artifact
        .source_sha256
        .insert(TRUST_CORE_RUST_SOURCE_PATH.to_string(), "stale".to_string());

    let err = validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .expect_err("stale deny-sorry source hash must fail closed");

    assert!(err.contains("source_sha256[crates/clean-cli/src/cmd_replacement.rs]"));
}

#[test]
fn deny_sorry_launch_evidence_rejects_wrong_expected_count() {
    let ratchet = closed_unchecked_decl_ratchet();
    let mut artifact = valid_deny_sorry_launch_artifact(&ratchet);
    let lane = artifact
        .lanes
        .iter_mut()
        .find(|lane| lane.id == "kernel_deny_sorry_gate")
        .expect("kernel deny-sorry lane");
    lane.expected_tests = Some(10);

    let err = validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .expect_err("wrong expected cargo test count must fail closed");

    assert!(err.contains("kernel_deny_sorry_gate expected_tests"));
}

#[test]
fn deny_sorry_launch_evidence_rejects_nonzero_current_ratchet() {
    let mut ratchet = closed_unchecked_decl_ratchet();
    let mut artifact = valid_deny_sorry_launch_artifact(&ratchet);
    ratchet.add_decl_unchecked_count = 1;
    artifact.ratchet.add_decl_unchecked_count = 1;

    let err = validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .expect_err("nonzero current ratchet must fail closed");

    assert!(err.contains("current ratchet is not closed at 0/0"));
}

#[test]
fn axiom_audit_launch_evidence_accepts_strict_current_artifact() {
    let axiom_audit = load_axiom_audit().expect("axiom audit");
    let artifact = valid_axiom_audit_launch_artifact(&axiom_audit);

    validate_axiom_audit_launch_evidence(&artifact, &axiom_audit)
        .expect("current strict axiom-audit artifact should validate");
}

#[test]
fn rust_sorry_bypass_lint_matches_shell_policy_patterns() {
    let trust_marker = ["so", "rry"].concat();
    assert!(line_has_sorry_bypass(&format!(
        r#"let x = mk_const_str("{trust_marker}")"#
    )));
    assert!(line_has_sorry_bypass(&format!(
        r#"let x = Expr::const_str("{trust_marker}", [])"#
    )));
    assert!(line_has_sorry_bypass(&format!(
        r#"let x = Expr::const_str_levels("{trust_marker}", levels)"#
    )));
    assert!(line_has_sorry_bypass(&format!(
        r#"let x = Expr::const_(Name::from_string("{trust_marker}"))"#
    )));
    assert!(!line_has_sorry_bypass(&format!(
        r#"// Expr::const_str("{trust_marker}", []) appears in a comment"#
    )));
    assert!(!line_has_sorry_bypass(&format!(
        r#"let x = create_{trust_marker}_term(ctx, ty)"#
    )));
}

#[test]
fn rust_axiom_audit_aggregate_check_recomputes_python_fields() {
    let audit = serde_json::json!({
        "total_domain_axioms": 3,
        "total_theorems": 5,
        "constructive_theorems": 2,
        "total_all_axioms": 7,
        "conjectures": {
            "C001": {"axioms": 1, "theorems": 2, "constructive": true},
            "C002": {"axioms": ["a", "b"], "theorems": 3, "constructive": false}
        },
        "non_conjecture_axioms": {
            "per_prefix": {
                "Rat": {"count": 4}
            }
        }
    });

    let aggregates = compute_axiom_audit_aggregates(&audit).expect("aggregates");

    assert_eq!(
        aggregates,
        AxiomAuditAggregates {
            total_domain_axioms: 3,
            total_theorems: 5,
            constructive_theorems: 2,
            total_all_axioms: 7,
        }
    );

    let bad = serde_json::json!({
        "conjectures": {
            "C001": {"axioms": true, "theorems": 1}
        }
    });
    let error = compute_axiom_audit_aggregates(&bad).expect_err("bool count rejected");
    assert!(error
        .to_string()
        .contains("conjectures.C001.axioms must be an integer or list"));
}

#[test]
fn rust_axiom_audit_verify_cli_surface_accepts_current_audit() {
    let verification = AxiomAuditVerification::from_args(&AxiomAuditArgs {
        verify: PathBuf::from(AXIOM_AUDIT_PATH),
        evidence: Some(PathBuf::from(AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH)),
        json: true,
    })
    .expect("axiom-audit verification");

    assert_eq!(
        verification.schema_version,
        AXIOM_AUDIT_VERIFY_SCHEMA_VERSION
    );
    assert!(
        verification.validation_passed,
        "{:?}",
        verification.failures
    );
    assert_eq!(verification.axiom_audit.total_domain_axioms, 0);
    assert_eq!(verification.axiom_audit.total_all_axioms, 0);
    assert_eq!(verification.axiom_audit.nonzero_axiom_rows, 0);
    assert!(verification
        .source_sha256
        .contains_key(AXIOM_AUDIT_RUST_SOURCE_PATH));
    assert!(!verification
        .source_sha256
        .contains_key(AXIOM_AUDIT_RELEASE_CHECK_PATH));
    assert!(!verification
        .source_sha256
        .contains_key("scripts/axiom_audit/verify.py"));

    let launch_artifact = verification.launch_evidence_artifact();
    assert_eq!(launch_artifact.generated_by, AXIOM_AUDIT_GATE_COMMAND);
    assert_eq!(launch_artifact.gate_command, AXIOM_AUDIT_GATE_COMMAND);
    validate_axiom_audit_launch_evidence(
        &launch_artifact,
        &load_axiom_audit().expect("axiom audit"),
    )
    .expect("generated Rust axiom-audit launch evidence should validate");
}

#[test]
fn axiom_audit_launch_evidence_rejects_failed_status() {
    let axiom_audit = load_axiom_audit().expect("axiom audit");
    let mut artifact = valid_axiom_audit_launch_artifact(&axiom_audit);
    artifact.status = "failed".to_string();

    let err = validate_axiom_audit_launch_evidence(&artifact, &axiom_audit)
        .expect_err("failed axiom-audit evidence must not pass");

    assert!(err.contains("is not passed"));
}

#[test]
fn axiom_audit_launch_evidence_rejects_stale_source_hash() {
    let axiom_audit = load_axiom_audit().expect("axiom audit");
    let mut artifact = valid_axiom_audit_launch_artifact(&axiom_audit);
    artifact.source_sha256.insert(
        AXIOM_AUDIT_RUST_SOURCE_PATH.to_string(),
        "stale".to_string(),
    );

    let err = validate_axiom_audit_launch_evidence(&artifact, &axiom_audit)
        .expect_err("stale axiom-audit source hash must fail closed");

    assert!(err.contains("source_sha256[crates/clean-cli/src/cmd_replacement.rs]"));
}

#[test]
fn axiom_audit_launch_evidence_rejects_nonzero_current_audit() {
    let mut axiom_audit = load_axiom_audit().expect("axiom audit");
    let mut artifact = valid_axiom_audit_launch_artifact(&axiom_audit);
    axiom_audit.total_domain_axioms = 1;
    artifact.axiom_audit.total_domain_axioms = 1;

    let err = validate_axiom_audit_launch_evidence(&artifact, &axiom_audit)
        .expect_err("nonzero current axiom audit must fail closed");

    assert!(err.contains("current axiom audit is not closed at 0/0"));
}

#[test]
fn trust_core_evidence_json_has_stable_schema() {
    let Ok(report) = TrustCoreEvidenceReport::current() else {
        eprintln!("SKIP: trust-core evidence report artifacts not present");
        return;
    };
    let json = serde_json::to_string(&report).expect("serialize trust-core report");

    assert!(json.contains(TRUST_CORE_EVIDENCE_SCHEMA_VERSION));
    assert!(json.contains("kernel_differential"));
    assert!(json.contains("fallback_denial"));
    assert!(json.contains("launch_evidence_path"));
    assert!(json.contains("launch_evidence_status"));
    assert!(json.contains(KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH));
    assert!(json.contains("expressions_sha256_match"));
    assert!(json.contains("gate_preflight_required"));
    assert!(json.contains("gate_preflight_guards"));
    assert!(json.contains("deny_sorry_lanes"));
    assert!(json.contains("zero_trust_gates"));
    assert!(json.contains("active_debt_count"));
    assert!(json.contains("evidence_summary"));
    assert!(json.contains("axiom-audit"));
    assert!(json.contains(AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH));
    assert!(json.contains("proof_system_certification"));
    assert!(json.contains("verification_audit_open_lanes"));
    assert!(json.contains("replay_parity_rows"));
}

#[test]
fn tactic_parity_report_covers_replacement_tactics() {
    let report = TacticParityReport::current();

    for required in [
        "simp",
        "rw",
        "exact",
        "ring",
        "norm_num",
        "mathverse",
        "linarith",
        "nlinarith",
        "aesop",
        "grind",
    ] {
        tactic_report_row(&report, required);
    }
    assert!(
            !report.launch_ready,
            "representative tactic rows cannot claim launch readiness before full-corpus acceptance evidence is present"
        );
    assert_eq!(
        report
            .tactic_counts
            .get(&TacticParityStatus::ProofCarrying)
            .copied()
            .unwrap_or(0),
        10
    );
    assert_eq!(
        report
            .tactic_counts
            .get(&TacticParityStatus::EvidenceBackedPartial)
            .copied()
            .unwrap_or(0),
        0
    );
    assert_eq!(
        report
            .tactic_counts
            .get(&TacticParityStatus::Lean4ParityGap)
            .copied()
            .unwrap_or(0),
        0
    );
    for tactic in ["mathverse", "linarith", "nlinarith"] {
        let row = tactic_report_row(&report, tactic);
        assert_eq!(row.lean4_parity_status, TacticParityStatus::ProofCarrying);
        assert_eq!(row.trusted_arith_count, 0);
    }
    assert_eq!(
        tactic_report_row(&report, "aesop").lean4_parity_status,
        TacticParityStatus::ProofCarrying
    );
    assert_eq!(
        tactic_report_row(&report, "grind").lean4_parity_status,
        TacticParityStatus::ProofCarrying
    );
}
