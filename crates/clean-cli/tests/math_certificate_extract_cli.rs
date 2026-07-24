// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused process-boundary tests for `clean math certificate extract`.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use clean_kernel::{Environment, Expr, Level, Name};
use clean_math_project::{obligation_fingerprint, MathObligation};
use clean_server::handlers::{
    handle_apply_tactic, handle_extract_proof, handle_init_proof_state, ApplyTacticParams,
    ExtractProofParams, InitProofStateParams, ServerState,
};
use clean_server::RequestId;
use serde_json::Value;

const CLEAN_MATH_CLI_BIN_ENV: &str = "CLEAN_MATH_CLI_BIN";
const CARGO_CLEAN_BIN_ENV: &str = "CARGO_BIN_EXE_clean";
const OBLIGATION_ID: &str = "sha256:certificate-kernel-boundary";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn clean_binary() -> PathBuf {
    if let Some(binary) = env::var_os(CLEAN_MATH_CLI_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_MATH_CLI_BIN_ENV} points to {}, but it is not a file",
            binary.display()
        );
        return binary;
    }

    if let Some(binary) = env::var_os(CARGO_CLEAN_BIN_ENV)
        .map(PathBuf::from)
        .filter(|binary| binary.is_file())
    {
        return binary;
    }

    build_clean_binary()
}

fn build_clean_binary() -> PathBuf {
    let root = workspace_root();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let status = Command::new(cargo)
        .args(["build", "--quiet", "-p", "clean", "--bin", "clean"])
        .current_dir(&root)
        .env("CARGO_TERM_COLOR", "never")
        .status()
        .expect("cargo build -p clean --bin clean should start");
    assert!(status.success(), "failed to build clean binary: {status}");

    let binary = root
        .join("target")
        .join("debug")
        .join(format!("clean{}", env::consts::EXE_SUFFIX));
    assert!(
        binary.is_file(),
        "cargo build succeeded, but {} does not exist",
        binary.display()
    );
    binary
}

fn run_clean(args: &[&str]) -> Output {
    Command::new(clean_binary())
        .args(args)
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
}

fn run_clean_json(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        output.status.success(),
        "clean {args:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn run_clean_json_expect_failure(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        !output.status.success(),
        "clean {args:?} unexpectedly succeeded\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn parse_json(args: &[&str], output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "clean {args:?} did not emit JSON on stdout: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn write_project_with_evidence(root: &Path, evidence: Value) -> PathBuf {
    fs::create_dir_all(root.join("evidence")).expect("create evidence dir");
    fs::write(
        root.join("evidence").join("kernel.json"),
        serde_json::to_string_pretty(&evidence).expect("serialize evidence"),
    )
    .expect("write evidence");

    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": "certificate-kernel-boundary",
        "domain_profile": "sat-pb",
        "owner": "clean-math-factory",
        "theorem_packs": [],
        "obligation_sources": [],
        "artifact_formats": ["proof-artifact-v1"],
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "trustedAy", "synthetic_sorry"],
            "require_artifact_replay": true,
            "allow_synthetic_sorry": false
        },
        "normalizers": ["sat_pb_nf"],
        "evidence": ["evidence/kernel.json"],
        "issue_routing": {
            "labels": ["math-project", "sat-pb"],
            "owners": [],
            "blocking_categories": ["trust"]
        }
    });
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&project).expect("serialize project"),
    )
    .expect("write project");
    project_path
}

fn clean_trust_summary() -> Value {
    serde_json::json!({
        "sorry_count": 0,
        "ay_count": 0,
        "arith_count": 0,
        "kernel_check_failures": 0,
        "fully_verified": true
    })
}

fn server_generated_kernel_evidence_with_tactics(
    obligation_id: &str,
    theorem: &str,
    tactics: &[&str],
) -> Value {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("proof extraction runtime");

    runtime.block_on(async move {
        let state = ServerState::new().with_env(Environment::with_prelude());
        let init_response = handle_init_proof_state(
            &state,
            RequestId::Number(1),
            InitProofStateParams {
                theorem: theorem.to_owned(),
                problem_id: Some(obligation_id.to_owned()),
                timeout_ms: None,
            },
        )
        .await;
        assert!(
            init_response.error.is_none(),
            "initProofState failed: {:?}",
            init_response.error
        );
        let mut state_id = init_response.result.expect("init result")["state_id"]
            .as_str()
            .expect("state_id")
            .to_owned();

        for (idx, tactic) in tactics.iter().copied().enumerate() {
            let apply_response = handle_apply_tactic(
                &state,
                RequestId::Number(idx as i64 + 2),
                ApplyTacticParams {
                    state_id,
                    goal_id: "g0".to_owned(),
                    tactic: tactic.to_owned(),
                    timeout_ms: None,
                },
            )
            .await;
            assert!(
                apply_response.error.is_none(),
                "applyTactic {tactic} failed: {:?}",
                apply_response.error
            );
            let apply = apply_response.result.expect("apply result");
            assert_eq!(
                apply["success"], true,
                "applyTactic {tactic} should succeed"
            );
            state_id = apply["new_state_id"]
                .as_str()
                .expect("new_state_id")
                .to_owned();
        }

        let extract_response = handle_extract_proof(
            &state,
            RequestId::Number(100),
            ExtractProofParams {
                state_id,
                format: "kernel_evidence".to_owned(),
            },
        )
        .await;
        assert!(
            extract_response.error.is_none(),
            "extractProof kernel_evidence failed: {:?}",
            extract_response.error
        );
        extract_response.result.expect("kernel evidence result")
    })
}

fn server_generated_kernel_evidence(obligation_id: &str) -> Value {
    server_generated_kernel_evidence_with_tactics(
        obligation_id,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
}

fn server_generated_true_kernel_evidence(obligation_id: &str) -> Value {
    server_generated_kernel_evidence_with_tactics(obligation_id, "True", &["exact True.intro"])
}

struct GenericTrueProjectCase {
    project: &'static str,
    domain_profile: &'static str,
    producer_system: &'static str,
    producer_commit: &'static str,
    artifact_formats: &'static [&'static str],
    normalizers: &'static [&'static str],
    labels: &'static [&'static str],
}

const SAT_PB_ARTIFACT_FORMATS: &[&str] = &[
    "lrat",
    "drat",
    "veripb",
    "ay-theorem-export",
    "proof-artifact-v1",
];
const SAT_PB_NORMALIZERS: &[&str] = &["cert_simp", "cert_mathverse", "sat_pb_nf"];
const SAT_PB_LABELS: &[&str] = &["math-project", "sat-pb", "proof-factory"];
const NN_ARTIFACT_FORMATS: &[&str] = &[
    "gamma-crown-farkas-v1",
    "gamma-crown-linear-entailment-v1",
    "proof-artifact-v1",
];
const NN_NORMALIZERS: &[&str] = &["cert_simp", "cert_mathverse", "nn_interval_nf"];
const NN_LABELS: &[&str] = &["math-project", "nn-verify", "gamma-crown", "proof-factory"];

const GENERIC_TRUE_CASES: &[GenericTrueProjectCase] = &[
    GenericTrueProjectCase {
        project: "sat-pb-generic-true-kernel-boundary",
        domain_profile: "sat-pb",
        producer_system: "ay",
        producer_commit: "fixture-ay-generic-true-kernel-boundary",
        artifact_formats: SAT_PB_ARTIFACT_FORMATS,
        normalizers: SAT_PB_NORMALIZERS,
        labels: SAT_PB_LABELS,
    },
    GenericTrueProjectCase {
        project: "nn-verify-generic-true-kernel-boundary",
        domain_profile: "nn-verify",
        producer_system: "gamma-crown",
        producer_commit: "fixture-gamma-crown-generic-true-kernel-boundary",
        artifact_formats: NN_ARTIFACT_FORMATS,
        normalizers: NN_NORMALIZERS,
        labels: NN_LABELS,
    },
];

fn generic_true_obligation(case: &GenericTrueProjectCase) -> Value {
    serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": case.project,
        "domain_profile": case.domain_profile,
        "producer": {
            "system": case.producer_system,
            "commit": case.producer_commit
        },
        "goal": {
            "expr": serde_json::to_value(Expr::const_(Name::from_string("True"), vec![]))
                .expect("serialize True expr"),
            "pretty": "True"
        },
        "local_context": [],
        "side_conditions": [],
        "metadata": {
            "fixture": "generic-true-kernel-boundary",
            "fixture_role": "certificate-extract-boundary",
            "kernel_evidence_scope": "server-generated prelude proof payload linked by obligation fingerprint"
        },
        "trust_policy": "constructive-only"
    })
}

fn write_generic_true_project_with_evidence(
    root: &Path,
    case: &GenericTrueProjectCase,
    evidence: Value,
) -> (PathBuf, PathBuf, String) {
    fs::create_dir_all(root.join("obligations")).expect("create obligations dir");
    fs::create_dir_all(root.join("evidence")).expect("create evidence dir");

    let obligation_value = generic_true_obligation(case);
    let obligation: MathObligation =
        serde_json::from_value(obligation_value.clone()).expect("parse generic True obligation");
    let obligation_id = obligation_fingerprint(&obligation);
    let obligation_path = root.join("obligations").join("generic_true.json");
    fs::write(
        &obligation_path,
        serde_json::to_string_pretty(&obligation_value).expect("serialize obligation"),
    )
    .expect("write obligation");

    fs::write(
        root.join("evidence").join("certificate_evidence.json"),
        serde_json::to_string_pretty(&evidence).expect("serialize evidence"),
    )
    .expect("write evidence");

    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": case.project,
        "domain_profile": case.domain_profile,
        "owner": "clean-math-factory",
        "theorem_packs": [],
        "obligation_sources": ["obligations/generic_true.json"],
        "artifact_formats": case.artifact_formats,
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "trustedAy", "synthetic_sorry"],
            "require_artifact_replay": true,
            "allow_synthetic_sorry": false
        },
        "normalizers": case.normalizers,
        "evidence": ["evidence/certificate_evidence.json"],
        "issue_routing": {
            "labels": case.labels,
            "owners": [],
            "blocking_categories": ["manifest", "obligation", "artifact", "trust"]
        }
    });
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&project).expect("serialize project"),
    )
    .expect("write project");
    (project_path, obligation_path, obligation_id)
}

fn certificate_extract_args(project: &Path) -> Vec<String> {
    vec![
        "math".to_owned(),
        "certificate".to_owned(),
        "extract".to_owned(),
        "--project".to_owned(),
        project.to_str().expect("utf8 project path").to_owned(),
        "--obligation".to_owned(),
        OBLIGATION_ID.to_owned(),
        "--json".to_owned(),
    ]
}

fn string_args(args: &[String]) -> Vec<&str> {
    args.iter().map(String::as_str).collect()
}

#[test]
fn certificate_extract_closes_on_server_generated_kernel_evidence() {
    let temp = tempfile::tempdir().expect("tempdir");
    let case = &GENERIC_TRUE_CASES[0];
    let obligation_value = generic_true_obligation(case);
    let obligation: MathObligation =
        serde_json::from_value(obligation_value).expect("parse generic True obligation");
    let obligation_id = obligation_fingerprint(&obligation);
    let evidence = server_generated_true_kernel_evidence(&obligation_id);
    assert_eq!(evidence["schema_version"], "clean-math-kernel-evidence-v1");
    assert_eq!(evidence["obligation"], obligation_id);
    assert_eq!(evidence["checked"], true);
    assert_eq!(evidence["trust_summary"]["fully_verified"], true);
    assert!(evidence.get("checked_proof_expr").is_some());
    assert!(evidence.get("checked_target_expr").is_some());
    assert!(evidence.get("proof_certificate").is_some());
    let (project, obligation_path, _) =
        write_generic_true_project_with_evidence(temp.path(), case, evidence);

    let report = run_clean_json(&[
        "math",
        "certificate",
        "extract",
        "--project",
        project.to_str().expect("utf8 project path"),
        "--obligation",
        obligation_path.to_str().expect("utf8 obligation path"),
        "--json",
    ]);

    assert_eq!(report["obligation"], obligation_id);
    assert_eq!(report["proof_status"], "closed");
    assert_eq!(report["evidence_kind"], "kernel_checked");
    assert_eq!(report["kernel_certified"], true);
    assert_eq!(report["kernel_evidence"]["checked"], true);
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "checked-kernel-proof"
    );
}

#[test]
fn certificate_extract_closes_server_kernel_evidence_linked_to_generic_true_for_sat_pb_and_nn_profiles(
) {
    for case in GENERIC_TRUE_CASES {
        let temp = tempfile::tempdir().expect("tempdir");
        let obligation_value = generic_true_obligation(case);
        let obligation: MathObligation =
            serde_json::from_value(obligation_value).expect("parse generic True obligation");
        let obligation_id = obligation_fingerprint(&obligation);
        let evidence = server_generated_true_kernel_evidence(&obligation_id);
        assert_eq!(evidence["schema_version"], "clean-math-kernel-evidence-v1");
        assert_eq!(evidence["obligation"], obligation_id);
        assert_eq!(evidence["checked"], true);
        assert_eq!(evidence["trust_summary"]["fully_verified"], true);
        assert!(evidence.get("checked_proof_expr").is_some());
        assert!(evidence.get("checked_target_expr").is_some());
        assert!(evidence.get("proof_certificate").is_some());
        let (project, obligation_path, fingerprint) =
            write_generic_true_project_with_evidence(temp.path(), case, evidence);

        let report = run_clean_json(&[
            "math",
            "certificate",
            "extract",
            "--project",
            project.to_str().expect("utf8 project path"),
            "--obligation",
            obligation_path.to_str().expect("utf8 obligation path"),
            "--json",
        ]);

        assert_eq!(fingerprint, obligation_id);
        assert_eq!(report["project"], case.project);
        assert_eq!(report["domain_profile"], case.domain_profile);
        assert_eq!(report["obligation"], obligation_id);
        assert_eq!(report["proof_status"], "closed");
        assert_eq!(report["evidence_kind"], "kernel_checked");
        assert_eq!(report["kernel_certified"], true);
        assert_eq!(report["kernel_evidence"]["checked"], true);
        assert_eq!(
            report["trust_summary"]["kernel_certification_status"],
            "checked-kernel-proof"
        );
    }
}

#[test]
fn certificate_extract_rejects_kernel_evidence_for_different_obligation_goal() {
    let temp = tempfile::tempdir().expect("tempdir");
    let case = &GENERIC_TRUE_CASES[0];
    let obligation_value = generic_true_obligation(case);
    let obligation: MathObligation =
        serde_json::from_value(obligation_value).expect("parse generic True obligation");
    let obligation_id = obligation_fingerprint(&obligation);
    let evidence = server_generated_kernel_evidence(&obligation_id);
    let (project, obligation_path, _) =
        write_generic_true_project_with_evidence(temp.path(), case, evidence);

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        project.to_str().expect("utf8 project path"),
        "--obligation",
        obligation_path.to_str().expect("utf8 obligation path"),
        "--json",
    ]);

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-obligation-goal-mismatch"
    );
    assert!(report.get("kernel_evidence").is_none());
}

#[test]
fn certificate_extract_rejects_kernel_evidence_with_trusted_proof_expr_even_when_summary_clean() {
    let temp = tempfile::tempdir().expect("tempdir");
    let case = &GENERIC_TRUE_CASES[0];
    let obligation_value = generic_true_obligation(case);
    let obligation: MathObligation =
        serde_json::from_value(obligation_value).expect("parse generic True obligation");
    let obligation_id = obligation_fingerprint(&obligation);
    let mut evidence = server_generated_true_kernel_evidence(&obligation_id);
    evidence["checked_proof_expr"] = serde_json::to_value(Expr::const_(
        Name::from_string("trustedArith"),
        vec![Level::zero()],
    ))
    .expect("serialize trustedArith proof marker");
    evidence["trust_summary"] = clean_trust_summary();
    let (project, obligation_path, _) =
        write_generic_true_project_with_evidence(temp.path(), case, evidence);

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        project.to_str().expect("utf8 project path"),
        "--obligation",
        obligation_path.to_str().expect("utf8 obligation path"),
        "--json",
    ]);

    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-trust-debt"
    );
    assert!(report.get("kernel_evidence").is_none());
}

#[test]
fn certificate_extract_keeps_replay_only_generic_true_evidence_non_closure_for_sat_pb_and_nn() {
    for case in GENERIC_TRUE_CASES {
        let temp = tempfile::tempdir().expect("tempdir");
        let obligation_value = generic_true_obligation(case);
        let obligation: MathObligation =
            serde_json::from_value(obligation_value).expect("parse generic True obligation");
        let obligation_id = obligation_fingerprint(&obligation);
        let replay_only_evidence = serde_json::json!({
            "schema_version": "clean-artifact-replay-report-v1",
            "artifact_path": "artifacts/replay-only.json",
            "project": case.project,
            "source_system": case.producer_system,
            "artifact_kind": "proof-artifact-v1",
            "problem_hash": obligation_id,
            "proof_hash": "sha256:generic-true-replay-only-proof",
            "certificate_format": "proof-artifact-v1",
            "evidence_kind": "replay_only",
            "kernel_certified": false,
            "replay_status": "pass",
            "replay_adapter": "fixture-replay-only",
            "linked_obligations": [obligation_id],
            "trusted_assumptions": [],
            "details": []
        });
        let (project, obligation_path, fingerprint) =
            write_generic_true_project_with_evidence(temp.path(), case, replay_only_evidence);

        let report = run_clean_json_expect_failure(&[
            "math",
            "certificate",
            "extract",
            "--project",
            project.to_str().expect("utf8 project path"),
            "--obligation",
            obligation_path.to_str().expect("utf8 obligation path"),
            "--json",
        ]);

        assert_eq!(fingerprint, obligation_id);
        assert_eq!(report["project"], case.project);
        assert_eq!(report["domain_profile"], case.domain_profile);
        assert_eq!(report["obligation"], obligation_id);
        assert_ne!(report["proof_status"], "closed");
        assert_eq!(report["evidence_kind"], "none");
        assert_eq!(report["kernel_certified"], false);
        assert!(report.get("kernel_evidence").is_none());
        assert_eq!(report["trust_summary"]["kernel_certified"], false);
    }
}

#[test]
fn certificate_extract_rejects_self_attested_kernel_evidence_without_replay_material() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-math-kernel-evidence-v1",
            "project": "certificate-kernel-boundary",
            "obligation": OBLIGATION_ID,
            "theorem": "CertificateKernelBoundary.selfAttested",
            "proof_hash": "sha256:self-attested-proof",
            "checker": "clean-kernel:claimed",
            "source": "clean-kernel:claimed",
            "checked": true,
            "trust_summary": clean_trust_summary()
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-incomplete"
    );
}

#[test]
fn certificate_extract_keeps_proof_state_extract_evidence_diagnostic_only() {
    let temp = tempfile::tempdir().expect("tempdir");
    let proof_expr = Expr::const_(Name::from_string("True.intro"), vec![]);
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "obligation": OBLIGATION_ID,
            "is_solved": true,
            "proof_expr": proof_expr,
            "verification": {
                "verified": true,
                "time_us": 12,
                "time_ns": 12000
            },
            "trust_summary": clean_trust_summary()
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["evidence_kind"], "none");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-proof-state-diagnostic-only"
    );
}

#[test]
fn certificate_extract_rejects_forged_proof_state_json_as_kernel_closure() {
    let temp = tempfile::tempdir().expect("tempdir");
    let forged_proof_expr = Expr::const_(Name::from_string("Forged.closed"), vec![]);
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "obligation": OBLIGATION_ID,
            "is_solved": true,
            "proof_expr": forged_proof_expr,
            "verification": {
                "verified": true,
                "time_us": 1,
                "time_ns": 1000
            },
            "checker": "clean-kernel:proof-state-extract",
            "source": "proof-state:forged-fixture",
            "trust_summary": clean_trust_summary()
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-proof-state-diagnostic-only"
    );
}

#[test]
fn certificate_extract_rejects_checked_proof_state_with_hidden_trust_debt() {
    let temp = tempfile::tempdir().expect("tempdir");
    let proof_expr = Expr::const_(Name::from_string("True.intro"), vec![]);
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "obligation": OBLIGATION_ID,
            "is_solved": true,
            "proof_expr": proof_expr,
            "verification": {
                "verified": true,
                "time_us": 12,
                "time_ns": 12000
            },
            "trust_summary": {
                "sorry_count": 1,
                "sorry_provenance": {
                    "has_explicit_sorry": false,
                    "has_synthetic_sorry": true
                },
                "ay_count": 0,
                "arith_count": 0,
                "kernel_check_failures": 0,
                "fully_verified": false
            },
            "metadata": {
                "trust_marker": "synthetic_sorry"
            }
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-trust-debt"
    );
}

#[test]
fn certificate_extract_rejects_checked_kernel_evidence_without_trust_summary() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-math-kernel-evidence-v1",
            "project": "certificate-kernel-boundary",
            "obligation": OBLIGATION_ID,
            "theorem": "CertificateKernelBoundary.checkedButNoTrustSummary",
            "proof_hash": "sha256:checked-no-trust-summary",
            "checker": "clean-kernel:local",
            "source": "kernel-evidence:test-fixture",
            "checked": true
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-missing-trust-summary"
    );
}

#[test]
fn certificate_extract_rejects_nested_kernel_evidence_for_other_obligation() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema": "clean-math-certificate-v1",
            "obligation": OBLIGATION_ID,
            "kernel_evidence": {
                "obligation": "sha256:other-obligation",
                "theorem": "CertificateKernelBoundary.wrong",
                "proof_hash": "sha256:checked-but-wrong-obligation",
                "checker": "clean-kernel:local",
                "source": "kernel-evidence:test-fixture",
                "checked": true,
                "trust_summary": clean_trust_summary()
            }
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-obligation-mismatch"
    );
}

#[test]
fn certificate_extract_rejects_nested_kernel_evidence_hidden_trust_debt() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema": "clean-math-certificate-v1",
            "obligation": OBLIGATION_ID,
            "kernel_evidence": {
                "theorem": "CertificateKernelBoundary.hiddenTrustDebt",
                "proof_hash": "sha256:checked-with-hidden-debt",
                "checker": "clean-kernel:local",
                "source": "kernel-evidence:test-fixture",
                "checked": true,
                "metadata": {
                    "trust_marker": "trustedAy"
                },
                "trust_summary": clean_trust_summary()
            }
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "kernel-evidence-trust-debt"
    );
}

#[test]
fn certificate_extract_does_not_close_manifest_kernel_evidence_over_unlinked_artifact() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-math-kernel-evidence-v1",
            "project": "certificate-kernel-boundary",
            "obligation": OBLIGATION_ID,
            "theorem": "CertificateKernelBoundary.closed",
            "proof_hash": "sha256:checked-explicit-proof",
            "checker": "clean-kernel:local",
            "source": "kernel-evidence:test-fixture",
            "checked": true,
            "trust_summary": clean_trust_summary()
        }),
    );
    let mut args = certificate_extract_args(&project);
    args.push("--artifact".to_owned());
    args.push(
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_checked.json"
            .to_owned(),
    );

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_eq!(report["proof_status"], "replayed-artifact-unlinked");
    assert_eq!(report["kernel_certified"], false);
    assert_eq!(
        report["trust_summary"]["artifact_evidence_status"],
        "replayed-artifact-unlinked"
    );
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "artifact-evidence-unlinked"
    );
}

#[test]
fn certificate_extract_does_not_close_manifest_kernel_evidence_over_failed_artifact() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-math-kernel-evidence-v1",
            "project": "certificate-kernel-boundary",
            "obligation": OBLIGATION_ID,
            "theorem": "CertificateKernelBoundary.closed",
            "proof_hash": "sha256:checked-explicit-proof",
            "checker": "clean-kernel:local",
            "source": "kernel-evidence:test-fixture",
            "checked": true,
            "trust_summary": clean_trust_summary()
        }),
    );
    let mut args = certificate_extract_args(&project);
    args.push("--artifact".to_owned());
    args.push(
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_malformed.json"
            .to_owned(),
    );

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_eq!(report["proof_status"], "artifact-replay-failed");
    assert_eq!(report["kernel_certified"], false);
    assert_eq!(
        report["trust_summary"]["artifact_evidence_status"],
        "artifact-replay-failed"
    );
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "artifact-evidence-replay-failed"
    );
}

#[test]
fn certificate_extract_enforces_project_profile_for_artifact_replay() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-math-kernel-evidence-v1",
            "project": "certificate-kernel-boundary",
            "obligation": OBLIGATION_ID,
            "theorem": "CertificateKernelBoundary.closed",
            "proof_hash": "sha256:checked-explicit-proof",
            "checker": "clean-kernel:local",
            "source": "kernel-evidence:test-fixture",
            "checked": true,
            "trust_summary": clean_trust_summary()
        }),
    );
    let mut args = certificate_extract_args(&project);
    args.push("--artifact".to_owned());
    args.push(
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json"
            .to_owned(),
    );

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_eq!(report["proof_status"], "artifact-replay-blocked");
    assert_eq!(
        report["trust_summary"]["artifact_evidence_status"],
        "artifact-replay-blocked"
    );
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "artifact-evidence-replay-blocked"
    );
    assert!(report["trust_summary"]["artifact_evidence_diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .any(|diagnostic| diagnostic["code"] == "AR001"));
}

#[test]
fn certificate_extract_does_not_promote_replay_only_evidence_to_kernel_closed() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_project_with_evidence(
        temp.path(),
        serde_json::json!({
            "schema_version": "clean-artifact-replay-report-v1",
            "artifact_path": "artifacts/proof.json",
            "project": "certificate-kernel-boundary",
            "source_system": "fixture",
            "artifact_kind": "proof-artifact-v1",
            "problem_hash": "sha256:problem",
            "proof_hash": "sha256:replay-only-proof",
            "certificate_format": "proof-artifact-v1",
            "evidence_kind": "replay_only",
            "kernel_certified": false,
            "replay_status": "pass",
            "replay_adapter": "fixture",
            "linked_obligations": [OBLIGATION_ID],
            "trusted_assumptions": [],
            "details": []
        }),
    );
    let args = certificate_extract_args(&project);

    let report = run_clean_json_expect_failure(&string_args(&args));

    assert_ne!(report["proof_status"], "closed");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(report["trust_summary"]["kernel_certified"], false);
}
