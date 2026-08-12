// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_mathverse::attempt_log::{
    append_authority_attempt_to, append_to, artifact_path, iter_from,
    prepare_replay_attempt_with_env, prepare_replay_attempt_with_env_and_result, put_artifact,
    query_attempts_limited, read_artifact, record_authority_gate_attempt, record_replay_attempt,
    since_duration_lower_bound_ns, validate_replay_binding, ArtifactRef, AttemptBudget,
    AttemptContext, AttemptFilter, AttemptId, AttemptProducer, AttemptStatus, AttemptStatusFilter,
    AuthorityGateAttempt, ProducerKind, ProofAttempt, ReplayAttemptResult,
    ReplayBindingValidationOptions, ReplayOptions, StateId,
};
use clean_mathverse::env_fingerprint::EnvFingerprint;
use clean_mathverse::types::TrustLevel;
use std::collections::BTreeSet;
use std::thread;

fn test_env() -> EnvFingerprint {
    EnvFingerprint {
        lean_toolchain: "leanprover/lean4:v4.18.0".to_owned(),
        clean_commit: "0123456789abcdef0123456789abcdef01234567".to_owned(),
        ay_revision: Some("tag:v0.10.1".to_owned()),
        llvm2_revision: None,
        host_arch: "test-arch".to_owned(),
        host_os: "test-os".to_owned(),
        solver_binaries: Vec::new(),
    }
}

fn hash(label: &str) -> String {
    blake3::hash(label.as_bytes()).to_hex().to_string()
}

fn attempt(status: AttemptStatus, env: EnvFingerprint, offset: u64) -> ProofAttempt {
    let mut attempt =
        ProofAttempt::new(hash("goal"), status, hash(&format!("audit-{offset}")), env);
    attempt.created_at = 1_700_000_000_000_000_000 + offset;
    attempt.wall_time_ms = 10 + offset / 1_000_000;
    attempt.proof_state_before = Some(StateId::from(format!("state-before-{offset}")));
    attempt.proof_state_after = Some(StateId::from(format!("state-after-{offset}")));
    attempt
}

fn replay_bound_authority_artifacts(root: &std::path::Path) -> (ArtifactRef, ArtifactRef) {
    let solver_artifact = put_artifact(
        root,
        b"authority solver report",
        Some("solver/lrat"),
        Some("authority.lrat"),
    )
    .expect("put solver artifact");
    let command_evidence = put_artifact(
        root,
        b"$ clean authority gate\naccepted\n",
        Some("command/transcript"),
        Some("authority-command.txt"),
    )
    .expect("put command evidence");
    (solver_artifact, command_evidence)
}

#[test]
fn accept_reject_timeout_attempts_round_trip_with_artifacts() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();

    let solver_artifact = put_artifact(
        root,
        b"drat proof bytes",
        Some("solver/drat"),
        Some("attempt.drat"),
    )
    .expect("put solver artifact");
    let model_response = put_artifact(
        root,
        br#"{"model":"mathverse-test","proof":"intro"}"#,
        Some("model/json"),
        Some("response.json"),
    )
    .expect("put model artifact");

    let mut accepted = attempt(AttemptStatus::Accepted, env.clone(), 0);
    accepted.solver_artifact = Some(solver_artifact.clone());
    accepted.model_response = Some(model_response.clone());
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.budget = Some(AttemptBudget {
        wall_time_ms: Some(5_000),
        solver_ms: Some(8),
        tokens: Some(512),
        hardware: Some("ci-x86_64".to_owned()),
    });

    let mut rejected = attempt(
        AttemptStatus::Rejected {
            reason: "kernel-type-mismatch".to_owned(),
        },
        env.clone(),
        1_000_000,
    );
    rejected.authority_gate = Some("native_authority_gate".to_owned());
    rejected.failure_mode = Some("kernel_type_mismatch".to_owned());
    rejected.trust_level = Some(TrustLevel::PartiallyAxiomatized);
    rejected.budget = Some(AttemptBudget {
        wall_time_ms: Some(5_000),
        solver_ms: Some(15),
        tokens: Some(768),
        hardware: Some("ci-x86_64".to_owned()),
    });

    let mut timeout = attempt(
        AttemptStatus::Timeout { after_ms: 5_000 },
        env.clone(),
        2_000_000,
    );
    timeout.authority_gate = Some("native_authority_gate".to_owned());
    timeout.failure_mode = Some("timeout".to_owned());
    timeout.trust_level = Some(TrustLevel::TrustedOracle);
    timeout.budget = Some(AttemptBudget {
        wall_time_ms: Some(5_000),
        solver_ms: Some(5_000),
        tokens: None,
        hardware: Some("ci-x86_64".to_owned()),
    });

    append_to(root, &accepted).expect("append accepted");
    append_to(root, &rejected).expect("append rejected");
    append_to(root, &timeout).expect("append timeout");

    let attempts: Vec<_> = iter_from(root, AttemptFilter::default())
        .expect("iter attempts")
        .collect();
    assert_eq!(attempts.len(), 3);
    assert_eq!(attempts[0], accepted);
    assert_eq!(attempts[1], rejected);
    assert_eq!(attempts[2], timeout);
    assert!(attempts.iter().all(|attempt| attempt.env == env));
    assert_eq!(
        attempts[0].budget.as_ref().and_then(|budget| budget.tokens),
        Some(512)
    );
    assert_eq!(
        attempts[1].failure_mode.as_deref(),
        Some("kernel_type_mismatch")
    );
    assert_eq!(attempts[2].failure_mode.as_deref(), Some("timeout"));

    let rejected_only: Vec<_> = iter_from(
        root,
        AttemptFilter {
            status: Some(AttemptStatusFilter::Rejected),
            ..AttemptFilter::default()
        },
    )
    .expect("iter rejected")
    .collect();
    assert_eq!(rejected_only, vec![rejected.clone()]);

    let gate_only: Vec<_> = iter_from(
        root,
        AttemptFilter {
            authority_gate: Some("native_authority_gate".to_owned()),
            ..AttemptFilter::default()
        },
    )
    .expect("iter gate attempts")
    .collect();
    assert_eq!(gate_only.len(), 3);

    let kernel_mismatch_only: Vec<_> = iter_from(
        root,
        AttemptFilter {
            failure_mode: Some("kernel_type_mismatch".to_owned()),
            ..AttemptFilter::default()
        },
    )
    .expect("iter failure mode")
    .collect();
    assert_eq!(kernel_mismatch_only, vec![rejected.clone()]);

    let kernel_verified_only: Vec<_> = iter_from(
        root,
        AttemptFilter {
            trust_level: Some(TrustLevel::KernelVerified),
            ..AttemptFilter::default()
        },
    )
    .expect("iter trust level")
    .collect();
    assert_eq!(kernel_verified_only, vec![accepted.clone()]);

    assert!(artifact_path(root, &solver_artifact).is_file());
    assert!(artifact_path(root, &model_response).is_file());
    assert_eq!(
        read_artifact(root, &solver_artifact).expect("read solver artifact"),
        b"drat proof bytes"
    );
    assert_eq!(
        read_artifact(root, &model_response).expect("read model artifact"),
        br#"{"model":"mathverse-test","proof":"intro"}"#
    );

    let log_path = root.join(".cake/attempts/2023-11-14.jsonl");
    assert!(log_path.is_file());
}

#[test]
fn concurrent_attempt_appends_preserve_complete_jsonl_records() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().to_path_buf();
    let env = test_env();
    let base_ns = 1_700_000_000_000_000_000;
    let attempt_count = 96;

    let expected_audits: BTreeSet<_> = (0..attempt_count)
        .map(|index| hash(&format!("audit-{index}")))
        .collect();

    let handles: Vec<_> = (0..attempt_count)
        .map(|index| {
            let root = root.clone();
            let env = env.clone();
            thread::spawn(move || {
                let mut attempt = ProofAttempt::new(
                    hash(&format!("goal-{index}")),
                    AttemptStatus::Accepted,
                    hash(&format!("audit-{index}")),
                    env,
                );
                attempt.created_at = base_ns + index;
                append_to(&root, &attempt).expect("append concurrent attempt");
            })
        })
        .collect();

    for handle in handles {
        handle.join().expect("append thread should not panic");
    }

    let attempts: Vec<_> = iter_from(&root, AttemptFilter::default())
        .expect("iter concurrent attempts")
        .collect();
    assert_eq!(attempts.len(), attempt_count as usize);

    let actual_audits: BTreeSet<_> = attempts
        .iter()
        .map(|attempt| attempt.trust_audit_hash.clone())
        .collect();
    assert_eq!(actual_audits, expected_audits);

    let log_path = root.join(".cake/attempts/2023-11-14.jsonl");
    let line_count = std::fs::read_to_string(&log_path)
        .expect("read attempt log")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .count();
    assert_eq!(line_count, attempt_count as usize);
}

#[test]
fn authority_gate_helper_records_append_only_attempts_with_metadata() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let (accepted_solver_artifact, accepted_command_evidence) =
        replay_bound_authority_artifacts(root);

    let accepted = AuthorityGateAttempt {
        wall_time_ms: 11,
        solver_artifact: Some(accepted_solver_artifact),
        command_evidence: Some(accepted_command_evidence),
        trust_level: Some(TrustLevel::KernelVerified),
        budget: Some(AttemptBudget {
            wall_time_ms: Some(1_000),
            solver_ms: Some(3),
            tokens: None,
            hardware: Some("gate-ci".to_owned()),
        }),
        ..AuthorityGateAttempt::new(
            "trust_audit",
            hash("accepted-gate-goal"),
            AttemptStatus::Accepted,
            hash("accepted-gate-audit"),
            env.clone(),
        )
    };
    let rejected = AuthorityGateAttempt {
        wall_time_ms: 12,
        failure_mode: Some("audit_delta_regression".to_owned()),
        trust_level: Some(TrustLevel::PartiallyAxiomatized),
        ..AuthorityGateAttempt::new(
            "trust_audit",
            hash("rejected-gate-goal"),
            AttemptStatus::Rejected {
                reason: "trust audit introduced new oracle dependency".to_owned(),
            },
            hash("rejected-gate-audit"),
            env.clone(),
        )
    };
    let timeout = AuthorityGateAttempt {
        wall_time_ms: 1_000,
        failure_mode: Some("timeout".to_owned()),
        trust_level: Some(TrustLevel::TrustedOracle),
        budget: Some(AttemptBudget {
            wall_time_ms: Some(1_000),
            solver_ms: Some(1_000),
            tokens: Some(128),
            hardware: Some("gate-ci".to_owned()),
        }),
        ..AuthorityGateAttempt::new(
            "statement_preservation",
            hash("timeout-gate-goal"),
            AttemptStatus::Timeout { after_ms: 1_000 },
            hash("timeout-gate-audit"),
            env,
        )
    };

    let accepted = record_authority_gate_attempt(root, accepted).expect("record accepted gate");
    let rejected = record_authority_gate_attempt(root, rejected).expect("record rejected gate");
    let timeout = record_authority_gate_attempt(root, timeout).expect("record timeout gate");

    let attempts: Vec<_> = iter_from(root, AttemptFilter::default())
        .expect("iter attempts")
        .collect();
    assert_eq!(attempts, vec![accepted.clone(), rejected.clone(), timeout]);
    assert_eq!(attempts[0].authority_gate.as_deref(), Some("trust_audit"));
    assert_eq!(
        attempts[1].failure_mode.as_deref(),
        Some("audit_delta_regression")
    );
    assert_eq!(
        attempts[2].budget.as_ref().and_then(|budget| budget.tokens),
        Some(128)
    );

    let rejected_trust_audit: Vec<_> = iter_from(
        root,
        AttemptFilter {
            authority_gate: Some("trust_audit".to_owned()),
            status: Some(AttemptStatusFilter::Rejected),
            failure_mode: Some("audit_delta_regression".to_owned()),
            ..AttemptFilter::default()
        },
    )
    .expect("iter rejected trust-audit gate")
    .collect();
    assert_eq!(rejected_trust_audit, vec![rejected]);

    let err = record_authority_gate_attempt(
        root,
        AuthorityGateAttempt::new(
            " ",
            hash("bad-gate-goal"),
            AttemptStatus::Accepted,
            hash("bad-gate-audit"),
            test_env(),
        ),
    )
    .expect_err("empty gate name should fail");
    assert!(err.to_string().contains("non-empty gate name"));
}

#[test]
fn replay_binding_validation_accepts_reproducible_accepted_attempts() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let solver_artifact = put_artifact(
        root,
        b"checked solver proof",
        Some("solver/lrat"),
        Some("proof.lrat"),
    )
    .expect("put solver artifact");

    let mut accepted = attempt(AttemptStatus::Accepted, env.clone(), 0);
    accepted.solver_artifact = Some(solver_artifact);
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.producer = Some(AttemptProducer {
        producer_kind: ProducerKind::Solver,
        provider: "clean-ci".to_owned(),
        name: "native-replay".to_owned(),
        version: Some("v1".to_owned()),
        command_digest: Some(hash("native-replay-command")),
    });

    validate_replay_binding(
        &accepted,
        ReplayBindingValidationOptions {
            allow_non_accepted: false,
            require_policy_metadata: true,
        },
    )
    .expect("accepted replay binding should validate");

    let transcript = put_artifact(
        root,
        b"$ clean mathverse replay --attempt abc\naccepted\n",
        Some("command/transcript"),
        Some("replay.txt"),
    )
    .expect("put transcript artifact");
    let mut transcript_bound = accepted;
    transcript_bound.producer = None;
    transcript_bound.command_evidence = Some(transcript);

    validate_replay_binding(
        &transcript_bound,
        ReplayBindingValidationOptions {
            allow_non_accepted: false,
            require_policy_metadata: true,
        },
    )
    .expect("command transcript artifact should satisfy command binding");
}

#[test]
fn authority_append_replay_binding_rejects_missing_command_evidence() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let (solver_artifact, _) = replay_bound_authority_artifacts(root);

    let mut accepted = attempt(AttemptStatus::Accepted, env, 0);
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.solver_artifact = Some(solver_artifact);

    let err = append_authority_attempt_to(root, &accepted)
        .expect_err("accepted authority attempt missing command binding should fail");
    assert!(err.to_string().contains("command digest"));
}

#[test]
fn authority_append_replay_binding_accepts_command_evidence() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let (solver_artifact, command_evidence) = replay_bound_authority_artifacts(root);

    let mut accepted = attempt(AttemptStatus::Accepted, env, 0);
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.solver_artifact = Some(solver_artifact);
    accepted.command_evidence = Some(command_evidence);

    append_authority_attempt_to(root, &accepted)
        .expect("accepted authority attempt with command evidence should append");
}

#[test]
fn authority_append_replay_binding_rejects_zero_byte_command_evidence() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let (solver_artifact, _) = replay_bound_authority_artifacts(root);

    let mut accepted = attempt(AttemptStatus::Accepted, env, 0);
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.solver_artifact = Some(solver_artifact);
    accepted.command_evidence = Some(ArtifactRef {
        blake3: hash("empty-command-evidence"),
        byte_len: 0,
        kind: Some("command/transcript".to_owned()),
        logical_name: Some("authority-command.txt".to_owned()),
    });

    let err = append_authority_attempt_to(root, &accepted)
        .expect_err("zero-byte command evidence should fail");
    assert!(err.to_string().contains("non-zero byte_len"));
}

#[test]
fn replay_binding_validation_fails_closed_for_incomplete_accepted_attempts() {
    let mut accepted = attempt(AttemptStatus::Accepted, test_env(), 0);

    let err = validate_replay_binding(&accepted, ReplayBindingValidationOptions::default())
        .expect_err("missing command binding should fail");
    assert!(err.to_string().contains("command digest"));

    accepted.producer = Some(AttemptProducer {
        producer_kind: ProducerKind::Solver,
        provider: "clean-ci".to_owned(),
        name: "native-replay".to_owned(),
        version: None,
        command_digest: Some(hash("native-replay-command")),
    });
    let err = validate_replay_binding(&accepted, ReplayBindingValidationOptions::default())
        .expect_err("missing solver artifact should fail");
    assert!(err.to_string().contains("solver/proof artifact"));

    accepted.solver_artifact = Some(ArtifactRef {
        blake3: hash("empty-proof"),
        byte_len: 0,
        kind: Some("solver/lrat".to_owned()),
        logical_name: Some("proof.lrat".to_owned()),
    });
    let err = validate_replay_binding(&accepted, ReplayBindingValidationOptions::default())
        .expect_err("zero-length solver artifact should fail");
    assert!(err.to_string().contains("non-zero byte_len"));

    accepted.solver_artifact = Some(ArtifactRef {
        blake3: hash("proof"),
        byte_len: 5,
        kind: Some("solver/lrat".to_owned()),
        logical_name: Some("proof.lrat".to_owned()),
    });
    let err = validate_replay_binding(
        &accepted,
        ReplayBindingValidationOptions {
            allow_non_accepted: false,
            require_policy_metadata: true,
        },
    )
    .expect_err("missing required policy metadata should fail");
    assert!(err.to_string().contains("policy metadata"));
}

#[test]
fn replay_binding_validation_can_skip_non_accepted_attempts() {
    let rejected = attempt(
        AttemptStatus::Rejected {
            reason: "kernel mismatch".to_owned(),
        },
        test_env(),
        0,
    );

    let err = validate_replay_binding(&rejected, ReplayBindingValidationOptions::default())
        .expect_err("rejected attempts should fail closed by default");
    assert!(err.to_string().contains("not accepted"));

    validate_replay_binding(
        &rejected,
        ReplayBindingValidationOptions {
            allow_non_accepted: true,
            require_policy_metadata: true,
        },
    )
    .expect("caller can skip rejected attempts");
}

#[test]
fn status_parse_and_since_query_return_json_safe_report() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let base_ns = 1_700_000_000_000_000_000;

    let accepted = attempt(AttemptStatus::Accepted, env.clone(), 0);
    let rejected = attempt(
        AttemptStatus::Rejected {
            reason: "kernel-type-mismatch".to_owned(),
        },
        env.clone(),
        1_000_000,
    );
    let timeout = attempt(AttemptStatus::Timeout { after_ms: 5_000 }, env, 2_000_000);

    append_to(root, &accepted).expect("append accepted");
    append_to(root, &rejected).expect("append rejected");
    append_to(root, &timeout).expect("append timeout");

    let since_ns =
        since_duration_lower_bound_ns(base_ns + 3_000_000, "2ms").expect("parse since duration");
    let report = query_attempts_limited(
        root,
        AttemptFilter {
            status: Some("rejected".parse().expect("parse status")),
            since_ns: Some(since_ns),
            ..AttemptFilter::default()
        },
        Some(10),
    )
    .expect("query attempts");

    assert_eq!(report.total, 1);
    assert_eq!(report.returned, 1);
    assert_eq!(report.attempts, vec![rejected]);
    assert_eq!(report.filter.status, Some(AttemptStatusFilter::Rejected));
    serde_json::to_string(&report).expect("query report should serialize");

    let timeout_filter: AttemptStatusFilter = "timed-out".parse().expect("parse timeout alias");
    assert_eq!(timeout_filter, AttemptStatusFilter::Timeout);
    assert!("unknown".parse::<AttemptStatusFilter>().is_err());
    assert!(since_duration_lower_bound_ns(base_ns, "7x").is_err());
}

#[test]
fn query_report_filters_and_summarizes_attempt_metadata() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();

    let mut accepted = attempt(AttemptStatus::Accepted, env.clone(), 0);
    accepted.authority_gate = Some("native_authority_gate".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);

    let mut rejected = attempt(
        AttemptStatus::Rejected {
            reason: "kernel-type-mismatch".to_owned(),
        },
        env.clone(),
        1_000_000,
    );
    rejected.authority_gate = Some("native_authority_gate".to_owned());
    rejected.failure_mode = Some("kernel_type_mismatch".to_owned());
    rejected.trust_level = Some(TrustLevel::PartiallyAxiomatized);

    let mut timeout = attempt(
        AttemptStatus::Timeout { after_ms: 5_000 },
        env.clone(),
        2_000_000,
    );
    timeout.authority_gate = Some("statement_preservation".to_owned());
    timeout.failure_mode = Some("timeout".to_owned());
    timeout.trust_level = Some(TrustLevel::TrustedOracle);

    let no_metadata = attempt(AttemptStatus::Accepted, env, 3_000_000);

    append_to(root, &accepted).expect("append accepted");
    append_to(root, &rejected).expect("append rejected");
    append_to(root, &timeout).expect("append timeout");
    append_to(root, &no_metadata).expect("append no metadata");

    let limited = query_attempts_limited(root, AttemptFilter::default(), Some(2))
        .expect("query limited attempts");

    assert_eq!(limited.total, 4);
    assert_eq!(limited.returned, 2);
    assert_eq!(limited.summary.by_status["accepted"], 2);
    assert_eq!(
        limited.summary.by_authority_gate["native_authority_gate"],
        2
    );
    assert_eq!(
        limited.summary.by_authority_gate["statement_preservation"],
        1
    );
    assert_eq!(limited.summary.by_failure_mode["kernel_type_mismatch"], 1);
    assert_eq!(limited.summary.by_failure_mode["timeout"], 1);
    assert_eq!(limited.summary.by_trust_level["KernelVerified"], 1);
    assert_eq!(limited.summary.by_trust_level["PartiallyAxiomatized"], 1);
    assert_eq!(limited.summary.by_trust_level["TrustedOracle"], 1);
    assert_eq!(limited.summary.without_authority_gate, 1);
    assert_eq!(limited.summary.without_failure_mode, 2);
    assert_eq!(limited.summary.without_trust_level, 1);

    let json = serde_json::to_value(&limited).expect("query report should serialize");
    assert_eq!(
        json["summary"]["by_authority_gate"]["native_authority_gate"],
        2
    );
    assert_eq!(
        json["summary"]["by_failure_mode"]["kernel_type_mismatch"],
        1
    );
    assert_eq!(json["summary"]["by_trust_level"]["KernelVerified"], 1);

    let native_gate = query_attempts_limited(
        root,
        AttemptFilter {
            authority_gate: Some("native_authority_gate".to_owned()),
            ..AttemptFilter::default()
        },
        None,
    )
    .expect("query by authority gate");
    assert_eq!(
        native_gate.attempts,
        vec![accepted.clone(), rejected.clone()]
    );
    assert_eq!(
        native_gate.summary.by_authority_gate["native_authority_gate"],
        2
    );

    let kernel_mismatch = query_attempts_limited(
        root,
        AttemptFilter {
            failure_mode: Some("kernel_type_mismatch".to_owned()),
            ..AttemptFilter::default()
        },
        None,
    )
    .expect("query by failure mode");
    assert_eq!(kernel_mismatch.attempts, vec![rejected.clone()]);
    assert_eq!(
        kernel_mismatch.summary.by_failure_mode["kernel_type_mismatch"],
        1
    );

    let kernel_verified = query_attempts_limited(
        root,
        AttemptFilter {
            trust_level: Some(TrustLevel::KernelVerified),
            ..AttemptFilter::default()
        },
        None,
    )
    .expect("query by trust level");
    assert_eq!(kernel_verified.attempts, vec![accepted]);
    assert_eq!(kernel_verified.summary.by_trust_level["KernelVerified"], 1);
}

#[test]
fn external_attempt_metadata_queries_cover_producer_task_status_trust_and_gate() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();

    let producer_a = AttemptProducer {
        producer_kind: ProducerKind::Model,
        provider: "mathbot-lab".to_owned(),
        name: "slot-a".to_owned(),
        version: Some("2026-05-20".to_owned()),
        command_digest: Some(hash("slot-a command")),
    };
    let producer_b = AttemptProducer {
        producer_kind: ProducerKind::Solver,
        provider: "clean-ci".to_owned(),
        name: "native-replay".to_owned(),
        version: None,
        command_digest: None,
    };

    let mut accepted = attempt(AttemptStatus::Accepted, env.clone(), 0);
    accepted.authority_gate = Some("external_patch".to_owned());
    accepted.trust_level = Some(TrustLevel::KernelVerified);
    accepted.producer = Some(producer_a.clone());
    accepted.context = Some(AttemptContext {
        external_run_id: Some("run-a".to_owned()),
        external_task_id: Some("task-a".to_owned()),
        prompt_digest: Some(hash("task-a prompt")),
        patch_artifact: None,
    });

    let mut rejected = attempt(
        AttemptStatus::Rejected {
            reason: "statement preservation failed".to_owned(),
        },
        env.clone(),
        1_000_000,
    );
    rejected.authority_gate = Some("statement_preservation".to_owned());
    rejected.trust_level = Some(TrustLevel::PartiallyAxiomatized);
    rejected.producer = Some(producer_b);
    rejected.context = Some(AttemptContext {
        external_run_id: Some("run-b".to_owned()),
        external_task_id: Some("task-b".to_owned()),
        prompt_digest: None,
        patch_artifact: None,
    });

    let mut timeout = attempt(AttemptStatus::Timeout { after_ms: 2_000 }, env, 2_000_000);
    timeout.authority_gate = Some("external_patch".to_owned());
    timeout.trust_level = Some(TrustLevel::TrustedOracle);
    timeout.producer = Some(producer_a);
    timeout.context = Some(AttemptContext {
        external_run_id: Some("run-a".to_owned()),
        external_task_id: Some("task-a".to_owned()),
        prompt_digest: Some(hash("task-a retry prompt")),
        patch_artifact: None,
    });

    append_to(root, &accepted).expect("append accepted");
    append_to(root, &rejected).expect("append rejected");
    append_to(root, &timeout).expect("append timeout");

    let slot_a_attempts: Vec<_> = iter_from(
        root,
        AttemptFilter {
            producer_provider: Some("mathbot-lab".to_owned()),
            producer: Some("slot-a".to_owned()),
            producer_kind: Some(ProducerKind::Model),
            ..AttemptFilter::default()
        },
    )
    .expect("query by producer")
    .collect();
    assert_eq!(slot_a_attempts, vec![accepted.clone(), timeout.clone()]);

    let task_a_timeouts: Vec<_> = iter_from(
        root,
        AttemptFilter {
            external_task_id: Some("task-a".to_owned()),
            status: Some(AttemptStatusFilter::Timeout),
            ..AttemptFilter::default()
        },
    )
    .expect("query by task and status")
    .collect();
    assert_eq!(task_a_timeouts, vec![timeout.clone()]);

    let accepted_kernel_external = query_attempts_limited(
        root,
        AttemptFilter {
            authority_gate: Some("external_patch".to_owned()),
            status: Some(AttemptStatusFilter::Accepted),
            trust_level: Some(TrustLevel::KernelVerified),
            external_task_id: Some("task-a".to_owned()),
            ..AttemptFilter::default()
        },
        None,
    )
    .expect("query accepted trusted external attempts");
    assert_eq!(accepted_kernel_external.attempts, vec![accepted]);
    assert_eq!(accepted_kernel_external.summary.by_producer["slot-a"], 1);
    assert_eq!(
        accepted_kernel_external.summary.by_producer_provider["mathbot-lab"],
        1
    );
    assert_eq!(
        accepted_kernel_external.summary.by_external_task_id["task-a"],
        1
    );
    assert_eq!(
        accepted_kernel_external.summary.by_authority_gate["external_patch"],
        1
    );

    let rejected_statement_gate: Vec<_> = iter_from(
        root,
        AttemptFilter {
            authority_gate: Some("statement_preservation".to_owned()),
            status: Some(AttemptStatusFilter::Rejected),
            trust_level: Some(TrustLevel::PartiallyAxiomatized),
            external_task_id: Some("task-b".to_owned()),
            ..AttemptFilter::default()
        },
    )
    .expect("query rejected external gate attempts")
    .collect();
    assert_eq!(rejected_statement_gate, vec![rejected]);
}

#[test]
fn replay_preflight_validates_env_and_records_linkage() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let original = attempt(AttemptStatus::Accepted, env.clone(), 0);
    append_to(root, &original).expect("append original");

    let plan = prepare_replay_attempt_with_env(
        root,
        &original.attempt_id,
        env.clone(),
        ReplayOptions::default(),
    )
    .expect("prepare replay");
    assert!(plan.env_matches);
    assert_eq!(plan.original, original);

    let mut replay = attempt(AttemptStatus::Accepted, env.clone(), 10_000_000);
    replay.attempt_id = AttemptId::new_v7();
    let replay = record_replay_attempt(root, &plan.original.attempt_id, replay)
        .expect("record replay attempt");
    assert_eq!(replay.replayed_from, Some(original.attempt_id.clone()));

    let attempts: Vec<_> = iter_from(root, AttemptFilter::default())
        .expect("iter attempts")
        .collect();
    assert_eq!(attempts.len(), 2);
    assert_eq!(attempts[1].replayed_from, Some(original.attempt_id));
}

#[test]
fn replay_preflight_rejects_env_mismatch_without_explanation() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let original = attempt(AttemptStatus::Accepted, env.clone(), 0);
    append_to(root, &original).expect("append original");

    let mut mismatched = env;
    mismatched.host_os = "different-os".to_owned();

    let err = prepare_replay_attempt_with_env(
        root,
        &original.attempt_id,
        mismatched,
        ReplayOptions::default(),
    )
    .expect_err("mismatch should fail");
    assert!(err.to_string().contains("environment mismatch"));
}

#[test]
fn replay_mismatch_allow_only_records_when_result_supplied() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path();
    let env = test_env();
    let original = attempt(AttemptStatus::Accepted, env.clone(), 0);
    append_to(root, &original).expect("append original");

    let mut mismatched = env;
    mismatched.host_arch = "different-arch".to_owned();

    let rejected = prepare_replay_attempt_with_env_and_result(
        root,
        &original.attempt_id,
        mismatched.clone(),
        ReplayOptions {
            allow_mismatch: true,
            mismatch_explanation: None,
        },
        None,
    )
    .expect_err("allowed mismatch still requires explanation");
    assert!(rejected
        .to_string()
        .contains("requires a non-empty explanation"));

    let preflight_only = prepare_replay_attempt_with_env_and_result(
        root,
        &original.attempt_id,
        mismatched.clone(),
        ReplayOptions {
            allow_mismatch: true,
            mismatch_explanation: Some("checking solver upgrade".to_owned()),
        },
        None,
    )
    .expect("preflight with allowed mismatch");
    assert!(!preflight_only.plan.env_matches);
    assert!(preflight_only.recorded_replay.is_none());
    assert_eq!(
        iter_from(root, AttemptFilter::default())
            .expect("iter after preflight")
            .count(),
        1
    );

    let mut result = ReplayAttemptResult::new(AttemptStatus::Accepted, hash("replay-audit"));
    result.wall_time_ms = 42;
    let recorded = prepare_replay_attempt_with_env_and_result(
        root,
        &original.attempt_id,
        mismatched,
        ReplayOptions {
            allow_mismatch: true,
            mismatch_explanation: Some("checking solver upgrade".to_owned()),
        },
        Some(result),
    )
    .expect("record replay result");

    let replay = recorded
        .recorded_replay
        .expect("replay attempt should be recorded");
    assert_eq!(replay.replayed_from, Some(original.attempt_id.clone()));
    assert_eq!(replay.goal_hash, original.goal_hash);
    assert_eq!(replay.proof_state_before, original.proof_state_before);
    assert_eq!(replay.wall_time_ms, 42);

    let attempts: Vec<_> = iter_from(root, AttemptFilter::default())
        .expect("iter attempts")
        .collect();
    assert_eq!(attempts.len(), 2);
    assert_eq!(attempts[1].replayed_from, Some(original.attempt_id));
}
