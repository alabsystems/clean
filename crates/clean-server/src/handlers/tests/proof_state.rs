// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use crate::proof_state::ApplyTacticResult;
use clean_elab::tactic::{
    convert, ProofState as InternalProofState, ProofTrustLedger, TrustedArithProvenanceLedger,
};
use clean_kernel::{Environment, Expr, Name};

fn assert_empty_mathverse_candidates_json(value: &serde_json::Value, context: &str) {
    let candidates = value
        .get("mathverse_candidates")
        .unwrap_or_else(|| panic!("{context} should serialize mathverse_candidates"));
    let candidates = candidates
        .as_array()
        .unwrap_or_else(|| panic!("{context} mathverse_candidates should be an array"));
    assert!(
        candidates.is_empty(),
        "{context} should default mathverse_candidates to []"
    );
}

fn minimal_open_obligation_request(
    goal: crate::proof_state::ObligationGoalPayload,
) -> crate::proof_state::OpenObligationRequest {
    crate::proof_state::OpenObligationRequest {
        schema_version: crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION.to_string(),
        environment_id: "test-env".to_string(),
        domain_profile: crate::proof_state::ObligationDomainProfile::General,
        goal,
        local_context: vec![],
        artifact_refs: vec![],
        metadata: None,
        trust_policy: crate::proof_state::ObligationTrustPolicy::ConstructiveOnly,
        ttl_sec: 60,
        max_states: 4,
        min_schema_version: crate::proof_state::PROOF_STATE_SCHEMA_VERSION.to_string(),
        max_schema_version: crate::proof_state::PROOF_STATE_SCHEMA_VERSION.to_string(),
    }
}

fn profile_open_obligation_request(
    profile: crate::proof_state::ObligationDomainProfile,
) -> crate::proof_state::OpenObligationRequest {
    let mut request = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: Some(Expr::prop()),
        pretty: "profile-aware proof-state target".to_string(),
        type_expr: None,
        type_pp: None,
    });
    request.domain_profile = profile;
    request
}

fn env_with_profile_theorems() -> Environment {
    let mut env = Environment::new();
    env.add_skolem_axiom(Name::from_string("Sat.PB.cert_sound"), Expr::prop());
    env.add_skolem_axiom(Name::from_string("NN.Verify.bound_sound"), Expr::prop());
    env.add_skolem_axiom(Name::from_string("Generic.helper"), Expr::prop());
    env
}

fn precomputed_project_theorem_index_json() -> &'static str {
    r#"{
  "schema_version": "clean-math-theorem-index-v1",
  "project": {
    "schema_version": "clean-math-project-v1",
    "project_path": "Math/project.json",
    "project_root": "Math",
    "name": "sat-pb-pilot",
    "domain_profile": "sat-pb",
    "owner": "proof-state-test",
    "trust_policy": "constructive-only",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": false
  },
  "profile": "sat-pb",
  "files_scanned": 1,
  "memory": {
    "candidate_count": 2,
    "local_count": 2,
    "project_count": 2,
    "domain_count": 2,
    "imported_count": 0,
    "artifact_derived_count": 0,
    "trust_policy_conforming_count": 1
  },
  "candidates": [
    {
      "name": "SatPb.Project.clean_sound",
      "source_path": "theorem_packs/Project.lean",
      "module": "SatPb.Project",
      "candidate_fingerprint": "1111111111111111111111111111111111111111111111111111111111111111",
      "classification": {
        "scope": "local",
        "local": true,
        "project": true,
        "domain": true,
        "imported": false,
        "artifact_derived": false
      },
      "domain_signals": {
        "profile": "sat-pb",
        "module_match": true,
        "semantic_head_matches": ["Clause"],
        "ranking_signal_matches": ["conclusion_head"]
      },
      "trust_decision": {
        "policy": "constructive-only",
        "conformance": "conforming",
        "kernel_proof_status": "not_claimed",
        "trust_debt": [],
        "promotion_allowed": true,
        "reasons": []
      }
    },
    {
      "name": "SatPb.Project.synthetic_bridge",
      "source_path": "theorem_packs/Project.lean",
      "module": "SatPb.Project",
      "candidate_fingerprint": "2222222222222222222222222222222222222222222222222222222222222222",
      "classification": {
        "scope": "local",
        "local": true,
        "project": true,
        "domain": true,
        "imported": false,
        "artifact_derived": false
      },
      "domain_signals": {
        "profile": "sat-pb",
        "module_match": true,
        "semantic_head_matches": ["Clause"],
        "ranking_signal_matches": ["trust_blocker"]
      },
      "trust_decision": {
        "policy": "constructive-only",
        "conformance": "blocked",
        "kernel_proof_status": "not_claimed",
        "trust_debt": ["synthetic_sorry"],
        "promotion_allowed": false,
        "reasons": ["synthetic sorry is forbidden by trust policy"]
      }
    }
  ],
  "factory_report": {
    "schema_version": "clean-theorem-index-v1",
    "diagnostics": []
  }
}"#
}

fn multi_goal_project_theorem_index_json() -> &'static str {
    r#"{
  "schema_version": "clean-math-theorem-index-v1",
  "project": {
    "schema_version": "clean-math-project-v1",
    "project_path": "Math/project.json",
    "project_root": "Math",
    "name": "multi-goal-search-test",
    "domain_profile": "general",
    "owner": "proof-state-test",
    "trust_policy": "constructive-only",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": false
  },
  "profile": "general",
  "files_scanned": 1,
  "memory": {
    "candidate_count": 2,
    "local_count": 2,
    "project_count": 2,
    "domain_count": 0,
    "imported_count": 0,
    "artifact_derived_count": 0,
    "trust_policy_conforming_count": 2
  },
  "candidates": [
    {
      "name": "ZGoalTrue.helper",
      "source_path": "theorem_packs/MultiGoal.lean",
      "module": "MultiGoal",
      "candidate_fingerprint": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
      "classification": {
        "scope": "local",
        "local": true,
        "project": true,
        "domain": false,
        "imported": false,
        "artifact_derived": false
      },
      "domain_signals": {
        "profile": "general",
        "module_match": false,
        "semantic_head_matches": [],
        "ranking_signal_matches": []
      },
      "trust_decision": {
        "policy": "constructive-only",
        "conformance": "conforming",
        "kernel_proof_status": "not_claimed",
        "trust_debt": [],
        "promotion_allowed": true,
        "reasons": []
      }
    },
    {
      "name": "AGoalFalse.helper",
      "source_path": "theorem_packs/MultiGoal.lean",
      "module": "MultiGoal",
      "candidate_fingerprint": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
      "classification": {
        "scope": "local",
        "local": true,
        "project": true,
        "domain": false,
        "imported": false,
        "artifact_derived": false
      },
      "domain_signals": {
        "profile": "general",
        "module_match": false,
        "semantic_head_matches": [],
        "ranking_signal_matches": []
      },
      "trust_decision": {
        "policy": "constructive-only",
        "conformance": "conforming",
        "kernel_proof_status": "not_claimed",
        "trust_debt": [],
        "promotion_allowed": true,
        "reasons": []
      }
    }
  ],
  "factory_report": {
    "schema_version": "clean-theorem-index-v1",
    "diagnostics": []
  }
}"#
}

#[tokio::test]
async fn test_open_obligation_minimal_expr_goal_opens_state() {
    let state = ServerState::new();
    let params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: Some(Expr::prop()),
        pretty: String::new(),
        type_expr: None,
        type_pp: None,
    });

    let response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(
        result.schema_version,
        crate::proof_state::PROOF_STATE_SCHEMA_VERSION
    );
    assert!(result.state_id.starts_with("ps_"));
    assert_eq!(result.environment_id, "test-env");
    assert_eq!(result.lifecycle.ttl_sec, 60);

    let snapshot = result
        .initial_snapshot
        .expect("open obligation should return initial snapshot");
    assert_eq!(snapshot.state_id, result.state_id);
    assert_eq!(snapshot.goals.len(), 1);
    assert!(!snapshot.is_solved);
}

#[tokio::test]
async fn test_open_obligation_follow_up_handlers_cover_snapshot_apply_extract() {
    let state = ServerState::new();
    let mut params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: Some(Expr::prop()),
        pretty: "math-project obligation target".to_string(),
        type_expr: None,
        type_pp: None,
    });
    params.trust_policy = crate::proof_state::ObligationTrustPolicy::AllowTrustedArith;
    params.artifact_refs = vec![crate::proof_state::ObligationArtifactRef {
        kind: crate::proof_state::ObligationArtifactKind::Lean,
        sha256: Some("0".repeat(64)),
        path: Some("artifacts/source.lean".to_string()),
        media_type: Some("text/x-lean".to_string()),
    }];
    params.metadata = Some(crate::proof_state::ProofStateMetadata {
        project: Some("metadata-project".to_string()),
        project_path: Some("Math/project.json".to_string()),
        project_root: Some("Math".to_string()),
        obligation_fingerprint: Some("sha256:metadata-obligation".to_string()),
        obligation_source_path: Some("Math/obligations/one.json".to_string()),
        source_origin: Some("unit-test".to_string()),
        producer: Some(crate::proof_state::ProofStateProducerMetadata {
            system: "test-producer".to_string(),
            commit: "abc123".to_string(),
            command: Some("generate-obligation".to_string()),
        }),
        artifact_refs: params.artifact_refs.clone(),
    });

    let open_response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    assert!(
        open_response.error.is_none(),
        "Unexpected open error: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();

    let get_response = handle_get_proof_state(
        &state,
        RequestId::Number(2),
        GetProofStateParams {
            state_id: opened.state_id.clone(),
            format: crate::proof_state::OutputFormat::Llm,
        },
    )
    .await;
    assert!(
        get_response.error.is_none(),
        "Unexpected snapshot error: {:?}",
        get_response.error
    );
    let snapshot: crate::proof_state::ApiProofState =
        serde_json::from_value(get_response.result.unwrap()).unwrap();
    assert_eq!(snapshot.state_id, opened.state_id);
    assert_eq!(snapshot.goals.len(), 1);
    assert_eq!(
        snapshot
            .metadata
            .as_ref()
            .and_then(|metadata| metadata.obligation_fingerprint.as_deref()),
        Some("sha256:metadata-obligation")
    );
    assert_eq!(
        snapshot
            .metadata
            .as_ref()
            .map(|metadata| metadata.artifact_refs.len()),
        Some(1)
    );

    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(3),
        ApplyTacticParams {
            state_id: opened.state_id.clone(),
            goal_id: snapshot.goals[0].goal_id.clone(),
            tactic: "sorry".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "Unexpected apply error: {:?}",
        apply_response.error
    );
    let applied: ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(applied.success, "sorry should close the obligation state");
    assert!(applied.is_solved);

    let child_response = handle_get_proof_state(
        &state,
        RequestId::Number(5),
        GetProofStateParams {
            state_id: applied.new_state_id.clone(),
            format: crate::proof_state::OutputFormat::Full,
        },
    )
    .await;
    assert!(
        child_response.error.is_none(),
        "Unexpected child snapshot error: {:?}",
        child_response.error
    );
    let child_snapshot: crate::proof_state::ApiProofState =
        serde_json::from_value(child_response.result.unwrap()).unwrap();
    assert_eq!(child_snapshot.parent_state_id, Some(opened.state_id));
    assert_eq!(
        child_snapshot
            .metadata
            .as_ref()
            .and_then(|metadata| metadata.producer.as_ref())
            .map(|producer| producer.system.as_str()),
        Some("test-producer")
    );

    let extract_response = handle_extract_proof(
        &state,
        RequestId::Number(6),
        ExtractProofParams {
            state_id: applied.new_state_id.clone(),
            format: "certificate".to_string(),
        },
    )
    .await;
    assert!(
        extract_response.error.is_none(),
        "Unexpected extract error: {:?}",
        extract_response.error
    );
    let extracted: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    assert!(extracted.is_solved);
    assert!(
        extracted.trust_summary.expect("trust summary").sorry_count > 0,
        "extracting a sorry-closed obligation must preserve trust debt"
    );
}

#[tokio::test]
async fn test_search_tactics_uses_sat_pb_profile_ranking() {
    let state = ServerState::new();
    let open_response = handle_open_obligation(
        &state,
        RequestId::Number(1),
        profile_open_obligation_request(crate::proof_state::ObligationDomainProfile::SatPb),
    )
    .await;
    assert!(
        open_response.error.is_none(),
        "Unexpected open error: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();
    let goal_id = opened.initial_snapshot.unwrap().goals[0].goal_id.clone();

    let search_response = handle_search_tactics(
        &state,
        RequestId::Number(2),
        ProofStateGoalSearchParams {
            state_id: opened.state_id,
            goal_id,
        },
    )
    .await;
    assert!(
        search_response.error.is_none(),
        "Unexpected tactic search error: {:?}",
        search_response.error
    );
    let result: SearchTacticsResult =
        serde_json::from_value(search_response.result.unwrap()).unwrap();

    assert_eq!(
        result.domain_profile,
        crate::proof_state::ObligationDomainProfile::SatPb
    );
    assert_eq!(
        &result.tactics[..3],
        ["cert_simp", "cert_mathverse", "sat_pb"]
    );
}

#[tokio::test]
async fn test_search_tactics_uses_nn_verify_profile_ranking() {
    let state = ServerState::new();
    let open_response = handle_open_obligation(
        &state,
        RequestId::Number(1),
        profile_open_obligation_request(crate::proof_state::ObligationDomainProfile::NnVerify),
    )
    .await;
    assert!(
        open_response.error.is_none(),
        "Unexpected open error: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();
    let goal_id = opened.initial_snapshot.unwrap().goals[0].goal_id.clone();

    let search_response = handle_search_tactics(
        &state,
        RequestId::Number(2),
        ProofStateGoalSearchParams {
            state_id: opened.state_id,
            goal_id,
        },
    )
    .await;
    assert!(
        search_response.error.is_none(),
        "Unexpected tactic search error: {:?}",
        search_response.error
    );
    let result: SearchTacticsResult =
        serde_json::from_value(search_response.result.unwrap()).unwrap();

    assert_eq!(
        result.domain_profile,
        crate::proof_state::ObligationDomainProfile::NnVerify
    );
    assert_eq!(&result.tactics[..3], ["cert_simp", "nn_norm", "nn_verify"]);
}

#[tokio::test]
async fn test_search_theorems_exposes_and_ranks_by_domain_profile() {
    let sat_state = ServerState::new().with_env(env_with_profile_theorems());
    let sat_open = handle_open_obligation(
        &sat_state,
        RequestId::Number(1),
        profile_open_obligation_request(crate::proof_state::ObligationDomainProfile::SatPb),
    )
    .await;
    assert!(
        sat_open.error.is_none(),
        "Unexpected open error: {:?}",
        sat_open.error
    );
    let sat_opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(sat_open.result.unwrap()).unwrap();
    let sat_goal_id = sat_opened.initial_snapshot.unwrap().goals[0]
        .goal_id
        .clone();
    let sat_search = handle_search_theorems(
        &sat_state,
        RequestId::Number(2),
        ProofStateGoalSearchParams {
            state_id: sat_opened.state_id,
            goal_id: sat_goal_id,
        },
    )
    .await;
    assert!(
        sat_search.error.is_none(),
        "Unexpected theorem search error: {:?}",
        sat_search.error
    );
    let sat_result: SearchTheoremsResult =
        serde_json::from_value(sat_search.result.unwrap()).unwrap();

    let nn_state = ServerState::new().with_env(env_with_profile_theorems());
    let nn_open = handle_open_obligation(
        &nn_state,
        RequestId::Number(3),
        profile_open_obligation_request(crate::proof_state::ObligationDomainProfile::NnVerify),
    )
    .await;
    assert!(
        nn_open.error.is_none(),
        "Unexpected open error: {:?}",
        nn_open.error
    );
    let nn_opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(nn_open.result.unwrap()).unwrap();
    let nn_goal_id = nn_opened.initial_snapshot.unwrap().goals[0].goal_id.clone();
    let nn_search = handle_search_theorems(
        &nn_state,
        RequestId::Number(4),
        ProofStateGoalSearchParams {
            state_id: nn_opened.state_id,
            goal_id: nn_goal_id,
        },
    )
    .await;
    assert!(
        nn_search.error.is_none(),
        "Unexpected theorem search error: {:?}",
        nn_search.error
    );
    let nn_result: SearchTheoremsResult =
        serde_json::from_value(nn_search.result.unwrap()).unwrap();

    assert_eq!(
        sat_result.domain_profile,
        crate::proof_state::ObligationDomainProfile::SatPb
    );
    assert_eq!(
        nn_result.domain_profile,
        crate::proof_state::ObligationDomainProfile::NnVerify
    );
    assert_eq!(sat_result.candidates[0].name, "Sat.PB.cert_sound");
    assert_eq!(nn_result.candidates[0].name, "NN.Verify.bound_sound");
}

#[tokio::test]
async fn test_search_theorems_uses_trusted_project_theorem_index_json() {
    let state = ServerState::new()
        .try_with_project_theorem_index_json(precomputed_project_theorem_index_json())
        .expect("precomputed project theorem index should parse");
    let open = handle_open_obligation(
        &state,
        RequestId::Number(1),
        profile_open_obligation_request(crate::proof_state::ObligationDomainProfile::SatPb),
    )
    .await;
    assert!(
        open.error.is_none(),
        "Unexpected open error: {:?}",
        open.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open.result.unwrap()).unwrap();
    let goal_id = opened.initial_snapshot.unwrap().goals[0].goal_id.clone();

    let search = handle_search_theorems(
        &state,
        RequestId::Number(2),
        ProofStateGoalSearchParams {
            state_id: opened.state_id,
            goal_id,
        },
    )
    .await;
    assert!(
        search.error.is_none(),
        "Unexpected theorem search error: {:?}",
        search.error
    );
    let result: SearchTheoremsResult = serde_json::from_value(search.result.unwrap()).unwrap();

    let trusted = result
        .candidates
        .iter()
        .find(|candidate| candidate.name == "SatPb.Project.clean_sound")
        .expect("trusted project theorem-index candidate should be returned");
    let provenance = trusted
        .provenance
        .as_ref()
        .expect("project candidate should expose theorem-index provenance");
    assert_eq!(provenance.source, "math-project-theorem-index");
    assert_eq!(provenance.project.as_deref(), Some("sat-pb-pilot"));
    let trust = trusted
        .trust
        .as_ref()
        .expect("project candidate should expose trust decision");
    assert_eq!(trust.policy, "constructive-only");
    assert_eq!(trust.conformance, "conforming");
    assert!(trust.promotion_allowed);
    assert!(trust.trust_debt.is_empty());
    assert!(
        result
            .candidates
            .iter()
            .all(|candidate| candidate.name != "SatPb.Project.synthetic_bridge"),
        "synthetic-sorry theorem-index candidates must be filtered under ConstructiveOnly"
    );
}

#[tokio::test]
async fn test_search_theorems_uses_requested_non_front_goal() {
    let state = ServerState::new()
        .with_env(Environment::with_prelude())
        .try_with_project_theorem_index_json(multi_goal_project_theorem_index_json())
        .expect("multi-goal project theorem index should parse");

    let init = handle_init_proof_state(
        &state,
        RequestId::Number(1),
        InitProofStateParams {
            theorem: "True ∧ False".to_string(),
            problem_id: Some("multi_goal_search".to_string()),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        init.error.is_none(),
        "Unexpected init error: {:?}",
        init.error
    );
    let init_result: InitProofStateResult = serde_json::from_value(init.result.unwrap()).unwrap();
    let goal_id = init_result.goals[0].goal_id.clone();

    let split = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: init_result.state_id,
            goal_id,
            tactic: "constructor".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        split.error.is_none(),
        "Unexpected split transport error: {:?}",
        split.error
    );
    let split_result: ApplyTacticResult = serde_json::from_value(split.result.unwrap()).unwrap();
    assert!(
        split_result.success,
        "constructor should create subgoals: {:?}",
        split_result.error
    );
    assert_eq!(split_result.new_goals.len(), 2);
    assert_eq!(split_result.new_goals[0].target_pp, "True");
    assert_eq!(split_result.new_goals[1].target_pp, "False");

    let first_search = handle_search_theorems(
        &state,
        RequestId::Number(3),
        ProofStateGoalSearchParams {
            state_id: split_result.new_state_id.clone(),
            goal_id: split_result.new_goals[0].goal_id.clone(),
        },
    )
    .await;
    assert!(
        first_search.error.is_none(),
        "Unexpected first-goal theorem search error: {:?}",
        first_search.error
    );
    let first_result: SearchTheoremsResult =
        serde_json::from_value(first_search.result.unwrap()).unwrap();

    let second_search = handle_search_theorems(
        &state,
        RequestId::Number(4),
        ProofStateGoalSearchParams {
            state_id: split_result.new_state_id,
            goal_id: split_result.new_goals[1].goal_id.clone(),
        },
    )
    .await;
    assert!(
        second_search.error.is_none(),
        "Unexpected second-goal theorem search error: {:?}",
        second_search.error
    );
    let second_result: SearchTheoremsResult =
        serde_json::from_value(second_search.result.unwrap()).unwrap();

    assert_eq!(first_result.candidates[0].name, "ZGoalTrue.helper");
    assert_eq!(second_result.candidates[0].name, "AGoalFalse.helper");
}

#[tokio::test]
async fn test_open_obligation_constructive_only_rejects_sorry_apply() {
    let state = ServerState::new();
    let params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: Some(Expr::prop()),
        pretty: "constructive-only target".to_string(),
        type_expr: None,
        type_pp: None,
    });

    let open_response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    assert!(
        open_response.error.is_none(),
        "Unexpected open error: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();
    let snapshot = opened
        .initial_snapshot
        .expect("open obligation should include an initial snapshot");

    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: opened.state_id.clone(),
            goal_id: snapshot.goals[0].goal_id.clone(),
            tactic: "sorry".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "policy rejection should be returned as an apply result: {:?}",
        apply_response.error
    );
    let applied: ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();

    assert!(!applied.success, "ConstructiveOnly must reject sorry");
    assert_eq!(applied.new_state_id, opened.state_id);
    let error = applied
        .error
        .expect("rejected tactic should report an error");
    assert_eq!(
        error.code,
        crate::proof_state::TacticErrorCode::TrustPolicyViolation
    );
    assert!(
        error.message.contains("constructive-only"),
        "unexpected policy error: {}",
        error.message
    );

    let get_response = handle_get_proof_state(
        &state,
        RequestId::Number(3),
        GetProofStateParams {
            state_id: opened.state_id.clone(),
            format: crate::proof_state::OutputFormat::Llm,
        },
    )
    .await;
    assert!(
        get_response.error.is_none(),
        "rejected apply should leave original state readable: {:?}",
        get_response.error
    );
    let unchanged: crate::proof_state::ApiProofState =
        serde_json::from_value(get_response.result.unwrap()).unwrap();
    assert!(!unchanged.is_solved);
    assert_eq!(unchanged.goals.len(), 1);
    assert_eq!(
        unchanged.trust_summary.expect("trust summary").sorry_count,
        0
    );
}

#[tokio::test]
async fn test_proof_state_failure_explain_retain_and_close_lifecycle() {
    let state = ServerState::new();
    let mut params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: Some(Expr::prop()),
        pretty: "lifecycle target".to_string(),
        type_expr: None,
        type_pp: None,
    });
    params.trust_policy = crate::proof_state::ObligationTrustPolicy::AllowTrustedArith;
    params.ttl_sec = 30;
    params.max_states = 2;

    let open_response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    assert!(
        open_response.error.is_none(),
        "Unexpected open error: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();
    assert_eq!(opened.lifecycle.ttl_sec, 30);
    assert_eq!(opened.lifecycle.max_states, 2);
    assert!(
        opened.warnings.is_empty(),
        "max_states should be enforced, not reported as advisory"
    );
    let goal_id = opened.initial_snapshot.unwrap().goals[0].goal_id.clone();

    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: opened.state_id.clone(),
            goal_id: goal_id.clone(),
            tactic: "definitely_unknown_tactic".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "failed apply should be returned as an apply result: {:?}",
        apply_response.error
    );
    let applied: ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(!applied.success);
    let attempt_id = applied
        .attempt_id
        .expect("failed apply should persist an attempt id");
    assert!(attempt_id.starts_with("pa_"));

    let explain_response = handle_explain_failure(
        &state,
        RequestId::Number(3),
        ExplainFailureParams {
            attempt_id: attempt_id.clone(),
        },
    )
    .await;
    assert!(
        explain_response.error.is_none(),
        "explainFailure should find persisted telemetry: {:?}",
        explain_response.error
    );
    let explained: ExplainFailureResult =
        serde_json::from_value(explain_response.result.unwrap()).unwrap();
    assert_eq!(explained.status, "failed");
    assert_eq!(explained.attempt_id, attempt_id);
    assert_eq!(explained.blockers.len(), 1);
    assert_eq!(explained.blockers[0].state_id, opened.state_id);
    assert_eq!(explained.blockers[0].goal_id, goal_id);
    assert_eq!(
        explained.blockers[0].code,
        crate::proof_state::TacticErrorCode::UnknownTactic
    );

    let retain_response = handle_retain_proof_state(
        &state,
        RequestId::Number(4),
        RetainProofStateParams {
            state_id: opened.state_id.clone(),
            ttl_sec: Some(45),
        },
    )
    .await;
    assert!(
        retain_response.error.is_none(),
        "retain should refresh a live state: {:?}",
        retain_response.error
    );
    let retained: RetainProofStateResult =
        serde_json::from_value(retain_response.result.unwrap()).unwrap();
    assert!(retained.retained);
    assert_eq!(retained.lifecycle.ttl_sec, 45);
    assert_eq!(retained.lifecycle.max_states, 2);

    let close_response = handle_close_proof_state(
        &state,
        RequestId::Number(5),
        CloseProofStateParams {
            state_id: opened.state_id.clone(),
        },
    )
    .await;
    assert!(
        close_response.error.is_none(),
        "close should return a lifecycle result: {:?}",
        close_response.error
    );
    let closed: CloseProofStateResult =
        serde_json::from_value(close_response.result.unwrap()).unwrap();
    assert!(closed.closed);

    let get_after_close = handle_get_proof_state(
        &state,
        RequestId::Number(6),
        GetProofStateParams {
            state_id: opened.state_id,
            format: crate::proof_state::OutputFormat::Llm,
        },
    )
    .await;
    assert!(
        get_after_close.error.is_some(),
        "getProofState after close should fail"
    );
}

#[tokio::test]
async fn test_open_obligation_rejects_missing_goal_payload() {
    let state = ServerState::new();
    let params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: None,
        pretty: "   ".to_string(),
        type_expr: None,
        type_pp: None,
    });

    let response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    let err = response
        .error
        .expect("missing goal payload should return an RPC error");
    assert_eq!(err.code, crate::rpc::error_codes::INVALID_PARAMS);
    let data = err
        .data
        .expect("open obligation errors should be structured");
    assert_eq!(data["method"], "proofState.openObligation");
    assert_eq!(data["code"], "INVALID_OPEN_OBLIGATION_REQUEST");
    assert_eq!(data["fail_closed"], true);
    assert!(
        err.message.contains("goal must include"),
        "unexpected error message: {}",
        err.message
    );
}

#[tokio::test]
async fn test_open_obligation_rejects_pretty_only_goal_fail_closed() {
    let state = ServerState::new();
    let params = minimal_open_obligation_request(crate::proof_state::ObligationGoalPayload {
        expr: None,
        pretty: "pretty target only".to_string(),
        type_expr: None,
        type_pp: None,
    });

    let response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    let err = response
        .error
        .expect("pretty-only goal should return an RPC error");
    assert_eq!(err.code, crate::rpc::error_codes::INVALID_PARAMS);
    let data = err
        .data
        .expect("open obligation errors should be structured");
    assert_eq!(data["method"], "proofState.openObligation");
    assert_eq!(data["code"], "PRETTY_ONLY_OBLIGATION");
    assert_eq!(data["fail_closed"], true);
}

#[tokio::test]
async fn test_init_proof_state_simple() {
    let state = ServerState::new();
    let params = InitProofStateParams {
        theorem: "Prop".to_string(),
        problem_id: Some("test_problem".to_string()),
        timeout_ms: None,
    };

    let response = handle_init_proof_state(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );
    let result: InitProofStateResult = serde_json::from_value(
        response
            .result
            .expect("init_proof_state should return a result"),
    )
    .unwrap();
    assert!(
        result.state_id.starts_with("ps_"),
        "state_id should start with ps_"
    );
    assert_eq!(result.goals.len(), 1, "Should have one goal");
    assert!(!result.is_solved, "Should not be solved yet");
}

#[tokio::test]
async fn test_init_proof_state_function_type() {
    let state = ServerState::new();
    let params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };

    let response = handle_init_proof_state(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: InitProofStateResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.goals.len(), 1);
}

#[tokio::test]
async fn test_get_proof_state() {
    let state = ServerState::new();

    // First init a state
    let init_params = InitProofStateParams {
        theorem: "Prop".to_string(),
        problem_id: Some("test".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Then get it
    let get_params = GetProofStateParams {
        state_id: init_result.state_id.clone(),
        format: crate::proof_state::OutputFormat::Llm,
    };
    let get_response = handle_get_proof_state(&state, RequestId::Number(2), get_params).await;
    assert!(
        get_response.error.is_none(),
        "Unexpected error: {:?}",
        get_response.error
    );

    let result_json = get_response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "getProofState llm");
    let api_state: crate::proof_state::ApiProofState = serde_json::from_value(result_json).unwrap();
    assert_eq!(api_state.state_id, init_result.state_id);
    assert_eq!(api_state.problem_id, Some("test".to_string()));
    assert!(api_state.mathverse_candidates.is_empty());
}

#[tokio::test]
async fn test_get_proof_state_invalid_id() {
    let state = ServerState::new();
    let params = GetProofStateParams {
        state_id: "ps_invalid123456789012345678901234".to_string(),
        format: crate::proof_state::OutputFormat::Llm,
    };

    let response = handle_get_proof_state(&state, RequestId::Number(1), params).await;
    // Should return error for invalid state
    assert!(
        response.error.is_some(),
        "invalid state_id should return an error"
    );
}

// =========================================================================
// extractProof error path tests (#1654)
// =========================================================================

/// Test extractProof with an invalid state_id returns an error.
#[tokio::test]
async fn test_extract_proof_invalid_state_id() {
    let state = ServerState::new();
    let params = ExtractProofParams {
        state_id: "ps_00000000000000000000000000000000".to_string(),
        format: "term".to_string(),
    };

    let response = handle_extract_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "extractProof with invalid state_id should return an error"
    );
    let err = response.error.unwrap();
    assert!(
        err.message.contains("not found") || err.message.contains("expired"),
        "Error should mention state not found, got: {}",
        err.message
    );
}

/// Test extractProof with a malformed (non-parseable) state_id returns an error.
#[tokio::test]
async fn test_extract_proof_malformed_state_id() {
    let state = ServerState::new();
    let params = ExtractProofParams {
        state_id: "not_a_valid_id".to_string(),
        format: "term".to_string(),
    };

    let response = handle_extract_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "extractProof with malformed state_id should return an error"
    );
    let err = response.error.unwrap();
    assert!(
        err.message.contains("invalid state_id"),
        "Error should mention invalid state_id, got: {}",
        err.message
    );
}

/// Test extractProof on an unsolved proof state returns an error.
#[tokio::test]
async fn test_extract_proof_incomplete_proof() {
    let state = ServerState::new();

    // Initialize a proof state (unsolved — has remaining goals)
    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: Some("extract_test".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();
    assert!(
        !init_result.is_solved,
        "Proof state should not be solved yet"
    );

    // Try to extract proof from unsolved state
    let extract_params = ExtractProofParams {
        state_id: init_result.state_id.clone(),
        format: "term".to_string(),
    };
    let extract_response = handle_extract_proof(&state, RequestId::Number(2), extract_params).await;
    assert!(
        extract_response.error.is_some(),
        "extractProof on incomplete proof should return an error"
    );
    let err = extract_response.error.unwrap();
    assert!(
        err.message.contains("not complete") || err.message.contains("goals remain"),
        "Error should mention incomplete proof, got: {}",
        err.message
    );
}

/// Test getProofState with Full output format.
#[tokio::test]
async fn test_get_proof_state_full_format() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "Prop".to_string(),
        problem_id: Some("format_test".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let get_params = GetProofStateParams {
        state_id: init_result.state_id.clone(),
        format: crate::proof_state::OutputFormat::Full,
    };
    let get_response = handle_get_proof_state(&state, RequestId::Number(2), get_params).await;
    assert!(
        get_response.error.is_none(),
        "Unexpected error: {:?}",
        get_response.error
    );

    let result_json = get_response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "getProofState full");
    let api_state: crate::proof_state::ApiProofState = serde_json::from_value(result_json).unwrap();
    assert_eq!(api_state.state_id, init_result.state_id);
    assert_eq!(api_state.problem_id, Some("format_test".to_string()));
    assert!(api_state.mathverse_candidates.is_empty());
}

#[test]
fn test_api_proof_state_deserializes_missing_mathverse_candidates_as_empty() {
    let state_json = serde_json::json!({
        "state_id": "ps_00000000000000000000000000000000",
        "goals": [],
        "is_solved": false,
        "step_number": 0
    });

    let api_state: crate::proof_state::ApiProofState =
        serde_json::from_value(state_json).expect("legacy proof-state JSON should decode");
    assert!(api_state.mathverse_candidates.is_empty());
}

// ============================================================================
// Interactive trust-summary surface tests (#2716)
// ============================================================================

/// getProofState returns trust_summary for a cached state.
#[tokio::test]
async fn test_get_proof_state_trust_summary_present() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: Some("trust_test".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let get_params = GetProofStateParams {
        state_id: init_result.state_id.clone(),
        format: crate::proof_state::OutputFormat::Llm,
    };
    let get_response = handle_get_proof_state(&state, RequestId::Number(2), get_params).await;
    assert!(get_response.error.is_none());

    let api_state: crate::proof_state::ApiProofState =
        serde_json::from_value(get_response.result.unwrap()).unwrap();

    let ts = api_state
        .trust_summary
        .expect("getProofState should include trust_summary for a valid cached state");
    assert_eq!(ts.sorry_count, 0);
    assert_eq!(ts.ay_count, 0);
    assert_eq!(ts.arith_count, 0);
    assert!(ts.arith_provenance.is_none());
    assert!(
        !ts.fully_verified,
        "unsolved proof state should not be fully_verified"
    );
}

/// getProofState trust_summary is consistent across re-reads of the same cached state.
#[tokio::test]
async fn test_get_proof_state_trust_summary_stable_across_reads() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Read the same state twice
    let get1 = {
        let params = GetProofStateParams {
            state_id: init_result.state_id.clone(),
            format: crate::proof_state::OutputFormat::Full,
        };
        let resp = handle_get_proof_state(&state, RequestId::Number(2), params).await;
        let api: crate::proof_state::ApiProofState =
            serde_json::from_value(resp.result.unwrap()).unwrap();
        api.trust_summary
    };
    let get2 = {
        let params = GetProofStateParams {
            state_id: init_result.state_id.clone(),
            format: crate::proof_state::OutputFormat::Full,
        };
        let resp = handle_get_proof_state(&state, RequestId::Number(3), params).await;
        let api: crate::proof_state::ApiProofState =
            serde_json::from_value(resp.result.unwrap()).unwrap();
        api.trust_summary
    };

    assert!(get1.is_some() && get2.is_some());
    let ts1 = get1.unwrap();
    let ts2 = get2.unwrap();
    assert_eq!(ts1.sorry_count, ts2.sorry_count);
    assert_eq!(ts1.ay_count, ts2.ay_count);
    assert_eq!(ts1.arith_count, ts2.arith_count);
    assert_eq!(ts1.arith_provenance, ts2.arith_provenance);
    assert_eq!(ts1.fully_verified, ts2.fully_verified);
}

#[tokio::test]
async fn test_get_proof_state_trust_summary_reports_arith_provenance() {
    let env = Environment::with_prelude();
    let mut proof_state =
        InternalProofState::new(env.clone(), Expr::const_(Name::from_string("True"), vec![]));
    convert(
        &mut proof_state,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    )
    .expect("True.intro should close the proof state");
    proof_state.set_trust_ledger(ProofTrustLedger {
        trusted_arith_count: 2,
        trusted_arith_provenance: TrustedArithProvenanceLedger {
            direct_steps: 1,
            goal_close_helper_steps: 1,
            ..TrustedArithProvenanceLedger::default()
        },
        ..ProofTrustLedger::default()
    });

    let state = ServerState::new().with_env(env);
    let state_id = state
        .proof_cache
        .insert(proof_state, None, None, 0)
        .to_string();

    let get_params = GetProofStateParams {
        state_id,
        format: crate::proof_state::OutputFormat::Full,
    };
    let get_response = handle_get_proof_state(&state, RequestId::Number(3), get_params).await;
    assert!(get_response.error.is_none(), "{:?}", get_response.error);

    let api_state: crate::proof_state::ApiProofState =
        serde_json::from_value(get_response.result.unwrap()).unwrap();
    let trust_summary = api_state
        .trust_summary
        .expect("getProofState should include trust_summary for cached states");
    let provenance = trust_summary
        .arith_provenance
        .as_ref()
        .expect("trustedArith debt should expose provenance details");

    assert_eq!(trust_summary.arith_count, 2);
    assert_eq!(provenance.direct_steps, 1);
    assert_eq!(provenance.goal_close_helper_steps, 1);
    assert_eq!(provenance.target_rewrite_helper_steps, 0);
    assert_eq!(provenance.unclassified_steps, 0);
    assert!(
        !trust_summary.fully_verified,
        "trustedArith-backed states must not be fully verified"
    );
}
