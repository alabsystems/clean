// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

/// Test verifyFile with simple theorem + proof
#[tokio::test]
async fn test_verify_file_simple() {
    let state = ServerState::new();

    let content = r#"
theorem eq_refl_test : 1 = 1 := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("rfl".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Handler error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // The theorem should be extracted
    let thm = result
        .theorem
        .expect("theorem should be extracted from simple file");
    assert_eq!(thm.name, "eq_refl_test");

    // Check timing breakdown
    assert!(
        result.timing.is_some(),
        "timing breakdown should be present"
    );
    assert!(result.time_ns > 0);
}

/// Test verifyFile without proof returns extracted info
#[tokio::test]
async fn test_verify_file_no_proof() {
    let state = ServerState::new();

    let content = r#"
theorem my_theorem (A : Type) : A -> A := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: None,
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Should not be verified (no proof provided)
    assert!(!result.verified);

    // But should extract theorem info
    let thm = result
        .theorem
        .expect("theorem info should be extracted even without proof");
    assert_eq!(thm.name, "my_theorem");

    // Should have sorry location
    assert!(!result.sorries.is_empty());

    // Error should mention no proof
    let err = result
        .error
        .expect("should have error when no proof provided");
    assert!(
        err.message.contains("no proof"),
        "error message should mention 'no proof', got: {}",
        err.message
    );
}

/// Test verifyFile replays constructor-based proof scripts.
#[tokio::test]
async fn test_verify_file_constructor_script() {
    let state = ServerState::new();

    let content = r#"
lemma pair_true : True ∧ True := by
  exact And.intro True.intro True.intro
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("constructor\nexact True.intro\nexact True.intro".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.verified,
        "constructor-based script should verify, got: {result:?}"
    );
    assert!(
        result.error.is_none(),
        "verified script should not report an error"
    );
    assert!(
        result.sorries.is_empty(),
        "text without explicit sorry should stay sorry-free"
    );
}

/// Test verifyFile with sorry detection
#[tokio::test]
async fn test_verify_file_sorry_detection() {
    let state = ServerState::new();

    let content = r#"
lemma multiple_goals : True ∧ True := by
  constructor
  sorry
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: None,
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Should detect multiple sorries
    assert_eq!(result.sorries.len(), 2, "Expected 2 sorries");

    // Both sorries should have the lemma as context
    for sorry in &result.sorries {
        assert_eq!(sorry.context, Some("multiple_goals".to_string()));
    }
}

/// Test verifyFile timing breakdown
#[tokio::test]
async fn test_verify_file_timing_breakdown() {
    let state = ServerState::new();

    let content = r#"
theorem timing_test : 1 = 1 := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("rfl".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Timing breakdown should be present
    let timing = result.timing.expect("timing breakdown should be present");

    // All timing fields should be positive
    assert!(timing.parse_ns > 0, "Parse time should be > 0");
    // Note: elaborate_ns and verify_ns may be 0 if goal parsing fails
    assert!(timing.total_ns > 0, "Total time should be > 0");

    // Total should be >= sum of parts
    assert!(timing.total_ns >= timing.parse_ns);
}

/// Test that verifyFile initializes FATE Mathlib stubs (#91)
#[tokio::test]
async fn test_verify_file_fate_stubs_initialized() {
    let state = ServerState::new();

    // Verify FATE stubs are NOT initialized before call
    {
        let env = state.env.read().await;
        assert!(
            !env.has_prime(),
            "Prime should not be initialized before verifyFile call"
        );
        assert!(
            !env.has_comm_ring(),
            "CommRing should not be initialized before verifyFile call"
        );
        assert!(
            !env.has_field(),
            "Field should not be initialized before verifyFile call"
        );
        assert!(
            !env.has_module(),
            "Module should not be initialized before verifyFile call"
        );
    }

    // FATE-style theorem that references Mathlib types
    // This uses a simple type that can actually be parsed
    let content = r#"
theorem fate_stub_test : Nat -> Nat := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: None, // No proof, just test stub initialization
        timeout_ms: Some(5000),
    };

    let _response = handle_verify_file(&state, RequestId::Number(1), params).await;

    // Verify core FATE stubs ARE initialized after call.
    // The handler uses `let _ = init_*()` to tolerate failures, so we check
    // the stubs whose dependencies are guaranteed available in a fresh env.
    {
        let env = state.env.read().await;
        assert!(
            env.has_ring(),
            "Ring should be initialized after verifyFile call"
        );
        assert!(env.has_comm_ring(), "CommRing should be initialized");
        assert!(env.has_field(), "Field should be initialized");
        assert!(
            env.has_integral_domain(),
            "IntegralDomain should be initialized"
        );
        assert!(env.has_module(), "Module should be initialized");
        assert!(env.has_algebra(), "Algebra should be initialized");
        assert!(env.has_domain_types(), "Domain types should be initialized");
        assert!(env.has_prime(), "Prime should be initialized");
        assert!(
            env.has_is_principal_ideal_ring(),
            "IsPrincipalIdealRing should be initialized"
        );
        assert!(env.has_associated(), "Associated should be initialized");
        assert!(env.has_ufm(), "UFM should be initialized");

        // Verify core type constants exist
        assert!(
            env.get_const(&clean_kernel::Name::from_string("CommRing"))
                .is_some(),
            "CommRing constant should exist"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("Field"))
                .is_some(),
            "Field constant should exist"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("Module"))
                .is_some(),
            "Module constant should exist"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("Prime"))
                .is_some(),
            "Prime constant should exist"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("IsPrincipalIdealRing"))
                .is_some(),
            "IsPrincipalIdealRing constant should exist"
        );
    }
}

// =========================================================================
// Error response path tests (#1654)
// =========================================================================

/// Test verifyFile with completely invalid syntax returns an error (not a crash).
#[tokio::test]
async fn test_verify_file_invalid_syntax_error() {
    let state = ServerState::new();

    let params = VerifyFileParams {
        content: "@@#$ completely invalid syntax !!{{".to_string(),
        proof: Some("rfl".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result (not RPC error) even for parse failures: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "Invalid syntax should not verify");
    assert!(
        result.theorem.is_none(),
        "No theorem should be extracted from garbage input"
    );

    let err = result
        .error
        .expect("Should have error details for invalid input");
    let msg = err.message.to_lowercase();
    // The handler's string-based parser doesn't fail on invalid syntax;
    // it simply finds no theorem/lemma keyword and reports "no theorem found".
    assert!(
        msg.contains("no theorem") || msg.contains("parse") || msg.contains("syntax"),
        "Error should indicate no theorem or parse failure, got: {}",
        err.message
    );
    assert!(
        !err.suggestions.is_empty(),
        "Should provide suggestions on error"
    );
}

/// Test verifyFile with file that contains no theorem/lemma declaration.
#[tokio::test]
async fn test_verify_file_no_theorem_found() {
    let state = ServerState::new();

    // Valid Lean-ish syntax but no theorem/lemma
    let content = r#"
-- just a comment
def my_func : Nat := 42
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("rfl".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result, not RPC error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "No theorem means not verified");

    let err = result
        .error
        .expect("Should have error when no theorem found");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("no theorem") || msg.contains("no proof"),
        "Error should mention missing theorem, got: {}",
        err.message
    );
}

/// Test verifyFile with a failing proof returns error details.
#[tokio::test]
async fn test_verify_file_failing_proof_error_details() {
    let state = ServerState::new();

    let content = r#"
theorem hard_theorem (n : Nat) : n = n + 1 := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("rfl".to_string()), // rfl can't prove n = n + 1
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result, not RPC error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "Wrong proof should not verify");

    // Theorem should still be extracted even if proof fails
    let thm = result
        .theorem
        .expect("Theorem info should be extracted even on proof failure");
    assert_eq!(thm.name, "hard_theorem");

    // Error should have details about why the proof failed
    assert!(
        result.error.is_some(),
        "Should have error details for failed proof"
    );
}

/// Test verifyFile with empty content.
#[tokio::test]
async fn test_verify_file_empty_content() {
    let state = ServerState::new();

    let params = VerifyFileParams {
        content: String::new(),
        proof: None,
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result, not RPC error for empty content: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified);
    // Should have timing even for empty input
    assert!(
        result.time_ns > 0,
        "Should have timing even for empty input"
    );
}

// ========================================================================
// Error-path gap coverage (#1654 — acceptance criterion 2)
// ========================================================================

/// Test verifyFile with a theorem whose goal references an unknown constant.
/// Covers the elaboration failure path at handle_verify_file lines 2236-2263:
///   "failed to elaborate goal: ..."
///   suggestion: "goal type may require Mathlib context"
#[tokio::test]
async fn test_verify_file_goal_elaboration_failure() {
    let state = ServerState::new();

    // The file has a valid theorem declaration referencing an unknown type.
    // parse_lean_file will extract the theorem, but elaborate will fail.
    let content = r#"
theorem my_thm : CompletelyUndefinedMathType42 := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("sorry".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "verify_file returns result even on elaboration error (not RPC error): {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.verified,
        "Should not be verified when goal fails elaboration"
    );

    let error = result.error.expect("Should have error details");
    let msg = error.message.to_lowercase();
    assert!(
        msg.contains("elaborate") || msg.contains("parse") || msg.contains("goal"),
        "Error should mention elaboration or goal issue, got: {}",
        error.message
    );
}

/// Test verifyFile where a proof is provided but tactics leave goals open.
/// Covers the "proof incomplete" fallback at handle_verify_file lines 2387-2396.
#[tokio::test]
async fn test_verify_file_proof_incomplete() {
    let state = ServerState::new();

    // A theorem with a multi-step goal.  Providing only one "intro" leaves goals open.
    let content = r#"
theorem id2 (A : Type) (a : A) : A := by
  intro
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("intro".to_string()), // Only introduces one binder; second goal remains
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "verify_file should return result, not RPC error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.verified,
        "Should not be verified when proof is incomplete"
    );

    // The error should indicate an incomplete proof or tactic failure
    let error = result.error.expect("Should have error details");
    let msg = error.message.to_lowercase();
    assert!(
        msg.contains("incomplete") || msg.contains("failed") || msg.contains("tactic"),
        "Error should mention incomplete proof or tactic failure, got: {}",
        error.message
    );
}

// ==== Premise Selection Tests ====
