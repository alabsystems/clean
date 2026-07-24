// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

/// Helper: create a `ServerState` pre-loaded with the kernel prelude (Nat, Bool, Eq, List, ...).
fn prelude_state() -> ServerState {
    let env =
        clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
    ServerState::new().with_env(env)
}

// =========================================================================
// Declaration path tests for handle_check (#1654, #2460)
// =========================================================================

/// Test handle_check with a valid declaration (theorem).
/// This exercises the parse_decl -> elaborate_decl path in check_code_impl.
#[tokio::test]
async fn test_check_valid_declaration() {
    let state = prelude_state();
    let params = CheckParams {
        code: "theorem trivial_check : True := True.intro".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Valid declaration should not produce RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.valid,
        "Valid theorem declaration should pass check, got errors: {:?}",
        result.errors
    );
    assert!(
        result.inferred_type.is_some(),
        "Declaration path should report its elaborated type"
    );
}

/// Test handle_check with a def declaration.
/// Requires prelude for Nat/Nat.zero.
#[tokio::test]
async fn test_check_valid_def_declaration() {
    let state = prelude_state();
    let params = CheckParams {
        code: "def myNat : Nat := Nat.zero".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Valid def should not produce RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.valid,
        "Valid def declaration should pass check, got errors: {:?}",
        result.errors
    );
    assert!(
        result.inferred_type.is_some(),
        "Valid definitions should report their elaborated type"
    );
}

#[tokio::test]
async fn test_check_rejects_type_mismatch_theorem() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "theorem bad_prop : Prop := Type".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Type-mismatched theorem should return a check result: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid, "Ill-typed theorem must be rejected");
    assert!(
        result
            .errors
            .iter()
            .any(|err| err.message.contains("Type check error")),
        "Expected kernel type-check diagnostics, got: {:?}",
        result.errors
    );
}

#[tokio::test]
async fn test_check_rejects_type_mismatch_def() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "def bad_prop : Prop := Type".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Type-mismatched definition should return a check result: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid, "Ill-typed definition must be rejected");
    assert!(
        result
            .errors
            .iter()
            .any(|err| err.message.contains("Type check error")),
        "Expected kernel type-check diagnostics, got: {:?}",
        result.errors
    );
}

#[tokio::test]
async fn test_check_rejects_non_prop_theorem_type() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "theorem not_a_prop : Type := Type".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Non-Prop theorem should return a check result: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.valid,
        "Theorem targets outside Prop must be rejected"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|err| err.message.contains("type must be a Prop")),
        "Expected theorem Prop-check diagnostic, got: {:?}",
        result.errors
    );
}

#[tokio::test]
async fn test_check_does_not_prefix_match_theorem_declaration() {
    let state = prelude_state();
    let params = CheckParams {
        code: "theorem id_true : True := True.intro".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Exact declaration parsing should succeed without RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.valid,
        "Full theorem declaration should be checked via the declaration path, got: {:?}",
        result.errors
    );
    assert!(
        result.inferred_type.is_some(),
        "Declaration-path success should still report the elaborated type"
    );
}

#[tokio::test]
async fn test_check_rejects_skipped_declaration_kind() {
    let state = prelude_state();
    let params = CheckParams {
        code: "example : True := True.intro".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Skipped declaration should return a check result: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.valid,
        "Skipped declaration kinds must not be reported as valid"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|err| err.message.contains("unsupported declaration kind")),
        "Expected unsupported declaration diagnostic, got: {:?}",
        result.errors
    );
}

/// Regression test: declaration with trailing garbage must be rejected.
/// Before #2553, the declaration fallback used a prefix parser that silently
/// accepted trailing tokens (e.g., `theorem t : True := True.intro, garbage`).
#[tokio::test]
async fn test_check_rejects_declaration_with_trailing_garbage() {
    let state = prelude_state();
    // Comma after body creates a trailing token the expr parser won't consume.
    let params = CheckParams {
        code: "theorem t : True := True.intro, garbage".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Trailing garbage should return a check result, not RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.valid,
        "Declaration with trailing garbage must be rejected"
    );
    assert!(
        result
            .errors
            .iter()
            .any(|err| err.message.contains("trailing")),
        "Error should mention trailing tokens, got: {:?}",
        result.errors
    );
}
