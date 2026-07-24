// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::env::TrustedEnvExt;

#[tokio::test]
async fn test_get_premises_hybrid() {
    let state = ServerState::new();

    // Add some constants to the environment so premise selection has something to work with
    {
        let mut env = state.env.write().await;
        // Add basic types and theorems
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat.add"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(
                clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
                clean_kernel::Expr::arrow(
                    clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
                    clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
                ),
            ),
        });
    }

    let params = GetPremisesParams {
        goal: "Nat".to_string(),
        method: "hybrid".to_string(),
        max_premises: 10,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );
    let result: GetPremisesResult = serde_json::from_value(
        response
            .result
            .expect("hybrid premise response should have result"),
    )
    .unwrap();
    assert_eq!(result.stats.method_used, "hybrid");
}

#[tokio::test]
async fn test_get_premises_mepo() {
    let state = ServerState::new();

    {
        let mut env = state.env.write().await;
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Bool"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
    }

    let params = GetPremisesParams {
        goal: "Bool".to_string(),
        method: "mepo".to_string(),
        max_premises: 5,
        threshold: 0.1,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: GetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.method_used, "mepo");
}

#[tokio::test]
async fn test_get_premises_mash() {
    let state = ServerState::new();

    {
        let mut env = state.env.write().await;
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Prop"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
    }

    let params = GetPremisesParams {
        goal: "Prop".to_string(),
        method: "mash".to_string(),
        max_premises: 5,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: GetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.method_used, "mash");
}

#[tokio::test]
async fn test_get_premises_invalid_goal() {
    let state = ServerState::new();

    let params = GetPremisesParams {
        goal: "<<<invalid>>>".to_string(),
        method: "hybrid".to_string(),
        max_premises: 10,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    // Should return an error for invalid goal syntax
    assert!(
        response.error.is_some(),
        "Expected error for invalid goal syntax"
    );
}

#[tokio::test]
async fn test_batch_get_premises() {
    let state = ServerState::new();

    {
        let mut env = state.env.write().await;
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Bool"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
    }

    let params = BatchGetPremisesParams {
        items: vec![
            BatchGetPremisesItem {
                id: "goal1".to_string(),
                goal: "Nat".to_string(),
            },
            BatchGetPremisesItem {
                id: "goal2".to_string(),
                goal: "Bool".to_string(),
            },
        ],
        method: "hybrid".to_string(),
        max_premises: 5,
        threshold: 0.0,
        timeout_ms: Some(10000),
    };

    let response = handle_batch_get_premises(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );
    let result: BatchGetPremisesResult = serde_json::from_value(
        response
            .result
            .expect("batch premise response should have result"),
    )
    .unwrap();
    assert_eq!(result.results.len(), 2);
    assert_eq!(result.results[0].id, "goal1");
    assert_eq!(result.results[1].id, "goal2");
    assert!(result.results[0].success, "First goal should succeed");
    assert!(result.results[1].success, "Second goal should succeed");
}

#[tokio::test]
async fn test_batch_get_premises_mixed_success() {
    let state = ServerState::new();

    {
        let mut env = state.env.write().await;
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });
    }

    let params = BatchGetPremisesParams {
        items: vec![
            BatchGetPremisesItem {
                id: "valid".to_string(),
                goal: "Nat".to_string(),
            },
            BatchGetPremisesItem {
                id: "invalid".to_string(),
                goal: "<<<invalid>>>".to_string(),
            },
        ],
        method: "hybrid".to_string(),
        max_premises: 5,
        threshold: 0.0,
        timeout_ms: Some(10000),
    };

    let response = handle_batch_get_premises(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Batch should complete even with failures: {:?}",
        response.error
    );

    let result: BatchGetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 2);
    assert!(result.results[0].success, "Valid goal should succeed");
    assert!(!result.results[1].success, "Invalid goal should fail");
    assert!(
        result.results[1].error.is_some(),
        "Failed item should have error message"
    );
}

#[tokio::test]
async fn test_batch_get_premises_empty() {
    let state = ServerState::new();

    let params = BatchGetPremisesParams {
        items: vec![],
        method: "hybrid".to_string(),
        max_premises: 5,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_batch_get_premises(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Empty batch should succeed: {:?}",
        response.error
    );

    let result: BatchGetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 0);
}

#[tokio::test]
async fn test_get_premises_with_populated_env() {
    let state = ServerState::new();

    // Populate environment with multiple relevant theorems
    {
        let mut env = state.env.write().await;

        // Base types
        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat"),
            level_params: vec![],
            type_: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        });

        // Theorems involving Nat
        let nat_type = clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let prop_type = clean_kernel::Expr::sort(clean_kernel::Level::zero());

        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat.zero_add"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(nat_type.clone(), prop_type.clone()),
        });

        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat.add_zero"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(nat_type.clone(), prop_type.clone()),
        });

        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat.add_comm"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(
                nat_type.clone(),
                clean_kernel::Expr::arrow(nat_type.clone(), prop_type.clone()),
            ),
        });

        env.add_decl_unchecked(clean_kernel::Declaration::Axiom {
            name: clean_kernel::Name::from_string("Nat.add_assoc"),
            level_params: vec![],
            type_: clean_kernel::Expr::arrow(
                nat_type.clone(),
                clean_kernel::Expr::arrow(
                    nat_type.clone(),
                    clean_kernel::Expr::arrow(nat_type, prop_type),
                ),
            ),
        });
    }

    let params = GetPremisesParams {
        goal: "Nat".to_string(),
        method: "hybrid".to_string(),
        max_premises: 10,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: GetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Should find premises from the populated environment
    assert!(
        result.stats.candidates_scanned > 0,
        "Should have scanned candidates"
    );
}
