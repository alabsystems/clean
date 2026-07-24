// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

#[tokio::test]
async fn test_save_load_roundtrip_bincode() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!(
        "clean_test_roundtrip_{}.bincode",
        std::process::id()
    ));

    // Get initial state
    let get_params1 = GetEnvironmentParams {
        include_json: false,
    };
    let get_response1 = handle_get_environment(&state, RequestId::Number(1), get_params1).await;
    let initial: GetEnvironmentResult =
        serde_json::from_value(get_response1.result.unwrap()).unwrap();

    // Save
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(2), save_params).await;
    assert!(
        save_response.error.is_none(),
        "unexpected save error: {:?}",
        save_response.error
    );

    // Load into fresh state
    let state2 = ServerState::new();
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state2, RequestId::Number(3), load_params).await;
    assert!(
        load_response.error.is_none(),
        "unexpected load error: {:?}",
        load_response.error
    );

    // Verify state matches
    let get_params2 = GetEnvironmentParams {
        include_json: false,
    };
    let get_response2 = handle_get_environment(&state2, RequestId::Number(4), get_params2).await;
    let final_state: GetEnvironmentResult =
        serde_json::from_value(get_response2.result.unwrap()).unwrap();

    assert_eq!(initial.num_constants, final_state.num_constants);
    assert_eq!(initial.num_inductives, final_state.num_inductives);

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_save_load_roundtrip_json() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_roundtrip_{}.json", std::process::id()));

    // Save as JSON
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_none(),
        "unexpected save error: {:?}",
        save_response.error
    );

    // Load from JSON
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(2), load_params).await;
    assert!(
        load_response.error.is_none(),
        "unexpected load error: {:?}",
        load_response.error
    );

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

// =========================================================================
// Error-path tests for save/load handlers (#1654)
// =========================================================================

/// Test loading a file saved as bincode with format "json" produces an error.
#[tokio::test]
async fn test_load_format_mismatch_bincode_as_json() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!(
        "clean_test_mismatch_{}.bincode",
        std::process::id()
    ));

    // Save as bincode
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_none(),
        "Save should succeed: {:?}",
        save_response.error
    );

    // Try to load as JSON — should fail with deserialization error
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(2), load_params).await;
    assert!(
        load_response.error.is_some(),
        "Loading bincode as JSON should produce an RPC error, got result: {:?}",
        load_response.result
    );
    let err = load_response.error.unwrap();
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("failed") || msg.contains("load") || msg.contains("parse"),
        "Error should describe load failure, got: {}",
        err.message
    );

    let _ = fs::remove_file(&temp_file);
}

/// Test loading a corrupt (garbage) file produces an error, not a panic.
#[tokio::test]
async fn test_load_corrupt_file_returns_error() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_corrupt_{}.bincode", std::process::id()));

    // Write garbage bytes
    fs::write(&temp_file, b"this is not valid bincode data \x00\xff\xfe").unwrap();

    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    assert!(
        load_response.error.is_some(),
        "Loading corrupt file should produce RPC error, got result: {:?}",
        load_response.result
    );

    let _ = fs::remove_file(&temp_file);
}

/// Test loading a corrupt JSON file produces an error.
#[tokio::test]
async fn test_load_corrupt_json_returns_error() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_corrupt_{}.json", std::process::id()));

    // Write invalid JSON
    fs::write(&temp_file, b"{\"not\": \"an environment\", broken}").unwrap();

    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    assert!(
        load_response.error.is_some(),
        "Loading corrupt JSON should produce RPC error, got result: {:?}",
        load_response.result
    );

    let _ = fs::remove_file(&temp_file);
}

/// Test saving to a nonexistent directory returns an error.
#[tokio::test]
async fn test_save_to_nonexistent_directory() {
    let state = ServerState::new();

    let save_params = SaveEnvironmentParams {
        path: "/nonexistent/dir/that/does/not/exist/env.bincode".to_string(),
        format: Some("bincode".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_some(),
        "Save to nonexistent dir should produce RPC error, got result: {:?}",
        save_response.result
    );
}

/// Test loading a nonexistent file returns an error.
#[tokio::test]
async fn test_load_nonexistent_file() {
    let state = ServerState::new();

    let load_params = LoadEnvironmentParams {
        path: "/tmp/clean_this_file_does_not_exist_12345.bincode".to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    assert!(
        load_response.error.is_some(),
        "Loading nonexistent file should produce RPC error, got result: {:?}",
        load_response.result
    );
}

// =========================================================================
// serverInfo handler tests (#1654)
// =========================================================================

/// Test serverInfo returns expected structure with name, version, and methods.
#[tokio::test]
async fn test_server_info_returns_name_and_version() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    assert!(
        response.error.is_none(),
        "serverInfo should succeed: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(info.name, "clean-server");
    assert!(!info.version.is_empty(), "version should be non-empty");
    assert!(!info.methods.is_empty(), "methods list should be non-empty");
}

/// Test serverInfo reports GPU disabled on default state.
#[tokio::test]
async fn test_server_info_gpu_disabled_by_default() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!info.gpu_available, "GPU should be disabled by default");
}

/// Test serverInfo reports GPU enabled when state has GPU.
#[tokio::test]
async fn test_server_info_gpu_enabled() {
    let state = ServerState::new().with_gpu(true);
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(info.gpu_available, "GPU should be reported as available");
}

/// Test serverInfo methods list includes core handlers.
#[tokio::test]
async fn test_server_info_methods_include_core() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.iter().any(|m| m == "check"),
        "methods should include 'check', got: {:?}",
        info.methods
    );
    assert!(
        info.methods.iter().any(|m| m == "getType"),
        "methods should include 'getType', got: {:?}",
        info.methods
    );
}

// =========================================================================
// getConfig handler tests (#1654)
// =========================================================================

/// Test getConfig returns expected defaults.
#[tokio::test]
async fn test_get_config_defaults() {
    let state = ServerState::new();
    let response = handle_get_config(&state, RequestId::Number(1)).await;
    assert!(
        response.error.is_none(),
        "getConfig should succeed: {:?}",
        response.error
    );
    let config: GetConfigResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!config.gpu_enabled, "GPU should be disabled by default");
    assert_eq!(config.default_timeout_ms, 5000, "default timeout is 5000ms");
    assert_eq!(
        config.worker_threads, 0,
        "default worker_threads is 0 (auto)"
    );
    assert!(
        config.effective_threads > 0,
        "effective_threads should be > 0 even with auto"
    );
}

/// Test getConfig reflects custom GPU and thread settings.
#[tokio::test]
async fn test_get_config_custom_settings() {
    let state = ServerState::new().with_gpu(true).with_worker_threads(4);
    let response = handle_get_config(&state, RequestId::Number(1)).await;
    let config: GetConfigResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(config.gpu_enabled, "GPU should be enabled");
    assert_eq!(config.worker_threads, 4);
    assert_eq!(
        config.effective_threads, 4,
        "effective_threads should equal worker_threads when explicitly set"
    );
}

// =========================================================================
// getEnvironment handler tests (#1654)
// =========================================================================

/// Test getEnvironment on empty state returns no JSON when not requested.
#[tokio::test]
async fn test_get_environment_no_json_by_default() {
    let state = ServerState::new();
    let params = GetEnvironmentParams {
        include_json: false,
    };
    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getEnvironment should succeed: {:?}",
        response.error
    );
    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.json.is_none(),
        "JSON should be None when not requested"
    );
}

/// Test getEnvironment with include_json returns JSON string.
#[tokio::test]
async fn test_get_environment_include_json() {
    let state = ServerState::new();
    let params = GetEnvironmentParams { include_json: true };
    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getEnvironment should succeed: {:?}",
        response.error
    );
    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    if let Some(json_str) = &result.json {
        let parsed: Result<serde_json::Value, _> = serde_json::from_str(json_str);
        assert!(
            parsed.is_ok(),
            "JSON representation should be valid JSON, got error: {:?}",
            parsed.err()
        );
    }
}

/// Test getEnvironment constant_names is bounded (max 100).
#[tokio::test]
async fn test_get_environment_constant_names_bounded() {
    let state = ServerState::new();
    let params = GetEnvironmentParams {
        include_json: false,
    };
    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.constant_names.len() <= 100,
        "constant_names should be bounded to 100, got {}",
        result.constant_names.len()
    );
}

/// Test that unknown format strings fall through to bincode (current behavior).
#[tokio::test]
async fn test_save_unknown_format_falls_through_to_bincode() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_unkfmt_{}.dat", std::process::id()));

    // Save with unknown format — should not error (falls through to bincode)
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("xml".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_none(),
        "Unknown format should fall through to bincode without error: {:?}",
        save_response.error
    );

    // Verify the file was created and is loadable as bincode
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(2), load_params).await;
    assert!(
        load_response.error.is_none(),
        "Should be loadable as bincode: {:?}",
        load_response.error
    );

    let _ = fs::remove_file(&temp_file);
}
