// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::env::TrustedEnvExt;

#[tokio::test]
async fn test_get_environment_empty() {
    let state = ServerState::new();

    let params = GetEnvironmentParams {
        include_json: false,
    };

    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // New environments auto-initialize sorry + trustedArith + trustedAy axioms
    assert_eq!(result.num_constants, 3);
    assert_eq!(result.num_inductives, 0);
    assert_eq!(result.constant_names.len(), 3);
    assert!(result.constant_names.contains(&"sorry".to_string()));
    assert!(result.constant_names.contains(&"trustedArith".to_string()));
    assert!(result.constant_names.contains(&"trustedAy".to_string()));
    assert!(
        result.json.is_none(),
        "json should be None when include_json=false"
    );
}

#[tokio::test]
async fn test_get_environment_with_json() {
    let state = ServerState::new();

    let params = GetEnvironmentParams { include_json: true };

    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // JSON should be present (even if empty environment)
    let json_str = result
        .json
        .expect("json should be present when include_json=true");
    assert!(!json_str.is_empty());
}

#[tokio::test]
async fn test_get_environment_json_serialization() {
    let result = GetEnvironmentResult {
        num_constants: 5,
        num_inductives: 3,
        constant_names: vec!["Nat".to_string(), "Bool".to_string()],
        json: Some("{\"test\": true}".to_string()),
    };

    let json = serde_json::to_string(&result).expect("Should serialize");
    let deserialized: GetEnvironmentResult =
        serde_json::from_str(&json).expect("Should deserialize");

    assert_eq!(deserialized.num_constants, 5);
    assert_eq!(deserialized.num_inductives, 3);
    assert_eq!(
        deserialized.constant_names,
        vec!["Nat".to_string(), "Bool".to_string()],
        "constant names should survive serialization roundtrip"
    );
    assert_eq!(
        deserialized.json.as_deref(),
        Some("{\"test\": true}"),
        "json content should survive serialization roundtrip"
    );
}

#[tokio::test]
async fn test_save_environment_bincode() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_env_{}.bincode", std::process::id()));

    let params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
    };

    let response = handle_save_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: SaveEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.success);
    // New environments auto-initialize sorry + trustedArith + trustedAy axioms
    assert_eq!(result.num_constants, 3);
    assert_eq!(result.num_inductives, 0);
    assert!(result.file_size > 0);

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_save_environment_json() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_env_{}.json", std::process::id()));

    let params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
    };

    let response = handle_save_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: SaveEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.success);

    // Verify the file is valid JSON
    let content = fs::read_to_string(&temp_file).expect("Should read file");
    let _: serde_json::Value = serde_json::from_str(&content).expect("Should be valid JSON");

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_save_environment_default_format() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_env_default_{}.bin", std::process::id()));

    let params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: None, // Should default to bincode
    };

    let response = handle_save_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: SaveEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.success);

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_save_environment_invalid_path() {
    let state = ServerState::new();

    let params = SaveEnvironmentParams {
        path: "/nonexistent/directory/that/does/not/exist/file.bin".to_string(),
        format: None,
    };

    let response = handle_save_environment(&state, RequestId::Number(1), params).await;
    // Should return an RPC error
    let err = response
        .error
        .expect("saving to nonexistent path should produce an error");
    assert!(
        err.message.contains("Failed to save"),
        "error should mention 'Failed to save', got: {}",
        err.message
    );
}

#[tokio::test]
async fn test_load_environment_bincode() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_load_{}.bincode", std::process::id()));

    // First save an environment
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_none(),
        "unexpected save error: {:?}",
        save_response.error
    );

    // Then load it
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let load_response = handle_load_environment(&state, RequestId::Number(2), load_params).await;
    assert!(
        load_response.error.is_none(),
        "Unexpected error: {:?}",
        load_response.error
    );

    let result: LoadEnvironmentResult =
        serde_json::from_value(load_response.result.unwrap()).unwrap();
    assert!(result.success);
    // Loaded environment has auto-initialized sorry + trustedArith + trustedAy axioms
    assert_eq!(result.num_constants, 3);
    assert_eq!(result.num_inductives, 0);

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_load_environment_json() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_load_{}.json", std::process::id()));

    // First save as JSON
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

    // Then load it
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

    let result: LoadEnvironmentResult =
        serde_json::from_value(load_response.result.unwrap()).unwrap();
    assert!(result.success);

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_load_environment_nonexistent_file() {
    let state = ServerState::new();

    let params = LoadEnvironmentParams {
        path: "/nonexistent/file/that/does/not/exist.bin".to_string(),
        format: None,
        replace: true,
    };

    let response = handle_load_environment(&state, RequestId::Number(1), params).await;
    let err = response
        .error
        .expect("loading nonexistent file should produce an error");
    assert!(
        err.message.contains("Failed to load"),
        "error should mention 'Failed to load', got: {}",
        err.message
    );
}

#[tokio::test]
async fn test_load_environment_replace_flag() {
    use std::fs;

    let state = ServerState::new();
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_replace_{}.bincode", std::process::id()));

    // Save environment
    let save_params = SaveEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
    };
    let save_response = handle_save_environment(&state, RequestId::Number(1), save_params).await;
    assert!(
        save_response.error.is_none(),
        "unexpected save error: {:?}",
        save_response.error
    );

    // Load with replace=true
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: true,
    };
    let response = handle_load_environment(&state, RequestId::Number(2), load_params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    // Load with replace=false (currently same behavior)
    let load_params2 = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: false,
    };
    let response2 = handle_load_environment(&state, RequestId::Number(3), load_params2).await;
    assert!(
        response2.error.is_none(),
        "load_environment should succeed, got: {:?}",
        response2.error
    );

    // cleanup
    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_save_environment_result_json_serialization() {
    let result = SaveEnvironmentResult {
        success: true,
        num_constants: 42,
        num_inductives: 7,
        file_size: 1024,
    };

    let json = serde_json::to_string(&result).expect("Should serialize");
    let deserialized: SaveEnvironmentResult =
        serde_json::from_str(&json).expect("Should deserialize");

    assert_eq!(deserialized.success, result.success);
    assert_eq!(deserialized.num_constants, result.num_constants);
    assert_eq!(deserialized.num_inductives, result.num_inductives);
    assert_eq!(deserialized.file_size, result.file_size);
}

#[tokio::test]
async fn test_load_environment_result_json_serialization() {
    let result = LoadEnvironmentResult {
        success: true,
        num_constants: 100,
        num_inductives: 20,
    };

    let json = serde_json::to_string(&result).expect("Should serialize");
    let deserialized: LoadEnvironmentResult =
        serde_json::from_str(&json).expect("Should deserialize");

    assert_eq!(deserialized.success, result.success);
    assert_eq!(deserialized.num_constants, result.num_constants);
    assert_eq!(deserialized.num_inductives, result.num_inductives);
}

#[tokio::test]
async fn test_import_module_nonexistent() {
    let state = ServerState::new();

    let params = ImportModuleParams {
        module: "NonExistent.Module.That.Does.Not.Exist".to_string(),
        search_paths: vec![],
    };

    let response = handle_import_module(&state, RequestId::Number(1), params).await;
    // Should return an error for a module that doesn't exist on disk
    let err = response
        .error
        .expect("importing nonexistent module should produce an error");
    assert!(
        err.message.contains("Failed to import module"),
        "error should mention import failure, got: {}",
        err.message
    );
}

fn get_lean_lib_path() -> std::path::PathBuf {
    clean_olean::default_search_paths()
        .into_iter()
        .find(|path| path.join("Init/Prelude.olean").exists())
        .unwrap_or_else(|| panic!("expected Lean 4 Init/Prelude.olean in default search paths"))
}

#[tokio::test]
async fn test_import_module_success_adds_constants_to_environment() {
    use clean_kernel::Name;

    let lib_path = get_lean_lib_path();

    let state = ServerState::new();
    let baseline_constants = {
        let env = state.env.read().await;
        assert!(
            env.get_const(&Name::from_string("Nat.zero")).is_none(),
            "Nat.zero should not be present before importing Init.Prelude"
        );
        env.num_constants()
    };

    let params = ImportModuleParams {
        module: "Init.Prelude".to_string(),
        search_paths: vec![lib_path.to_string_lossy().to_string()],
    };

    let response = handle_import_module(&state, RequestId::Number(2), params).await;
    assert!(
        response.error.is_none(),
        "importModule should succeed for Init.Prelude, got: {:?}",
        response.error
    );

    let result: ImportModuleResult = serde_json::from_value(
        response
            .result
            .expect("successful importModule should include a result"),
    )
    .expect("importModule result should deserialize");
    assert!(result.success, "importModule should report success");
    assert!(
        result
            .modules_loaded
            .iter()
            .any(|module| module == "Init.Prelude"),
        "expected Init.Prelude in loaded modules, got: {:?}",
        result.modules_loaded
    );
    assert!(
        result.constants_added > 0,
        "expected Init.Prelude import to add constants, got {}",
        result.constants_added
    );

    let env = state.env.read().await;
    assert!(
        env.num_constants() > baseline_constants,
        "import should increase constant count (before {}, after {})",
        baseline_constants,
        env.num_constants()
    );
    assert!(
        env.get_const(&Name::from_string("Nat.zero")).is_some(),
        "Nat.zero should be queryable after importing Init.Prelude"
    );
}

#[tokio::test]
async fn test_import_module_result_json_serialization() {
    let result = ImportModuleResult {
        success: true,
        modules_loaded: vec!["Init".to_string(), "Init.Core".to_string()],
        constants_added: 500,
        constants_skipped: 10,
    };

    let json = serde_json::to_string(&result).expect("Should serialize");
    let deserialized: ImportModuleResult = serde_json::from_str(&json).expect("Should deserialize");

    assert_eq!(deserialized.success, result.success);
    assert_eq!(deserialized.modules_loaded, result.modules_loaded);
    assert_eq!(deserialized.constants_added, result.constants_added);
    assert_eq!(deserialized.constants_skipped, result.constants_skipped);
}

/// Test that ServerState::with_env propagates a pre-populated environment.
/// This exercises the same code path as --init/--stdlib CLI pre-loading.
#[tokio::test]
async fn test_server_state_with_env_preloaded() {
    use clean_kernel::{Declaration, Expr, Name};

    // Build an environment with a custom declaration
    let mut env = clean_kernel::Environment::new();
    let decl = Declaration::Axiom {
        name: Name::from_string("Test.MyAxiom"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero),
    };
    env.add_decl_unchecked(decl);

    // Create server state with the pre-populated env
    let state = ServerState::new().with_env(env);

    // Query the environment via the handler
    let params = GetEnvironmentParams {
        include_json: false,
    };
    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Should contain our custom axiom + sorry (auto-initialized)
    assert!(
        result.constant_names.contains(&"Test.MyAxiom".to_string()),
        "Pre-loaded environment should contain Test.MyAxiom, got: {:?}",
        result.constant_names
    );
}

/// Helper: create a `ServerState` pre-loaded with the kernel prelude (Nat, Bool, Eq, List, …).
/// Exercises the same code path as `clean server --init`.
fn prelude_state() -> ServerState {
    let env =
        clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
    ServerState::new().with_env(env)
}

/// Helper: assert that `check` RPC succeeds for the given code string.
async fn assert_check_valid(state: &ServerState, code: &str) {
    let params = CheckParams {
        code: code.to_string(),
        timeout_ms: None,
    };
    let response = handle_check(state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "check {code} error: {:?}",
        response.error
    );
    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.valid, "{code} should be valid: {:?}", result.errors);
}

#[tokio::test]
async fn test_preloaded_env_check_nat() {
    assert_check_valid(&prelude_state(), "Nat").await;
}

#[tokio::test]
async fn test_preloaded_env_check_bool() {
    assert_check_valid(&prelude_state(), "Bool").await;
}

#[tokio::test]
async fn test_preloaded_env_check_eq_nat() {
    assert_check_valid(&prelude_state(), "@Eq Nat").await;
}

#[tokio::test]
async fn test_preloaded_env_check_list_nat() {
    assert_check_valid(&prelude_state(), "@List Nat").await;
}

#[tokio::test]
async fn test_preloaded_env_get_environment_counts() {
    let state = prelude_state();
    let params = GetEnvironmentParams {
        include_json: false,
    };
    let response = handle_get_environment(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getEnvironment error: {:?}",
        response.error
    );
    let result: GetEnvironmentResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.num_constants > 10,
        "prelude should have >10 constants, got {}",
        result.num_constants
    );
    assert!(
        result.num_inductives > 0,
        "prelude should have inductives, got {}",
        result.num_inductives
    );
}

/// Test that loadEnvironment merge (replace=false) preserves existing declarations.
#[tokio::test]
async fn test_load_environment_merge_preserves_existing() {
    use clean_kernel::{Declaration, Expr, Name};
    use std::fs;

    // Create state with a custom axiom
    let mut env = clean_kernel::Environment::new();
    let decl = Declaration::Axiom {
        name: Name::from_string("Existing.Axiom"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero),
    };
    env.add_decl_unchecked(decl);
    let state = ServerState::new().with_env(env);

    // Save a different environment to a temp file
    let mut env2 = clean_kernel::Environment::new();
    let decl2 = Declaration::Axiom {
        name: Name::from_string("New.Axiom"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero),
    };
    env2.add_decl_unchecked(decl2);

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_merge_{}.bincode", std::process::id()));
    env2.save_to_file(&temp_file).expect("save should work");

    // Load with replace=false — should merge
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: false,
    };
    let response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    // Verify both axioms exist
    let get_params = GetEnvironmentParams {
        include_json: false,
    };
    let get_response = handle_get_environment(&state, RequestId::Number(2), get_params).await;
    let result: GetEnvironmentResult =
        serde_json::from_value(get_response.result.unwrap()).unwrap();
    assert!(
        result
            .constant_names
            .contains(&"Existing.Axiom".to_string()),
        "Merge should preserve existing Existing.Axiom"
    );
    assert!(
        result.constant_names.contains(&"New.Axiom".to_string()),
        "Merge should add New.Axiom"
    );

    let _ = fs::remove_file(&temp_file);
}

/// Regression test for the loadEnvironment merge path: unchecked serialized constants
/// must be kernel-checked before they enter the server environment.
#[tokio::test]
async fn test_load_environment_merge_rejects_uncheckable_theorem_or_opaque() {
    use clean_kernel::{Declaration, Expr, Name};
    use std::fs;

    // Create an environment with constants that structural insertion used to accept,
    // but whose values do not type-check against their declared types.
    let mut env = clean_kernel::Environment::new();

    let thm_decl = Declaration::Theorem {
        name: Name::from_string("My.Theorem"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero), // Prop
        value: Expr::sort(clean_kernel::Level::Zero), // proof term
    };
    env.add_decl_unchecked(thm_decl);

    let opaque_decl = Declaration::Opaque {
        name: Name::from_string("My.Opaque"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero),
        value: Expr::sort(clean_kernel::Level::Zero),
    };
    env.add_decl_unchecked(opaque_decl);

    // Save to temp file
    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!("clean_test_opaque_{}.bincode", std::process::id()));
    env.save_to_file(&temp_file).expect("save should work");

    // Load via merge into empty state
    let state = ServerState::new();
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("bincode".to_string()),
        replace: false,
    };
    let response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    let err = response
        .error
        .expect("uncheckable serialized constants should be rejected");
    assert!(
        err.message.contains("Kernel validation failed"),
        "error should come from checked kernel registration, got: {}",
        err.message
    );

    let merged_env = state.env.read().await;
    assert!(
        merged_env
            .get_const(&Name::from_string("My.Theorem"))
            .is_none(),
        "uncheckable theorem must not be structurally inserted"
    );
    assert!(
        merged_env
            .get_const(&Name::from_string("My.Opaque"))
            .is_none(),
        "uncheckable opaque constant must not be structurally inserted"
    );

    let _ = fs::remove_file(&temp_file);
}

#[tokio::test]
async fn test_load_environment_merge_rejects_value_less_definition() {
    use clean_kernel::{Declaration, Expr, Name};
    use serde_json::Value;
    use std::fs;

    let mut env = clean_kernel::Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Loaded.Prop"),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::Zero),
    })
    .expect("checked axiom should be valid");

    let mut json: Value =
        serde_json::from_str(&env.to_json().expect("environment should serialize")).unwrap();
    let constants = json["constants"]
        .as_array_mut()
        .expect("environment JSON should contain constants");
    let loaded_prop = constants
        .iter_mut()
        .find(|constant| {
            serde_json::from_value::<Name>(constant["name"].clone())
                .is_ok_and(|name| name == Name::from_string("Loaded.Prop"))
        })
        .expect("fixture constant should exist");
    loaded_prop["kind"] = Value::String("Definition".to_string());
    loaded_prop["value"] = Value::Null;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join(format!(
        "clean_test_value_less_definition_{}.json",
        std::process::id()
    ));
    fs::write(&temp_file, serde_json::to_string(&json).unwrap()).expect("write fixture");

    let state = ServerState::new();
    let load_params = LoadEnvironmentParams {
        path: temp_file.to_string_lossy().to_string(),
        format: Some("json".to_string()),
        replace: false,
    };
    let response = handle_load_environment(&state, RequestId::Number(1), load_params).await;
    let err = response
        .error
        .expect("value-less definition should be rejected");
    assert!(
        err.message
            .contains("Cannot load value-less definition Loaded.Prop"),
        "error should reject the value-less definition, got: {}",
        err.message
    );

    let merged_env = state.env.read().await;
    assert!(
        merged_env
            .get_const(&Name::from_string("Loaded.Prop"))
            .is_none(),
        "value-less definition must not be imported as an axiom"
    );

    let _ = fs::remove_file(&temp_file);
}
