// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

#[tokio::test]
async fn test_verify_c_simple_function() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: r"
                //@ requires n >= 0;
                //@ ensures \result >= 0;
                int id(int n) { return n; }
            "
        .to_string(),
        fail_unknown: false,
        include_details: false,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );
    let result: VerifyCResult = serde_json::from_value(
        response
            .result
            .expect("verify_c response should have result"),
    )
    .unwrap();
    assert_eq!(result.num_functions, 1);
    assert!(result.total_vcs > 0, "Should generate VCs");
    assert!(
        result.functions[0].name == "id",
        "Function name should be 'id'"
    );
}

#[tokio::test]
async fn test_verify_c_with_details() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: r"
                //@ requires x >= 0;
                //@ ensures \result >= 0;
                int identity(int x) { return x; }
            "
        .to_string(),
        fail_unknown: false,
        include_details: true,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: VerifyCResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.num_functions, 1);
    // With include_details=true, details should be populated
    // (may be empty if all VCs are trivially proved without details)
}

#[tokio::test]
async fn test_verify_c_no_functions() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: "int x;".to_string(), // just a declaration, no function
        fail_unknown: false,
        include_details: false,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: VerifyCResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.num_functions, 0);
    assert!(result.success);
}

#[tokio::test]
async fn test_verify_c_malformed_code() {
    // tree-sitter is lenient and parses partial/invalid code as "error" nodes
    // so it won't raise a parse error, but may return no valid functions
    let state = ServerState::new();
    let params = VerifyCParams {
        code: "int func( { invalid".to_string(),
        fail_unknown: false,
        include_details: false,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    // tree-sitter tolerates invalid syntax - returns success with no functions
    assert!(
        response.error.is_none() || response.result.is_some(),
        "malformed code should produce either no error or a result, got error: {:?}",
        response.error
    );
    if let Some(result_json) = response.result {
        let result: VerifyCResult = serde_json::from_value(result_json).unwrap();
        // Either no functions found or some partial parse
        assert!(result.num_functions <= 1);
    }
}

/// Test the fail-closed success predicate and the `fail_unknown` flag.
///
/// SOUNDNESS: `verify_c_impl` is fail-closed — a `Failed` OR an `Unknown`
/// obligation makes the result unsuccessful UNCONDITIONALLY (an `Unknown` is a
/// verification gap, not a pass). `Unverified` (a sound SMT-UNSAT goal without
/// a reconstructed proof term) is accepted unless `fail_unknown` is set, which
/// tightens further. See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md.
///
/// The `id` fixture below has no `Unknown` obligations, so both modes agree
/// (all obligations established). The `unknown > 0` branch documents that when
/// a gap exists, the result is NOT successful regardless of `fail_unknown`.
#[tokio::test]
async fn test_verify_c_fail_unknown_flag() {
    let state = ServerState::new();

    let code = r"
        //@ requires n >= 0;
        //@ ensures \result >= 0;
        int id(int n) { return n; }
    "
    .to_string();

    // With fail_unknown=false
    let params_lenient = VerifyCParams {
        code: code.clone(),
        fail_unknown: false,
        include_details: false,
        timeout_ms: None,
    };
    let response_lenient =
        handle_verify_c(&state, RequestId::Number(1), params_lenient, None).await;
    let result_lenient: VerifyCResult =
        serde_json::from_value(response_lenient.result.unwrap()).unwrap();

    // With fail_unknown=true
    let params_strict = VerifyCParams {
        code,
        fail_unknown: true,
        include_details: false,
        timeout_ms: None,
    };
    let response_strict = handle_verify_c(&state, RequestId::Number(2), params_strict, None).await;
    let result_strict: VerifyCResult =
        serde_json::from_value(response_strict.result.unwrap()).unwrap();

    // Both should parse the same number of functions and VCs
    assert_eq!(result_lenient.num_functions, result_strict.num_functions);
    assert_eq!(result_lenient.total_vcs, result_strict.total_vcs);
    assert_eq!(result_lenient.proved, result_strict.proved);
    assert_eq!(result_lenient.failed, result_strict.failed);
    assert_eq!(result_lenient.unknown, result_strict.unknown);

    // SOUNDNESS: an `Unknown` obligation is a verification gap — it makes the
    // result NOT successful in BOTH modes (fail-closed). `fail_unknown` only
    // additionally rejects sound SMT-UNSAT `Unverified` goals.
    if result_lenient.unknown > 0 {
        assert!(
            !result_lenient.success,
            "An unknown obligation must make the result unsuccessful even with fail_unknown=false"
        );
        assert!(
            !result_strict.success,
            "An unknown obligation must make the result unsuccessful with fail_unknown=true"
        );
    } else if result_lenient.failed == 0 && result_lenient.unverified == 0 {
        // Every obligation established — both modes should succeed.
        assert!(result_lenient.success);
        assert!(result_strict.success);
    }
}

/// Test verifyC with multiple functions aggregates results correctly.
#[tokio::test]
async fn test_verify_c_multiple_functions() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: r"
            //@ requires x >= 0;
            //@ ensures \result >= 0;
            int foo(int x) { return x; }

            //@ requires y >= 0;
            //@ ensures \result >= 0;
            int bar(int y) { return y; }
        "
        .to_string(),
        fail_unknown: false,
        include_details: true,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: VerifyCResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.num_functions, 2, "Should find both functions");
    assert_eq!(result.functions.len(), 2);

    // Verify aggregate counts are sum of per-function counts
    let sum_vcs: usize = result.functions.iter().map(|f| f.total_vcs).sum();
    let sum_proved: usize = result.functions.iter().map(|f| f.proved).sum();
    let sum_failed: usize = result.functions.iter().map(|f| f.failed).sum();
    let sum_unknown: usize = result.functions.iter().map(|f| f.unknown).sum();
    assert_eq!(result.total_vcs, sum_vcs);
    assert_eq!(result.proved, sum_proved);
    assert_eq!(result.failed, sum_failed);
    assert_eq!(result.unknown, sum_unknown);

    // Check function names
    let names: Vec<&str> = result.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(names.contains(&"foo"), "Should find function 'foo'");
    assert!(names.contains(&"bar"), "Should find function 'bar'");
}

/// Test verifyC records metrics correctly.
#[tokio::test]
async fn test_verify_c_records_metrics() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: r"
            //@ ensures \result >= 0;
            int zero(void) { return 0; }
        "
        .to_string(),
        fail_unknown: false,
        include_details: false,
        timeout_ms: None,
    };

    let _response = handle_verify_c(&state, RequestId::Number(1), params, None).await;

    assert!(
        state
            .metrics
            .total_requests
            .load(std::sync::atomic::Ordering::Relaxed)
            > 0,
        "Metrics should record the verifyC request"
    );
}

/// Test verifyC with include_details populates VC detail entries.
#[tokio::test]
async fn test_verify_c_details_populated() {
    let state = ServerState::new();
    let params = VerifyCParams {
        code: r"
            //@ requires x >= 0;
            //@ ensures \result >= 0;
            int id(int x) { return x; }
        "
        .to_string(),
        fail_unknown: false,
        include_details: true,
        timeout_ms: None,
    };

    let response = handle_verify_c(&state, RequestId::Number(1), params, None).await;
    let result: VerifyCResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.num_functions, 1);

    // With include_details=true and VCs present, details should be populated
    if result.total_vcs > 0 {
        let func = &result.functions[0];
        assert!(
            !func.details.is_empty(),
            "With include_details=true and {} VCs, details should be populated",
            result.total_vcs
        );
        // Each detail should have a valid status string
        for detail in &func.details {
            assert!(
                detail.status == "proved"
                    || detail.status == "failed"
                    || detail.status == "unknown",
                "VC detail status should be proved/failed/unknown, got: {}",
                detail.status
            );
            // Failed details should have a reason
            if detail.status == "failed" {
                assert!(detail.reason.is_some(), "Failed VC should include a reason");
            }
        }
    }
}
