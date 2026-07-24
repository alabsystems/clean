// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Contract tests for `searchProof` response shape.

use crate::handlers::{ProveStatus, SearchProofResult, SearchStats};

#[test]
fn test_search_proof_result_serializes_mathverse_candidates() {
    let result = SearchProofResult {
        found: false,
        status: ProveStatus::Unknown,
        proof_term: None,
        tactic_script: None,
        proof_sketch: None,
        method: Some("auto_only".to_string()),
        reason: Some("not found".to_string()),
        trust_summary: None,
        stats: SearchStats::default(),
        mathverse_candidates: Vec::new(),
        time_ns: 0,
    };

    let json = serde_json::to_value(&result).expect("searchProof result should serialize");
    let mathverse_candidates = json
        .get("mathverse_candidates")
        .and_then(|value| value.as_array())
        .expect("searchProof result should serialize mathverse_candidates as an array");
    assert!(
        mathverse_candidates.is_empty(),
        "searchProof should default mathverse_candidates to []"
    );
}

#[test]
fn test_search_proof_result_deserializes_missing_mathverse_candidates_as_empty() {
    let json = serde_json::json!({
        "found": false,
        "status": "unknown",
        "reason": "not found",
        "stats": {"nodes_explored": 0},
        "time_ns": 0
    });

    let result: SearchProofResult =
        serde_json::from_value(json).expect("legacy searchProof result should decode");
    assert!(result.mathverse_candidates.is_empty());
}
