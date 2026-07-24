// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::trust::policy::propagate_axiom_profiles;
use crate::types::{AxiomProfile, MathverseConstantHeader};

#[test]
fn test_codec_roundtrip_passes() {
    let result = verify_codec_roundtrip();
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_hash_consing_passes() {
    let result = verify_hash_consing();
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_topological_order_passes() {
    let result = verify_topological_order();
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_axiom_profile_propagation_passes() {
    let result = verify_axiom_profile_propagation();
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_trust_no_leakage_passes() {
    let result = verify_trust_no_leakage();
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_run_all_self_verify_passes() {
    let result = run_all_self_verify();
    assert!(result.all_passed, "summary:\n{}", result.summary());
    assert_eq!(result.proofs.len(), 5);
    assert_eq!(result.passed, 5);
    assert_eq!(result.failed, 0);
}

#[test]
fn test_self_verify_result_summary_format() {
    let result = run_all_self_verify();
    let summary = result.summary();
    assert!(summary.contains("Self-verification PASS"));
    assert!(summary.contains("5/5"));
    assert!(summary.contains("[OK]"));
    assert!(!summary.contains("[FAIL]"));
}

#[test]
fn test_proof_result_names_are_distinct() {
    let result = run_all_self_verify();
    let names: Vec<&str> = result.proofs.iter().map(|p| p.name.as_str()).collect();
    for (i, a) in names.iter().enumerate() {
        for (j, b) in names.iter().enumerate() {
            if i != j {
                assert_ne!(a, b, "duplicate proof name: {a}");
            }
        }
    }
}

#[test]
fn test_self_verify_result_from_mixed_results() {
    let proofs = vec![
        ProofResult {
            name: "pass1".to_owned(),
            passed: true,
            evidence: "ok".to_owned(),
        },
        ProofResult {
            name: "fail1".to_owned(),
            passed: false,
            evidence: "bad".to_owned(),
        },
        ProofResult {
            name: "pass2".to_owned(),
            passed: true,
            evidence: "ok".to_owned(),
        },
    ];
    let result = SelfVerifyResult::from_proofs(proofs);
    assert_eq!(result.passed, 2);
    assert_eq!(result.failed, 1);
    assert!(!result.all_passed);
}

#[test]
fn test_self_verify_result_serde_roundtrip() {
    let result = run_all_self_verify();
    let json = serde_json::to_string(&result).expect("serialize");
    let restored: SelfVerifyResult = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored.passed, result.passed);
    assert_eq!(restored.failed, result.failed);
    assert_eq!(restored.all_passed, result.all_passed);
    assert_eq!(restored.proofs.len(), result.proofs.len());
}

#[test]
fn test_codec_roundtrip_boundary_values() {
    let header = MathverseConstantHeader {
        name_idx: u32::MAX,
        type_idx: u32::MAX,
        value_idx: u32::MAX,
        source_system: u8::MAX,
        import_confidence: u8::MAX,
        content_domain: u8::MAX,
        decl_kind: 0,
        axiom_profile: AxiomProfile::new(u64::MAX),
        sidecar_digest: u32::MAX,
        provenance_idx: u32::MAX,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    let bytes = header.to_bytes();
    let restored = MathverseConstantHeader::from_bytes(&bytes);
    assert_eq!(header.name_idx, restored.name_idx);
    assert_eq!(header.axiom_profile, restored.axiom_profile);
    assert_eq!(header.sidecar_digest, restored.sidecar_digest);
}

#[test]
fn test_topological_order_empty_graph() {
    let deps: Vec<Vec<u32>> = vec![];
    let checked: usize = deps
        .iter()
        .enumerate()
        .flat_map(|(p, ds)| ds.iter().map(move |&c| (p, c)))
        .filter(|&(p, c)| c >= p as u32)
        .count();
    assert_eq!(checked, 0);
}

#[test]
fn test_propagation_detects_cycles() {
    let mut constants = vec![
        make_kernel_header(0, 0, 0, AxiomProfile::NONE),
        make_kernel_header(1, 1, 1, AxiomProfile::NONE),
    ];
    let deps = vec![vec![1], vec![0]];
    let result = propagate_axiom_profiles(&mut constants, &deps);
    assert!(result.is_err());
}
