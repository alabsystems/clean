// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Phase 1 artifact parser.
//!
//! `C004_PRIMARY_JSON` and `C002_BASIC_JSON` are verbatim copies of
//! `gamma-crown/reports/experiments/C004/primary.json` and
//! `gamma-crown/reports/experiments/C002/cross_block_vs_per_block_basic.json`
//! (fix commit `883c37149`, mail #3505). Keeping them inline lets the tests
//! run in any environment without depending on a sibling repo checkout.

use super::*;

const C004_PRIMARY_JSON: &str = r#"{
  "conjecture": "C004",
  "experiment": "primary",
  "hypothesis": "CROWN backward through LayerNorm produces bounds identical to IBP (ratio ≈ 1.000). The dense LayerNorm Jacobian destroys the sparsity CROWN exploits.",
  "configurations": [{"hidden":8,"epsilon":0.500000,"seed":1}],
  "results": [
    {"hidden":8,"epsilon":0.500000,"dim":0,"crown_width":7.860092,"ibp_width":7.860092,"ratio_crown_ibp":1.000000},
    {"hidden":8,"epsilon":0.500000,"dim":1,"crown_width":7.291619,"ibp_width":7.291619,"ratio_crown_ibp":1.000000},
    {"hidden":8,"epsilon":0.500000,"dim":2,"crown_width":8.295236,"ibp_width":8.295236,"ratio_crown_ibp":1.000000}
  ],
  "summary": {"mean_ratio":1.000000,"min_ratio":1.000000,"max_ratio":1.000000,"finding":"CROWN/IBP ratio >= 0.99 across all tested output dims — C004 degeneracy confirmed"}
}"#;

const C002_BASIC_JSON: &str = r#"{
  "conjecture": "C002",
  "experiment": "cross_block_vs_per_block_basic",
  "hypothesis": "Per-block fresh zonotopes produce bounds no worse than cross-block zonotopes because LayerNorm's dense Jacobian destroys sparse correlation structure.",
  "configurations": [{"hidden":8,"epsilon":0.500000,"seed":1}],
  "results": [
    {"hidden":8,"epsilon":0.500000,"dim":0,"cross_width":6536348.000000,"perblock_width":1317355.125000,"ratio_pb_cb":0.201543},
    {"hidden":8,"epsilon":0.500000,"dim":1,"cross_width":4631755.500000,"perblock_width":913462.250000,"ratio_pb_cb":0.197217},
    {"hidden":8,"epsilon":0.500000,"dim":2,"cross_width":5229846.500000,"perblock_width":1058879.875000,"ratio_pb_cb":0.202469}
  ],
  "summary": {"mean_ratio":0.200616,"min_ratio":0.197217,"max_ratio":0.202469,"finding":"per-block 3-100x tighter across tested dims (supports C002)"}
}"#;

#[test]
fn parse_c004_primary_matches_upstream_schema() {
    let artifact = parse_phase1_artifact(C004_PRIMARY_JSON).expect("C004 primary must parse");
    assert_eq!(artifact.conjecture(), Conjecture::C004);
    assert_eq!(artifact.experiment(), "primary");
    assert_eq!(artifact.configurations().len(), 1);
    assert_eq!(artifact.results().len(), 3);

    for r in artifact.results() {
        match r {
            ExperimentResult::C004 {
                crown_width,
                ibp_width,
                ratio_crown_ibp,
                ..
            } => {
                // At primary configuration, CROWN degenerates exactly to IBP.
                assert!((crown_width - ibp_width).abs() < 1e-6);
                assert!((*ratio_crown_ibp - 1.0).abs() < 1e-6);
            }
            other => panic!("expected C004 row, got {other:?}"),
        }
    }
}

#[test]
fn c004_primary_satisfies_hard_regression_guard() {
    let artifact = parse_phase1_artifact(C004_PRIMARY_JSON).unwrap();
    let Phase1Artifact::C004 { summary, .. } = artifact else {
        panic!("expected C004 variant");
    };
    // gamma-crown hard-asserts ratio >= 0.99 in the primary fixture.
    summary
        .assert_degeneracy_threshold(0.99)
        .expect("C004 primary must clear the 0.99 guard");
}

#[test]
fn parse_c002_basic_matches_upstream_schema() {
    let artifact = parse_phase1_artifact(C002_BASIC_JSON).expect("C002 basic must parse");
    assert_eq!(artifact.conjecture(), Conjecture::C002);
    assert_eq!(artifact.experiment(), "cross_block_vs_per_block_basic");
    assert_eq!(artifact.results().len(), 3);

    for r in artifact.results() {
        match r {
            ExperimentResult::C002 {
                cross_width,
                perblock_width,
                ratio_pb_cb,
                ..
            } => {
                // Per-block strictly tighter than cross-block at every dim.
                assert!(perblock_width < cross_width);
                assert!(*ratio_pb_cb < 1.0);
                // Sanity-check ratio consistency with the widths.
                let recomputed = perblock_width / cross_width;
                assert!((recomputed - *ratio_pb_cb).abs() < 1e-3);
            }
            other => panic!("expected C002 row, got {other:?}"),
        }
    }
}

#[test]
fn c002_basic_respects_firewall_direction() {
    let artifact = parse_phase1_artifact(C002_BASIC_JSON).unwrap();
    let Phase1Artifact::C002 { summary, .. } = artifact else {
        panic!("expected C002 variant");
    };
    // Per-block must be no worse than cross-block; allow 1% float slack.
    summary
        .assert_firewall_direction(0.01)
        .expect("C002 basic must respect firewall direction");
}

#[test]
fn unknown_conjecture_is_rejected() {
    let bad = r#"{
        "conjecture": "C999",
        "experiment": "nope",
        "configurations": [],
        "results": [],
        "summary": {"mean_ratio":1.0,"min_ratio":1.0,"max_ratio":1.0,"finding":""}
    }"#;
    let err = parse_phase1_artifact(bad).unwrap_err();
    match err {
        MathverseError::ImportFailed { system, reason } => {
            assert_eq!(system, "gamma-crown/phase1");
            assert!(reason.contains("C999"));
        }
        other => panic!("expected ImportFailed, got {other:?}"),
    }
}

#[test]
fn c004_threshold_detects_regression_drift() {
    // Synthetic fixture where ratio drops below 0.99 — simulates drift.
    let drifted = r#"{
      "conjecture": "C004",
      "experiment": "synthetic_drift",
      "configurations": [{"hidden":4,"epsilon":0.1,"seed":1}],
      "results": [{"hidden":4,"epsilon":0.1,"dim":0,"crown_width":1.0,"ibp_width":2.0,"ratio_crown_ibp":0.5}],
      "summary": {"mean_ratio":0.5,"min_ratio":0.5,"max_ratio":0.5,"finding":"synthetic"}
    }"#;
    let artifact = parse_phase1_artifact(drifted).unwrap();
    let Phase1Artifact::C004 { summary, .. } = artifact else {
        panic!("expected C004 variant");
    };
    let err = summary.assert_degeneracy_threshold(0.99).unwrap_err();
    assert!(err.contains("min_ratio=0.5"));
}

#[test]
fn c002_direction_detects_regression_drift() {
    // Synthetic fixture where per-block is WORSE than cross-block.
    let drifted = r#"{
      "conjecture": "C002",
      "experiment": "synthetic_violation",
      "configurations": [{"hidden":4,"epsilon":0.1,"seed":1}],
      "results": [{"hidden":4,"epsilon":0.1,"dim":0,"cross_width":1.0,"perblock_width":2.0,"ratio_pb_cb":2.0}],
      "summary": {"mean_ratio":2.0,"min_ratio":2.0,"max_ratio":2.0,"finding":"synthetic"}
    }"#;
    let artifact = parse_phase1_artifact(drifted).unwrap();
    let Phase1Artifact::C002 { summary, .. } = artifact else {
        panic!("expected C002 variant");
    };
    let err = summary.assert_firewall_direction(0.01).unwrap_err();
    assert!(err.contains("max_ratio=2"));
}

#[test]
fn malformed_row_is_rejected_with_context() {
    // Missing `ratio_crown_ibp` — parse_phase1_artifact should flag C004 row 0.
    let bad = r#"{
      "conjecture": "C004",
      "experiment": "broken",
      "configurations": [{"hidden":4,"epsilon":0.1,"seed":1}],
      "results": [{"hidden":4,"epsilon":0.1,"dim":0,"crown_width":1.0,"ibp_width":1.0}],
      "summary": {"mean_ratio":1.0,"min_ratio":1.0,"max_ratio":1.0,"finding":""}
    }"#;
    let err = parse_phase1_artifact(bad).unwrap_err();
    match err {
        MathverseError::ImportFailed { reason, .. } => {
            assert!(reason.contains("C004 row 0"));
        }
        other => panic!("expected ImportFailed, got {other:?}"),
    }
}
