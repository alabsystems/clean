// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Chain 18's EVIDENCE gates** — the tip-era census row and the lineage
//! fixture, pinned at the strength they were measured (`deferred_to_seam:
//! true`, `calls.resolved: 1`, the callee shim-refused and flipless).
//!
//! Split out of `has_loose_bvars.rs` following the ninth and tenth chains
//! (`get_char_val_trunc_evidence.rs`, `meta_tag_shl_evidence.rs`): that file
//! is the CFG gates, the call-target identity and the drift proofs; this one
//! is everything read out of the frontier census and
//! `tests/fixtures/has_loose_bvars.lineage.json`.

use super::super::*;

/// The TIP-ERA census (a second, later producer): the caller is one of five
/// call-carrying -O3 flip bodies, and the CALLEE'S EVIDENCE IS ITS ABSENCE —
/// no flip row, no chainable row. A callee row appearing here means the
/// record moved and this chain's evidence statement must be rewritten.
#[test]
fn has_loose_bvars_census_evidence_is_recorded_at_measured_strength() {
    let p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../data/crystal_frontier_census_2026-08-21.json");
    let census: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&p).expect("the frontier census must be readable"),
    )
    .expect("the frontier census must be valid JSON");
    let rows = census["chainable_O3"]["carrying_gep_or_call"]
        .as_array()
        .expect("the census carries the call/gep chainable rows");
    let caller = rows
        .iter()
        .find(|r| r["def_path"] == "expr::meta::ExprMeta::has_loose_bvars")
        .expect("the caller must be a chainable call-carrying row");
    assert_eq!(caller["ops"]["call"].as_u64(), Some(1));
    // The tip-era digest DIFFERS from the fixture era's (sha256:b09a6b60…) —
    // recorded, not reconciled.
    assert!(caller["lineage"]
        .as_str()
        .is_some_and(|l| l.starts_with("sha256:446663acce")));
    let closure = census["call_bodies_with_a_bodyful_closure"]
        .as_array()
        .expect("the census carries the bodyful-closure call rows");
    let row = closure
        .iter()
        .find(|r| r["def_path"] == "expr::meta::ExprMeta::has_loose_bvars")
        .expect("the caller must be a bodyful-closure call body");
    assert_eq!(row["verdict"].as_str(), Some("agreed"));
    assert_eq!(row["markers_exact"].as_bool(), Some(true));
    assert_eq!(row["flip_O3"].as_bool(), Some(true));
    assert_eq!(row["flip_O0"].as_bool(), Some(true));
    assert_eq!(row["reachable"].as_u64(), Some(1), "one bodyful callee");
    for list in [rows, closure] {
        assert!(
            !list
                .iter()
                .any(|r| r["def_path"] == "expr::meta::ExprMeta::loose_bvar_range"),
            "the callee must NOT appear as a flip/chainable row — its differential is refused"
        );
    }
}

/// The chain's own lineage evidence, pinned at the strength it was measured —
/// including the two facts the ten-chain helper `assert_a0_a6` would REFUSE
/// (`deferred_to_seam: true`, `calls.resolved: 1`), which is why this chain
/// pins its evidence itself instead of borrowing that helper.
#[test]
fn has_loose_bvars_lineage_evidence_is_recorded_at_measured_strength() {
    let ev: serde_json::Value = serde_json::from_str(&fixture("has_loose_bvars.lineage.json"))
        .expect("the lineage evidence must be valid JSON");
    assert_eq!(
        ev["def_path"].as_str(),
        Some("expr::meta::ExprMeta::has_loose_bvars")
    );
    // A digest and its domain travel together or neither means anything.
    assert_eq!(
        ev["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2")
    );
    let lin = ev["lineage"].as_str().expect("a lineage digest");
    assert!(lin.starts_with("sha256:") && lin.len() > "sha256:".len());

    let body = &ev["body"];
    assert_eq!(body["instr_count"].as_u64(), Some(4));
    assert_eq!(body["lowered"].as_bool(), Some(true));
    assert_eq!(body["spliced"].as_bool(), Some(true));
    assert_eq!(
        body["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(body["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(body["derived_mir"]["markers_exact"].as_bool(), Some(true));
    // markers_exact compares FOUR real marker lines here — non-vacuous.
    assert_eq!(
        body["derived_mir"]["markers_detail"].as_str(),
        Some("4 marker line(s) identical")
    );
    // THE INTERPRETER: NOT-RUN, zero samples — a call-bearing body cannot run
    // standalone, and nothing may quote interpreter agreement.
    assert_eq!(body["interpreter"]["verdict"].as_str(), Some("not-run"));
    assert_eq!(body["interpreter"]["samples"].as_u64(), Some(0));
    // THE SEAM DEFERRAL, recorded rather than hidden: the semantic
    // differential defers to the crate-finalize seam, whose baseline evidence
    // is nearly empty (seam_agreed 2 / samples 4).
    assert_eq!(body["deferred_to_seam"].as_bool(), Some(true));
    assert!(body["seam_note"]
        .as_str()
        .is_some_and(|n| n.contains("seam_agreed 2 / samples 4")));
    assert_eq!(body["calls"]["resolved"].as_u64(), Some(1));
    assert_eq!(body["calls"]["unresolved"].as_u64(), Some(0));
    // A6's join: coverage row == flip event == the named artifact.
    assert_eq!(body["coverage_row_lineage"].as_str(), Some(lin));
    assert_eq!(body["flip_event_lineage"].as_str(), Some(lin));
    assert_eq!(body["flip_lineage_equals_coverage"].as_bool(), Some(true));

    // THE CALLEE, at recorded strength: refused by the shim, does not flip.
    let callee = &ev["supporting_callee"];
    assert_eq!(
        callee["def_path"].as_str(),
        Some("expr::meta::ExprMeta::loose_bvar_range")
    );
    assert_eq!(
        callee["fixture"].as_str(),
        Some("loose_bvar_range_callee.trust-ir.txt")
    );
    assert_eq!(callee["instr_count"].as_u64(), Some(9));
    assert_eq!(
        callee["derived_mir"]["verdict"].as_str(),
        Some("unsupported")
    );
    // The shim refusal, verbatim: no differential exists for the callee.
    assert!(callee["derived_mir"]["detail"]
        .as_str()
        .is_some_and(|d| d.contains("pending local const")));
    assert_eq!(callee["does_not_flip"].as_bool(), Some(true));

    // Reproduction and the head-measurement pointer.
    assert_eq!(
        ev["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true)
    );
    assert_eq!(
        ev["head_measurement"]["record"].as_str(),
        Some("data/crystal_fixture_freshness_2026-08-21_lane18.json")
    );
    assert_eq!(
        ev["head_measurement"]["at_head_lineage"].as_str(),
        Some(lin)
    );
}
