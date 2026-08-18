// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The TENTH chain's A0/A6 EVIDENCE gates** — the measured row, the
//! re-derived CTFE-seam census, the twenty-one assert-carrying candidates, and
//! the two answers the lane owes: what a CTFE flip binds, and where the build
//! item actually was.
//!
//! Split out of `meta_tag_shl.rs` at the commit that creates it, following the
//! ninth chain: that file is the CFG gate and the lane-drift proofs, this one
//! is everything read out of `tests/fixtures/meta_tag_shl.lineage.json`.

use super::super::*;

/// The measurement the chain rests on, pinned so it cannot quietly rot.
///
/// The seam and the assert count are passed EXPLICITLY, because they are the
/// two facts that make this chain different from the other nine and because
/// both were hard-coded in the shared helper until this lane.
#[test]
fn meta_tag_shl_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("meta_tag_shl.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6_on_seam(
        &evidence,
        "tc::local_context::LocalContext::push_low_local::META_TAG",
        "ctfe",
        1,
    );
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("agreed"),
        "the producer's own interpreter differential RAN on this body"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(1)
    );
    assert!(
        !j.contains("shlprobe") && !j.contains("metaprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
    assert_eq!(evidence["instr_count"].as_u64(), Some(9));
    assert_eq!(evidence["func_id"].as_u64(), Some(5758));
    assert_eq!(evidence["def_index"].as_u64(), Some(19642));
    assert_eq!(evidence["kind"].as_str(), Some("const-init"));
}

/// **`markers_exact` IS VACUOUS HERE, and saying so is the point.**
///
/// The ninth chain's `markers_detail` is `2 marker line(s) identical` — two real
/// lines compared. This body's is `0 marker line(s) identical`: two EMPTY
/// sequences, which is a true statement that compares nothing. That is the
/// vacuity §4c measured across the crate (27 of 1,085 rows non-vacuous), and it
/// is a property of the whole assert-carrying CTFE population rather than of
/// this body — a const initializer has no `StorageLive`/`StorageDead` to
/// compare.
///
/// It is recorded as an assertion, not a footnote, so that quoting
/// `markers_exact: true` for this chain without the qualifier is impossible.
#[test]
fn meta_tag_shl_markers_exact_is_vacuous_and_the_gate_says_so() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("meta_tag_shl.lineage.json"))
        .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "0 marker line(s) identical",
        "this chain's markers_exact is VACUOUS — two empty sequences. If it ever becomes \
         non-vacuous that is a gain and this assertion should be updated to record it, but it \
         must never be quoted as evidence while it reads `0 `."
    );
    assert_eq!(
        evidence["derived_mir"]["markers_exact_is_vacuous"].as_bool(),
        Some(true),
        "and the record must SAY so rather than leaving a reader to parse the detail string"
    );
    assert_eq!(
        evidence["candidate_selection"]["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27),
        "the crate-wide figure, re-derived by this lane's own dump"
    );
}

/// **The whole point of the lane, as a number: 21 of 32 CTFE flips carry an
/// assert and 0 of 178 codegen flips do.**
#[test]
fn meta_tag_shl_the_panic_arm_population_is_ctfe_only() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("meta_tag_shl.lineage.json"))
        .expect("evidence must be valid JSON");
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["codegen_flips"].as_u64(), Some(178));
    assert_eq!(sel["ctfe_flips"].as_u64(), Some(32));
    assert_eq!(
        sel["codegen_flips_carrying_an_assert"].as_u64(),
        Some(0),
        "`panic arms 0` is TRUE of the codegen population — and it is the whole of what that \
         claim ever said"
    );
    assert_eq!(
        sel["ctfe_flips_carrying_an_assert"].as_u64(),
        Some(21),
        "…and FALSE of the CTFE population, which is the finding this chain is built on"
    );
    assert_eq!(
        sel["re_derived_by_this_lane"].as_bool(),
        Some(true),
        "the candidate row must be re-derived, not inherited from the analysis that named it"
    );
    // The two shapes, and the reason eight of the nine `no_overflow` bodies are
    // NOT chained. It is a gate, not a preference.
    let shapes = &sel["the_twenty_one_by_shape"];
    assert_eq!(shapes["no_overflow"]["count"].as_u64(), Some(9));
    assert_eq!(shapes["shift_in_range"]["count"].as_u64(), Some(12));
    assert!(
        shapes["no_overflow"]["refused_because"]
            .as_str()
            .is_some_and(|r| r.starts_with("every operand is `usize`")),
        "the refusal must name `usize` — resolving it is a target assumption the ninth chain \
         declined to make, and this lane inherits that rather than reopening it"
    );
    assert_eq!(
        shapes["shift_in_range"]["unique_shift_amounts"]
            .as_array()
            .map(Vec::len),
        Some(3),
        "three of the twelve are not duplicates by shift amount; META_TAG is one of them"
    );
}

/// **WHAT LINK 2b MEANS FOR A CTFE FLIP — recorded, with the axis on which it
/// is WEAKER stated first.**
///
/// This is the gate that makes the honest reading survive: a later reader who
/// quotes "the tenth chain has all five links" must also meet the sentence that
/// says what the second one binds.
#[test]
fn meta_tag_shl_link_2b_is_recorded_as_weaker_than_the_codegen_form() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("meta_tag_shl.lineage.json"))
        .expect("evidence must be valid JSON");
    let l2 = &evidence["link_2b_on_the_ctfe_seam"];
    assert_eq!(
        l2["is_weaker_than_the_codegen_form"].as_bool(),
        Some(true),
        "it is weaker, and the record must say so rather than implying parity"
    );
    assert!(
        l2["what_it_does_NOT_bind"]
            .as_str()
            .is_some_and(|s| s.starts_with("no machine code")),
        "the weakening must be stated as what is NOT bound, first"
    );
    assert!(
        l2["what_it_binds"]
            .as_str()
            .is_some_and(|s| s.contains("const-eval interpreter")),
        "…and what IS bound must name the consumer"
    );
    assert_eq!(
        l2["same_registry_writer"].as_str(),
        Some("record_green -- the sole writer, on DerivedAgreed, for BOTH seams"),
    );
    assert_eq!(
        l2["same_markers_gate"].as_str(),
        Some(
            "flip_registry.rs:641 -- emit_lifetime_markers() && !markers_exact, consulted \
             identically on both seams"
        ),
        "the marker gate does NOT differ by seam; the panic-arm asymmetry is a POPULATION \
         difference, and conflating the two would be the wrong causal story"
    );
    assert_eq!(
        l2["one_axis_where_it_is_STRONGER"]["what"].as_str(),
        Some(
            "verify_assert_parity (flip.rs:1767) verified 1 assert; on all 178 codegen flips \
             that check is vacuous at 0"
        ),
    );
}

/// **The build item was NOT the assert — and the record has to say where it
/// was, because the obvious guess is wrong.**
#[test]
fn meta_tag_shl_the_build_item_is_recorded_and_it_is_not_the_assert() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("meta_tag_shl.lineage.json"))
        .expect("evidence must be valid JSON");
    let w = &evidence["build_items"];
    assert_eq!(
        w["was_the_assert_a_build_item"].as_str(),
        Some("NO"),
        "`ir_assert_exec` -> `ir_assert_b` was already exact: ub assert_failed on false, \
         type_error not_bool on a non-Bool, advance on true"
    );
    assert_eq!(
        w["semantics_build_item"]["what"].as_str(),
        Some("IRCastOp.bitcast, which was a blanket ir_width_fault")
    );
    assert!(
        w["semantics_build_item"]["what_stays_refused"]
            .as_array()
            .is_some_and(|a| a.len() >= 3),
        "narrowing a refusal must enumerate what is still refused, or it is a relaxation \
         wearing a narrowing's clothes"
    );
    assert_eq!(w["gate_build_items"].as_array().map(Vec::len), Some(3));
    // And the correction this lane owes the ninth chain's own record.
    let corr = &evidence["correction_to_the_ninth_chain"];
    assert!(
        corr["claim"]
            .as_str()
            .is_some_and(|c| c.contains("no body in clean-kernel flips one")),
        "the ninth chain recorded that no clean-kernel body flips a bitcast; it is false at the \
         CTFE seam, and it is the same `codegen-only` reading error the panic-arm claim had"
    );
    assert_eq!(corr["is_false_at_HEAD"].as_bool(), Some(true));
}

/// **The negative control and the reproduction, for a CTFE flip specifically.**
#[test]
fn meta_tag_shl_the_negative_control_kills_the_ctfe_event_too() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("meta_tag_shl.lineage.json"))
        .expect("evidence must be valid JSON");
    let nc = &evidence["negative_control"];
    assert_eq!(nc["flag"].as_str(), Some("-Ztrust-ir-flip=no"));
    assert_eq!(nc["flip_events_crate_wide"].as_u64(), Some(0));
    assert_eq!(nc["ctfe_flip_events_crate_wide"].as_u64(), Some(0));
    assert_eq!(nc["event_for_this_body_present"].as_bool(), Some(false));
    assert_eq!(
        evidence["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true)
    );
    assert_eq!(
        evidence["build"]["compiler_identified_by_behaviour_not_stamp"]
            .as_str()
            .map(|s| s.contains("BY OUTPUT")),
        Some(true),
        "`selftest` returns UNPROVEN on identical class sets; identification is by output digest"
    );
}
