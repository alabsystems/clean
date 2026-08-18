// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The NINTH chain's A0/A6 EVIDENCE gates** — the measured row, the
//! re-derived operator census, the two unchained `zext` siblings, and the
//! recorded answer to the question the lane was set (is a cast expressible in
//! EvalIR, or is it a build item?).
//!
//! Split out of `get_char_val_trunc.rs` at the commit that created it rather
//! than after a later lane is flagged for it: that file is the CFG gate and the
//! lane-drift proofs, this one is everything read out of
//! `tests/fixtures/get_char_val_trunc.lineage.json`.

use super::super::*;

/// The measurement the chain rests on, pinned so it cannot quietly rot.
#[test]
fn get_char_val_trunc_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("get_char_val_trunc.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6(
        &evidence,
        "env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}",
    );
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("agreed"),
        "the producer's own interpreter differential RAN on this body — which is the third reason \
         it was chosen over the two zext bodies, whose parameter is a by-value struct and whose \
         differential is `not-run`"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(5)
    );
    assert!(
        evidence["interpreter_differential"]["detail"]
            .as_str()
            .is_some_and(|d| d.contains("proven-never-read opaque param")),
        "the producer's own record that the closure environment is never read — which is why A4 \
         quantifies over it with no premise instead of assuming one"
    );
    assert!(
        !j.contains("truncprobe") && !j.contains("castprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
    assert_eq!(evidence["instr_count"].as_u64(), Some(2));
    assert_eq!(evidence["func_id"].as_u64(), Some(4302));
    assert_eq!(evidence["def_index"].as_u64(), Some(14930));
}

/// **The non-vacuity of `markers_exact`, recorded as a number.**
#[test]
fn get_char_val_trunc_markers_exact_is_not_vacuous() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("get_char_val_trunc.lineage.json"))
            .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "2 marker line(s) identical",
        "the marker sequence is TWO lines long and equal line for line; if this becomes \
         `0 marker line(s) identical` then markers_exact has gone vacuous here too"
    );
    assert!(!detail.starts_with("0 "));
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["markers_exact_rows_total"].as_u64(), Some(1085));
    assert_eq!(
        sel["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27),
        "the fourth independent confirmation of the vacuity figure, from this lane's own \
         whole-crate dump — a markers_exact gain is not a fidelity gain"
    );
    assert_eq!(
        sel["re_derived_by_this_lane"].as_bool(),
        Some(true),
        "the candidate row must be re-derived, not inherited from the census that named it"
    );
}

/// **The operator census, re-derived rather than inherited.**
///
/// The float lane published it; this lane recomputed it from its own dump with
/// its own parser and reproduced it exactly, at BOTH clean HEADs it measured —
/// 177 codegen flips at `e2e732f7a` and 178 at `6e56720c5`, with every
/// per-operator count identical. It is what makes "a `trunc` is the only one of
/// its kind in the whole chainable set" a measurement.
#[test]
fn get_char_val_trunc_the_operator_census_is_re_derived_and_agrees() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("get_char_val_trunc.lineage.json"))
            .expect("evidence must be valid JSON");
    let sel = &evidence["candidate_selection"];
    let census = &sel["operator_census_over_every_codegen_flip"];
    assert_eq!(sel["codegen_flips"].as_u64(), Some(178));
    for (op, n) in [
        ("const", 116u64),
        ("extractfield", 37),
        ("insertfield", 22),
        ("load", 15),
        ("icmp", 11),
        ("zext", 2),
        ("trunc", 1),
        ("and", 1),
        ("or", 1),
        ("fadd", 1),
        ("fsub", 1),
        ("fmul", 1),
        ("fdiv", 1),
    ] {
        assert_eq!(
            census[op].as_u64(),
            Some(n),
            "the {op} count must reproduce the float lane's census"
        );
    }
    assert_eq!(
        census["trunc"].as_u64(),
        Some(1),
        "there is exactly ONE trunc in the crate's codegen flips, and this chain covers it"
    );
}

/// **The two `zext` bodies, measured — and the reason they were not chosen.**
///
/// This is the census row this lane owes the next one. `trunc` was chosen on
/// semantic content, so the fact that the alternatives are a duplicated pair
/// must not have to be re-derived, and neither must the one thing a zext chain
/// still owes.
#[test]
fn get_char_val_trunc_the_zext_siblings_are_recorded_not_left_to_be_rederived() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("get_char_val_trunc.lineage.json"))
            .expect("evidence must be valid JSON");
    let sib = &evidence["the_other_two_cast_bodies"];
    for (name, idx, lin) in [
        (
            "cert::builder::state::NodeId::index",
            1787u64,
            "sha256:8a8aa6ba1b9903461934d613a555b7155ca39eea75edeed80c2f6db79a475dec",
        ),
        (
            "env::persistent_ext::ExtensionIdx::index",
            13453,
            "sha256:b4dfec7cb414f992f0e53bbdd7520dfb5761b0c9c122d0b88bc7d96c5a8d8a9c",
        ),
    ] {
        assert_eq!(sib[name]["def_index"].as_u64(), Some(idx));
        assert_eq!(sib[name]["lineage"].as_str(), Some(lin));
        assert!(sib[name]["cast"]
            .as_str()
            .is_some_and(|c| c == "zext u32 %1 to usize"));
        assert!(
            sib[name]["interpreter"]
                .as_str()
                .is_some_and(|s| s.starts_with("not-run")),
            "the zext bodies' differential does NOT run — their parameter is a by-value struct. \
             That is the third measured reason the trunc was chosen."
        );
    }
    assert_eq!(
        sib["they_are_the_same_body_twice"].as_bool(),
        Some(true),
        "identical instruction sequence, instr count, canonical-line count, marker count and call \
         counts; they differ only in their struct id"
    );
    assert!(
        sib["what_a_later_lane_still_owes"]
            .as_str()
            .is_some_and(|s| s.starts_with("the transcription, and a decision about `usize`")),
        "a zext chain owes a decision about `usize`, which the type lane deliberately leaves \
         unresolved rather than assuming a width for. Asserted as a PREFIX, not as a substring: \
         a substring test passed a mutation that replaced the whole claim with `nothing.` and \
         left a later mention of `usize` in the sentence — measured by this chain's own \
         perturbation battery, which is what that battery is for."
    );
}

/// **The cast-semantics answer, pinned as data rather than left in prose.**
///
/// The lane brief asked whether a cast is expressible in EvalIR at all or is a
/// build item like the float arms were. The answer is recorded where a gate
/// reads it, so a later lane that disagrees must move the measurement.
#[test]
fn get_char_val_trunc_the_semantics_answer_is_recorded_with_its_reasons() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("get_char_val_trunc.lineage.json"))
            .expect("evidence must be valid JSON");
    let wall = &evidence["cast_semantics_wall"];
    assert!(
        wall["answer"]
            .as_str()
            .is_some_and(|a| a.starts_with("EXPRESSIBLE, EXACTLY")),
        "unlike the float lane's PARTLY, a truncation to a narrower integer is TOTAL — no \
         rounding, no saturation, no refusal arm"
    );
    assert!(
        wall["what_WAS_the_build_item"]
            .as_str()
            .is_some_and(|s| s.contains("CFG GATE") && s.contains("EMPTY Cfg")),
        "the build item this lane owed was the GATE, not the semantics, and the reason must stay \
         stated: two empty CFGs compare equal"
    );
    let widths = &wall["both_widths_are_semantic_and_both_are_compared"];
    assert!(widths["destination"]
        .as_str()
        .is_some_and(|s| s.contains("ir_wrap dw x")));
    assert!(
        widths["source"]
            .as_str()
            .is_some_and(|s| s.contains("ir_nat_leb dw sw") && s.contains("FAULT versus VALUE")),
        "the SOURCE width is the half with no analogue in binop_tys, because a binop has one type \
         and a cast has two"
    );
    assert!(widths["opcode"]
        .as_str()
        .is_some_and(|s| s.contains("ir_width_fault")));
    assert!(
        widths["why_this_check_was_run_first"]
            .as_str()
            .is_some_and(|s| s.contains("fdiv f32") && s.contains("NO lane")),
        "the float lane's hole was looked for on BOTH types before this lane's own lane was \
         trusted"
    );
    assert!(
        wall["refused_and_why"]["unconditional periodicity"]
            .as_str()
            .is_some_and(|s| s.contains("ACCELERATED CONSTANTS") && s.contains("CONDITIONAL")),
        "the general periodicity law is refused, and the refusal must name BOTH halves: what it \
         would cost in trust, and what is proved in its place"
    );
    assert_eq!(
        wall["accelerated_constants_added"].as_u64(),
        Some(0),
        "if this ever becomes non-zero the trust argument has changed"
    );
}
