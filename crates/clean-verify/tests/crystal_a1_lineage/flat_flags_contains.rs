// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the FOURTH complete chain — and the first over a body
//! that COMPUTES: `flat::types::FlatFlags::contains`.**
//!
//! The same two gates the other chains have, plus the three instruction lanes
//! that had nothing to compare until a chained body contained an operation: the
//! registered `ir_fc_*` module must encode the CFG trustc emitted **including
//! its `binop`, its `icmp` and all three of its `extractfield`s in order**, and
//! the flip event's A-LIN lineage must equal the coverage row's.
//!
//! Measured on `clean-kernel` itself at `c4e33541d`, sealed stage1 trustc
//! (trust `352aa0306d`), three clean non-incremental builds with a
//! byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("5 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 8 REAL marker lines
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:2f0e826d…
//! flip event                 FIRED, codegen seam, same lineage
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! ## Why the marker row is called out
//!
//! `markers_exact: true` is not one predicate. Measured at this HEAD, **1,082**
//! coverage rows carry it and only **27** compare a non-empty marker sequence;
//! the other 1,055 — including all three chains that existed before this lane —
//! carry `markers_detail: "0 marker line(s) identical"`, which is a true
//! statement about two empty sequences. This body is in the 27. That is the
//! honest difference and it is recorded in the fixture rather than asserted in
//! prose.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed from the artifact here. And `ir_fc_module` is hand-transcribed:
//! this makes an incorrect transcription FAIL, it does not make a correct one
//! automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn flat_flags_contains_proved_module_matches_the_emitted_artifact() {
    let text = fixture("flat_flags_contains.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @flat::types::FlatFlags::contains("),
        "the fixture must be the contains body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_contains.rs", "const SRC_IR_FC_B"),
        "def ir_fc_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(
        emitted.blocks,
        vec![0u32],
        "ONE block; parser found {:?}",
        emitted.blocks
    );
    assert!(
        emitted.cases.is_empty() && emitted.default == u32::MAX,
        "no switch at all: {:?} / {}",
        emitted.cases,
        emitted.default
    );
    assert!(
        emitted.branches.is_empty() && emitted.param_blocks.is_empty(),
        "straight line: no branch, no join block"
    );
    assert!(
        emitted.consts.is_empty() && emitted.int_consts.is_empty() && emitted.agg_consts.is_empty(),
        "THE POINT OF THIS CHAIN: the body materializes NO constant in any of the three constant \
         lanes — its answer is computed. bool {:?} int {:?} agg {:?}",
        emitted.consts,
        emitted.int_consts,
        emitted.agg_consts
    );

    // The three lanes that made this body worth chaining.
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(2, 0, 0), (3, 1, 0), (5, 1, 0)])]),
        "THREE field reads in emission order: self.0 into %2, other.0 into %3, and other.0 AGAIN \
         into %5. The compiler does not reuse %3 for the comparison's operand, and a \
         transcription that did would be one instruction shorter than the shipped artifact."
    );
    assert_eq!(
        emitted.binops,
        BTreeMap::from([(0, vec![("and".to_string(), 4, 2, 3)])]),
        "one bitwise AND, of the two field reads, binding %4"
    );
    assert_eq!(
        emitted.icmps,
        BTreeMap::from([(0, vec![("eq".to_string(), 6, 4, 5)])]),
        "one equality, of the AND against the SECOND read of other.0 — not against %3"
    );
    assert!(
        emitted.loads.is_empty(),
        "both arguments arrive BY VALUE: an emitted body with a load is a different body, and the \
         heap-free representation premise would no longer be the honest one. Found {:?}",
        emitted.loads
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_contains.rs", "const SRC_IR_FC_FUNC"),
        "flat_flags_contains",
    );
    assert_lanes(&emitted, &clean, "flat_flags_contains");
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. Both must be empty.",
        emitted.cases, clean.cases
    );
    assert_eq!(emitted.default, clean.default, "switch DEFAULT differs");
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: emitted {:?} vs Clean {:?}",
        emitted.agg_consts, clean.agg_consts
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}",
        emitted.param_blocks, clean.param_blocks
    );
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call @func."),
        "the body must make no calls — that is what makes its reachable closure bodyful, and it \
         is the A0 criterion Level::is_zero fails"
    );
}

/// The measurement the chain rests on, pinned so it cannot quietly rot.
#[test]
fn flat_flags_contains_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("flat_flags_contains.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        evidence["def_path"].as_str(),
        Some("flat::types::FlatFlags::contains")
    );

    // A0, criterion by criterion.
    assert_eq!(evidence["lowered"].as_bool(), Some(true));
    assert_eq!(evidence["spliced"].as_bool(), Some(true));
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true),
        "markers_exact is the -O gate Level::is_zero fails; it must be TRUE here"
    );
    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            evidence["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(evidence["deferred_to_seam"].as_bool(), Some(false));
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(true));
    assert_eq!(evidence["flip_event"]["seam"].as_str(), Some("codegen"));
    assert_eq!(evidence["flip_event"]["asserts"].as_u64(), Some(0));

    // A6: the artifact inspected must be the artifact compiled.
    let artifact_lineage = evidence["lineage"]
        .as_str()
        .expect("artifact lineage must be a string");
    let flip_lineage = evidence["flip_event"]["lineage"]
        .as_str()
        .expect("flip-event lineage must be a string");
    assert!(
        artifact_lineage.starts_with("sha256:") && artifact_lineage.len() > "sha256:".len(),
        "artifact lineage must be a non-empty sha256 identifier"
    );
    assert_eq!(
        artifact_lineage, flip_lineage,
        "the artifact inspected by the differential gate must be the artifact compiled by A6"
    );
    assert_eq!(
        evidence["flip_event"]["matches_artifact_lineage"].as_bool(),
        Some(true)
    );
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains(artifact_lineage)),
        "the raw flip event must carry the same lineage"
    );
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains("clean_kernel[")),
        "attribution: THIS chain's flip event must name clean_kernel, whatever the aggregates say"
    );

    // The negative control is part of the evidence, not an aside.
    assert_eq!(
        evidence["negative_control"]["flip_events_crate_wide"].as_u64(),
        Some(0)
    );
    assert_eq!(
        evidence["negative_control"]["event_for_this_body_present"].as_bool(),
        Some(false)
    );
    assert_eq!(
        evidence["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true),
        "three clean builds must reproduce the digest, or `lineage` is not a measurement"
    );
    assert!(
        !j.contains("fcprobe") && !j.contains("flagsprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// **The non-vacuity of `markers_exact`, recorded as a number.**
///
/// This is the field that separates this chain from the three before it, and a
/// prose claim about it would rot silently. The fixture carries the marker
/// count and the whole-crate denominators, and this asserts them.
#[test]
fn flat_flags_contains_markers_exact_is_not_vacuous() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("flat_flags_contains.lineage.json"))
            .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "8 marker line(s) identical",
        "the marker sequence is EIGHT lines long and equal line for line; if this becomes \
         `0 marker line(s) identical` then markers_exact has gone vacuous here too and the \
         chain's distinguishing claim is false"
    );
    assert!(
        !detail.starts_with("0 "),
        "a zero-length marker sequence makes markers_exact a comparison of two empty sequences"
    );
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["markers_exact_rows_total"].as_u64(), Some(1082));
    assert_eq!(
        sel["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27)
    );
    assert_eq!(
        sel["codegen_flips_carrying_a_computing_construct"].as_u64(),
        Some(14),
        "the measured size of the pool this body was chosen from"
    );
    assert_eq!(
        sel["codegen_flips_with_a_gep_a_call_or_a_panic_arm"].as_u64(),
        Some(0),
        "the boundary is stated rather than worked around: no chainable body in this crate \
         contains a gep, a call or a panic arm at the deployed profile"
    );
    // The re-measurement disagreed with the committed census and says so.
    assert!(
        sel["disagreements_with_the_committed_census"]
            .as_array()
            .is_some_and(|d| !d.is_empty()),
        "this lane re-derived the candidate set rather than inheriting it; where it disagrees \
         with data/crystal_flip_census_2026-08-13.json the disagreement must be recorded, not \
         reconciled away"
    );
}
