// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the SEVENTH complete chain — the widest dispatch, and
//! the first body chained here that a DERIVE wrote:
//! `<tc::expr_location::ExprPathStep as Clone>::clone`.**
//!
//! Thirteen blocks, ten explicit switch cases plus a reachable default over
//! eleven variants, eleven aggregate constants, one `load`, one `extractfield`,
//! one aggregate-carrying join. It is the first chained body that combines the
//! first chain's `load` + `extractfield` prologue with the third chain's
//! aggregate-constant arms, so this gate is the first to compare all four of
//! those lanes on one body.
//!
//! Measured on `clean-kernel` itself at this HEAD, freshly sealed stage1 trustc
//! (`seal_driver.sh guard` PASS before the run), three clean non-incremental
//! builds with a byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("16 canonical line(s) identical")
//! derived_mir.markers_exact  true    over ZERO marker lines — VACUOUS, see below
//! interpreter differential   not-run ("param 0 (ptr) is READ … opaque sampling refused")
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:f02dcc4b…
//! flip event                 FIRED, codegen seam, same lineage
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! ## The marker row is vacuous here, and the gate says so out loud
//!
//! Unlike the fourth, fifth and sixth chains, this body is in the vacuous
//! majority: `markers_exact: true` over two EMPTY sequences. The test below
//! asserts that it IS vacuous rather than leaving it unstated, so that the
//! evidence list for this chain cannot silently acquire a sentence it has not
//! earned. What backs it instead is the longest canonical-line comparison of
//! any chained body — sixteen — plus the lineage equality and the flip.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_ep_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn expr_path_step_clone_proved_module_matches_the_emitted_artifact() {
    let text = fixture("expr_path_step_clone.trust-ir.txt");
    assert!(
        text.starts_with(
            "rustcc fn @<tc::expr_location::ExprPathStep as std::clone::Clone>::clone("
        ),
        "the fixture must be the derived clone body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_path_step.rs", "const SRC_IR_EP_B"),
        "def ir_ep_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so pin what the
    // emitted body actually contains before comparing anything.
    assert_eq!(
        emitted.blocks,
        (0..13).collect::<Vec<u32>>(),
        "thirteen blocks, bb0..bb12; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.cases.len(),
        10,
        "TEN explicit switch cases over ELEVEN variants: {:?}",
        emitted.cases
    );
    assert_eq!(
        emitted.agg_consts.len(),
        11,
        "eleven aggregate constants, one per arm: {:?}",
        emitted.agg_consts
    );
    assert!(
        emitted.condbrs.is_empty(),
        "this body dispatches with a switch, not with condbrs: {:?}",
        emitted.condbrs
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([12]),
        "ONE join block, and it carries an aggregate: {:?}",
        emitted.param_blocks
    );

    // The emitted facts, spelled out.
    assert_eq!(
        emitted.cases,
        (0..10u32)
            .map(|k| (k, k + 1))
            .collect::<BTreeMap<u32, u32>>(),
        "cases 0..9 map to bb1..bb10 — CONTIGUOUS, unlike from_source_system's"
    );
    assert_eq!(
        emitted.default, 11,
        "tag 10 (ProjExpr) is the value the DEFAULT edge carries, so the default is neither a \
         trap nor unreachable: it is one specific real variant"
    );
    assert_eq!(
        emitted.agg_consts,
        (0..11u32)
            .map(|k| (k + 1, vec![(k + 4, k)]))
            .collect::<BTreeMap<u32, Vec<(u32, u32)>>>(),
        "arm bbK+1 materialises `const enum.184 {{ K }}` — eleven DISTINCT constants; a clone \
         that answered the same variant twice would be caught here and nowhere else"
    );
    assert_eq!(
        emitted.loads,
        BTreeMap::from([(0, vec![(2, 0)])]),
        "one load, through the &self pointer, binding %2"
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(3, 2, 0)])]),
        "one extractfield: field 0 of the LOADED value, not of the pointer"
    );
    assert_eq!(
        emitted.branches,
        (1..12u32).map(|k| (k, 12)).collect::<BTreeMap<u32, u32>>(),
        "every arm branches to the single join block"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. Ten explicit cases and one variant on \
         the default edge; a table transcribed as 0..10 is a different switch.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted bb{} vs Clean bb{}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: emitted {:?} vs Clean {:?}",
        emitted.agg_consts, clean.agg_consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. This body's answers are \
         `const enum.184 {{ k }}` aggregates, NOT `const u8 k`; the two route through different \
         evaluators and both sides of this lane must be empty.",
        emitted.int_consts, clean.int_consts
    );
    assert!(
        emitted.int_consts.is_empty() && emitted.consts.is_empty(),
        "the clone body materializes no scalar constant of any kind"
    );
    // …and the same lane against CLEAN's. Until the 2026-08-16 lane audit this
    // chain checked the line above and nothing else: the emitted side was
    // asserted empty, the Clean side was never read, and an `IRConst.bool_`
    // appearing in `ir_ep_*` would have been invisible to the only chain in the
    // file that omitted this comparison.
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN block differs: emitted {:?} vs Clean {:?}",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_path_step.rs", "const SRC_IR_EP_FUNC"),
        "expr_path_step_clone",
    );
    assert_lanes(&emitted, &clean, "expr_path_step_clone");
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
fn expr_path_step_clone_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("expr_path_step_clone.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6(
        &evidence,
        "<tc::expr_location::ExprPathStep as std::clone::Clone>::clone",
    );
    assert!(
        evidence["derive_provenance"]
            .as_str()
            .is_some_and(|s| s.contains("#[derive(")),
        "the body's authorship is part of what makes this chain interesting and is recorded"
    );
    assert!(
        !j.contains("epprobe") && !j.contains("cloneprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// **`markers_exact` is VACUOUS here, and that is asserted rather than omitted.**
///
/// The inverse of the fourth/fifth/sixth chains' non-vacuity gate, and it earns
/// its place for the same reason: an unstated vacuity is how "and the markers
/// agreed" gets quoted as evidence for a chain where the marker channel
/// compared nothing. If this body ever GAINS marker content the assertion fails
/// and the claim gets rewritten deliberately.
#[test]
fn expr_path_step_clone_markers_exact_is_vacuous_and_says_so() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("expr_path_step_clone.lineage.json"))
            .expect("evidence must be valid JSON");
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true),
        "the -O gate must still pass: it is what admits the flip"
    );
    assert_eq!(
        evidence["derived_mir"]["markers_detail"].as_str(),
        Some("0 marker line(s) identical"),
        "and it must be recorded as comparing NOTHING"
    );
    assert!(
        evidence["derived_mir"]["markers_exact_is_vacuous_here"]
            .as_str()
            .is_some_and(|s| s.starts_with("VACUOUS")),
        "the fixture must state the vacuity in words as well as in the count"
    );
    // What actually backs the chain, as a number.
    assert_eq!(
        evidence["derived_mir"]["detail"].as_str(),
        Some("16 canonical line(s) identical"),
        "the canonical channel did real work here — sixteen lines, the longest of any chained \
         body — and that is the row this chain's evidence rests on"
    );
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("not-run"),
        "the producer refuses to sample a dereferenced opaque pointer; claiming an interpreter \
         differential here would be false"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(0),
        "a not-run differential carries ZERO samples. Asserted separately from the verdict \
         because the two can drift apart in a hand-edited fixture, and `agreed on 0 samples` is \
         precisely the vacuous shape the fifth chain's gate already pins from the other side"
    );
}
