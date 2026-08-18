// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the SIXTH complete chain — the second and last body in
//! `clean-kernel` that BRANCHES: `env::native_reducers_char::is_valid_char`.**
//!
//! The registered `ir_vc_*` module must encode the CFG trustc emitted, and two
//! of its rows are things no earlier gate could have caught:
//!
//! * the entry `condbr`'s targets are `(bb2, bb1)` — the HIGHER block first.
//!   Every other branching body in this program branches the other way, so a
//!   transcription that copied the fifth chain's polarity computes the negation
//!   of this body and agrees with every lane except `condbrs`.
//! * `bb1`'s `icmp` has the MATERIALISED CONSTANT AS ITS LEFT OPERAND
//!   (`icmp ult u64 %5, %0`). No earlier chained body does. Exchanging the two
//!   operands turns `0xDFFF < n` into `n < 0xDFFF`, leaves the block count, the
//!   branch targets, the constants and the result ids identical, and is caught
//!   only because the `icmp` lane compares operand ORDER.
//!
//! Measured on `clean-kernel` itself at this HEAD, freshly sealed stage1 trustc
//! (`seal_driver.sh guard` PASS before the run), three clean non-incremental
//! builds with a byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("8 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 12 REAL marker lines
//! interpreter differential   agreed  on 5 sampled inputs
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:2f956ee9…
//! flip event                 FIRED, codegen seam, same lineage
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_vc_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn is_valid_char_proved_module_matches_the_emitted_artifact() {
    let text = fixture("is_valid_char.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::native_reducers_char::is_valid_char("),
        "the fixture must be the is_valid_char body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_valid_char.rs", "const SRC_IR_VC_B"),
        "def ir_vc_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(
        emitted.blocks,
        (0..7).collect::<Vec<u32>>(),
        "seven blocks, bb0..bb6; parser found {:?}",
        emitted.blocks
    );
    assert!(
        emitted.cases.is_empty() && emitted.default == u32::MAX,
        "NO switch: this body dispatches with condbr. cases {:?} default {}",
        emitted.cases,
        emitted.default
    );
    assert_eq!(
        emitted.condbrs.len(),
        2,
        "TWO conditional branches: {:?}",
        emitted.condbrs
    );
    assert_eq!(
        emitted.icmps.values().map(Vec::len).sum::<usize>(),
        3,
        "three comparisons: {:?}",
        emitted.icmps
    );
    assert_eq!(
        emitted.int_consts.len(),
        3,
        "three u64 constants, one per comparison: {:?}",
        emitted.int_consts
    );
    assert_eq!(
        emitted.consts.len(),
        2,
        "two bool constants, one per short-circuit answer: {:?}",
        emitted.consts
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([3, 6]),
        "TWO join blocks take a parameter: {:?}",
        emitted.param_blocks
    );

    // The emitted facts, spelled out, so the equality below is checked against
    // a known body rather than against whatever the parser happened to find.
    assert_eq!(
        emitted.condbrs,
        BTreeMap::from([(0, (4, 2, 1)), (1, (6, 4, 5))]),
        "bb0 branches on %4 to (bb2, bb1) — the HIGHER block on the TRUE edge, the opposite \
         polarity to expr::bvar_in_range — and bb1 branches on %6 to (bb4, bb5)"
    );
    assert_eq!(
        emitted.icmps,
        BTreeMap::from([
            (0, vec![("ult".to_string(), 4, 0, 3)]),
            (1, vec![("ult".to_string(), 6, 5, 0)]),
            (4, vec![("ult".to_string(), 9, 0, 8)]),
        ]),
        "three `ult`s, and the MIDDLE one has the constant %5 on the LEFT: that operand order \
         is the structurally new thing in this chain"
    );
    assert_eq!(
        emitted.int_consts,
        BTreeMap::from([
            (0, vec![(3, 55296)]),
            (1, vec![(5, 57343)]),
            (4, vec![(8, 1_114_112)])
        ]),
        "0xD800, 0xDFFF and 0x110000, each materialised in its own block, each bound to its own \
         SSA id"
    );
    assert_eq!(
        emitted.consts,
        BTreeMap::from([(2, vec![(7, true)]), (5, vec![(10, false)])]),
        "bb2 answers true directly; bb5 is the short circuit's `false` and never evaluates the \
         upper bound"
    );
    assert_eq!(
        emitted.branches,
        BTreeMap::from([(2, 3), (4, 6), (5, 6), (6, 3)]),
        "bb2 reaches the OUTER join directly; bb4 and bb5 reach the INNER join, which forwards \
         to the outer one"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. These are the three \
         Unicode boundaries; one transcribed off by one is a different predicate.",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: emitted {:?} vs Clean {:?}. This body's answers \
         are Bools, so BOTH sides must be empty.",
        emitted.agg_consts, clean.agg_consts
    );
    assert!(
        emitted.agg_consts.is_empty(),
        "is_valid_char materializes no aggregate constants"
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. Both must be empty — a module that \
         dispatches with a switch is not this body.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted {} vs Clean {}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}. Collapsing the two joins into one \
         agrees on every answer and is a different graph.",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_valid_char.rs", "const SRC_IR_VC_FUNC"),
        "is_valid_char",
    );
    assert_lanes(&emitted, &clean, "is_valid_char");
    assert!(
        emitted.loads.is_empty() && emitted.extracts.is_empty() && emitted.binops.is_empty(),
        "this body takes its argument by value, reads no field and computes no arithmetic"
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
fn is_valid_char_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("is_valid_char.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6(&evidence, "env::native_reducers_char::is_valid_char");
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("agreed"),
        "the producer's own interpreter differential RAN on this body"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(5)
    );
    assert!(
        !j.contains("vcprobe") && !j.contains("charprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// **The non-vacuity of `markers_exact`, recorded as a number.**
#[test]
fn is_valid_char_markers_exact_is_not_vacuous() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("is_valid_char.lineage.json"))
        .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "12 marker line(s) identical",
        "the marker sequence is TWELVE lines long and equal line for line; if this becomes \
         `0 marker line(s) identical` then markers_exact has gone vacuous here too"
    );
    assert!(!detail.starts_with("0 "));
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["markers_exact_rows_total"].as_u64(), Some(1084));
    assert_eq!(
        sel["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27),
        "the population moved from 1082 to 1084 rows and the non-vacuous count did NOT move — \
         the second independent confirmation that a markers_exact gain is not a fidelity gain"
    );
}

// The COST and ATTRIBUTION measurements — the residue cost law, the law that
// replaced it, the eleven-minute attribution and what the comparison lemmas
// cost. Moved out VERBATIM on 2026-08-17: this file had reached 602 lines
// against the 500-line convention `files_over_500` enforces shrink-only. This
// file stays the links-2a/2c gate; that one is the recorded cost model.
#[path = "is_valid_char_cost.rs"]
mod cost;
