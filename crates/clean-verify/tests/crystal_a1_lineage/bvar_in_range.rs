// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the FIFTH complete chain — the first over a body that
//! BRANCHES: `expr::bvar_in_range`.**
//!
//! The registered `ir_br_*` module must encode the CFG trustc emitted,
//! including the lane no earlier chain had anything in: **`condbr`**. Swapping
//! a conditional branch's two targets negates the predicate the body computes
//! and leaves every other lane — blocks, branches, join parameters, constants —
//! bit-identical, so before this lane the gate could not have seen it.
//!
//! Measured on `clean-kernel` itself at `c4e33541d`, sealed stage1 trustc
//! (trust `352aa0306d`), three clean non-incremental builds with a
//! byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("10 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 21 REAL marker lines
//! interpreter differential   agreed  on 125 sampled inputs
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:2789682b…
//! flip event                 FIRED, codegen seam, same lineage
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! Two of those rows are firsts for this program. The marker sequence is the
//! longest of any chained body (21 lines; 1,055 of the 1,082 `markers_exact`
//! rows in this crate compare two EMPTY sequences, and all three pre-existing
//! chains are in that majority). And the producer's own interpreter
//! differential actually ran here — 125 sampled inputs, THIR-trust-ir against
//! MIR-trust-ir — where every other chained body is `not-run`.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_br_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn bvar_in_range_proved_module_matches_the_emitted_artifact() {
    let text = fixture("bvar_in_range.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @expr::bvar_in_range("),
        "the fixture must be the bvar_in_range body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_bvar_range.rs", "const SRC_IR_BR_B"),
        "def ir_br_b",
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
        "NO switch: this body dispatches with condbr, which is the whole reason it was chained. \
         cases {:?} default {}",
        emitted.cases,
        emitted.default
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([3, 6]),
        "TWO join blocks take a parameter, not one: {:?}",
        emitted.param_blocks
    );
    assert_eq!(
        emitted.int_consts,
        BTreeMap::from([(0, vec![(5, 4294967295)])]),
        "one integer constant — u32::MAX, the sentinel: {:?}",
        emitted.int_consts
    );
    assert_eq!(
        emitted.consts,
        BTreeMap::from([(5, vec![(10, false)])]),
        "one bool constant, in bb5 — the short circuit's untaken side. It is the only place a \
         constant appears on an answer path: {:?}",
        emitted.consts
    );
    assert!(
        emitted.agg_consts.is_empty(),
        "no aggregate constants here: {:?}",
        emitted.agg_consts
    );
    assert!(
        emitted.loads.is_empty() && emitted.extracts.is_empty(),
        "three u32 arguments BY VALUE: no load, no field read. loads {:?} extracts {:?}",
        emitted.loads,
        emitted.extracts
    );
    assert!(
        emitted.binops.is_empty(),
        "the short circuit is CONTROL FLOW, not an `and` instruction — a body with a bitwise or \
         logical binop would be a different program and the reflected function would be a \
         Bool.and rather than a nested Bool.rec. Found {:?}",
        emitted.binops
    );

    // ── the two lanes that are new with this chain ──────────────────────────
    assert_eq!(
        emitted.condbrs,
        BTreeMap::from([(0, (6, 1, 2)), (2, (8, 4, 5))]),
        "TWO conditional branches: bb0 tests the sentinel (%6 -> bb1 / bb2) and bb2 tests the \
         lower bound (%8 -> bb4 / bb5). Exchanging either pair of targets negates what the body \
         computes and changes no other lane."
    );
    assert_eq!(
        emitted.icmps,
        BTreeMap::from([
            (0, vec![("eq".to_string(), 6, 2, 5)]),
            (1, vec![("uge".to_string(), 7, 0, 1)]),
            (2, vec![("uge".to_string(), 8, 0, 1)]),
            (4, vec![("ult".to_string(), 9, 0, 2)]),
        ]),
        "FOUR comparisons. Note bb1 and bb2 compute the SAME comparison into DIFFERENT SSA ids \
         (%7 and %8): the compiler does not share it across the sentinel branch, and a \
         transcription that did would have six blocks instead of seven."
    );
    assert_eq!(
        emitted.branches,
        BTreeMap::from([(1, 3), (4, 6), (5, 6), (6, 3)]),
        "four unconditional edges, and the last one is the load-bearing shape: the INNER join \
         (bb6) branches into the OUTER join (bb3). Collapsing the two joins agrees on every \
         answer and is a different graph."
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
        &clean_block_sources("eval_ir_bvar_range.rs", "const SRC_IR_BR_FUNC"),
        "bvar_in_range",
    );
    assert_lanes(&emitted, &clean, "bvar_in_range");
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. Both must be empty.",
        emitted.cases, clean.cases
    );
    assert_eq!(emitted.default, clean.default, "switch DEFAULT differs");
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. The sentinel is \
         4294967295 exactly; any other literal is a different function.",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
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
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}. Two joins, chained.",
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
    assert!(
        !text.contains("assert"),
        "no panic arm: `asserts=0` in the flip event, and no chainable body in this crate has \
         one at the deployed profile"
    );
}

/// The measurement the chain rests on, pinned so it cannot quietly rot.
#[test]
fn bvar_in_range_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("bvar_in_range.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(evidence["def_path"].as_str(), Some("expr::bvar_in_range"));

    assert_eq!(evidence["lowered"].as_bool(), Some(true));
    assert_eq!(evidence["spliced"].as_bool(), Some(true));
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true)
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
    assert_eq!(
        evidence["flip_event"]["asserts"].as_u64(),
        Some(0),
        "no panic arm survives into the flipped body"
    );

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
        "attribution: THIS chain's flip event must name clean_kernel"
    );

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
        Some(true)
    );
    assert!(
        !j.contains("bvarprobe") && !j.contains("rangeprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// **The two rows that are firsts for this program**, asserted as numbers so
/// they cannot be claimed in prose after they stop being true.
#[test]
fn bvar_in_range_marker_and_interpreter_rows_are_not_vacuous() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("bvar_in_range.lineage.json"))
        .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "21 marker line(s) identical",
        "the longest marker sequence of any chained body; if this becomes `0 marker line(s) \
         identical` then markers_exact has gone vacuous here and the claim is false"
    );
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("agreed"),
        "the producer's own interpreter differential RAN on this body — every other chained body \
         is `not-run`"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(125),
        "125 sampled inputs; a sample count of 0 with verdict `agreed` would be vacuous"
    );
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["markers_exact_rows_total"].as_u64(), Some(1082));
    assert_eq!(
        sel["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27)
    );
    assert_eq!(
        sel["of_those_with_a_clean_kernel_codegen_flip_event"].as_u64(),
        Some(177)
    );
    assert_eq!(
        sel["codegen_flips_carrying_a_computing_construct"].as_u64(),
        Some(14)
    );
    assert!(
        sel["disagreements_with_the_committed_census"]
            .as_array()
            .is_some_and(|d| !d.is_empty()),
        "this lane re-derived the candidate set rather than inheriting it; the disagreements with \
         data/crystal_flip_census_2026-08-13.json must be recorded, not reconciled away"
    );
}
