// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the ELEVENTH chain — and the first over a body that
//! COMPUTES AN ADDRESS AND DEREFERENCES IT: `env::types::SimpPriority::value`.**
//!
//! Every gate the other chains have, plus the lane that had nothing to compare
//! until now: **`geps`**. `Cfg` gained it on 2026-08-20 with this chain, for the
//! reason every lane in this file was added — a slot the artifact prints, the
//! registered term carries, and neither parser read. Before it, a transcription
//! that geps a different base, by a different index, at a different element
//! type, or that dropped `inbounds`, compared EQUAL in every other lane.
//!
//! ```text
//! derived_mir.verdict        agreed  ("7 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 2 REAL marker lines (NOT vacuous)
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:cbdd069b…
//! flip event                 FIRED, codegen seam, -O3, same lineage
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! perturbation control       switch-map REACHES the body (applications=1)
//!                            and turns it agreed -> mismatch
//! ```
//!
//! ## Why the perturbation row is called out
//!
//! The other `gep`-carrying chainable flip at HEAD,
//! `env::types::Reducibility::height`, is an equally good target on every axis
//! but one: `-Ztrust-sat-perturb=switch-map` records **`applications=0`** on it
//! — the control never reaches the body — so a green perturbation row there
//! would be a statement about nothing. It reaches THIS body and turns it
//! `mismatch`. Recorded in the fixture, not worked around.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed from the artifact here. And the layout premise —
//! that the payload lives at byte 4 — is `EncodesSimpPriority.custom`'s
//! hypothesis, not anything this gate checks.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn simp_priority_value_proved_module_matches_the_emitted_artifact() {
    let text = fixture("simp_priority_value.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::types::SimpPriority::value("),
        "the fixture must be the value body itself"
    );
    let emitted = parse_emitted(&text);
    // The registered blocks are the MINTED script (crystal A2, `src/ir_mint`),
    // not hand-written constants. The comparator is unchanged and is still an
    // independent reader: it reads the emitted TEXT on one side and Clean spec
    // source on the other, and neither path goes through the minter.
    let clean = parse_clean(
        &clean_block_sources("generated/ir_pv.defs.txt", "def ir_pv_"),
        "def ir_pv_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(emitted.blocks.len(), 4, "parser found {:?}", emitted.blocks);
    assert_eq!(
        emitted.cases.len(),
        1,
        "ONE explicit switch case (tag 0 -> the Default arm); the Custom arm rides the DEFAULT \
         edge, which is the shape that makes this body's gep sit on the default: {:?}",
        emitted.cases
    );
    assert_ne!(emitted.default, u32::MAX, "a switch default");
    assert_eq!(
        emitted.branches.len(),
        2,
        "two br edges into the join: {:?}",
        emitted.branches
    );
    assert!(
        !emitted.param_blocks.is_empty(),
        "a join block taking a u32 parameter"
    );

    // *** THE LANE THIS CHAIN EXISTS FOR. ***
    assert_eq!(
        emitted.geps,
        BTreeMap::from([(2, vec![(6, "int8".to_string(), 0, vec![5], true)])]),
        "ONE gep, in the DEFAULT-edge block: `gep inbounds i8, ptr %0, %5` — element type i8, \
         base the receiver %0, one index %5 (the materialized byte offset), inbounds. Found {:?}",
        emitted.geps
    );
    assert_eq!(
        emitted.loads,
        BTreeMap::from([(0, vec![(2, 0)]), (2, vec![(7, 6)])]),
        "TWO loads, and the second is the point: %2 reads through the receiver %0, and %7 reads \
         through %6 — THE GEP'S RESULT. No earlier chained body loads through an address it \
         computed. Found {:?}",
        emitted.loads
    );
    assert_eq!(
        emitted.int_consts,
        BTreeMap::from([(1, vec![(4, 1000)]), (2, vec![(5, 4)])]),
        "the Default arm materializes 1000 and the Custom arm materializes the byte offset 4; \
         the second is the gep's index. Found {:?}",
        emitted.int_consts
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(3, 2, 0)])]),
        "one extractfield: the discriminant of the loaded value. The PAYLOAD is NOT read this \
         way — that is what the gep is for, and a body that read it with a second extractfield \
         would be a different body with no gep at all."
    );
    assert!(
        emitted.icmps.is_empty() && emitted.binops.is_empty() && emitted.condbrs.is_empty(),
        "this body compares nothing, computes no arithmetic and branches conditionally nowhere"
    );
    assert!(
        emitted.consts.is_empty() && emitted.agg_consts.is_empty(),
        "its answers are integers: neither the bool nor the aggregate constant lane is used"
    );
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call "),
        "the emitted body CALLS NOTHING, which is what makes its reachable closure bodyful and \
         links 3/4 provable where Level::is_zero's are not"
    );

    // Now the comparison, lane by lane.
    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. The compiler emits only tag 0 and \
         routes Custom through the default; a module enumerating both tags is a different CFG.",
        emitted.cases, clean.cases
    );
    assert_eq!(emitted.default, clean.default, "switch DEFAULT differs");
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
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block BOOL constants differ: both must be empty. emitted {:?} vs Clean {:?}",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. 1000 is the Default \
         answer and 4 is the gep's byte offset; getting either wrong changes what the body \
         returns or where it reads.",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: both must be empty. emitted {:?} vs Clean {:?}",
        emitted.agg_consts, clean.agg_consts
    );
    assert_entry_params(
        &text,
        &clean_block_sources("generated/ir_pv.defs.txt", "def ir_pv_func"),
        "simp_priority_value",
    );
    assert_lanes(&emitted, &clean, "simp_priority_value");
}

/// **Falsification of the new lane.** A gate that cannot fail is not a gate,
/// and `geps` is one day old.
///
/// Four perturbations of the emitted `gep`, each a different program, each
/// caught HERE and by nothing else in this file: a different base, a different
/// index, a different element type, and a dropped `inbounds`.
#[test]
fn the_gep_lane_actually_discriminates() {
    let text = fixture("simp_priority_value.trust-ir.txt");
    let real = parse_emitted(&text);
    for (what, from, to) in [
        (
            "a different BASE — reads a different object entirely",
            "gep inbounds i8, ptr %0, %5",
            "gep inbounds i8, ptr %2, %5",
        ),
        (
            "a different INDEX — reads a different field of the same object",
            "gep inbounds i8, ptr %0, %5",
            "gep inbounds i8, ptr %0, %3",
        ),
        (
            "a different ELEMENT TYPE — trust-ir's own semantics scales the offset by it",
            "gep inbounds i8, ptr %0, %5",
            "gep inbounds i32, ptr %0, %5",
        ),
        (
            "a dropped INBOUNDS — the no-wrap licence, a Bool field of IRInst.gep",
            "gep inbounds i8, ptr %0, %5",
            "gep i8, ptr %0, %5",
        ),
    ] {
        let mutated = text.replace(from, to);
        assert_ne!(
            mutated, text,
            "the perturbation must actually apply: {what}"
        );
        let got = parse_emitted(&mutated);
        assert_ne!(
            got.geps, real.geps,
            "PERTURBATION NOT CAUGHT ({what}): the gep lane read {:?} for a body the artifact \
             does not emit",
            got.geps
        );
        // And it is caught THERE and not incidentally elsewhere: every other
        // lane is unmoved, which is the whole argument for the lane existing.
        assert_eq!(
            got.loads, real.loads,
            "({what}) the load lane moved too, so this perturbation would have been caught \
             without the gep lane and proves nothing about it"
        );
        assert_eq!(got.blocks, real.blocks, "({what}) block set moved");
        assert_eq!(got.int_consts, real.int_consts, "({what}) constants moved");
        assert_eq!(got.extracts, real.extracts, "({what}) extracts moved");
    }
}

/// The measurement the whole chain rests on, pinned so it cannot quietly rot.
#[test]
fn simp_priority_value_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("simp_priority_value.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6(&evidence, "env::types::SimpPriority::value");

    // The three facts this chain adds to the shared helper's list.
    assert_eq!(
        evidence["derived_mir"]["markers_detail"].as_str(),
        Some("2 marker line(s) identical"),
        "markers_exact here must be NON-VACUOUS. 1,055 of the tree's markers_exact rows compare \
         two EMPTY sequences and are true statements about nothing; a chain that landed in that \
         majority would be claiming a gate it never passed."
    );
    assert!(
        !evidence["derived_mir"]["markers_detail"]
            .as_str()
            .unwrap_or("")
            .starts_with("0 marker line(s)"),
        "the vacuous form is exactly `0 marker line(s) identical` and it must not appear here"
    );
    let p = &evidence["perturbation_control"];
    assert_eq!(
        p["flag"].as_str(),
        Some("-Ztrust-sat-perturb=switch-map"),
        "the fail-closed control must name the perturbation class it ran"
    );
    assert_eq!(
        p["reached_this_body"].as_bool(),
        Some(true),
        "A CONTROL THAT DOES NOT REACH THE BODY IS NOT A CONTROL. This is the axis on which \
         Reducibility::height was rejected as this lane's target: switch-map records \
         applications=0 on it."
    );
    assert!(
        p["applications"].as_u64().is_some_and(|n| n > 0),
        "applications must be non-zero, and it is the number the compiler PRINTED"
    );
    assert_eq!(
        p["verdict_under_perturbation"].as_str(),
        Some("mismatch"),
        "and having reached the body it must turn the differential red"
    );
    assert_eq!(
        p["flip_event_under_perturbation"].as_bool(),
        Some(false),
        "a perturbed body must not flip: the gate is fail-closed on disagreement"
    );
    assert_eq!(
        evidence["bodyful_reachable_closure"]
            .as_str()
            .map(|s| s.starts_with("PASS")),
        Some(true),
        "the A0 criterion Level::is_zero fails"
    );
}
