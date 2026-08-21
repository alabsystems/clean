// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the FIRST complete chain:
//! `mode::CleanMode::has_cubical_layer`.**
//!
//! Moved out of `crystal_a1_lineage.rs` on 2026-08-16, when the ninth chain
//! took that file past the 500-line convention. Nothing here changed in the
//! move. It is also the file the first chain should always have had: every
//! other chain has one, and the first was the only one squatting in the root
//! module beside the shared `assert_a0_a6` helper and the numeral gate.
//!
//! The rationale for the gate itself — including the FOUR structural ways the
//! first hand-authored version disagreed with the shipped body — is in the
//! module doc of `crystal_a1_lineage.rs`, which is where it belongs, because it
//! is the rationale for every chain's gate and not for this one's.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn proved_module_matches_the_emitted_artifact() {
    let text = fixture("has_cubical_layer.trust-ir.txt");
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        // The registered blocks are now the MINTED script, not seven hand-
        // written constants (crystal A2, `src/ir_mint`). The comparator itself
        // is unchanged and still an independent reader: it reads the emitted
        // TEXT on one side and Clean spec source on the other, and neither
        // path goes through the minter.
        &clean_block_sources("generated/ir_h2.defs.txt", "def ir_h2_"),
        "def ir_h2_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(emitted.blocks.len(), 5, "parser found {:?}", emitted.blocks);
    assert_eq!(
        emitted.cases.len(),
        2,
        "two switch cases: {:?}",
        emitted.cases
    );
    assert_eq!(
        emitted.consts.len(),
        3,
        "three constant-producing arms: {:?}",
        emitted.consts
    );
    assert_eq!(
        emitted.branches.len(),
        3,
        "three br edges: {:?}",
        emitted.branches
    );
    assert!(
        !emitted.param_blocks.is_empty(),
        "a join block taking a parameter"
    );
    assert_ne!(emitted.default, u32::MAX, "a switch default");

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. The first version of this module \
         enumerated all six tags; the compiler emits only the true ones and routes the rest \
         through the default.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted bb{} vs Clean bb{}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block CONSTANTS differ: emitted {:?} vs Clean {:?}. Two distinct true blocks are \
         emitted; collapsing them into one is a different CFG.",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. This body's answers are \
         Bools, so BOTH sides must be empty; an integer appearing on one side only is a \
         transcription that changed the constant lane.",
        emitted.int_consts, clean.int_consts
    );
    assert!(
        emitted.int_consts.is_empty(),
        "has_cubical_layer materializes no integer constants"
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE constants differ: emitted {:?} vs Clean {:?}. This body's answers \
         are Bools, so BOTH sides must be empty — the aggregate lane exists for \
         from_source_system and must not leak into a chain that has none.",
        emitted.agg_consts, clean.agg_consts
    );
    assert!(
        emitted.agg_consts.is_empty(),
        "has_cubical_layer materializes no aggregate constants"
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}. The emitted body funnels every arm \
         into a block taking a bool parameter and returns it; returning directly from each arm \
         is a different body.",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("generated/ir_h2.defs.txt", "def ir_h2_func"),
        "has_cubical_layer",
    );
    assert_lanes(&emitted, &clean, "has_cubical_layer");
    // This body loads through its receiver and reads field 0; it computes
    // nothing. Pinning the three empty lanes is the coverage denominator for
    // them — an empty-vs-empty comparison proves nothing on its own.
    assert_eq!(
        emitted.loads,
        BTreeMap::from([(0, vec![(2, 0)])]),
        "one load, of the receiver, binding %2"
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(3, 2, 0)])]),
        "one extractfield: the discriminant of the loaded value"
    );
    assert!(
        emitted.icmps.is_empty() && emitted.binops.is_empty() && emitted.condbrs.is_empty(),
        "this body compares nothing, computes nothing and branches conditionally nowhere"
    );
    assert!(
        !fixture("has_cubical_layer.trust-ir.txt").contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
}

/// The measurement the whole chain rests on, pinned so it cannot quietly rot.
///
/// Taken on **clean-kernel itself**, not on a probe crate: the differential
/// verdict, the flip event, and the equality of the two lineage digests.
#[test]
fn a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("has_cubical_layer.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        evidence["def_path"].as_str(),
        Some("mode::CleanMode::has_cubical_layer")
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true)
    );
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(true));
    assert_eq!(
        evidence["flip_event"]["matches_artifact_lineage"].as_bool(),
        Some(true)
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
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains(artifact_lineage)),
        "the raw flip event must carry the same lineage"
    );
    assert!(
        !j.contains("hclprobe") && !j.contains("hclflip"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}
