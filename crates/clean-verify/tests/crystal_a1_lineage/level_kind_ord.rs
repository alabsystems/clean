// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the SECOND complete chain: `level::Level::kind_ord`.**
//!
//! Same two gates `has_cubical_layer` has, over a structurally different body:
//! the registered `ir_ko_*` module must encode the CFG trustc actually emitted,
//! and the flip event's A-LIN lineage must equal the coverage row's.
//!
//! The fixture is the verbatim emission from a whole-crate release differential
//! of `clean-kernel`, RE-MEASURED 2026-08-13 at trustc `bd36c65a8` (the values below
//! were first taken at `fcecd8d7e`; the lineage digest shown there, `sha256:223ca899…`,
//! is now SUPERSEDED — see the fixture's `supersedes` block for why):
//!
//! ```text
//! derived_mir.verdict        agreed  ("10 canonical line(s) identical")
//! derived_mir.markers_exact  true
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:0082ed43…  (was sha256:223ca899…, v1 domain)
//! flip event                 FIRED, codegen seam, same lineage
//! ```
//!
//! The `calls` row is why the A0 criterion `bodyful reachable closure` PASSES
//! here and FAILS for `Level::is_zero`: this body has no callees at all, so its
//! reachable closure is itself and contains no declaration-only entry. Nothing
//! was widened to achieve that — it is a property of the body.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed from the artifact here; verifying it at flip time is the
//! compiler's job. And `ir_ko_module` is hand-transcribed: this makes an
//! incorrect transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn kind_ord_proved_module_matches_the_emitted_artifact() {
    let text = fixture("level_kind_ord.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @level::Level::kind_ord("),
        "the fixture must be the kind_ord body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_kind_ord.rs", "const SRC_IR_KO_B"),
        "def ir_ko_b",
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
    assert_eq!(
        emitted.cases.len(),
        4,
        "four EXPLICIT switch cases: {:?}",
        emitted.cases
    );
    assert_eq!(
        emitted.int_consts.len(),
        5,
        "five integer-constant arms: {:?}",
        emitted.int_consts
    );
    assert!(
        emitted.consts.is_empty(),
        "this body materializes no BOOL constants: {:?}",
        emitted.consts
    );
    assert_eq!(
        emitted.branches.len(),
        5,
        "five br edges into the join: {:?}",
        emitted.branches
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([6]),
        "exactly one join block takes a parameter"
    );
    assert_ne!(emitted.default, u32::MAX, "a switch default");

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 3), (3, 4)]),
        "the emitted switch routes Zero->bb1 Succ->bb2 Max->bb3 IMax->bb4"
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. The compiler emits four explicit tags \
         and routes Param through the default; a five-case table is a different body.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, 5,
        "the default edge carries the reachable Param arm"
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted bb{} vs Clean bb{}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER CONSTANTS differ: emitted {:?} vs Clean {:?}. Five distinct answers \
         are emitted, one per arm; permuting or collapsing any two is a different function.",
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
         are u8 scalars, so BOTH sides must be empty — the aggregate lane exists for \
         from_source_system and must not leak into a chain that has none.",
        emitted.agg_consts, clean.agg_consts
    );
    assert!(
        emitted.agg_consts.is_empty(),
        "kind_ord materializes no aggregate constants"
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.param_blocks, clean.param_blocks,
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}. The emitted body funnels all five \
         arms into a block taking a u8 parameter and returns it; returning directly from each \
         arm is a different body.",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_kind_ord.rs", "const SRC_IR_KO_FUNC"),
        "level_kind_ord",
    );
    assert_lanes(&emitted, &clean, "level_kind_ord");
    assert_eq!(
        emitted.loads,
        BTreeMap::from([(0, vec![(2, 0)])]),
        "one load, of the &Level receiver, binding %2"
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(3, 2, 0)])]),
        "one extractfield, at field 0 — the tag — of the LOADED value, not of the pointer"
    );
    assert!(
        emitted.icmps.is_empty() && emitted.binops.is_empty() && emitted.condbrs.is_empty(),
        "kind_ord dispatches on a tag; it compares nothing and computes nothing"
    );
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block: exhaustiveness is expressed by the default edge \
         carrying the Param answer, so a Clean module with an `unreachable` default is not this \
         body"
    );
    assert!(
        !text.contains("call @func."),
        "the body must make no calls — that is what makes its reachable closure bodyful, and it \
         is the A0 criterion Level::is_zero fails"
    );
}

/// The measurement the chain rests on, pinned so it cannot quietly rot.
///
/// Taken on **clean-kernel itself**, not on a probe crate: the differential
/// verdict, the flip event, and the equality of the two lineage digests.
#[test]
fn kind_ord_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("level_kind_ord.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        evidence["def_path"].as_str(),
        Some("level::Level::kind_ord")
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
    // bodyful reachable closure — established by there being no callees at all
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

    // The negative control is part of the evidence, not an aside: without it a
    // flip count is not attributable to the flag that is supposed to cause it.
    assert_eq!(
        evidence["negative_control"]["flip_events_crate_wide"].as_u64(),
        Some(0)
    );
    assert_eq!(
        evidence["negative_control"]["coverage_json_byte_identical_to_flip_build"].as_bool(),
        Some(true),
        "the two clean builds must reproduce the digest, or `lineage` is not a measurement"
    );

    assert!(
        !j.contains("koprobe") && !j.contains("lvlprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// The candidate set is a MEASUREMENT and travels with the chain, because the
/// choice of this body is only defensible against it.
#[test]
fn kind_ord_candidate_selection_is_recorded() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("level_kind_ord.lineage.json"))
        .expect("evidence must be valid JSON");
    let why = evidence["candidate_selection"]["why_this_body"]
        .as_str()
        .expect("the selection rationale must be recorded");
    for figure in ["1058", "185", "153", "138"] {
        assert!(
            why.contains(figure),
            "the measured candidate-set figure {figure} must be recorded"
        );
    }
    // The count the candidate set is cut from is the CLEAN-KERNEL-ATTRIBUTED one, not the
    // build-wide total. Those were the same number when this evidence was first taken (185,
    // all of them clean-kernel's); they are not any more. The trust-ir fragment has widened
    // far enough that dependency crates flip too — 4575 events build-wide at this HEAD, of
    // which 199 name clean_kernel — so a build-wide total no longer attributes to this crate
    // and must never be quoted as if it did.
    assert_eq!(
        evidence["build"]["flip_events_clean_kernel"].as_u64(),
        Some(209),
        "the clean-kernel-attributed flip count the candidate set was cut from"
    );
    assert_eq!(
        evidence["build"]["flip_events_codegen"]
            .as_u64()
            .zip(evidence["build"]["flip_events_ctfe"].as_u64())
            .map(|(codegen, ctfe)| codegen + ctfe),
        evidence["build"]["flip_events_clean_kernel"].as_u64(),
        "the two seams must exhaust the clean-kernel count, or one of the three is mis-scoped"
    );
    // Attribution used to rest on `flip_events_all_from_clean_kernel == true`. That invariant
    // is dead — it is now measurably false — so it is replaced by the STRONGER property it was
    // standing in for: THIS body's own raw flip event names clean_kernel. An aggregate never
    // established that; the raw event does.
    assert_eq!(
        evidence["build"]["flip_events_all_from_clean_kernel"].as_bool(),
        Some(false),
        "recorded as measured: dependency crates flip too at this HEAD"
    );
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains("clean_kernel[")),
        "attribution: THIS chain's flip event must name clean_kernel, whatever the aggregates say"
    );
}
