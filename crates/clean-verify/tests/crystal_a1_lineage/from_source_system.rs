// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the THIRD complete chain:
//! `mode::CleanMode::from_source_system`.**
//!
//! Same two gates the other two chains have, over the structurally widest
//! fully-flippable body in `clean-kernel`: the registered `ir_fs_*` module must
//! encode the CFG trustc actually emitted, and the flip event's A-LIN lineage
//! must equal the coverage row's.
//!
//! The fixture is the verbatim emission from a whole-crate release differential
//! of `clean-kernel`, reproduced by two clean non-incremental builds with
//! byte-identical coverage:
//!
//! ```text
//! derived_mir.verdict        agreed  ("17 canonical line(s) identical")
//! derived_mir.markers_exact  true
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:b2ff2df4…
//! flip event                 FIRED, codegen seam, same lineage
//! ```
//!
//! ## What is new here, and what it cost
//!
//! This body was measured as **not chainable** on 2026-08-12
//! (`data/crystal_width_candidates_2026-08-12.json`, rank 2) because every arm
//! emits `const enum.13 { k }` — a `trust_ir::Constant::Aggregate` — and
//! Clean's `IRConst` had seven constructors and no aggregate form. The gap was
//! closed by BUILDING the missing form, per the standing rule; the third
//! constant lane in [`super::Cfg`] (`agg_consts`) exists so that the aggregate
//! arms are checked as aggregates rather than being folded into the integer
//! lane they are not.
//!
//! It is also the first chain whose argument arrives **by value**: there is no
//! `load` in the emitted body and no heap in the theorem.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed from the artifact here; verifying it at flip time is the
//! compiler's job. And `ir_fs_module` is hand-transcribed: this makes an
//! incorrect transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn from_source_system_proved_module_matches_the_emitted_artifact() {
    let text = fixture("from_source_system.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @mode::CleanMode::from_source_system("),
        "the fixture must be the from_source_system body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_from_source.rs", "const SRC_IR_FS_B"),
        "def ir_fs_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(
        emitted.blocks,
        (0..14).collect::<Vec<u32>>(),
        "fourteen blocks, bb0..bb13; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.cases.len(),
        11,
        "eleven EXPLICIT switch cases: {:?}",
        emitted.cases
    );
    assert_eq!(
        emitted.agg_consts.len(),
        12,
        "twelve AGGREGATE-constant arms — eleven explicit plus the default: {:?}",
        emitted.agg_consts
    );
    assert!(
        emitted.int_consts.is_empty() && emitted.consts.is_empty(),
        "this body materializes NO scalar constants; every arm is an aggregate. int {:?} bool {:?}",
        emitted.int_consts,
        emitted.consts
    );
    assert_eq!(
        emitted.branches.len(),
        12,
        "twelve br edges into the join: {:?}",
        emitted.branches
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([13]),
        "exactly one join block takes a parameter"
    );
    assert_ne!(emitted.default, u32::MAX, "a switch default");

    // The constant text form is the aggregate one, checked on the RAW fixture
    // rather than through the parser: `{ k }` is `Constant::Aggregate`'s
    // spelling (`trust-ir/src/display.rs:1280`), and it is the whole reason
    // this body needed a build item before it could be chained.
    assert!(
        text.contains("= const enum.13 { 0 }"),
        "the emitted arms must be AGGREGATE constants — that construct is what IRConst was \
         extended for, and a fixture without it would make this chain's premise false"
    );
    assert!(
        !text.contains("load "),
        "the argument arrives BY VALUE: an emitted body with a load is a different body, and \
         the heap-free representation premise would no longer be the honest one"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases,
        BTreeMap::from([
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 4),
            (4, 5),
            (5, 6),
            (6, 7),
            (7, 8),
            (8, 9),
            (9, 10),
            (11, 11),
        ]),
        "the emitted switch case list is NON-CONTIGUOUS: 0..9 then 11, with tag 10 (PVS) routed \
         through the default"
    );
    assert!(
        !emitted.cases.contains_key(&10),
        "tag 10 must NOT be an explicit case — it is the value the default edge carries, and a \
         transcription that listed it would be a different CFG that happens to agree on answers"
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. Eleven explicit tags with a hole at \
         10; a contiguous twelve-case table is a different body.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, 12,
        "the default edge carries the reachable PVS arm"
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted bb{} vs Clean bb{}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.agg_consts,
        BTreeMap::from([
            (1, vec![(3, 0)]),
            (2, vec![(4, 1)]),
            (3, vec![(5, 0)]),
            (4, vec![(6, 2)]),
            (5, vec![(7, 4)]),
            (6, vec![(8, 4)]),
            (7, vec![(9, 4)]),
            (8, vec![(10, 5)]),
            (9, vec![(11, 5)]),
            (10, vec![(12, 4)]),
            (11, vec![(13, 4)]),
            (12, vec![(14, 4)]),
        ]),
        "the twelve arms answer with five distinct modes through a many-to-one map"
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-block AGGREGATE CONSTANTS differ: emitted {:?} vs Clean {:?}. Twelve arms map onto \
         five distinct discriminants; permuting or collapsing any two is a different function.",
        emitted.agg_consts, clean.agg_consts
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-block INTEGER constants differ: emitted {:?} vs Clean {:?}. BOTH must be empty — an \
         integer appearing on one side only is a transcription that changed the constant lane, \
         which is exactly the mistake the third lane exists to catch.",
        emitted.int_consts, clean.int_consts
    );
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
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}. The emitted body funnels all twelve \
         arms into a block taking an enum.13 parameter and returns it; returning directly from \
         each arm is a different body.",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_from_source.rs", "const SRC_IR_FS_FUNC"),
        "from_source_system",
    );
    assert_lanes(&emitted, &clean, "from_source_system");
    assert!(
        emitted.loads.is_empty(),
        "the argument arrives by value, so there is no load lane at all: {:?}",
        emitted.loads
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(2, 0, 0)])]),
        "one extractfield, at field 0 of the by-value argument itself"
    );
    assert!(
        emitted.icmps.is_empty() && emitted.binops.is_empty() && emitted.condbrs.is_empty(),
        "this body dispatches on a tag; it compares nothing and computes nothing"
    );
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block: exhaustiveness is expressed by the default edge \
         carrying the PVS answer, so a Clean module with an `unreachable` default is not this \
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
fn from_source_system_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("from_source_system.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        evidence["def_path"].as_str(),
        Some("mode::CleanMode::from_source_system")
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
        !j.contains("fsprobe") && !j.contains("modeprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}

/// The build item this chain needed is recorded WITH the chain, because the
/// claim "link 3 now holds for this body" is only defensible against it.
#[test]
fn from_source_system_records_the_measured_aggregate_shape() {
    let evidence: serde_json::Value =
        serde_json::from_str(&fixture("from_source_system.lineage.json"))
            .expect("evidence must be valid JSON");
    let agg = &evidence["link3_build_item"];
    assert_eq!(
        agg["constant_shape"].as_str(),
        Some("trust_ir::Constant::Aggregate([Constant::Int(k)])"),
        "the aggregate shape must be recorded as MEASURED, not described"
    );
    assert_eq!(agg["arity"].as_u64(), Some(1));
    assert_eq!(agg["nesting_depth"].as_u64(), Some(1));
    assert_eq!(agg["element_kind"].as_str(), Some("Int"));
    assert_eq!(
        agg["irconst_constructors_before"].as_u64(),
        Some(7),
        "the census this build item moved"
    );
    assert_eq!(agg["irconst_constructors_after"].as_u64(), Some(10));
    let sibling = agg["also_emitted_by"]
        .as_str()
        .expect("the other body with this shape must be named");
    assert!(
        sibling.contains("ExprPathStep"),
        "rank 3 shares the shape and is the second body this build item unblocks: {sibling}"
    );
}
