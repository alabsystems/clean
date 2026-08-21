// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the WITH chain — `flat::types::FlatFlags::with`, the
//! first chained body that BUILDS its returned aggregate.**
//!
//! ```text
//! bb0(%0: struct.1017, %1: struct.1017):
//!     %2 = extractfield u8 %0, 0
//!     %3 = extractfield u8 %1, 0
//!     %4 = or u8 %2, %3
//!     %5 = const struct.1017 { 0 }
//!     %6 = insertfield struct.1017 %5, 0, %4
//!     ret %6
//! }
//! ```
//!
//! The sibling of the chained `FlatFlags::contains` — same two-parameter
//! struct.1017 signature, same two field reads — with the `icmp` half replaced
//! by a WRITE half. That half is what this gate is about: `or`, an aggregate
//! `const` at a STRUCT type, and `insertfield` were each in no chained body
//! before this one, and the `insertfields` lane this file exercises landed in
//! `emitted_cfg.rs` AHEAD of the chain (2026-08-20), with its discrimination
//! proofs in `lane_matrix_writes.rs`. The perturbation batteries below drive
//! the lane in both directions on the REGISTERED transcription rather than on
//! the test-local candidate that file used.
//!
//! ## The evidence, at the strength it was measured — and no higher
//!
//! From the coherent 2026-08-20 whole-crate dump (irdump2, trustc `10130575c`),
//! three clean non-incremental builds with a byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("5 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 6 REAL marker lines
//! interpreter differential   NOT-RUN (0 samples)
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! flip event                 codegen seam, flip lineage == coverage lineage
//! ```
//!
//! **The interpreter row is a boundary, not a blemish to gloss:** unlike the
//! float closures (agreed/64), the producer's interpreter differential sampled
//! this body ZERO times. The chain's evidence is agreed + markers_exact +
//! flip-lineage equality + the kernel-executed witnesses in
//! `spec/core_spec/eval_ir_flat_flags_with.rs` — nothing here or there claims
//! interpreter agreement, and the evidence test below pins the NOT-RUN record
//! so a later dump cannot silently upgrade the claim without moving the
//! fixture.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_fw_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn flat_flags_with_proved_module_matches_the_emitted_artifact() {
    let text = fixture("flat_flags_with.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @flat::types::FlatFlags::with("),
        "the fixture must be the with body itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_flat_flags_with.rs", "const SRC_IR_FW_B"),
        "def ir_fw_b",
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
        emitted.cases.is_empty() && emitted.default == u32::MAX && emitted.switch_on == u32::MAX,
        "no switch at all: {:?} / {} / {}",
        emitted.cases,
        emitted.default,
        emitted.switch_on
    );
    assert!(
        emitted.branches.is_empty()
            && emitted.param_blocks.is_empty()
            && emitted.condbrs.is_empty(),
        "straight line: no branch, no join block"
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(2, 0, 0), (3, 1, 0)])]),
        "TWO field reads in emission order: self.0 into %2 and other.0 into %3 — one each, where \
         the sibling contains body reads other.0 twice"
    );
    assert_eq!(
        emitted.extract_tys,
        BTreeMap::from([(0, vec![(2, "uint8".to_string()), (3, "uint8".to_string())])]),
        "…both at u8"
    );
    assert_eq!(
        emitted.binops,
        BTreeMap::from([(0, vec![("or".to_string(), 4, 2, 3)])]),
        "one bitwise OR of the two field reads, binding %4 — the operator that distinguishes this \
         body from its sibling's `and`"
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("or".to_string(), 4, "uint8".to_string())])]),
        "…at width 8"
    );
    assert_eq!(
        emitted.agg_consts,
        BTreeMap::from([(0, vec![(5, 0)])]),
        "the TEMPLATE: one aggregate constant `const struct.1017 {{ 0 }}` binding %5. The sibling \
         chain materializes NO constant; this one materializes exactly one and then writes into it"
    );
    assert_eq!(
        emitted.const_tys,
        BTreeMap::from([(0, vec![(5, "struct1017".to_string())])]),
        "…at the STRUCT type, which routes it through ir_const_agg_eval rather than \
         ir_const_int_eval"
    );
    assert_eq!(
        emitted.insertfields,
        BTreeMap::from([(0, vec![(6, "struct1017".to_string(), 5, 0, 4)])]),
        "THE WRITE, every slot: result %6, type struct.1017, source aggregate %5 (the template — \
         not %0, not %1), field index 0, inserted value %4 (the OR — not either field read)"
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![6u32])]),
        "the body returns %6 — the WRITTEN aggregate, not the template %5 and not the OR %4: {:?}",
        emitted.rets
    );
    assert!(
        emitted.consts.is_empty() && emitted.int_consts.is_empty(),
        "no bool and no scalar-int constant: the one constant is the aggregate template"
    );
    assert!(
        emitted.loads.is_empty() && emitted.stores.is_empty() && emitted.geps.is_empty(),
        "both arguments arrive BY VALUE and the result leaves by value: no memory instruction at \
         all, so the heap-free representation premise is the honest one. Found loads {:?} stores \
         {:?} geps {:?}",
        emitted.loads,
        emitted.stores,
        emitted.geps
    );
    assert!(
        emitted.icmps.is_empty() && emitted.casts.is_empty() && emitted.asserts.is_empty(),
        "no comparison, no cast, no panic arm"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against
    // the registered `IRFunc`.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_flat_flags_with.rs", "const SRC_IR_FW_FUNC"),
        "flat_flags_with",
    );
    assert_lanes(&emitted, &clean, "flat_flags_with");
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

/// **The A0/A6 evidence, pinned at the strength it was measured — including
/// the row that is WEAKER than the floats': the interpreter differential is
/// NOT-RUN, 0 samples, and this test fails if the fixture ever claims more.**
#[test]
fn flat_flags_with_a0_evidence_is_recorded_at_the_strength_it_was_measured() {
    let j = fixture("flat_flags_with.lineage.json");
    let ev: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0 evidence must be valid JSON");
    assert_eq!(
        ev["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert!(
        !j.contains("fwprobe") && !j.contains("flagsprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );

    let body = &ev["body"];
    assert_eq!(
        body["def_path"].as_str(),
        Some("flat::types::FlatFlags::with")
    );
    assert_eq!(body["instr_count"].as_u64(), Some(6));

    // A0, criterion by criterion — the nested-body shape the 2026-08-20 dump
    // records, not the flat shape `assert_a0_a6` reads.
    assert_eq!(body["lowered"].as_bool(), Some(true));
    assert_eq!(body["spliced"].as_bool(), Some(true));
    assert_eq!(
        body["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(body["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(body["derived_mir"]["markers_exact"].as_bool(), Some(true));
    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            body["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(body["flip_kind"].as_str(), Some("codegen"));

    // THE NOT-RUN ROW. This is the honest difference from the float cohort and
    // it is pinned as a measurement, in both directions: the verdict must be
    // not-run AND the sample count must be zero, so neither a silent upgrade
    // ("agreed" with 0 samples) nor a silent claim (samples without a rerun)
    // can pass. A later dump that actually runs the differential must move the
    // fixture through this test.
    assert_eq!(
        body["interpreter"]["verdict"].as_str(),
        Some("not-run"),
        "the producer's interpreter differential did NOT run on this body; the fixture must say \
         so, and nothing in this chain may claim interpreter agreement"
    );
    assert_eq!(body["interpreter"]["samples"].as_u64(), Some(0));
    assert!(
        body["interpreter"]["note"]
            .as_str()
            .is_some_and(|n| n.contains("NOT-RUN") && n.contains("nothing may claim")),
        "the note must state the boundary in prose a reader of the fixture alone will see"
    );

    // A6's join, as recorded: flag AND digests, top level AND body block.
    assert_eq!(
        ev["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2"),
        "a digest and its domain travel together or neither means anything"
    );
    assert_eq!(body["flip_lineage_equals_coverage"].as_bool(), Some(true));
    let coverage = body["coverage_row_lineage"]
        .as_str()
        .expect("the coverage-row lineage must be recorded");
    let flip = body["flip_event_lineage"]
        .as_str()
        .expect("the flip-event lineage must be recorded");
    assert!(coverage.starts_with("sha256:") && coverage.len() > "sha256:".len());
    assert_eq!(
        flip.trim_end_matches(','),
        coverage,
        "the flip-event and coverage-row digests must be the same characters"
    );
    assert_eq!(
        Some(coverage),
        ev["lineage"].as_str(),
        "the lineage this chain is about is recorded once at the top level and mirrored in the \
         body block"
    );
    assert_eq!(
        body["def_index"].as_u64(),
        ev["def_index"].as_u64(),
        "the body block and the top level must record the same def_index (a per-run key, pinned \
         for internal consistency only — joins across runs go by def_path + lineage)"
    );

    // The provenance and the reproduction, at their recorded strength: three
    // byte-identical clean builds of an UNSEALED local stage1, with the
    // float_div byte-for-byte control tying the producer to the lane's series.
    assert!(
        ev["build"]["provenance_strength"]
            .as_str()
            .is_some_and(|s| s.contains("THREE clean non-incremental builds")
                && s.contains("unsealed local stage1")),
        "the provenance must be carried at the strength it was measured — stronger than one \
         build, weaker than the sealed-driver protocol, and the text must say so"
    );
    assert!(
        ev["build"]["control"]
            .as_str()
            .is_some_and(|s| s.contains("float_div.trust-ir.txt")),
        "the control: the same dump reproduces the pinned eighth-chain artifact byte-for-byte"
    );
    assert_eq!(
        ev["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true),
        "three clean builds must reproduce the digest, or `lineage` is not a measurement"
    );
    let r1 = ev["reproduction"]["sha256_run1"].as_str();
    assert!(r1.is_some_and(|s| !s.is_empty()));
    assert_eq!(r1, ev["reproduction"]["sha256_run2"].as_str());
    assert_eq!(r1, ev["reproduction"]["sha256_run3"].as_str());
    assert_eq!(
        ev["head_measurement"]["at_head_lineage"].as_str(),
        Some(coverage),
        "the fixture was cut from the dump the freshness record compares against; its row there \
         must read identical"
    );
}

/// **The non-vacuity of `markers_exact`, recorded as a number.**
#[test]
fn flat_flags_with_markers_exact_is_not_vacuous() {
    let ev: serde_json::Value = serde_json::from_str(&fixture("flat_flags_with.lineage.json"))
        .expect("evidence must be valid JSON");
    let detail = ev["body"]["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "6 marker line(s) identical",
        "the marker sequence is SIX lines long and equal line for line; if this becomes \
         `0 marker line(s) identical` then markers_exact has gone vacuous here too and the \
         chain's distinguishing claim is false"
    );
    assert!(!detail.starts_with("0 "));
    assert_eq!(
        ev["body"]["derived_mir"]["detail"].as_str(),
        Some("5 canonical line(s) identical")
    );
}

/// **The write lane is load-bearing on THIS body's registered transcription —
/// the artifact direction.** Each drifted emission differs from the fixture in
/// exactly the lane that owns the drift, while every other lane compares
/// equal — so no pre-existing lane could have caught it.
#[test]
fn flat_flags_with_the_write_lane_catches_what_every_old_lane_misses() {
    let text = fixture("flat_flags_with.trust-ir.txt");
    let emitted = parse_emitted(&text);

    let assert_only_insertfields_differ = |drifted: &str, what: &str| {
        let d = parse_emitted(drifted);
        assert_eq!(emitted.extracts, d.extracts, "{what}: extracts blind");
        assert_eq!(emitted.binops, d.binops, "{what}: binops blind");
        assert_eq!(emitted.binop_tys, d.binop_tys, "{what}: binop_tys blind");
        assert_eq!(emitted.agg_consts, d.agg_consts, "{what}: agg_consts blind");
        assert_eq!(emitted.const_tys, d.const_tys, "{what}: const_tys blind");
        assert_eq!(emitted.rets, d.rets, "{what}: rets blind");
        assert_eq!(
            emitted.order, d.order,
            "{what}: order blind (same class, same result)"
        );
        assert_ne!(
            emitted.insertfields, d.insertfields,
            "{what}: …and the INSERTFIELD lane must see it"
        );
    };

    // Drift 1: writing field 1 instead of field 0 — a different field of the
    // same struct, and the exact scenario the lane's doc names.
    assert_only_insertfields_differ(
        &text.replace(
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %5, 1, %4",
        ),
        "field index 0 -> 1",
    );
    // Drift 2: inserting a field READ instead of the OR — returns `other`
    // re-wrapped rather than the union.
    assert_only_insertfields_differ(
        &text.replace(
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %5, 0, %3",
        ),
        "inserted value %4 -> %3",
    );
    // Drift 3: writing into the first ARGUMENT instead of the fresh template —
    // same answer at slot 0, but a spine the template did not donate.
    assert_only_insertfields_differ(
        &text.replace(
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %0, 0, %4",
        ),
        "source aggregate %5 -> %0",
    );
    // Drift 4: the write at a type the artifact does not name.
    assert_only_insertfields_differ(
        &text.replace(
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.999 %5, 0, %4",
        ),
        "insertfield type struct.1017 -> struct.999",
    );

    // Drift 5: the SIBLING operator. Caught by the pre-existing binop lanes —
    // named so the expected catcher is recorded, and the write lane is blind,
    // which is why they are separate lanes.
    let as_and = parse_emitted(&text.replace("or u8 %2, %3", "and u8 %2, %3"));
    assert_ne!(emitted.binops, as_and.binops);
    assert_ne!(emitted.binop_tys, as_and.binop_tys);
    assert_eq!(emitted.insertfields, as_and.insertfields);

    // Drift 6: a different template value. Caught by agg_consts alone.
    let tpl_one =
        parse_emitted(&text.replace("const struct.1017 { 0 }", "const struct.1017 { 1 }"));
    assert_ne!(emitted.agg_consts, tpl_one.agg_consts);
    assert_eq!(emitted.insertfields, tpl_one.insertfields);
    assert_eq!(emitted.const_tys, tpl_one.const_tys);

    // Drift 7: returning the untouched template. Caught by rets alone.
    let ret_tpl = parse_emitted(&text.replace("ret %6", "ret %5"));
    assert_ne!(emitted.rets, ret_tpl.rets);
    assert_eq!(emitted.insertfields, ret_tpl.insertfields);

    // Drift 8: hoisting the write above the template that feeds it. Every
    // per-kind lane is bit-identical; only the program-order lane can see it.
    let good = "rustcc fn @x(functy.489) {\nbb0(%0: struct.1017, %1: struct.1017):\n    %2 = \
                extractfield u8 %0, 0\n    %3 = extractfield u8 %1, 0\n    %4 = or u8 %2, %3\n    \
                %5 = const struct.1017 { 0 }\n    %6 = insertfield struct.1017 %5, 0, %4\n    ret \
                %6\n}\n";
    let hoisted = "rustcc fn @x(functy.489) {\nbb0(%0: struct.1017, %1: struct.1017):\n    %2 = \
                   extractfield u8 %0, 0\n    %3 = extractfield u8 %1, 0\n    %4 = or u8 %2, \
                   %3\n    %6 = insertfield struct.1017 %5, 0, %4\n    %5 = const struct.1017 { 0 \
                   }\n    ret %6\n}\n";
    let (g, h) = (parse_emitted(good), parse_emitted(hoisted));
    assert_eq!(
        g.insertfields, h.insertfields,
        "the write lane cannot see it"
    );
    assert_eq!(g.agg_consts, h.agg_consts, "nor the constant lanes");
    assert_eq!(g.rets, h.rets);
    assert_ne!(
        g.order, h.order,
        "…and the ORDER lane must: the write reads a binding that does \
                                  not exist yet"
    );
}

/// **The other direction: perturb the REGISTERED spec module.** Mutations are
/// applied to the registered `SRC_IR_FW_B0` source itself, parsed with the same
/// reader the gate uses, and each must break exactly the lane that owns it.
#[test]
fn flat_flags_with_the_lanes_catch_a_drifted_spec_module_too() {
    let emitted = parse_emitted(&fixture("flat_flags_with.trust-ir.txt"));
    let src = clean_block_sources("eval_ir_flat_flags_with.rs", "const SRC_IR_FW_B");
    let good = parse_clean(&src, "def ir_fw_b");
    assert_eq!(
        emitted.insertfields, good.insertfields,
        "the unmutated registered module must agree, or the mutations below prove nothing"
    );
    assert_eq!(emitted.binops, good.binops);
    assert_eq!(emitted.agg_consts, good.agg_consts);
    assert_eq!(emitted.rets, good.rets);
    assert_eq!(emitted.order, good.order);

    // The registered write at field 1.
    let field_one = parse_clean(
        &src.replace("ir_d5 ir_d0 ir_d4", "ir_d5 ir_d1 ir_d4"),
        "def ir_fw_b",
    );
    assert_eq!(
        emitted.binops, field_one.binops,
        "the BINOP lane cannot see it"
    );
    assert_eq!(
        emitted.agg_consts, field_one.agg_consts,
        "nor the constant lanes"
    );
    assert_eq!(emitted.order, field_one.order, "nor the order lane");
    assert_ne!(
        emitted.insertfields, field_one.insertfields,
        "…and the INSERTFIELD lane must: field 0 vs field 1"
    );

    // The registered write into the first argument instead of the template.
    let into_arg = parse_clean(
        &src.replace(
            "ir_fc_tflags ir_d5 ir_d0 ir_d4",
            "ir_fc_tflags ir_d0 ir_d0 ir_d4",
        ),
        "def ir_fw_b",
    );
    assert_ne!(emitted.insertfields, into_arg.insertfields);
    assert_eq!(emitted.rets, into_arg.rets);

    // The registered write at the SCALAR type — the mutation the `?`-refusals
    // and the type slot exist for.
    let at_u8 = parse_clean(
        &src.replace(
            "IRInst.insertfield ir_fc_tflags",
            "IRInst.insertfield ir_tU8",
        ),
        "def ir_fw_b",
    );
    assert_ne!(
        emitted.insertfields, at_u8.insertfields,
        "struct1017 vs uint8 in the write's type slot"
    );

    // The registered module at the sibling's operator — the mutation that
    // would make A4 a theorem about `contains`' AND.
    let as_and = parse_clean(&src.replace("IRBinOp.or_", "IRBinOp.and_"), "def ir_fw_b");
    assert_ne!(
        emitted.binops, as_and.binops,
        "the BINOP lane must reject a spec module proved about the sibling's operator"
    );
    assert_eq!(emitted.insertfields, as_and.insertfields);

    // The registered template at value 1.
    let tpl_one = parse_clean(
        &src.replace("(ir_cvar ir_d0)", "(ir_cvar ir_d1)"),
        "def ir_fw_b",
    );
    assert_ne!(emitted.agg_consts, tpl_one.agg_consts);
    assert_eq!(emitted.insertfields, tpl_one.insertfields);

    // The registered module returning the untouched template.
    let ret_tpl = parse_clean(
        &src.replace("IRInst.ret (ir_nl1 ir_d6)", "IRInst.ret (ir_nl1 ir_d5)"),
        "def ir_fw_b",
    );
    assert_ne!(emitted.rets, ret_tpl.rets);
    assert_eq!(emitted.insertfields, ret_tpl.insertfields);
}
