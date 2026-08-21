// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the zext chain: `cert::builder::state::NodeId::index`.**
//!
//! ```text
//! bb0(%0: struct.323):
//!     %1 = extractfield u32 %0, 0
//!     %2 = zext u32 %1 to usize
//!     ret %2
//! ```
//!
//! ## THE `usize` DECISION lives HERE, and nowhere else
//!
//! The ninth chain left `usize` deliberately UNRESOLVED: `norm_emitted_ty`
//! returns the loud `?usize` token and `assert_lanes` refuses a `?`-prefixed
//! cast type on either side, precisely so the first `zext u32 -> usize` chain
//! would have to decide the width visibly instead of inheriting one. This
//! file is that decision, in three honest steps: the RAW parse is asserted to
//! carry exactly `?usize` (an artifact that ever prints `u64` fails FIRST);
//! the token is then resolved to `uint64` — a TARGET assumption, 64-bit
//! `usize`, anchored to the recorded `aarch64-apple-darwin` producer pinned
//! in `node_id_index.lineage.json`; and `assert_lanes` compares the resolved
//! side against the registered module, whose `ir_ni_tusize` is
//! `IRTy.uint_ ir_d64` — the same decision, made once, in one named alias.
//! The PARSER keeps refusing `?usize`, so the unchained twin body
//! (`env::persistent_ext::ExtensionIdx::index`, `struct.848`) still fails
//! closed until its own lane makes its own decision.
//!
//! ## Evidence honesty
//!
//! From the 2026-08-20 dump (trustc `10130575c`, three byte-identical clean
//! builds of the unsealed local stage1): verdict `agreed` (4 canonical lines),
//! `markers_exact` true over 2 REAL marker lines, codegen flip event with
//! lineage == coverage row. **The producer's interpreter differential is
//! NOT-RUN on this body — 0 samples** — pinned below as recorded; nothing
//! here or in the spec module claims interpreter agreement.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst.cast`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_ni_module` is hand-transcribed: an incorrect transcription
//! FAILS here; a correct one is not automatic. Nothing says
//! `ir_wrap ir_d64 (ir_wrap ir_d32 n)` is Rust's `as usize` — see the module
//! doc of `spec/core_spec/eval_ir_node_id_index.rs`.

use super::*;

/// The one resolution this chain owns: the raw emitted cast destination must
/// be EXACTLY `?usize`, and only then does it become `uint64`.
fn resolve_usize(emitted: &mut Cfg, who: &str) {
    let tys = emitted
        .cast_tys
        .get_mut(&0)
        .unwrap_or_else(|| panic!("{who}: the body's one cast must be in the cast type lane"));
    assert_eq!(tys.len(), 1, "{who}: one cast carries the usize slot");
    assert_eq!(tys[0].0, "zext");
    assert_eq!(tys[0].1, 2);
    assert_eq!(tys[0].2, "uint32");
    assert_eq!(
        tys[0].3, "?usize",
        "{who}: the RAW parse must carry the loud `?usize` token — an artifact that prints a \
         resolved width here is not the recorded body, and resolving anything else would turn \
         the decision into a default"
    );
    // THE DECISION: usize = 64 bits, matching `ir_ni_tusize := IRTy.uint_
    // ir_d64` on the spec side and the aarch64-apple-darwin producer pinned in
    // the lineage fixture (asserted in the evidence gate below).
    tys[0].3 = "uint64".to_string();
}

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn node_id_index_proved_module_matches_the_emitted_artifact() {
    let text = fixture("node_id_index.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @cert::builder::state::NodeId::index("),
        "the fixture must be NodeId::index itself"
    );
    let mut emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_node_id_index.rs", "const SRC_IR_NI_B0"),
        "def ir_ni_b0",
    );

    // COVERAGE DENOMINATOR, before the resolution touches anything.
    assert_eq!(
        emitted.blocks,
        vec![0u32],
        "ONE block, bb0; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.extracts,
        BTreeMap::from([(0, vec![(1u32, 0u32, 0u32)])]),
        "exactly one field read: field 0 of %0 into %1: {:?}",
        emitted.extracts
    );
    assert_eq!(
        emitted.extract_tys,
        BTreeMap::from([(0, vec![(1u32, "uint32".to_string())])]),
        "…at u32, the field's own type: {:?}",
        emitted.extract_tys
    );
    assert_eq!(
        emitted.casts,
        BTreeMap::from([(0, vec![("zext".to_string(), 2, 1)])]),
        "exactly one cast, `zext` of %1 into %2: {:?}",
        emitted.casts
    );
    resolve_usize(&mut emitted, "node_id_index");
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![2u32])]),
        "the body returns %2 — the EXTENDED value, not %1 the raw field: {:?}",
        emitted.rets
    );
    assert_eq!(
        emitted.order,
        BTreeMap::from([(
            0,
            vec![
                ("extractfield".to_string(), vec![1u32]),
                ("cast".to_string(), vec![2u32]),
                ("ret".to_string(), vec![]),
            ]
        )]),
        "three instructions, in this order and no other: {:?}",
        emitted.order
    );
    assert!(
        emitted.icmps.is_empty()
            && emitted.binops.is_empty()
            && emitted.binop_tys.is_empty()
            && emitted.icmp_tys.is_empty()
            && emitted.condbrs.is_empty()
            && emitted.cases.is_empty()
            && emitted.branches.is_empty()
            && emitted.consts.is_empty()
            && emitted.int_consts.is_empty()
            && emitted.agg_consts.is_empty()
            && emitted.loads.is_empty()
            && emitted.load_tys.is_empty()
            && emitted.geps.is_empty()
            && emitted.insertfields.is_empty()
            && emitted.stores.is_empty()
            && emitted.asserts.is_empty()
            && emitted.param_blocks.is_empty()
            && emitted.const_tys.is_empty()
            && emitted.edge_args.is_empty()
            && emitted.block_params.is_empty(),
        "this body compares nothing, branches nowhere, materializes no constant, loads nothing, \
         WRITES nothing (the new insertfield/store lanes are empty on it) and asserts nothing: \
         one field read, one cast, one return"
    );
    assert_eq!(emitted.default, u32::MAX, "no switch");
    assert_eq!(emitted.switch_on, u32::MAX, "…and therefore no scrutinee");

    // ONE parameter, self by value — and the struct id is the ONLY thing
    // separating this body from its unchained twin (ExtensionIdx::index,
    // struct.848), so it is pinned in the text.
    assert!(
        text.contains("bb0(%0: struct.323):"),
        "one by-value parameter of type struct.323 — NodeId, not ExtensionIdx"
    );
    let func = clean_block_sources("eval_ir_node_id_index.rs", "const SRC_IR_NI_FUNC");
    assert!(
        func.contains("IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0"),
        "the registered IRFunc must bind the same single parameter id: {func}"
    );
    let tself = clean_block_sources("eval_ir_node_id_index.rs", "const SRC_IR_NI_TSELF");
    assert!(
        tself.contains("IRTy.struct_ 323"),
        "the registered receiver type must carry the SAME struct id the artifact prints: {tself}"
    );

    assert_eq!(emitted.blocks, clean.blocks);
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_node_id_index.rs", "const SRC_IR_NI_FUNC"),
        "node_id_index",
    );
    assert_lanes(&emitted, &clean, "node_id_index");
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call @func."),
        "the body must make no calls — that is what makes its reachable closure bodyful"
    );
}

/// **Artifact-side drifts: each lane is load-bearing by measurement.** Every
/// drifted transcription below leaves the OTHER lanes bit-identical, so the
/// lane that catches it is the only thing standing between the theorem and a
/// body the compiler did not emit.
#[test]
fn node_id_index_the_lanes_catch_a_drifted_artifact() {
    let raw = parse_emitted(&fixture("node_id_index.trust-ir.txt"));
    let head = "rustcc fn @x(functy.97) {\nbb0(%0: struct.323):\n";
    let body = |mid: &str| {
        parse_emitted(&format!(
            "{head}    %1 = extractfield u32 %0, 0\n{mid}    ret %2\n}}\n"
        ))
    };

    // Drift 0: the cast DELETED. Before the ninth chain's lanes this was
    // invisible; on THIS body it also breaks `order`, which is asserted so the
    // two catches stay distinct.
    let no_cast = parse_emitted(&format!(
        "{head}    %1 = extractfield u32 %0, 0\n    ret %2\n}}\n"
    ));
    assert_eq!(raw.extracts, no_cast.extracts);
    assert_eq!(raw.rets, no_cast.rets, "the RET lane cannot see it");
    assert_ne!(raw.casts, no_cast.casts, "…and the CAST lane must");
    assert_ne!(raw.order, no_cast.order, "…and the ORDER lane too");

    // Drift 1: sext instead of zext — identical below the sign bit, different
    // on the whole top half of the u32 range.
    let as_sext = body("    %2 = sext u32 %1 to usize\n");
    assert_eq!(raw.rets, as_sext.rets);
    assert_eq!(raw.extracts, as_sext.extracts);
    assert_eq!(
        raw.order, as_sext.order,
        "the ORDER lane sees only the class `cast`, which is why the opcode token lane matters"
    );
    assert_ne!(raw.casts, as_sext.casts, "the CAST lane sees the opcode");

    // Drift 2: a RESOLVED destination in the artifact. The raw-token assert in
    // `resolve_usize` refuses it before any comparison — here it is shown to
    // be a real difference, not a spelling.
    let as_u64 = body("    %2 = zext u32 %1 to u64\n");
    assert_eq!(raw.casts, as_u64.casts, "the operand lane cannot see it");
    assert_ne!(
        raw.cast_tys, as_u64.cast_tys,
        "`?usize` and `uint64` differ in the raw parse — the artifact prints `usize` and only \
         this gate may resolve it"
    );

    // Drift 3: the SOURCE width.
    let src_u8 = body("    %2 = zext u8 %1 to usize\n");
    assert_eq!(raw.casts, src_u8.casts);
    assert_ne!(
        raw.cast_tys, src_u8.cast_tys,
        "the TYPE lane must see the source width: it is the canonicalizer"
    );

    // Drift 4: the OPERAND — casting the receiver aggregate instead of the
    // extracted field.
    let wrong_operand = body("    %2 = zext u32 %0 to usize\n");
    assert_eq!(raw.cast_tys, wrong_operand.cast_tys, "TYPE lane blind");
    assert_ne!(raw.casts, wrong_operand.casts, "…and the CAST lane must");

    // Drift 5: the FIELD INDEX — reading a field the struct does not have.
    let wrong_field = parse_emitted(&format!(
        "{head}    %1 = extractfield u32 %0, 1\n    %2 = zext u32 %1 to usize\n    ret %2\n}}\n"
    ));
    assert_eq!(raw.casts, wrong_field.casts);
    assert_eq!(raw.extract_tys, wrong_field.extract_tys);
    assert_ne!(raw.extracts, wrong_field.extracts, "EXTRACT lane sees it");

    // Drift 6: the extractfield TYPE.
    let field_u8 = parse_emitted(&format!(
        "{head}    %1 = extractfield u8 %0, 0\n    %2 = zext u32 %1 to usize\n    ret %2\n}}\n"
    ));
    assert_eq!(raw.extracts, field_u8.extracts, "operand lane blind");
    assert_ne!(raw.extract_tys, field_u8.extract_tys, "the TYPE lane must");

    // Drift 7: returning the raw field instead of the extension.
    let wrong_ret = parse_emitted(&format!(
        "{head}    %1 = extractfield u32 %0, 0\n    %2 = zext u32 %1 to usize\n    ret %1\n}}\n"
    ));
    assert_eq!(raw.casts, wrong_ret.casts);
    assert_ne!(raw.rets, wrong_ret.rets, "the RET lane must see [2] vs [1]");
}

/// **The other direction: perturb the CLEAN side.** The registered
/// `SRC_IR_NI_B0` source itself is mutated and parsed with the same reader the
/// gate uses; each mutation must break exactly the lane that owns it.
#[test]
fn node_id_index_the_lanes_catch_a_drifted_spec_module_too() {
    let text = fixture("node_id_index.trust-ir.txt");
    let mut emitted = parse_emitted(&text);
    resolve_usize(&mut emitted, "node_id_index (spec-drift control)");
    let src = clean_block_sources("eval_ir_node_id_index.rs", "const SRC_IR_NI_B0");
    let good = parse_clean(&src, "def ir_ni_b0");
    assert_eq!(
        emitted.casts, good.casts,
        "the unmutated registered module must agree, or the mutations below prove nothing"
    );
    assert_eq!(emitted.cast_tys, good.cast_tys);
    assert_eq!(emitted.extracts, good.extracts);
    assert_eq!(emitted.rets, good.rets);

    // The registered module at a 32-bit usize — the OTHER answer the decision
    // could have given, and the one the recorded 64-bit producer refutes.
    let at_u32 = parse_clean(&src.replace("ir_ni_tusize", "ir_br_tu32"), "def ir_ni_b0");
    assert_eq!(emitted.casts, at_u32.casts, "operand lane blind");
    assert_ne!(
        emitted.cast_tys, at_u32.cast_tys,
        "…and the TYPE lane must: uint64 vs uint32 destination"
    );

    // The registered module sign-extending.
    let as_sext = parse_clean(
        &src.replace("IRCastOp.zext", "IRCastOp.sext"),
        "def ir_ni_b0",
    );
    assert_ne!(
        emitted.casts, as_sext.casts,
        "the CAST lane must reject a spec module proved about sign extension"
    );
    assert_eq!(emitted.rets, as_sext.rets);

    // The registered module casting the receiver instead of the field.
    let wrong_operand = parse_clean(
        &src.replace("ir_ni_tusize ir_d1", "ir_ni_tusize ir_d0"),
        "def ir_ni_b0",
    );
    assert_eq!(emitted.cast_tys, wrong_operand.cast_tys);
    assert_ne!(emitted.casts, wrong_operand.casts);

    // The registered module reading field 1.
    let wrong_field = parse_clean(
        &src.replace(
            "ir_br_tu32 ir_d0 ir_d0) ir_d1",
            "ir_br_tu32 ir_d0 ir_d1) ir_d1",
        ),
        "def ir_ni_b0",
    );
    assert_ne!(emitted.extracts, wrong_field.extracts);

    // The registered module returning the raw field.
    let wrong_ret = parse_clean(
        &src.replace("IRInst.ret (ir_nl1 ir_d2)", "IRInst.ret (ir_nl1 ir_d1)"),
        "def ir_ni_b0",
    );
    assert_eq!(emitted.casts, wrong_ret.casts);
    assert_ne!(emitted.rets, wrong_ret.rets);
}

/// **The refusal survives this chain.** The twin body's shape still parses to
/// `?usize` and `assert_lanes` still refuses it — the decision made here is
/// scoped to this gate, not smuggled into the shared parser.
#[test]
fn node_id_index_the_parser_still_refuses_an_unresolved_usize() {
    let twin = parse_emitted(
        "rustcc fn @x(functy.97) {\nbb0(%0: struct.848):\n    %1 = extractfield u32 %0, 0\n    \
         %2 = zext u32 %1 to usize\n    ret %2\n}\n",
    );
    let tys = twin.cast_tys.get(&0).expect("the cast must be in the lane");
    assert_eq!(
        tys[0].3, "?usize",
        "the shared parser must keep returning the loud token; only a chain's own gate may \
         resolve it, against its own recorded producer"
    );
    // …and the spec side of the decision is exactly one 64-bit alias.
    let spec = spec_source("eval_ir_node_id_index.rs");
    assert!(
        spec.contains("def ir_ni_tusize : IRTy := IRTy.uint_ ir_d64"),
        "the registered usize alias must be the 64-bit decision this gate resolves to"
    );
}

/// **The A0 evidence, pinned at the strength it was measured — including the
/// NOT-RUN interpreter.** This body's differential evidence is agreed +
/// markers_exact + flip-lineage equality; the producer's interpreter sampled
/// it ZERO times, and that is asserted as recorded so nothing downstream can
/// quietly upgrade it to the float cohort's agreed/64.
#[test]
fn node_id_index_a0_evidence_is_recorded_at_the_strength_it_was_measured() {
    let j = fixture("node_id_index.lineage.json");
    let ev: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0 evidence must be valid JSON");
    assert_eq!(
        ev["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        ev["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2"),
        "a digest and its domain travel together or neither means anything"
    );

    let body = &ev["body"];
    assert_eq!(
        body["def_path"].as_str(),
        Some("cert::builder::state::NodeId::index")
    );
    assert_eq!(body["instr_count"].as_u64(), Some(3));
    assert_eq!(body["lowered"].as_bool(), Some(true));
    assert_eq!(body["spliced"].as_bool(), Some(true));
    let unsup = body["unsupported"].as_array().map(Vec::is_empty);
    assert_eq!(unsup, Some(true));
    assert_eq!(body["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        body["derived_mir"]["detail"].as_str(),
        Some("4 canonical line(s) identical")
    );
    assert_eq!(body["derived_mir"]["markers_exact"].as_bool(), Some(true));
    assert_eq!(
        body["derived_mir"]["markers_detail"].as_str(),
        Some("2 marker line(s) identical"),
        "markers_exact is vacuous on most rows; here it compares TWO real marker lines"
    );

    // THE INTERPRETER VERDICT, AS RECORDED: NOT-RUN, ZERO SAMPLES. A prefix
    // test on the note (the ninth chain's battery caught a `contains` here).
    assert_eq!(body["interpreter"]["verdict"].as_str(), Some("not-run"));
    assert_eq!(body["interpreter"]["samples"].as_u64(), Some(0));
    assert!(
        body["interpreter"]["note"]
            .as_str()
            .is_some_and(|n| n.starts_with("NOT-RUN.")),
        "the note must state the absence up front; this chain's evidence claims NO interpreter \
         agreement and nothing may quote one"
    );

    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            body["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(body["flip_kind"].as_str(), Some("codegen"));

    // A6's join: flag AND digests, because the two have disagreed before.
    assert_eq!(body["flip_lineage_equals_coverage"].as_bool(), Some(true));
    let coverage = body["coverage_row_lineage"]
        .as_str()
        .expect("the coverage-row lineage must be recorded");
    let flip = body["flip_event_lineage"]
        .as_str()
        .expect("the flip-event lineage must be recorded");
    assert!(coverage.starts_with("sha256:") && coverage.len() > "sha256:".len());
    assert_eq!(flip.trim_end_matches(','), coverage);
    assert_eq!(Some(coverage), ev["lineage"].as_str());
    assert_eq!(body["def_index"].as_u64(), ev["def_index"].as_u64());

    // Provenance at recorded strength: three byte-identical clean builds of
    // the UNSEALED local stage1 — stronger than one build, weaker than the
    // sealed-driver protocol — tied to the float cohort by the same-dump
    // control.
    assert!(
        ev["build"]["provenance_strength"]
            .as_str()
            .is_some_and(|s| s.contains("THREE clean non-incremental builds")
                && s.contains("unsealed local stage1")),
        "provenance must be carried at the strength it was measured"
    );
    assert!(
        ev["build"]["control"]
            .as_str()
            .is_some_and(|s| s.contains("float_div.trust-ir.txt")),
        "the one cross-check: the same dump reproduces the pinned eighth-chain artifact"
    );
    assert_eq!(
        ev["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true)
    );
    let r1 = ev["reproduction"]["sha256_run1"].as_str();
    assert!(r1.is_some(), "a recorded dump digest");
    assert_eq!(ev["reproduction"]["sha256_run2"].as_str(), r1);
    assert_eq!(ev["reproduction"]["sha256_run3"].as_str(), r1);

    // THE usize ANCHOR: the producer this evidence was measured on is a
    // 64-bit target, which is what licenses `ir_ni_tusize := uint_ 64` and
    // this gate's resolution of `?usize` to `uint64`.
    assert!(
        ev["build"]["trustc"]
            .as_str()
            .is_some_and(|s| s.contains("aarch64-apple-darwin")),
        "the recorded producer must be the 64-bit target the usize decision is anchored to"
    );
    assert!(
        ev["head_measurement"]["record"]
            .as_str()
            .is_some_and(|s| s.starts_with("data/crystal_fixture_freshness_")),
        "the fixture must point at a dated revalidation record"
    );
    assert_eq!(
        ev["head_measurement"]["at_head_lineage"].as_str(),
        Some(coverage),
        "the fixture and its revalidation row must name the same artifact"
    );
}
