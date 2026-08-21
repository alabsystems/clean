// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the FLOAT ADDITION chain:
//! `env::native_reducers_float::reduce_float_add::{closure#0}`.**
//!
//! ```text
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fadd f64 %1, %2
//!     ret %3
//! ```
//!
//! Structurally the eighth chain's body character for character except the
//! opcode token and the source column (`fadd` for `fdiv`, 210 for 222), so the
//! two lanes that body forced into `emitted_cfg.rs` are the two that matter
//! here as well:
//!
//! * **the binop's TYPE.** `ir_float_binop` reads the width off it and decides
//!   only binary64, so a module transcribed at `IRTy.float_ 32` returns the
//!   tagged `unmodelled` verdict where the artifact returns a value. Nothing
//!   but `binop_tys` can see it.
//! * **the RETURNED value id.** `ret %1` instead of `ret %3` returns the LEFT
//!   OPERAND instead of the sum, agrees with every other lane, and on a
//!   two-instruction body is the entire semantics. Only `rets` can see it.
//!
//! ## Why the operator token is worth more here than on any earlier float body
//!
//! `fadd` and `fdiv` are the same graph at DIFFERENT semantics, and since
//! 2026-08-16 the difference is not only which cells refuse: `ir_f64_add`'s
//! `fin`/`fin` cell is `super::eval_ir_float_fin`'s correctly-rounded sum where
//! `ir_f64_div`'s is `IROption.none`. A spec module transcribed at the wrong
//! opcode would therefore RETURN A VALUE where the artifact's operator refuses,
//! or the reverse. The pre-existing `binops` lane catches it, in both
//! directions, and this file executes that rather than asserting it.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. `ir_fa_module` is hand-transcribed:
//! this makes an incorrect transcription FAIL, it does not make a correct one
//! automatic. Nothing here says `ir_f64_add` is the hardware adder — see the
//! module docs of `spec/core_spec/eval_ir_float.rs`,
//! `spec/core_spec/eval_ir_float_fin.rs` and
//! `spec/core_spec/eval_ir_float_add.rs` for exactly what is and is not
//! claimed.
//!
//! And the A0/A6 evidence for this body is **weaker than the eighth chain's and
//! says so in its own file**: ONE build rather than the sealed driver's three,
//! no negative control, no reproduction stanza. The last test below pins it at
//! that strength — no lower and no higher — including the two respects in which
//! the eighth chain's census row for this same closure DISAGREES with it.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn float_add_proved_module_matches_the_emitted_artifact() {
    let text = fixture("float_add.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::native_reducers_float::reduce_float_add::{closure#0}("),
        "the fixture must be the reduce_float_add closure itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_float_add.rs", "const SRC_IR_FA_B"),
        "def ir_fa_b",
    );

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(
        emitted.blocks,
        vec![0u32],
        "ONE block, bb0; parser found {:?}",
        emitted.blocks
    );
    assert_eq!(
        emitted.binops,
        BTreeMap::from([(0, vec![("fadd".to_string(), 3, 1, 2)])]),
        "exactly one binop, `fadd %1, %2` into %3: {:?}",
        emitted.binops
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("fadd".to_string(), 3, "float64".to_string())])]),
        "…at BINARY64. This is the lane float arithmetic forced: {:?}",
        emitted.binop_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![3u32])]),
        "the body returns %3 — the SUM, not %1 the left operand: {:?}",
        emitted.rets
    );
    assert!(
        emitted.icmps.is_empty()
            && emitted.condbrs.is_empty()
            && emitted.cases.is_empty()
            && emitted.branches.is_empty()
            && emitted.consts.is_empty()
            && emitted.int_consts.is_empty()
            && emitted.agg_consts.is_empty()
            && emitted.loads.is_empty()
            && emitted.extracts.is_empty()
            && emitted.param_blocks.is_empty()
            && emitted.const_tys.is_empty()
            && emitted.edge_args.is_empty()
            && emitted.block_params.is_empty(),
        "this body compares nothing, branches nowhere, materializes no constant, reads no field \
         and loads nothing: it is one arithmetic instruction and a return"
    );
    assert_eq!(emitted.default, u32::MAX, "no switch");
    assert_eq!(
        emitted.switch_on,
        u32::MAX,
        "…and therefore no scrutinee: {}",
        emitted.switch_on
    );

    // The three parameters, read off the emitted entry-block signature. They are
    // not in `Cfg` — `parse_emitted` treats the entry block's parameter list as
    // the function signature — so they are asserted here against the text and
    // against the registered `IRFunc`, in both directions.
    assert!(
        text.contains("bb0(%0: ptr, %1: f64, %2: f64):"),
        "THREE parameters: the closure environment pointer and the two f64 operands"
    );
    // …and the FIRST one is never read. That is the artifact-side reason A4
    // quantifies over the environment pointer with no premise on it at all,
    // and it is a count rather than a reading: `%0` occurs once in the whole
    // body, in the parameter list. (`{closure#0}` in the header is `#0`, not
    // `%0`.) This body's fixture, unlike `float_div`'s, carries no
    // `proven-never-read opaque param` note from the producer, so the claim is
    // made here where it can be checked instead of inherited.
    assert_eq!(
        text.matches("%0").count(),
        1,
        "the closure environment pointer must be BOUND AND NEVER READ: {text}"
    );
    let func = clean_block_sources("eval_ir_float_add.rs", "const SRC_IR_FA_FUNC");
    assert!(
        func.contains("IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0"),
        "the registered IRFunc must bind the same three parameter ids in the same order: {func}"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
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
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}",
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
        "the JOIN blocks differ: emitted {:?} vs Clean {:?}",
        emitted.param_blocks, clean.param_blocks
    );
    // The FUNCTION signature: the emitted entry block's parameter list against the
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0`.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_float_add.rs", "const SRC_IR_FA_FUNC"),
        "float_add",
    );
    assert_lanes(&emitted, &clean, "float_add");
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

/// **The two lanes the eighth chain added are load-bearing here too — this is
/// the negative half.** It constructs the drifted ARTIFACT transcriptions and
/// checks that every pre-existing lane still compares equal on them, so the
/// lanes are load-bearing by measurement rather than by assertion.
#[test]
fn float_add_the_new_lanes_catch_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("float_add.trust-ir.txt"));

    // Drift 1: the same body at binary32.
    let at_f32 = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f32, %2: f32):\n    %3 = fadd f32 %1, %2\n \
         ret %3\n}\n",
    );
    assert_eq!(
        emitted.binops, at_f32.binops,
        "the BINOP lane cannot see it"
    );
    assert_eq!(emitted.rets, at_f32.rets, "the RET lane cannot see it");
    assert_eq!(emitted.blocks, at_f32.blocks);
    assert_ne!(
        emitted.binop_tys, at_f32.binop_tys,
        "…and the TYPE lane must: float64 vs float32"
    );

    // Drift 2: returning the left operand instead of the sum.
    let wrong_ret = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fadd f64 %1, %2\n \
         ret %1\n}\n",
    );
    assert_eq!(
        emitted.binops, wrong_ret.binops,
        "the BINOP lane cannot see it"
    );
    assert_eq!(
        emitted.binop_tys, wrong_ret.binop_tys,
        "the TYPE lane cannot see it either"
    );
    assert_eq!(emitted.blocks, wrong_ret.blocks);
    assert_eq!(emitted.consts, wrong_ret.consts);
    assert_eq!(emitted.branches, wrong_ret.branches);
    assert_ne!(
        emitted.rets, wrong_ret.rets,
        "…and the RET lane must: [3] vs [1]"
    );

    // Drift 3: the operator itself — the eighth chain's body, which is the same
    // graph at a DIFFERENT semantics (`fdiv`'s fin/fin cell is `IROption.none`
    // where `fadd`'s is the rounded sum). Caught by the pre-existing binop lane.
    let as_div = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fdiv f64 %1, %2\n \
         ret %3\n}\n",
    );
    assert_ne!(emitted.binops, as_div.binops);
    assert_ne!(emitted.binop_tys, as_div.binop_tys);
    assert_eq!(
        emitted.rets, as_div.rets,
        "the RET lane cannot see the operator, which is why it is a SEPARATE lane"
    );

    // Drift 4: exchanging the operands. Every witness this chain can execute
    // agrees on the pair it exchanges — `ir_fa_one_plus_two_answers` and
    // `ir_fa_two_plus_one_answers` both return 3.0, and nothing in this
    // repository proves `ir_f64_add` commutative in general — so execution is
    // NOT what gates the operand order here. The `binops` lane is, and it does
    // not need to know whether the difference is observable.
    let swapped = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fadd f64 %2, %1\n \
         ret %3\n}\n",
    );
    assert_ne!(
        emitted.binops, swapped.binops,
        "the BINOP lane carries (op, result, lhs, rhs) and must reject the swap"
    );
    assert_eq!(
        emitted.binop_tys, swapped.binop_tys,
        "the type lane cannot see an operand swap, which is why it is a SEPARATE lane and not a \
         replacement for the operand order"
    );
    assert_eq!(emitted.rets, swapped.rets, "nor can the ret lane");
}

/// **The other direction: perturb the CLEAN side.**
///
/// Every drift above is in the artifact. A gate that only ever mutated the
/// fixture would be blind to the failure mode this whole file exists for — the
/// registered spec module drifting away from a body that never moved. These
/// mutations are applied to the registered `SRC_IR_FA_B0` source itself, parsed
/// with the same reader the gate uses, and each must break exactly the lane
/// that owns it.
#[test]
fn float_add_the_lanes_catch_a_drifted_spec_module_too() {
    let emitted = parse_emitted(&fixture("float_add.trust-ir.txt"));
    let src = clean_block_sources("eval_ir_float_add.rs", "const SRC_IR_FA_B");
    let good = parse_clean(&src, "def ir_fa_b");
    assert_eq!(
        emitted.binops, good.binops,
        "the unmutated registered module must agree, or the mutations below prove nothing"
    );
    assert_eq!(emitted.binop_tys, good.binop_tys);
    assert_eq!(emitted.rets, good.rets);

    // The registered module at binary32.
    let at_f32 = parse_clean(
        &src.replace("ir_fa_tf64", "(IRTy.float_ 32)"),
        "def ir_fa_b",
    );
    assert_eq!(
        emitted.binops, at_f32.binops,
        "the BINOP lane cannot see it"
    );
    assert_eq!(emitted.rets, at_f32.rets, "the RET lane cannot see it");
    assert_ne!(
        emitted.binop_tys, at_f32.binop_tys,
        "…and the TYPE lane must: the Clean side resolves the alias to float32"
    );

    // The registered module returning the left operand.
    let wrong_ret = parse_clean(
        &src.replace("IRInst.ret (ir_nl1 ir_d3)", "IRInst.ret (ir_nl1 ir_d1)"),
        "def ir_fa_b",
    );
    assert_eq!(
        emitted.binop_tys, wrong_ret.binop_tys,
        "the TYPE lane cannot see it"
    );
    assert_eq!(emitted.binops, wrong_ret.binops, "nor can the BINOP lane");
    assert_ne!(
        emitted.rets, wrong_ret.rets,
        "…and the RET lane must: [3] vs [1]"
    );

    // The registered module at the eighth chain's operator — the mutation that
    // would make A4 a theorem about a function whose finite fragment refuses.
    let as_div = parse_clean(&src.replace("IRBinOp.fadd", "IRBinOp.fdiv"), "def ir_fa_b");
    assert_ne!(
        emitted.binops, as_div.binops,
        "the BINOP lane must reject a spec module proved about division"
    );
    assert_eq!(emitted.rets, as_div.rets);

    // The registered module with the operands exchanged.
    let swapped = parse_clean(
        &src.replace("ir_fa_tf64 ir_d1 ir_d2", "ir_fa_tf64 ir_d2 ir_d1"),
        "def ir_fa_b",
    );
    assert_ne!(
        emitted.binops, swapped.binops,
        "the BINOP lane must reject the swap on the Clean side too"
    );
    assert_eq!(emitted.binop_tys, swapped.binop_tys);
}

/// **The A0 evidence, pinned at the strength it was actually measured — which
/// is NOT the eighth chain's.**
///
/// `float_add.lineage.json` is not the shape `assert_a0_a6` reads and must not
/// be forced into it: it records ONE build via `scripts/trust_ir_build.sh
/// --print-only` instead of the sealed driver's three clean non-incremental
/// builds, it carries no negative control and no reproduction stanza, and it
/// records `flip_lineage_equals_coverage: true`. Every one of those is
/// asserted here as written, so a later re-pin under the sealed protocol has to
/// come through this test rather than around it.
#[test]
fn float_add_a0_evidence_is_recorded_at_the_strength_it_was_measured() {
    let j = fixture("float_add.lineage.json");
    let ev: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0 evidence must be valid JSON");
    assert_eq!(
        ev["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert!(
        !j.contains("faddprobe") && !j.contains("floatprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );

    let body = &ev["body"];
    assert_eq!(
        body["def_path"].as_str(),
        Some("env::native_reducers_float::reduce_float_add::{closure#0}")
    );
    assert_eq!(body["instr_count"].as_u64(), Some(2));

    // A0, criterion by criterion — the same list `assert_a0_a6` walks.
    assert_eq!(body["lowered"].as_bool(), Some(true));
    assert_eq!(body["spliced"].as_bool(), Some(true));
    assert_eq!(
        body["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(body["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(body["derived_mir"]["markers_exact"].as_bool(), Some(true));
    assert_eq!(
        body["derived_mir"]["markers_detail"].as_str(),
        Some("4 marker line(s) identical"),
        "markers_exact is vacuous on most rows; here it compares FOUR real marker lines, and if \
         this ever reads `0 marker line(s) identical` the flag has gone vacuous here too"
    );
    assert_eq!(body["interpreter"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(body["interpreter"]["samples"].as_u64(), Some(64));
    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            body["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(body["flip_kind"].as_str(), Some("codegen"));

    // A6's join, as recorded: the artifact the differential inspected must be
    // the artifact codegen compiled. Both the FLAG and the digests underneath
    // it are pinned, because reporting only one of them would be a claim rather
    // than a measurement — and the two have disagreed in this very file, whose
    // first version recorded the flag false while the digests matched, because
    // the flip log emits its lineage with a trailing separator that the string
    // comparison counted.
    assert_eq!(
        ev["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2"),
        "a digest and its domain travel together or neither means anything"
    );
    assert_eq!(
        body["flip_lineage_equals_coverage"].as_bool(),
        Some(true),
        "the flag must not regress; if it does, the digests below say whether the join actually \
         broke or the comparison did"
    );
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
        "the flip-event and coverage-row digests must be the same characters, trailing separator \
         or not"
    );

    // The provenance, stated as the file states it.
    assert!(
        ev["build"]["provenance_strength"]
            .as_str()
            .is_some_and(|s| s.contains("THREE clean non-incremental builds")
                && s.contains("unsealed local stage1")),
        "the provenance must be carried in the evidence at the strength it was measured — \
         three byte-identical clean builds of an UNSEALED local driver, which is stronger \
         than one build and weaker than the sealed-driver protocol, and the text must say so"
    );
    assert!(
        ev["build"]["control"]
            .as_str()
            .is_some_and(|s| s.contains("float_div.trust-ir.txt")),
        "the one control this measurement has: the same run reproduces the already-pinned eighth \
         chain artifact byte-for-byte"
    );

    // **The eighth chain's census row for this same closure disagrees with this
    // file, and the disagreement is recorded rather than averaged away.**
    // `float_div`'s `the_other_three_float_closures` records `reduce_float_add`
    // at def_index 15282 with a different lineage; this file records its OWN
    // run's pair. def_index is per-crate and not stable across runs, and the
    // body lineage is a per-BUILD identity — a re-pin of this fixture against a
    // moved tree changes BOTH while the emitted IR text stays byte-identical
    // (measured on 2026-08-20: 12,451 of 13,778 digests moved together across
    // an unrelated tree change, IR text identical). So this test pins fixture-
    // INTERNAL consistency, not run-specific constants.
    assert_eq!(
        body["def_index"].as_u64(),
        ev["def_index"].as_u64(),
        "the body block and the top level must record the same def_index"
    );
    assert_eq!(
        Some(coverage),
        ev["lineage"].as_str(),
        "the lineage this chain is about is the one in ITS OWN fixture, recorded once at the \
         top level and mirrored in the body block"
    );
    let sibling: serde_json::Value = serde_json::from_str(&fixture("float_div.lineage.json"))
        .expect("the eighth chain's evidence must be valid JSON");
    let row = &sibling["the_other_three_float_closures"]
        ["env::native_reducers_float::reduce_float_add::{closure#0}"];
    assert_eq!(row["def_index"].as_u64(), Some(15282));
    assert!(
        row["lineage"]
            .as_str()
            .is_some_and(|l| l != coverage && l.starts_with("sha256:")),
        "the census row and the measurement disagree; if they are ever reconciled, this is where \
         it has to be recorded"
    );
}
