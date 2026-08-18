// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the EIGHTH complete chain — the first over FLOAT
//! ARITHMETIC: `env::native_reducers_float::reduce_float_div::{closure#0}`.**
//!
//! ```text
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fdiv f64 %1, %2
//!     ret %3
//! ```
//!
//! One block, two instructions — and with this little in a body, everything the
//! gate does not compare is most of the function. That is why it forced two new
//! lanes into `emitted_cfg.rs`.
//!
//! (It is NOT the smallest chainable body, and the correction is measured: 106
//! of the 177 chainable bodies are one instruction, every one of them a bare
//! `ret`. What is rare here is the OPERATOR — across all 177, `fadd`, `fsub`,
//! `fmul` and `fdiv` appear exactly once each.)
//!
//! * **the binop's TYPE.** `fdiv f32` and `fdiv f64` differ in no lane the gate
//!   had. They are different operations: `ir_float_binop` reads the width off
//!   the type and decides only binary64, so a module transcribed at
//!   `IRTy.float_ 32` returns the tagged `unmodelled` verdict where the artifact
//!   returns a value. The `binop_tys` lane closes it — and `icmp_tys` closes the
//!   same hole for the three earlier chains' integer comparisons, whose widths
//!   were equally uncompared.
//! * **the RETURNED value id.** Nothing in this file had ever looked at what a
//!   body returns. `ret %1` instead of `ret %3` returns the DIVIDEND instead of
//!   the quotient, agrees with every pre-existing lane on every chain, and on
//!   this body is the entire semantics. The `rets` lane closes it.
//!
//! Measured on `clean-kernel` itself at this HEAD, with the sealed lane-8
//! stage1 trustc (`seal_driver.sh verify` OK and `guard` PASS before the run),
//! three clean non-incremental builds plus a negative control, all four with a
//! byte-identical `coverage.json`:
//!
//! ```text
//! derived_mir.verdict        agreed  ("6 canonical line(s) identical")
//! derived_mir.markers_exact  true    over 4 REAL marker lines
//! interpreter differential   agreed  on 64 sampled inputs
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:a457b9c0…
//! flip event                 FIRED, codegen seam, same lineage, flipped_so_far=209
//! negative control           -Ztrust-ir-flip=no -> 0 events crate-wide
//! ```
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. The lineage digest is RECORDED, not
//! recomputed. `ir_fd_module` is hand-transcribed: this makes an incorrect
//! transcription FAIL, it does not make a correct one automatic. And nothing
//! here says `ir_f64_div` is the hardware divider — see the module doc of
//! `spec/core_spec/eval_ir_float.rs` for exactly what is and is not claimed.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn float_div_proved_module_matches_the_emitted_artifact() {
    let text = fixture("float_div.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::native_reducers_float::reduce_float_div::{closure#0}("),
        "the fixture must be the reduce_float_div closure itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_float_div.rs", "const SRC_IR_FD_B"),
        "def ir_fd_b",
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
        BTreeMap::from([(0, vec![("fdiv".to_string(), 3, 1, 2)])]),
        "exactly one binop, `fdiv %1, %2` into %3: {:?}",
        emitted.binops
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("fdiv".to_string(), 3, "float64".to_string())])]),
        "…at BINARY64. This is the lane float arithmetic forced: {:?}",
        emitted.binop_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![3u32])]),
        "the body returns %3 — the QUOTIENT, not %1 the dividend: {:?}",
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
    let func = clean_block_sources("eval_ir_float_div.rs", "const SRC_IR_FD_FUNC");
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
    // registered `IRFunc`. Not in `Cfg` — Clean's entry `IRBlock` carries `ir_nl0` — and
    // uncompared on seven of the nine chains until the 2026-08-16 lane audit.
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_float_div.rs", "const SRC_IR_FD_FUNC"),
        "float_div",
    );
    assert_lanes(&emitted, &clean, "float_div");
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
fn float_div_a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("float_div.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_a0_a6(
        &evidence,
        "env::native_reducers_float::reduce_float_div::{closure#0}",
    );
    assert_eq!(
        evidence["interpreter_differential"]["verdict"].as_str(),
        Some("agreed"),
        "the producer's own interpreter differential RAN on this body"
    );
    assert_eq!(
        evidence["interpreter_differential"]["samples"].as_u64(),
        Some(64),
        "64 sampled inputs — the widest interpreter differential of any chained body except \
         expr::bvar_in_range's 125"
    );
    assert!(
        evidence["interpreter_differential"]["detail"]
            .as_str()
            .is_some_and(|d| d.contains("proven-never-read opaque param")),
        "the producer's own record that the closure environment pointer is never read — which is \
         why A4 quantifies over it with no premise instead of assuming one"
    );
    assert!(
        !j.contains("fdivprobe") && !j.contains("floatprobe"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
    assert_eq!(evidence["instr_count"].as_u64(), Some(2));
    assert_eq!(evidence["func_id"].as_u64(), Some(4415));
}

/// **The non-vacuity of `markers_exact`, recorded as a number.**
#[test]
fn float_div_markers_exact_is_not_vacuous() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("float_div.lineage.json"))
        .expect("evidence must be valid JSON");
    let detail = evidence["derived_mir"]["markers_detail"]
        .as_str()
        .expect("markers_detail must be recorded");
    assert_eq!(
        detail, "4 marker line(s) identical",
        "the marker sequence is FOUR lines long and equal line for line; if this becomes \
         `0 marker line(s) identical` then markers_exact has gone vacuous here too"
    );
    assert!(!detail.starts_with("0 "));
    let sel = &evidence["candidate_selection"];
    assert_eq!(sel["markers_exact_rows_total"].as_u64(), Some(1084));
    assert_eq!(
        sel["markers_exact_rows_that_are_NON_vacuous"].as_u64(),
        Some(27),
        "the third independent confirmation of the vacuity figure, from this lane's own \
         whole-crate dump — a markers_exact gain is not a fidelity gain"
    );
    assert_eq!(
        sel["re_derived_by_this_lane"].as_bool(),
        Some(true),
        "the candidate row must be re-derived, not inherited from the census that named it"
    );
}

/// **The float-semantics wall, pinned as data rather than left in prose.**
///
/// This chain exists because the value domain did not. The boundary of what
/// EvalIR can say about binary64 is the deliverable next to the chain itself, so
/// it is recorded where a gate reads it: a later lane that wants the finite case
/// must move the measurement, not the sentence.
#[test]
fn float_div_the_semantics_wall_is_recorded_with_its_reasons() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("float_div.lineage.json"))
        .expect("evidence must be valid JSON");
    let wall = &evidence["float_semantics_wall"];
    assert!(
        wall["answer"]
            .as_str()
            .is_some_and(|a| a.starts_with("PARTLY")),
        "the honest answer is PARTLY; a gate that let this become YES or NO would be recording a \
         claim rather than a measurement"
    );
    let refused = &wall["refused_and_why"];
    assert!(
        refused["NaN result"]
            .as_str()
            .is_some_and(|s| s.contains("implementation-defined")),
        "the NaN refusal is a wall in the STANDARD — the payload is not determined — and must be \
         distinguished from the ones that are walls in the substrate"
    );
    assert!(
        refused["finite (+,-,*,/) finite"]
            .as_str()
            .is_some_and(|s| s.contains("2^53") && s.contains("ACCELERATED CONSTANTS")),
        "the rounding refusal must name BOTH halves: the walk that makes it unaffordable, and \
         the trust that buying it with Nat.div/Nat.mod would cost"
    );
    assert_eq!(
        wall["accelerated_constants_added"].as_u64(),
        Some(0),
        "the whole point of the ir_nat_ltb_sub route is that the substrate gains no new \
         accelerated constant; if this ever becomes non-zero the trust argument has changed"
    );
    assert!(wall["what_made_the_classification_affordable"]
        .as_str()
        .is_some_and(|s| s.contains("ir_nat_ltb_sub_eq")));
}

/// The other three float closures are chainable on identical terms, and the
/// four that are NOT are recorded with the producer's reason.
///
/// This is the census row this lane owes the next one: `fdiv` was chosen on
/// semantic content, so the fact that `fadd`/`fsub`/`fmul` are equally available
/// — and that `fneg` and the three `FCmp` closures are not — must not have to be
/// re-derived.
#[test]
fn float_div_the_sibling_closures_are_recorded_not_left_to_be_rederived() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("float_div.lineage.json"))
        .expect("evidence must be valid JSON");
    let sib = &evidence["the_other_three_float_closures"];
    for (name, idx, lin) in [
        (
            "env::native_reducers_float::reduce_float_add::{closure#0}",
            15282u64,
            "sha256:21501d78053d7cc053554ffa9aa1d83770c3610fccf394aed4da3caffb2b5421",
        ),
        (
            "env::native_reducers_float::reduce_float_sub::{closure#0}",
            15284,
            "sha256:b0d6fcaf121ac2459eaf02f220648452fc67068e7e8dac3cc103544682181d7f",
        ),
        (
            "env::native_reducers_float::reduce_float_mul::{closure#0}",
            15286,
            "sha256:f36d43f7059eaf1e333aad3a426f0511caf654eaa019c2e1884d106898371287",
        ),
    ] {
        assert_eq!(sib[name]["def_index"].as_u64(), Some(idx));
        assert_eq!(sib[name]["lineage"].as_str(), Some(lin));
    }
    let refused = &evidence["float_closures_that_are_NOT_chainable"];
    assert!(
        refused["env::native_reducers_float::reduce_float_neg::{closure#0}"]
            .as_str()
            .is_some_and(|s| s.contains("UnOp(FNeg)"))
    );
    for beq in [
        "env::native_reducers_float::reduce_float_beq::{closure#0}",
        "env::native_reducers_float::reduce_float_blt::{closure#0}",
        "env::native_reducers_float::reduce_float_ble::{closure#0}",
    ] {
        assert!(
            refused[beq]
                .as_str()
                .is_some_and(|s| s.contains("Inst::FCmp")),
            "the three float COMPARISON closures do not lower, which is the measured reason the \
             value domain leaves IRFCmpOp at its unmodelled verdict"
        );
    }
}

/// **The two new lanes are not decoration: without them the perturbations
/// below are invisible.** This test is the negative half — it constructs the
/// two drifted transcriptions and checks that every PRE-EXISTING lane still
/// compares equal on them, so the lanes are load-bearing by measurement.
#[test]
fn float_div_the_new_lanes_catch_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("float_div.trust-ir.txt"));

    // Drift 1: the same body at binary32.
    let at_f32 = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f32, %2: f32):\n    %3 = fdiv f32 %1, %2\n \
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

    // Drift 2: returning the dividend instead of the quotient.
    let wrong_ret = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fdiv f64 %1, %2\n \
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

    // Drift 3: the operator itself. Caught by the pre-existing binop lane —
    // recorded here so the perturbation battery's `fdiv -> fmul` case has its
    // expected catcher named rather than assumed.
    let as_mul = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fmul f64 %1, %2\n \
         ret %3\n}\n",
    );
    assert_ne!(emitted.binops, as_mul.binops);
    assert_ne!(emitted.binop_tys, as_mul.binop_tys);
    assert_eq!(emitted.rets, as_mul.rets);

    // Drift 4: exchanging the operands. Non-commutative, so this is a different
    // function — caught by the operand order the binop lane already carried.
    let swapped = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fdiv f64 %2, %1\n \
         ret %3\n}\n",
    );
    assert_ne!(emitted.binops, swapped.binops);
    assert_eq!(
        emitted.binop_tys, swapped.binop_tys,
        "the type lane cannot see an operand swap, which is why it is a SEPARATE lane and not a \
         replacement for the operand order"
    );
}
