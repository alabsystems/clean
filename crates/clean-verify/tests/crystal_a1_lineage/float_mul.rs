// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the ELEVENTH chain — the second over FLOAT ARITHMETIC:
//! `env::native_reducers_float::reduce_float_mul::{closure#0}`.**
//!
//! ```text
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fmul f64 %1, %2
//!     ret %3
//! ```
//!
//! Structurally the eighth chain's body character for character except the
//! opcode token and the source column (`fmul` for `fdiv`, 218 for 222), so the
//! two lanes that body forced into `emitted_cfg.rs` are the two that matter
//! here as well:
//!
//! * **the binop's TYPE.** `ir_float_binop` reads the width off it and decides
//!   only binary64, so a module transcribed at `IRTy.float_ 32` returns the
//!   tagged `unmodelled` verdict where the artifact returns a value. Nothing
//!   but `binop_tys` can see it.
//! * **the RETURNED value id.** `ret %1` instead of `ret %3` returns the LEFT
//!   OPERAND instead of the product, agrees with every other lane, and on a
//!   two-instruction body is the entire semantics. Only `rets` can see it.
//!
//! ## The lane this operator makes load-bearing on its own
//!
//! `fmul` is COMMUTATIVE on the modelled fragment, and the spec module proves
//! it by execution (`ir_fm_two_times_three` / `ir_fm_three_times_two` return
//! the same bit pattern). So unlike `fdiv`, a transcription that swapped the
//! operands would compute the same function on every input this semantics
//! answers on, and NO witness could catch it. What catches it is the `binops`
//! lane, which compares `(op, result, lhs, rhs)` against the artifact and does
//! not care whether the swap is observable —
//! `float_mul_operand_order_is_gated_structurally_even_though_it_is_unobservable`
//! is that separation, executed in both directions.
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. `ir_fm_module` is hand-transcribed:
//! this makes an incorrect transcription FAIL, it does not make a correct one
//! automatic. Nothing here says `ir_f64_mul` is the hardware multiplier — see
//! the module docs of `spec/core_spec/eval_ir_float.rs` and
//! `spec/core_spec/eval_ir_float_mul.rs` for exactly what is and is not
//! claimed.
//!
//! **This module asserts nothing about A0 or A6, and has no counterpart to
//! `float_div_a0_a6_evidence_is_pinned_on_the_shipped_kernel`.** Read that
//! literally, because `fixtures/float_mul.lineage.json` DOES carry the A0
//! criteria by name — `body.derived_mir.verdict = "agreed"`,
//! `body.derived_mir.markers_exact = true`, `body.interpreter.verdict =
//! "agreed"` over 64 samples, and a full-digest
//! `flip_lineage_equals_coverage: true` — but its own `provenance_strength`
//! field records three clean non-incremental builds with byte-identical coverage
//! and a reproduction stanza, but all three use one unsealed local-stage1
//! producer rather than the sealed driver behind `float_div.lineage.json`, and
//! there is no negative control. Asserting A0 over it here would dress a
//! weaker-PROVENANCE measurement in a stronger gate's clothes; the criteria
//! themselves are present and true.
//!
//! The eighth chain's evidence file separately records this closure as a
//! SIBLING row (`the_other_three_float_closures`, `def_index` 15286) — a census
//! entry saying it is chainable on identical terms, not a measurement of it.
//! Link 2a is what this file provides; A0 and A6 for `reduce_float_mul` stay
//! open until a measurement at the eighth chain's protocol is taken and pinned.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn float_mul_proved_module_matches_the_emitted_artifact() {
    let text = fixture("float_mul.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::native_reducers_float::reduce_float_mul::{closure#0}("),
        "the fixture must be the reduce_float_mul closure itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_named_const_source("eval_ir_float_mul.rs", "SRC_IR_FM_B0"),
        "def ir_fm_b",
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
        BTreeMap::from([(0, vec![("fmul".to_string(), 3, 1, 2)])]),
        "exactly one binop, `fmul %1, %2` into %3: {:?}",
        emitted.binops
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("fmul".to_string(), 3, "float64".to_string())])]),
        "…at BINARY64. This is the lane float arithmetic forced: {:?}",
        emitted.binop_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![3u32])]),
        "the body returns %3 — the PRODUCT, not %1 the left operand: {:?}",
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
    let func = clean_block_sources("eval_ir_float_mul.rs", "const SRC_IR_FM_FUNC");
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
        &clean_block_sources("eval_ir_float_mul.rs", "const SRC_IR_FM_FUNC"),
        "float_mul",
    );
    assert_lanes(&emitted, &clean, "float_mul");
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
fn float_mul_the_new_lanes_catch_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("float_mul.trust-ir.txt"));

    // Drift 1: the same body at binary32.
    let at_f32 = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f32, %2: f32):\n    %3 = fmul f32 %1, %2\n \
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

    // Drift 2: returning the left operand instead of the product.
    let wrong_ret = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fmul f64 %1, %2\n \
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

    // Drift 3: the operator itself — the sibling body, which is the same graph
    // at a DIFFERENT semantics (`fdiv`'s fin/fin cell is `IROption.none` where
    // `fmul`'s is the rounded product). Caught by the pre-existing binop lane.
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
}

/// **Operand order, on the one chained body where execution cannot see it.**
///
/// `fdiv` is non-commutative, so the eighth chain has a WITNESS
/// (`ir_fd_order_is_observable`: `+inf` one way and `+0` the other) as well as
/// a lane. `fmul` is commutative on the whole modelled fragment — the spec
/// module executes that as `ir_fm_two_times_three` / `ir_fm_three_times_two` —
/// so a transcription with the operands exchanged computes the SAME function
/// and no witness in this repository could distinguish it. Only the structural
/// lane can, and it does not need to know the difference is unobservable.
#[test]
fn float_mul_operand_order_is_gated_structurally_even_though_it_is_unobservable() {
    let emitted = parse_emitted(&fixture("float_mul.trust-ir.txt"));
    let swapped = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fmul f64 %2, %1\n \
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
    assert_eq!(emitted.blocks, swapped.blocks);
}

/// **The other direction: perturb the CLEAN side.**
///
/// Every drift above is in the artifact. A gate that only ever mutated the
/// fixture would be blind to the failure mode this whole file exists for — the
/// registered spec module drifting away from a body that never moved. These
/// three mutations are applied to the registered `SRC_IR_FM_B0` source itself,
/// parsed with the same reader the gate uses, and each must break exactly the
/// lane that owns it.
#[test]
fn float_mul_the_lanes_catch_a_drifted_spec_module_too() {
    let emitted = parse_emitted(&fixture("float_mul.trust-ir.txt"));
    let src = clean_named_const_source("eval_ir_float_mul.rs", "SRC_IR_FM_B0");
    let good = parse_clean(&src, "def ir_fm_b");
    assert_eq!(
        emitted.binops, good.binops,
        "the unmutated registered module must agree, or the mutations below prove nothing"
    );

    // The registered module at binary32.
    let at_f32 = parse_clean(
        &src.replace("ir_fm_tf64", "(IRTy.float_ 32)"),
        "def ir_fm_b",
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
        "def ir_fm_b",
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

    // The registered module at the sibling operator.
    let as_div = parse_clean(&src.replace("IRBinOp.fmul", "IRBinOp.fdiv"), "def ir_fm_b");
    assert_ne!(
        emitted.binops, as_div.binops,
        "the BINOP lane must reject a spec module proved about division"
    );
    assert_eq!(emitted.rets, as_div.rets);

    // The registered module with the operands exchanged — unobservable to every
    // witness the spec module can execute, and still rejected here.
    let swapped = parse_clean(
        &src.replace("ir_fm_tf64 ir_d1 ir_d2", "ir_fm_tf64 ir_d2 ir_d1"),
        "def ir_fm_b",
    );
    assert_ne!(
        emitted.binops, swapped.binops,
        "the BINOP lane must reject the swap on the Clean side too"
    );
    assert_eq!(emitted.binop_tys, swapped.binop_tys);
}
