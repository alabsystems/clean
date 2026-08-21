// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the float SUBTRACTION chain —
//! `env::native_reducers_float::reduce_float_sub::{closure#0}`.**
//!
//! ```text
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fsub f64 %1, %2
//!     ret %3
//! ```
//!
//! The `fdiv` chain's body with one token changed, and this file is that gate
//! under the same rename. The two lanes `float_div.rs` forced into
//! `emitted_cfg.rs` are the two that matter here too, and on this operator the
//! second one is sharper:
//!
//! * **the binop's TYPE.** `fsub f32` and `fsub f64` differ in no lane the gate
//!   had before 2026-08-15. They are different operations: `ir_float_binop`
//!   reads the width off the type and decides only binary64, so a module
//!   transcribed at `IRTy.float_ 32` returns the tagged `unmodelled` verdict
//!   where the artifact returns a value.
//! * **the RETURNED value id.** `ret %1` instead of `ret %3` returns the
//!   MINUEND instead of the difference, agrees with every lane that predates the
//!   `rets` lane, and on a two-instruction body is the entire semantics.
//! * **the OPERAND ORDER**, carried by the pre-existing `binops` lane and
//!   load-bearing here in a way it is not on a commutative operator: `fsub f64
//!   %2, %1` computes `b - a`. The perturbation battery below pins which lane
//!   catches it rather than leaving the coverage to be re-derived.
//!
//! ## What this gate does NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst`
//! encoding means what trust-ir's does. `ir_fs2_module` is hand-transcribed:
//! this makes an incorrect transcription FAIL, it does not make a correct one
//! automatic. And nothing here says `ir_f64_sub` is the hardware subtracter —
//! see the module docs of `spec/core_spec/eval_ir_float.rs` and
//! `eval_ir_float_fin.rs` for exactly what is and is not claimed.
//!
//! **A0/A6 are NOT asserted here, deliberately.** The evidence for this body is
//! committed at `fixtures/float_sub.lineage.json`, and it is a weaker
//! measurement than `float_div.lineage.json`: three clean non-incremental
//! builds via `scripts/trust_ir_build.sh --print-only` have byte-identical
//! coverage and are recorded in a reproduction block, but they use an unsealed
//! local-stage1 producer rather than a sealed driver and carry no negative
//! control. `assert_a0_a6` would therefore fail on the missing sealed provenance
//! and control, not on reproducibility. Wiring that file into `freshness.rs`'s
//! `EVIDENCE` table and into an A0/A6 test is a separate, honest piece of work;
//! recording the gap here is better than asserting a strength nobody measured.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn float_sub_proved_module_matches_the_emitted_artifact() {
    let text = fixture("float_sub.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @env::native_reducers_float::reduce_float_sub::{closure#0}("),
        "the fixture must be the reduce_float_sub closure itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_named_const_source("eval_ir_float_sub.rs", "SRC_IR_FS2_B0"),
        "def ir_fs2_b",
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
        BTreeMap::from([(0, vec![("fsub".to_string(), 3, 1, 2)])]),
        "exactly one binop, `fsub %1, %2` into %3 — IN THAT ORDER, because subtraction is not \
         commutative: {:?}",
        emitted.binops
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("fsub".to_string(), 3, "float64".to_string())])]),
        "…at BINARY64. This is the lane float arithmetic forced: {:?}",
        emitted.binop_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![3u32])]),
        "the body returns %3 — the DIFFERENCE, not %1 the minuend: {:?}",
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
    let func = clean_block_sources("eval_ir_float_sub.rs", "const SRC_IR_FS2_FUNC");
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
        &clean_block_sources("eval_ir_float_sub.rs", "const SRC_IR_FS2_FUNC"),
        "float_sub",
    );
    assert_lanes(&emitted, &clean, "float_sub");
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

/// **The two new lanes are not decoration: without them the perturbations
/// below are invisible.** This test is the negative half — it constructs the
/// drifted transcriptions and checks that every PRE-EXISTING lane still
/// compares equal on them, so the lanes are load-bearing by measurement.
#[test]
fn float_sub_the_new_lanes_catch_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("float_sub.trust-ir.txt"));

    // Drift 1: the same body at binary32.
    let at_f32 = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f32, %2: f32):\n    %3 = fsub f32 %1, %2\n \
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

    // Drift 2: returning the minuend instead of the difference.
    let wrong_ret = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fsub f64 %1, %2\n \
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
    // recorded here so the `fsub -> fadd` case has its expected catcher named
    // rather than assumed. `fadd` is the drift that matters on this body: the
    // two agree on every input EXCEPT the sign of the subtrahend, so a reader
    // checking the witnesses by eye would not necessarily notice.
    let as_add = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fadd f64 %1, %2\n \
         ret %3\n}\n",
    );
    assert_ne!(emitted.binops, as_add.binops);
    assert_ne!(emitted.binop_tys, as_add.binop_tys);
    assert_eq!(emitted.rets, as_add.rets);

    // Drift 4: exchanging the operands. Non-commutative, so this is a different
    // function — `1.0 - 2.0` and `2.0 - 1.0` differ in the sign bit, and the
    // chain executes both. Caught by the operand order the binop lane carries.
    let swapped = parse_emitted(
        "rustcc fn @x(functy.551) {\nbb0(%0: ptr, %1: f64, %2: f64):\n    %3 = fsub f64 %2, %1\n \
         ret %3\n}\n",
    );
    assert_ne!(emitted.binops, swapped.binops);
    assert_eq!(
        emitted.binop_tys, swapped.binop_tys,
        "the type lane cannot see an operand swap, which is why it is a SEPARATE lane and not a \
         replacement for the operand order"
    );
    assert_eq!(
        emitted.rets, swapped.rets,
        "and neither can the ret lane: the swapped body still returns %3"
    );
}

/// **The port is a port, and that is a measurement rather than a claim.**
///
/// The whole justification for `eval_ir_float_sub.rs` being
/// `eval_ir_float_div.rs` under a rename is that the two EMITTED bodies are the
/// same body with one token changed. If that ever stops being true — a
/// different operand order, a different width, a third instruction — the
/// shape-generic half of the port stops being justified and this test is where
/// it is noticed.
#[test]
fn float_sub_is_float_div_with_exactly_one_token_changed() {
    let sub = parse_emitted(&fixture("float_sub.trust-ir.txt"));
    let div = parse_emitted(&fixture("float_div.trust-ir.txt"));
    assert_eq!(sub.blocks, div.blocks);
    assert_eq!(sub.rets, div.rets, "both return %3");
    assert_eq!(
        sub.binops,
        BTreeMap::from([(0, vec![("fsub".to_string(), 3, 1, 2)])])
    );
    assert_eq!(
        div.binops,
        BTreeMap::from([(0, vec![("fdiv".to_string(), 3, 1, 2)])])
    );
    // The type lane carries the operator token too, so it is compared with that
    // token dropped: what must agree is the RESULT ID and the WIDTH.
    let id_and_width = |c: &Cfg| {
        c.binop_tys
            .get(&0)
            .and_then(|v| v.first())
            .map(|(_, r, t)| (*r, t.clone()))
    };
    assert_eq!(
        id_and_width(&sub),
        id_and_width(&div),
        "same result id at the same width; only the OPERATOR differs"
    );

    // …and at the text level, which is what a reader checks. The two fixtures
    // differ in the closure name, the operator, and the `#loc` column (214 vs
    // 222) — and in nothing else.
    let sub_text = fixture("float_sub.trust-ir.txt");
    let normalised = sub_text
        .replace("reduce_float_sub", "reduce_float_div")
        .replace("fsub", "fdiv")
        .replace("356 214 ", "356 222 ");
    assert_eq!(
        normalised,
        fixture("float_div.trust-ir.txt"),
        "the two emitted bodies must be identical modulo the closure name, the operator token and \
         the source column; if they are not, the shape-generic half of the port needs re-deriving \
         rather than renaming"
    );
}
