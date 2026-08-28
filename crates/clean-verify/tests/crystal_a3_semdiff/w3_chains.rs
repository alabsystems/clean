// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W3 synthetic chains** — the OVERFLOW value domain
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W3): one unsigned
//! (`u8`) and one signed (`i8`) chain, each running all three `OverflowOp`s on
//! the same operands and returning every bound result through the six-value
//! `ret`. After this lane only `fcmp` (plan W4) lacks battery rows.
//!
//! Same lane contract as `synth_chains.rs` (read its module doc first, and
//! `eval_ir_w3_synth.rs`'s for the module design and the polarity coverage).
//! Every chain is [`EnumModel::Synthetic`], E3 absent by construction, reusing
//! the W2a table structs verbatim. NO declared executor delta exists in this
//! lane: every row is a value-returning `Ret` compared exactly — the first
//! multi-value rows in the battery ([`RunResult::Many`]), which also puts the
//! machine's positional multi-value return (`ir_ret_to`) under measurement
//! for the first time.
//!
//! ## Why the rows look like they do
//!
//! One body computes add, sub and mul on the SAME operands, so a row's inputs
//! feed all three ops at once and polarity coverage is spread ACROSS rows
//! (each op overflows on some rows and stays quiet on others — the per-op
//! ledger is in the stage's module doc). The u8 lane exercises the unsigned
//! flag rules (past-the-mask, borrow), the i8 lane the signed ones — the
//! bounds of [-128, 127], including both MIN edges the plan names:
//! `-128 - 1` (sub overflows) and `-128 * -1` (mul overflows to +128, the
//! two's-complement negation asymmetry) beside `-128 + 1` / `-128 * 1`
//! sitting exactly one inside. Values cross the E1/E2 boundary as raw
//! width-8 residues (Clean's canonical `int_` patterns; trust-ir's masked
//! `InterpretInt.raw`), so `-56` compares as `200` on both sides by the same
//! rule.
//!
//! Cost offsets are DECLARED 0 on every row; the E2 half of that declaration
//! is measured here by `crystal_a3_w3_e2_instrument_smoke` (3 overflow nodes
//! + ret = 4 steps per row), and the E1 half (least fuels and their
//! tightness) pends the big box (`data/evalir_w3.PENDING.md`).

use clean_verify::ir_semdiff::wide::{wide_args, wide_int, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::Ty;

use super::synth_chains::{SynthChain, SynthExpect, SynthInput, SYNTHETIC_NO_E3};

/// A `u8` argument value.
fn iv_u8(n: u8) -> InterpretValue {
    InterpretValue::int(Ty::U8, i128::from(n)).expect("u8 is an integer type")
}

/// An `i8` argument value, from the SIGNED number (the constructor masks it
/// to the raw two's-complement pattern the interpreter carries).
fn iv_i8(n: i8) -> InterpretValue {
    InterpretValue::int(Ty::I8, i128::from(n)).expect("i8 is an integer type")
}

/// The six-value expectation: three (value, flag) pairs in instruction order
/// (add, sub, mul), values as raw width-8 residues.
fn pair6(av: u64, af: bool, sv: u64, sf: bool, mv: u64, mf: bool) -> SynthExpect {
    SynthExpect::Ret(RunResult::Many(vec![
        RunResult::Int(av),
        RunResult::Bool(af),
        RunResult::Int(sv),
        RunResult::Bool(sf),
        RunResult::Int(mv),
        RunResult::Bool(mf),
    ]))
}

/// The W3 chains, in measurement order.
pub fn w3_chains() -> Vec<SynthChain> {
    vec![overflow_u8_probe(), overflow_i8_probe()]
}

/// `overflow`, unsigned lane — `%2,%3 = add.overflow u8 %0,%1` (and sub, and
/// mul), six-value ret. Constructor under measure: `overflow` (+ the
/// already-measured `ret`, here in its multi-value form for the first time).
fn overflow_u8_probe() -> SynthChain {
    let case = |label, a: u8, b: u8, expect: SynthExpect| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_int(u64::from(a)), wide_int(u64::from(b))])
        ),
        trust_args: vec![iv_u8(a), iv_u8(b)],
        expect,
    };
    SynthChain {
        name: "synth_overflow_u8",
        fixtures: &[(
            "synth/synth_overflow_u8.trust-ir.txt",
            "@synth::overflow_u8_probe",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(
            922,
            vec![Ty::U8, Ty::U8],
            vec![Ty::U8, Ty::Bool, Ty::U8, Ty::Bool, Ty::U8, Ty::Bool],
        )],
        clean_module: "ir_w3_ou_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w3_ou_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            // 16*16 = 256: mul's value wraps to 0 AT the boundary, flag true.
            case(
                "16 op 16: mul wraps at exactly 2^8",
                16,
                16,
                pair6(32, false, 0, false, 0, true),
            ),
            // 0-1 borrows: sub's flag is the strict lhs<rhs rule.
            case(
                "0 op 1: sub borrows to 255",
                0,
                1,
                pair6(1, false, 255, true, 0, false),
            ),
            // 240+32 = 272 past the mask AND 240*32 = 7680 past it: two ops
            // overflow in one execution, sub stays quiet.
            case(
                "240 op 32: add and mul overflow together",
                240,
                32,
                pair6(16, true, 208, false, 0, true),
            ),
            // The all-quiet row.
            case(
                "3 op 2: nothing overflows",
                3,
                2,
                pair6(5, false, 1, false, 6, false),
            ),
        ],
    }
}

/// `overflow`, signed lane — the same body at `i8`, where the flag follows
/// trust-ir's `signed_overflow` bounds. Arguments are written as SIGNED
/// numbers; both executors carry them as raw two's-complement residues.
fn overflow_i8_probe() -> SynthChain {
    let case = |label, a: i8, b: i8, expect: SynthExpect| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[
                wide_int(u64::from(a.cast_unsigned())),
                wide_int(u64::from(b.cast_unsigned())),
            ])
        ),
        trust_args: vec![iv_i8(a), iv_i8(b)],
        expect,
    };
    SynthChain {
        name: "synth_overflow_i8",
        fixtures: &[(
            "synth/synth_overflow_i8.trust-ir.txt",
            "@synth::overflow_i8_probe",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(
            923,
            vec![Ty::I8, Ty::I8],
            vec![Ty::I8, Ty::Bool, Ty::I8, Ty::Bool, Ty::I8, Ty::Bool],
        )],
        clean_module: "ir_w3_os_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w3_os_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            // 96+64 = 160 > 127 and 96*64 = 6144 > 127: add and mul overflow,
            // sub (32) quiet. The wrapped sum's raw pattern is 160 (-96).
            case(
                "96 op 64: add and mul escape the signed maximum",
                96,
                64,
                pair6(160, true, 32, false, 0, true),
            ),
            // MIN edge, one inside on two sides: -128+1 = -127 (raw 129) and
            // -128*1 = -128 (raw 128) are IN range; -128-1 = -129 overflows
            // (value raw 127).
            case(
                "-128 op 1: only sub leaves the range",
                -128,
                1,
                pair6(129, false, 127, true, 128, false),
            ),
            // Mixed signs, all quiet; the negative product crosses as its
            // raw pattern 250 (-6).
            case(
                "3 op -2: nothing overflows",
                3,
                -2,
                pair6(1, false, 5, false, 250, false),
            ),
            // The MIN asymmetry: -128 * -1 = +128 > 127 overflows (value
            // wraps back to raw 128) and -128 + -1 = -129 overflows (raw
            // 127), while -128 - -1 = -127 (raw 129) is fine.
            case(
                "-128 op -1: the MIN * -1 asymmetry",
                -128,
                -1,
                pair6(127, true, 129, false, 128, true),
            ),
        ],
    }
}
