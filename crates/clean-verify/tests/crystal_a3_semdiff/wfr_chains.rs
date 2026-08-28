// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **float-RESIDUE synthetic chains** — the battery lane for the wave
//! `evalir_w4.PENDING.md` delta 5 named: three binary64 chains measuring the
//! seven newly-answering residue operators (`fneg`/`fabs`,
//! `ffloor`/`fceil`/`ftrunc`, `fmin`/`fmax`) through multi-value `ret`s.
//!
//! Same lane contract as `synth_chains.rs` (read its module doc first;
//! `eval_ir_float_res.rs` carries the semantics, its trust-ir `a4e81b6`
//! ground truth and its model status; `eval_ir_wfr_synth.rs` carries the
//! module design). Every chain is [`EnumModel::Synthetic`], E3 absent by
//! construction, reusing the W2a table structs verbatim. **ZERO declared
//! executor deltas IN THE ROWS**: every row is exact multi-value `Ret`
//! agreement on `RunResult::Float` bit patterns. The wave's real divergences
//! are cell-shaped, not row-shaped, and deliberately have NO battery row —
//! a tagged refusal and an answer share no row vocabulary (the W2b delta-2 /
//! W4 f32 class):
//!
//! * the rounding family on a NaN (Clean refuses — payload; E2 answers);
//! * `fmin`/`fmax` on both-NaN and on the opposite-signed-zero pair (Clean
//!   refuses — the host may return either; E2 answers whatever it returns);
//! * `frem`/`fsqrt`/the fp casts (Clean refuses the whole operator, dated;
//!   E2 answers).
//!
//! Each is kernel-witnessed (`eval_ir_float_res_witnesses.rs`), recorded in
//! `data/evalir_float_residue.PENDING.md`, and carried as a declared-delta
//! row of the adequacy grid — never a silent gap.
//!
//! Expectations are computed by [`fsign2`]/[`fround3`]/[`fminmax2`], which
//! restate the PINNED interpreter's own formulas (`eval_float_unop` /
//! `eval_float_binop`, F64 arms: `-x`/`abs`/`floor`/`ceil`/`trunc`,
//! `min`/`max`) on host `f64` — results as BIT PATTERNS, so NaN payloads and
//! signed zeros compare exactly. The E2 smoke asserts the interpreter really
//! computes them; the E1 probes measure the Clean kernel against them on the
//! big box.
//!
//! Cost offsets are DECLARED 0 on every row; the E2 half is measured here by
//! `crystal_a3_wfr_e2_instrument_smoke` (2 ops + ret = 3 steps for the sign
//! and minmax chains, 3 ops + ret = 4 for the rounding chain), and the E1
//! half (least fuels 3/4/3 and their tightness) pends the big box
//! (`data/evalir_float_residue.PENDING.md`).

use clean_verify::ir_semdiff::wide::{wide_args, wide_float, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::ty::Ty;

use super::synth_chains::{SynthChain, SynthExpect, SynthInput, SYNTHETIC_NO_E3};

/// The binary64 bit patterns the rows use, named once.
const ONE: u64 = 4_607_182_418_800_017_408; // 1.0
const TWO: u64 = 4_611_686_018_427_387_904; // 2.0
const OPF: u64 = 4_609_434_218_613_702_656; // 1.5
const M_OPF: u64 = 13_832_806_255_468_478_464; // -1.5
const HALF: u64 = 4_602_678_819_172_646_912; // 0.5
const M_HALF: u64 = 13_826_050_856_027_422_720; // -0.5
const M_ONE: u64 = 13_830_554_455_654_793_216; // -1.0
const M_TWO: u64 = 13_835_058_055_282_163_712; // -2.0
const P_ZERO: u64 = 0; // +0.0
const M_ZERO: u64 = 9_223_372_036_854_775_808; // -0.0
const P_INF: u64 = 9_218_868_437_227_405_312; // +inf
const M_INF: u64 = 18_442_240_474_082_181_120; // -inf
const Q_NAN: u64 = 9_221_120_237_041_090_560; // 0x7FF8000000000000
const BELOW_TWO: u64 = 4_611_686_018_427_387_903; // 1.9999999999999998
const K1_EDGE: u64 = 4_836_865_999_795_912_705; // 2251799813685248.5 (one fractional bit)

/// An `f64` argument value, from its bit pattern (deterministic — no host
/// NaN canonicalization can touch a pattern that is never an `f64` here).
fn iv_f64(bits: u64) -> InterpretValue {
    InterpretValue {
        ty: Ty::F64,
        kind: InterpretValueKind::FloatBits(bits),
    }
}

/// The sign chain's expectation: `[fneg x, fabs x]` as bit patterns — the
/// pinned interpreter's `eval_float_unop` F64 arms (`-x`, `x.abs()`)
/// restated on host `f64`.
fn fsign2(bits: u64) -> SynthExpect {
    let x = f64::from_bits(bits);
    SynthExpect::Ret(RunResult::Many(vec![
        RunResult::Float((-x).to_bits()),
        RunResult::Float(x.abs().to_bits()),
    ]))
}

/// The rounding chain's expectation: `[ffloor x, fceil x, ftrunc x]` — the
/// interpreter's `x.floor()`/`x.ceil()`/`x.trunc()`.
fn fround3(bits: u64) -> SynthExpect {
    let x = f64::from_bits(bits);
    SynthExpect::Ret(RunResult::Many(vec![
        RunResult::Float(x.floor().to_bits()),
        RunResult::Float(x.ceil().to_bits()),
        RunResult::Float(x.trunc().to_bits()),
    ]))
}

/// The minmax chain's expectation: `[fmin x y, fmax x y]` — the
/// interpreter's `lhs.min(rhs)`/`lhs.max(rhs)`.
fn fminmax2(lhs: u64, rhs: u64) -> SynthExpect {
    let (l, r) = (f64::from_bits(lhs), f64::from_bits(rhs));
    SynthExpect::Ret(RunResult::Many(vec![
        RunResult::Float(l.min(r).to_bits()),
        RunResult::Float(l.max(r).to_bits()),
    ]))
}

/// The float-residue chains, in measurement order.
pub fn wfr_chains() -> Vec<SynthChain> {
    vec![fsign_probe(), fround_probe(), fminmax_probe()]
}

/// `fneg`/`fabs` — `%1 = fneg f64 %0; %2 = fabs f64 %0`, two-value ret.
fn fsign_probe() -> SynthChain {
    let case = |label, x: u64| SynthInput {
        label,
        clean_tail: format!("{} ir_mem0 ir_d0", wide_args(&[wide_float(x)])),
        trust_args: vec![iv_f64(x)],
        expect: fsign2(x),
    };
    SynthChain {
        name: "synth_fsign",
        fixtures: &[("synth/synth_fsign.trust-ir.txt", "@synth::fsign_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(925, vec![Ty::F64], vec![Ty::F64; 2])],
        clean_module: "ir_frs_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_frs_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("1.5: both sign ops on a positive", OPF),
            case("-1.5: both sign ops on a negative", M_OPF),
            case("+0: fneg makes -0, fabs keeps +0", P_ZERO),
            case("-0: both land on +0", M_ZERO),
            case("+inf: sign ops on the top", P_INF),
            case("-inf: sign ops on the bottom", M_INF),
            case("NaN: bit ops answer, payload kept", Q_NAN),
        ],
    }
}

/// `ffloor`/`fceil`/`ftrunc` — three roundings of one operand, three-value
/// ret. No NaN row by design (module doc).
fn fround_probe() -> SynthChain {
    let case = |label, x: u64| SynthInput {
        label,
        clean_tail: format!("{} ir_mem0 ir_d0", wide_args(&[wide_float(x)])),
        trust_args: vec![iv_f64(x)],
        expect: fround3(x),
    };
    SynthChain {
        name: "synth_fround",
        fixtures: &[("synth/synth_fround.trust-ir.txt", "@synth::fround_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(926, vec![Ty::F64], vec![Ty::F64; 3])],
        clean_module: "ir_frr_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_frr_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("1.5: the mid-range split", OPF),
            case("-1.5: floor/ceil exchange sides", M_OPF),
            case("0.5: the small-magnitude arm", HALF),
            case("-0.5: ceil keeps the minus sign", M_HALF),
            case("2.0: an exact integer is itself", TWO),
            case("1.9999...: ceil carries the exponent", BELOW_TWO),
            case("+0: a zero is its own rounding", P_ZERO),
            case("-0: sign preserved through rounding", M_ZERO),
            case("+inf: an infinity is its own rounding", P_INF),
            case("-inf: the negative infinity too", M_INF),
            case("2^51-scale half: one fractional bit", K1_EDGE),
        ],
    }
}

/// `fmin`/`fmax` — both picks of one operand pair, two-value ret. The
/// both-NaN and opposite-zero pairs are NOT rows (module doc).
fn fminmax_probe() -> SynthChain {
    let case = |label, a: u64, b: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_float(a), wide_float(b)])
        ),
        trust_args: vec![iv_f64(a), iv_f64(b)],
        expect: fminmax2(a, b),
    };
    SynthChain {
        name: "synth_fminmax",
        fixtures: &[("synth/synth_fminmax.trust-ir.txt", "@synth::fminmax_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(927, vec![Ty::F64, Ty::F64], vec![Ty::F64; 2])],
        clean_module: "ir_frm_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_frm_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("1 vs 2: opposite picks", ONE, TWO),
            case("2 vs 1: picks follow value, not slot", TWO, ONE),
            case("-2 vs -1: negative order reverses", M_TWO, M_ONE),
            case("NaN vs 2: one NaN is ignored", Q_NAN, TWO),
            case("2 vs NaN: on the right too", TWO, Q_NAN),
            case("-inf vs 1: the bottom is the min", M_INF, ONE),
            case("1 vs +inf: the top is the max", ONE, P_INF),
            case("+0 vs +0: same-sign zeros answer", P_ZERO, P_ZERO),
            case("-0 vs -0: the negative pair too", M_ZERO, M_ZERO),
            case("1.5 vs 1.5: equal finites", OPF, OPF),
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The named patterns are the binary64s the comments claim.
    #[test]
    fn test_the_row_patterns_are_binary64s() {
        assert_eq!(ONE, 1.0f64.to_bits());
        assert_eq!(TWO, 2.0f64.to_bits());
        assert_eq!(OPF, 1.5f64.to_bits());
        assert_eq!(M_OPF, (-1.5f64).to_bits());
        assert_eq!(HALF, 0.5f64.to_bits());
        assert_eq!(M_HALF, (-0.5f64).to_bits());
        assert_eq!(M_ONE, (-1.0f64).to_bits());
        assert_eq!(M_TWO, (-2.0f64).to_bits());
        assert_eq!(P_ZERO, 0.0f64.to_bits());
        assert_eq!(M_ZERO, (-0.0f64).to_bits());
        assert_eq!(P_INF, f64::INFINITY.to_bits());
        assert_eq!(M_INF, f64::NEG_INFINITY.to_bits());
        assert!(f64::from_bits(Q_NAN).is_nan());
        assert_eq!(BELOW_TWO, 1.999_999_999_999_999_8f64.to_bits());
        assert_eq!(K1_EDGE, 2_251_799_813_685_248.5f64.to_bits());
    }

    /// The rows avoid every cell the Clean side refuses, so a row can never
    /// silently measure a refusal: no NaN reaches the rounding chain, and no
    /// both-NaN or opposite-signed-zero pair reaches the minmax chain.
    #[test]
    fn test_the_rows_avoid_the_refused_cells() {
        for input in fround_probe().inputs {
            let x = match &input.trust_args[0].kind {
                InterpretValueKind::FloatBits(b) => f64::from_bits(*b),
                other => panic!("fround args are floats, got {other:?}"),
            };
            assert!(
                !x.is_nan(),
                "the rounding chain must not carry a NaN row: {}",
                input.label
            );
        }
        for input in fminmax_probe().inputs {
            let bits: Vec<u64> = input
                .trust_args
                .iter()
                .map(|v| match &v.kind {
                    InterpretValueKind::FloatBits(b) => *b,
                    other => panic!("fminmax args are floats, got {other:?}"),
                })
                .collect();
            let (l, r) = (f64::from_bits(bits[0]), f64::from_bits(bits[1]));
            assert!(
                !(l.is_nan() && r.is_nan()),
                "the minmax chain must not carry a both-NaN row: {}",
                input.label
            );
            assert!(
                !(l == r && bits[0] != bits[1]),
                "the minmax chain must not carry the opposite-signed-zero pair: {}",
                input.label
            );
        }
    }

    /// The two facts the lane exists to measure, asserted on the expectation
    /// generators themselves: sign ops preserve a NaN's payload, and one NaN
    /// operand is ignored by both picks.
    #[test]
    fn test_the_generators_carry_the_semantics() {
        let SynthExpect::Ret(RunResult::Many(sign)) = fsign2(Q_NAN) else {
            panic!("fsign2 must produce a Many expectation");
        };
        assert_eq!(
            sign,
            vec![
                RunResult::Float(Q_NAN | (1u64 << 63)),
                RunResult::Float(Q_NAN)
            ],
            "fneg flips the NaN's sign bit, fabs clears it — payload untouched"
        );
        let SynthExpect::Ret(RunResult::Many(mm)) = fminmax2(Q_NAN, TWO) else {
            panic!("fminmax2 must produce a Many expectation");
        };
        assert_eq!(
            mm,
            vec![RunResult::Float(TWO), RunResult::Float(TWO)],
            "one NaN operand is ignored: both picks return the other operand"
        );
        let SynthExpect::Ret(RunResult::Many(rnd)) = fround3(M_OPF) else {
            panic!("fround3 must produce a Many expectation");
        };
        assert_eq!(
            rnd,
            vec![
                RunResult::Float(M_TWO),
                RunResult::Float(M_ONE),
                RunResult::Float(M_ONE)
            ],
            "floor rounds a negative away from zero; ceil and trunc do not"
        );
    }
}
