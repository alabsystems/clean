// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W4 synthetic chain** — the FLOAT-COMPARISON lane
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W4): one binary64
//! chain running all twelve `FCmpOp` predicates on the same two operands and
//! returning every Bool through the twelve-value `ret`. **The last lane: with
//! it every `IRInst` constructor has battery rows.**
//!
//! Same lane contract as `synth_chains.rs` (read its module doc first, and
//! `eval_ir_w4_synth.rs`'s for the module design; `eval_ir_fcmp.rs` carries
//! the semantics, its ground truth and its model status). The chain is
//! [`EnumModel::Synthetic`], E3 absent by construction, reusing the W2a table
//! structs verbatim. **ZERO declared executor deltas**: comparison is TOTAL
//! on classified binary64 operands — a NaN produces an ANSWER on both
//! executors, never a fault — so every row is exact twelve-value `Ret`
//! agreement ([`RunResult::Many`], the W3 vocabulary).
//!
//! ## Why the rows look like they do
//!
//! One body computes all 12 predicates, so a row's operand pair feeds the
//! whole ordered/unordered split at once. The input set's spine is the four
//! NaN quadrants the plan names — normal/normal (three orderings),
//! NaN/normal, normal/NaN, NaN/NaN — every one observed through all 12
//! predicates (strictly more than the plan's eq/lt minimum), plus the
//! signed-zero pair, an infinity row and the reversed negative ordering.
//! Operands cross the E1/E2 boundary as binary64 BIT PATTERNS (Clean's
//! `IRScalar.float_ n` carrier; trust-ir's `FloatBits`), spelled as raw
//! decimal literals per the W0/W1 large-literal rule — literals are not
//! names, and the kernel folds them natively (`wide_float`'s doc).
//!
//! Expectations are computed by [`fcmp12`], which restates the PINNED
//! interpreter's own formula (`eval_fcmp_f64`, trust-ir `a4e81b6`
//! `interpret.rs:6056-6072`) on host `f64` — the ground-truth semantics the
//! wave implements, stated once instead of 108 hand-copied Bools. The E2
//! smoke asserts the interpreter really computes it; the E1 probes measure
//! the Clean kernel against it on the big box.
//!
//! Cost offsets are DECLARED 0 on every row; the E2 half of that declaration
//! is measured here by `crystal_a3_w4_e2_instrument_smoke` (12 compares +
//! ret = 13 steps per row), and the E1 half (least fuel 13 and its
//! tightness) pends the big box (`data/evalir_w4.PENDING.md`).
//!
//! One boundary this lane does NOT measure, recorded not smoothed: the
//! pinned interpreter also answers `f32` compares (`eval_fcmp_f32`), where
//! Clean's fragment is binary64-only and tags `unmodelled float_domain`
//! (`ir_fcmp_f32_unmodelled`, kernel-witnessed). A refusal and an answer
//! share no row vocabulary, so no w=32 row exists — the fragment boundary
//! lives in the stage docs and the PENDING file, not in a silent gap.

use clean_verify::ir_semdiff::wide::{wide_args, wide_float, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::ty::Ty;

use super::synth_chains::{SynthChain, SynthExpect, SynthInput, SYNTHETIC_NO_E3};

/// The binary64 bit patterns the rows use, named once.
const ONE: u64 = 4_607_182_418_800_017_408; // 1.0
const TWO: u64 = 4_611_686_018_427_387_904; // 2.0
const M_ONE: u64 = 13_830_554_455_654_793_216; // -1.0
const M_TWO: u64 = 13_835_058_055_282_163_712; // -2.0
const P_ZERO: u64 = 0; // +0.0
const M_ZERO: u64 = 9_223_372_036_854_775_808; // -0.0
const P_INF: u64 = 9_218_868_437_227_405_312; // +inf
const Q_NAN: u64 = 9_221_120_237_041_090_560; // 0x7FF8000000000000

/// An `f64` argument value, from its bit pattern (deterministic — no host
/// NaN canonicalization can touch a pattern that is never an `f64` here).
fn iv_f64(bits: u64) -> InterpretValue {
    InterpretValue {
        ty: Ty::F64,
        kind: InterpretValueKind::FloatBits(bits),
    }
}

/// The twelve-predicate expectation in instruction order (oeq one olt ole
/// ogt oge ueq une ult ule ugt uge) — the pinned interpreter's formula
/// (`eval_fcmp_f64`, a4e81b6 `interpret.rs:6056-6072`) restated on host
/// `f64`: `unordered = l.is_nan() || r.is_nan()`; ordered arms are
/// `!unordered && cmp`, unordered arms `unordered || cmp`.
fn fcmp12(lhs_bits: u64, rhs_bits: u64) -> SynthExpect {
    let (l, r) = (f64::from_bits(lhs_bits), f64::from_bits(rhs_bits));
    let u = l.is_nan() || r.is_nan();
    let cmp = [l == r, l != r, l < r, l <= r, l > r, l >= r];
    let mut v: Vec<RunResult> = cmp.iter().map(|c| RunResult::Bool(!u && *c)).collect();
    v.extend(cmp.iter().map(|c| RunResult::Bool(u || *c)));
    SynthExpect::Ret(RunResult::Many(v))
}

/// The W4 chains, in measurement order.
pub fn w4_chains() -> Vec<SynthChain> {
    vec![fcmp_probe()]
}

/// `fcmp` — `%2..%13 = fcmp <op> f64 %0, %1`, twelve-value ret. Constructor
/// under measure: `fcmp` (+ the already-measured multi-value `ret`).
fn fcmp_probe() -> SynthChain {
    let case = |label, a: u64, b: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_float(a), wide_float(b)])
        ),
        trust_args: vec![iv_f64(a), iv_f64(b)],
        expect: fcmp12(a, b),
    };
    SynthChain {
        name: "synth_fcmp",
        fixtures: &[("synth/synth_fcmp.trust-ir.txt", "@synth::fcmp_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(924, vec![Ty::F64, Ty::F64], vec![Ty::Bool; 12])],
        clean_module: "ir_w4_fc_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w4_fc_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            // normal/normal, all three orderings.
            case("1 vs 2: ordered ascending", ONE, TWO),
            case("2 vs 1: ordered descending", TWO, ONE),
            case("1 vs 1: equal finites", ONE, ONE),
            // The NaN quadrants: left, right, both.
            case("NaN vs 1: left NaN splits the families", Q_NAN, ONE),
            case("1 vs NaN: right NaN splits them too", ONE, Q_NAN),
            case(
                "NaN vs NaN: identical patterns, still unordered",
                Q_NAN,
                Q_NAN,
            ),
            // The format's one many-to-one value.
            case("+0 vs -0: different bits, equal value", P_ZERO, M_ZERO),
            // Mixed signs across an infinity.
            case("-1 vs +inf: negative below the top", M_ONE, P_INF),
            // The negative side's reversed magnitude order.
            case("-2 vs -1: negative ordering reverses", M_TWO, M_ONE),
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
        assert_eq!(M_ONE, (-1.0f64).to_bits());
        assert_eq!(M_TWO, (-2.0f64).to_bits());
        assert_eq!(P_ZERO, 0.0f64.to_bits());
        assert_eq!(M_ZERO, (-0.0f64).to_bits());
        assert_eq!(P_INF, f64::INFINITY.to_bits());
        assert!(f64::from_bits(Q_NAN).is_nan());
    }

    /// The NaN quadrants really split the families, and the zeros really
    /// compare equal — the two facts the whole lane exists to measure,
    /// asserted on the expectation generator itself.
    #[test]
    fn test_fcmp12_carries_the_split() {
        let SynthExpect::Ret(RunResult::Many(nan_row)) = fcmp12(Q_NAN, ONE) else {
            panic!("fcmp12 must produce a Many expectation");
        };
        assert!(
            nan_row[..6].iter().all(|r| *r == RunResult::Bool(false)),
            "ordered on NaN must be all false: {nan_row:?}"
        );
        assert!(
            nan_row[6..].iter().all(|r| *r == RunResult::Bool(true)),
            "unordered on NaN must be all true: {nan_row:?}"
        );
        let SynthExpect::Ret(RunResult::Many(zeros)) = fcmp12(P_ZERO, M_ZERO) else {
            panic!("fcmp12 must produce a Many expectation");
        };
        // oeq/ole/oge true, one/olt/ogt false — and the unordered family
        // agrees on non-NaN operands.
        let want = [true, false, false, true, false, true];
        for (i, w) in want.iter().enumerate() {
            assert_eq!(zeros[i], RunResult::Bool(*w), "ordered zeros arm {i}");
            assert_eq!(zeros[i + 6], RunResult::Bool(*w), "unordered zeros arm {i}");
        }
    }
}
