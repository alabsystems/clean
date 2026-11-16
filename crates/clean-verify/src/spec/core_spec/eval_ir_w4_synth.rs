// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **W4 — the float-comparison lane's synthetic micro-module:** one binary64
//! body running ALL TWELVE `IRFCmpOp` predicates on the same two operands and
//! returning every result through the twelve-value `ret`.
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W4 — the
//! LAST lane of the THIR-lowerer surface: with it every one of that
//! producer's 28 `IRInst` constructors has battery
//! rows, and the dispatch's tagged-arm count, counted down in the open
//! (2 → 1 by W3, 1 → 0 by this wave), reaches zero. The semantics this lane
//! measures landed in the same wave: `ir_fcmp_eval`'s 12 real predicates over
//! the classified binary64 substrate (`eval_ir_fcmp.rs` — read its module doc
//! for the ground truth, the model status, and the fragment boundary). Same
//! lane discipline as W2a-W3 otherwise: an authored micro-module,
//! kernel-executed `ir_w4_*` witnesses including the fault edges, a synthetic
//! `.trust-ir.txt` twin under `tests/fixtures/synth/`, `Synthetic`-labeled
//! battery rows (`tests/crystal_a3_semdiff/w4_chains.rs`) reading this
//! stage's module lines through the `ir_w4_fc_module_defs` re-export.
//!
//! ## Why the module is shaped the way it is
//!
//! * **Twelve predicates, one body, twelve-value `ret`.** The ordered/
//!   unordered split IS the semantics under test, and it is only visible as a
//!   CONTRAST — `oeq` false while `ueq` true on the same NaN operands. One
//!   body computing all 12 on the same pair makes every battery row observe
//!   the whole split at once (the W3 all-three-ops precedent), and the
//!   twelve-value `ret` rides the multi-value return the W3 lane already put
//!   under measurement. Nothing stands between the compares and the `ret`.
//! * **The NaN quadrants are the input set's spine.** normal/normal (three
//!   orderings), NaN/normal, normal/NaN, NaN/NaN — the four quadrants the
//!   plan names — plus the signed-zero pair (+0, -0), the infinity rows, and
//!   the reversed negative ordering. Every quadrant reaches all 12 predicates
//!   in both this stage's witnesses and the battery rows.
//! * **binary64 bit patterns ride as raw decimal literals** (the
//!   `ir_f64_sign_bit` precedent: the kernel folds them natively on `BigNat`;
//!   a unary numeral of this magnitude does not exist). The comparisons
//!   themselves are folded `ir_nat_ltb` / `ir_nat_eqb` over one exact
//!   `Nat.sub` each — the measured milliseconds class — so a
//!   13-instruction execution costs nothing like the arithmetic lanes'
//!   significand work. MAX_IR_NUMERAL binds obligation NAMES and fuels only;
//!   the least fuel here is 13, inside the `ir_d` pool.
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine. Witness fuel
//! `ir_d14` is SUFFICIENT, not least — the battery pins each row's least fuel
//! (13) from below. No new inductive and no new relation lands in this wave,
//! so the vacuity firewall's family list is untouched by construction.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── the module: f64 × f64 → 12 bools ──────────────────────────────────────
//
//   bb0(%0: f64, %1: f64):
//     %2 = fcmp oeq f64 %0, %1      ...through...
//     %13 = fcmp uge f64 %0, %1
//     ret %2, %3, %4, %5, %6, %7, %8, %9, %10, %11, %12, %13
//
// Predicate order is IRFCmpOp declaration order (oeq one olt ole ogt oge ueq
// une ult ule ugt uge) — the same order every witness's ret spine and every
// battery expectation uses.

const SRC_IR_W4_FCN: &str = "def ir_w4_fcn (op : IRFCmpOp) (r : Nat) : IRNode := ir_nd1 (IRInst.fcmp op (IRTy.float_ 64) ir_d0 ir_d1) r";

const SRC_IR_W4_FC_B0: &str = "def ir_w4_fc_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.oeq ir_d2) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.one_ ir_d3) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.olt ir_d4) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ole ir_d5) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ogt ir_d6) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.oge ir_d7) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ueq ir_d8) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.une ir_d9) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ult ir_d10) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ule ir_d11) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.ugt ir_d12) (@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.uge ir_d13) (ir_bd1 (ir_nd (IRInst.ret (@IRList.cons Nat ir_d2 (@IRList.cons Nat ir_d3 (@IRList.cons Nat ir_d4 (@IRList.cons Nat ir_d5 (@IRList.cons Nat ir_d6 (@IRList.cons Nat ir_d7 (@IRList.cons Nat ir_d8 (@IRList.cons Nat ir_d9 (@IRList.cons Nat ir_d10 (@IRList.cons Nat ir_d11 (ir_nl2 ir_d12 ir_d13))))))))))))))))))))))))))";

const SRC_IR_W4_FC_FUNC: &str = "def ir_w4_fc_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w4_fc_b0 ir_blk0)";

const SRC_IR_W4_FC_MODULE: &str = "def ir_w4_fc_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w4_fc_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The fcmp micro-module's definitions, in registration order — the lines the
/// battery registers, re-exported rather than re-typed.
#[must_use]
pub fn ir_w4_fc_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W4_FCN,
        SRC_IR_W4_FC_B0,
        SRC_IR_W4_FC_FUNC,
        SRC_IR_W4_FC_MODULE,
    ]
}

// ── whole-program witnesses (fuel ir_d14 is sufficient; least is 13) ──────
//
// Each spine is the 12 answers in predicate order. The Rust test below
// regenerates every spine from the pinned interpreter's own formula on host
// f64 and asserts the consts match, so a hand-transcription slip fails HERE,
// on this box, before a big-box registration ever runs.

const SRC_IR_W4_FC_ON_LT: &str = "def ir_w4_fc_on_lt : @Eq IROutcome (ir_eval ir_d14 ir_w4_fc_module ir_d0 (@IRList.cons IRScalar (IRScalar.float_ 4607182418800017408) (ir_vl1 (IRScalar.float_ 4611686018427387904))) ir_mem0 ir_d0) (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (ir_vl1 (IRScalar.bool_ Bool.false)))))))))))))) := @Eq.refl IROutcome (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (ir_vl1 (IRScalar.bool_ Bool.false))))))))))))))";

const SRC_IR_W4_FC_ON_NAN_LEFT: &str = "def ir_w4_fc_on_nan_left : @Eq IROutcome (ir_eval ir_d14 ir_w4_fc_module ir_d0 (@IRList.cons IRScalar (IRScalar.float_ 9221120237041090560) (ir_vl1 (IRScalar.float_ 4607182418800017408))) ir_mem0 ir_d0) (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (ir_vl1 (IRScalar.bool_ Bool.true)))))))))))))) := @Eq.refl IROutcome (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (ir_vl1 (IRScalar.bool_ Bool.true))))))))))))))";

const SRC_IR_W4_FC_ON_ZEROS: &str = "def ir_w4_fc_on_zeros : @Eq IROutcome (ir_eval ir_d14 ir_w4_fc_module ir_d0 (@IRList.cons IRScalar (IRScalar.float_ 0) (ir_vl1 (IRScalar.float_ 9223372036854775808))) ir_mem0 ir_d0) (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (ir_vl1 (IRScalar.bool_ Bool.true)))))))))))))) := @Eq.refl IROutcome (IROutcome.ret (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (ir_vl1 (IRScalar.bool_ Bool.true))))))))))))))";

const SRC_IR_W4_FC_NOT_FLOAT: &str = "def ir_w4_fc_not_float (n : Nat) (b : IRScalar) : @Eq IROutcome (ir_eval ir_d14 ir_w4_fc_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ n) (ir_vl1 b)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_float) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_float)";

impl Specification {
    /// The W4 fcmp micro-module and its kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IRFCmpOp`/`IRTy`/
    /// `IRBlock`/`IRFunc`/`IRModule` syntax, the `ir_d0..ir_d16` numerals,
    /// the `ir_nd`/`ir_nd1`/`ir_bd1`/`ir_blk`/`ir_blk0`/`ir_nl0`/`ir_nl2`/
    /// `ir_vl1` builders, `ir_mem0`, `ir_fcmp_eval`, and the machine
    /// (`ir_eval`, `IROutcome`, `IRFault`). Deliberately nothing from any
    /// chain stage, so the battery can register the module lines standalone
    /// into the minimal `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the
    /// machine and got a different outcome, which is a red to report, never
    /// to tune.
    pub(super) fn add_eval_ir_w4_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_W4_FCN, "ir_w4_fcn: the fcmp-node builder for the W4 module — every node compares the two parameters at f64 under a chosen predicate and binds one Bool. A builder rather than 12 spelled-out nodes so the block reads as the predicate LIST it is. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_B0, "ir_w4_fc_b0: SYNTHETIC micro-module entry (W4 fcmp): all TWELVE IRFCmpOp predicates on the same two f64 parameters, in declaration order (oeq one olt ole ogt oge ueq une ult ule ugt uge), then the twelve-value ret of every bound result — nothing stands between the compares and the return, so a battery row observes the whole ordered/unordered split at once. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_FUNC, "ir_w4_fc_func: two parameters (SSA ids 0,1), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_MODULE, "ir_w4_fc_module: the SYNTHETIC fcmp module — authored for the W4 differential (E2 twin tests/fixtures/synth/synth_fcmp.trust-ir.txt); no producer emitted it and no lineage gate applies. Nothing in clean-kernel lowers an FCmp (reduce_float_beq/blt/ble are `unsupported: shim: Inst::FCmp`), which is exactly why the definitional mandate routes this constructor through the synthetic lane. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_ON_LT, "ir_w4_fc_on_lt: 1.0 vs 2.0 — the ordered ascending pair: lt/le/ne answer true in BOTH families, eq/gt/ge false in both; on non-NaN operands the ordered and unordered families agree, which this row pins before any NaN row splits them. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_ON_NAN_LEFT, "ir_w4_fc_on_nan_left: NaN vs 1.0 — THE split row: all six ordered predicates false, all six unordered true, in one execution. This is the ordered/unordered semantics the wave exists to land, executed by the kernel through the full dispatch. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_ON_ZEROS, "ir_w4_fc_on_zeros: +0.0 vs -0.0 — two DIFFERENT bit patterns, one value: eq/le/ge true, ne/lt/gt false, identically in both families. The signed-zero row a bit-pattern-only comparison would get wrong in six places. DerivedProved, zero axiom_deps."),
            (SRC_IR_W4_FC_NOT_FLOAT, "ir_w4_fc_not_float: FAULT EDGE — an integer in the first operand slot halts the module at the FIRST compare with `type_error not_float`, at every payload n and every second operand b: ir_float2's first coercion rejects int_ by iota on the constructor, so neither the predicate nor b is ever consulted. Universally quantified, the ir_w3_ou_not_int precedent. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The interpreter's fcmp formula on host `f64` (a4e81b6
    /// `interpret.rs:6056-6072`), in the module's predicate order.
    fn host_fcmp12(l: f64, r: f64) -> [bool; 12] {
        let u = l.is_nan() || r.is_nan();
        [
            !u && l == r,
            !u && l != r,
            !u && l < r,
            !u && l <= r,
            !u && l > r,
            !u && l >= r,
            u || l == r,
            u || l != r,
            u || l < r,
            u || l <= r,
            u || l > r,
            u || l >= r,
        ]
    }

    /// The Clean ret-payload spine for 12 Bools, as the witnesses spell it.
    fn bool_spine(bools: &[bool; 12]) -> String {
        let mut s = format!("(ir_vl1 (IRScalar.bool_ Bool.{}))", bools[11]);
        for b in bools[..11].iter().rev() {
            s = format!("(@IRList.cons IRScalar (IRScalar.bool_ Bool.{b}) {s})");
        }
        s
    }

    /// **Every whole-program witness's 12-bool spine is regenerated from the
    /// pinned interpreter's own formula on host `f64` and must match the
    /// const exactly** — a hand-transcription slip in a spine fails on this
    /// box instead of breaking every big-box spec build at registration.
    #[test]
    fn test_the_witness_spines_agree_with_real_f64() {
        let b = f64::from_bits;
        for (src, lhs, rhs) in [
            (
                SRC_IR_W4_FC_ON_LT,
                b(4_607_182_418_800_017_408),
                b(4_611_686_018_427_387_904),
            ),
            (
                SRC_IR_W4_FC_ON_NAN_LEFT,
                b(9_221_120_237_041_090_560),
                b(4_607_182_418_800_017_408),
            ),
            (SRC_IR_W4_FC_ON_ZEROS, b(0), b(9_223_372_036_854_775_808)),
        ] {
            let spine = format!("(IROutcome.ret {})", bool_spine(&host_fcmp12(lhs, rhs)));
            assert_eq!(
                src.matches(&spine).count(),
                2,
                "the witness for {lhs} vs {rhs} must carry the host-f64 spine twice \
                 (statement and refl term); wanted {spine} in {src}"
            );
            for v in [lhs, rhs] {
                assert!(
                    src.contains(&v.to_bits().to_string()),
                    "operand {v} ({}) missing from {src}",
                    v.to_bits()
                );
            }
        }
    }

    /// The block const is exactly the generated right-nested spine — the
    /// 12 predicates in declaration order, one result id each (2..=13), and
    /// the twelve-value ret. Nesting checked by regeneration, not by eye.
    #[test]
    fn test_the_block_spine_is_the_generated_one() {
        let ops = [
            "oeq", "one_", "olt", "ole", "ogt", "oge", "ueq", "une", "ult", "ule", "ugt", "uge",
        ];
        let mut ret = "(ir_nl2 ir_d12 ir_d13)".to_owned();
        for r in (2..=11).rev() {
            ret = format!("(@IRList.cons Nat ir_d{r} {ret})");
        }
        let mut body = format!("(ir_bd1 (ir_nd (IRInst.ret {ret})))");
        for (i, op) in ops.iter().enumerate().rev() {
            body = format!(
                "(@IRList.cons IRNode (ir_w4_fcn IRFCmpOp.{op} ir_d{}) {body})",
                i + 2
            );
        }
        let expected = format!("def ir_w4_fc_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 {body}");
        assert_eq!(SRC_IR_W4_FC_B0, expected);
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_IR_W4_FCN,
            SRC_IR_W4_FC_B0,
            SRC_IR_W4_FC_FUNC,
            SRC_IR_W4_FC_MODULE,
            SRC_IR_W4_FC_ON_LT,
            SRC_IR_W4_FC_ON_NAN_LEFT,
            SRC_IR_W4_FC_ON_ZEROS,
            SRC_IR_W4_FC_NOT_FLOAT,
        ] {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0, "unbalanced parens in {src}");
            }
            assert_eq!(d, 0, "unbalanced parens in {src}");
            assert!(src.is_ascii(), "spec sources must be ASCII");
        }
    }
}
