// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The float-RESIDUE synthetic micro-modules** (the wave
//! `evalir_w4.PENDING.md` delta 5 named): three binary64 bodies putting the
//! seven answering residue operators under battery measurement — `fneg`/
//! `fabs` (one body, both sign ops on one operand), `ffloor`/`fceil`/
//! `ftrunc` (one body, all three roundings of one operand), `fmin`/`fmax`
//! (one body, both picks of one operand pair) — each returning every result
//! through the multi-value `ret`, the W4 fcmp shape.
//!
//! The semantics under measure landed in the same wave
//! ([`super::eval_ir_float_res`] — read its module doc for the ground truth,
//! the model status and the refused cells). Same lane discipline as W2a-W4:
//! authored micro-modules, kernel-executed `ir_fr*` witnesses including the
//! fault edge, synthetic `.trust-ir.txt` twins under `tests/fixtures/synth/`,
//! `Synthetic`-labeled battery rows
//! (`tests/crystal_a3_semdiff/wfr_chains.rs`) reading this stage's module
//! lines through the `ir_fr*_module_defs` re-exports.
//!
//! ## Why three modules and not one
//!
//! The refused cells differ per family, and a battery row measures a whole
//! module execution: a NaN operand ANSWERS under `fneg`/`fabs` (sign-bit
//! ops) and under one-sided `fmin`/`fmax`, but REFUSES under the rounding
//! family — so a NaN row through a fused body would refuse everything and
//! measure nothing. Splitting by refusal boundary lets the sign and minmax
//! lanes carry NaN rows while the rounding lane's NaN boundary stays where
//! it belongs: a kernel-witnessed refusal and a grid delta, not a battery
//! row.
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine. Witness fuels are
//! SUFFICIENT, not least (`ir_d4` over least 3; `ir_d5` over least 4); the
//! battery pins each row's least fuel from below. No new inductive and no
//! new relation lands in this wave, so the vacuity firewall's family list is
//! untouched by construction.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── fsign: f64 → (fneg, fabs) ──────────────────────────────────────────────
const SRC_IR_FRS_B0: &str = "def ir_frs_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.unop IRUnOp.fneg (IRTy.float_ 64) ir_d0) ir_d1) (ir_nd1 (IRInst.unop IRUnOp.fabs (IRTy.float_ 64) ir_d0) ir_d2) (ir_nd (IRInst.ret (ir_nl2 ir_d1 ir_d2))))";
const SRC_IR_FRS_FUNC: &str =
    "def ir_frs_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_frs_b0 ir_blk0)";
const SRC_IR_FRS_MODULE: &str = "def ir_frs_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_frs_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── fround: f64 → (ffloor, fceil, ftrunc) ──────────────────────────────────
const SRC_IR_FRR_B0: &str = "def ir_frr_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.unop IRUnOp.ffloor (IRTy.float_ 64) ir_d0) ir_d1) (ir_bd3 (ir_nd1 (IRInst.unop IRUnOp.fceil (IRTy.float_ 64) ir_d0) ir_d2) (ir_nd1 (IRInst.unop IRUnOp.ftrunc (IRTy.float_ 64) ir_d0) ir_d3) (ir_nd (IRInst.ret (IRList.cons Nat ir_d1 (ir_nl2 ir_d2 ir_d3))))))";
const SRC_IR_FRR_FUNC: &str =
    "def ir_frr_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_frr_b0 ir_blk0)";
const SRC_IR_FRR_MODULE: &str = "def ir_frr_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_frr_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── fminmax: f64 × f64 → (fmin, fmax) ──────────────────────────────────────
const SRC_IR_FRM_B0: &str = "def ir_frm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.binop IRBinOp.fmin (IRTy.float_ 64) ir_d0 ir_d1) ir_d2) (ir_nd1 (IRInst.binop IRBinOp.fmax (IRTy.float_ 64) ir_d0 ir_d1) ir_d3) (ir_nd (IRInst.ret (ir_nl2 ir_d2 ir_d3))))";
const SRC_IR_FRM_FUNC: &str = "def ir_frm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_frm_b0 ir_blk0)";
const SRC_IR_FRM_MODULE: &str = "def ir_frm_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_frm_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The fsign micro-module's definitions, in registration order.
#[must_use]
pub fn ir_frs_module_defs() -> &'static [&'static str] {
    &[SRC_IR_FRS_B0, SRC_IR_FRS_FUNC, SRC_IR_FRS_MODULE]
}

/// The fround micro-module's definitions, in registration order.
#[must_use]
pub fn ir_frr_module_defs() -> &'static [&'static str] {
    &[SRC_IR_FRR_B0, SRC_IR_FRR_FUNC, SRC_IR_FRR_MODULE]
}

/// The fminmax micro-module's definitions, in registration order.
#[must_use]
pub fn ir_frm_module_defs() -> &'static [&'static str] {
    &[SRC_IR_FRM_B0, SRC_IR_FRM_FUNC, SRC_IR_FRM_MODULE]
}

// ── whole-program witnesses (fuels sufficient, not least) ──────────────────
const SRC_IR_FRS_ON_NAN: &str = "def ir_frs_on_nan : Eq IROutcome (ir_eval ir_d4 ir_frs_module ir_d0 (ir_vl1 (IRScalar.float_ 9221120237041090560)) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 18444492273895866368) (ir_vl1 (IRScalar.float_ 9221120237041090560)))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 18444492273895866368) (ir_vl1 (IRScalar.float_ 9221120237041090560))))";
const SRC_IR_FRS_ON_MZERO: &str = "def ir_frs_on_mzero : Eq IROutcome (ir_eval ir_d4 ir_frs_module ir_d0 (ir_vl1 (IRScalar.float_ 9223372036854775808)) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 0) (ir_vl1 (IRScalar.float_ 0)))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 0) (ir_vl1 (IRScalar.float_ 0))))";
const SRC_IR_FRR_ON_NEG: &str = "def ir_frr_on_neg : Eq IROutcome (ir_eval ir_d5 ir_frr_module ir_d0 (ir_vl1 (IRScalar.float_ 13832806255468478464)) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 13835058055282163712) (IRList.cons IRScalar (IRScalar.float_ 13830554455654793216) (ir_vl1 (IRScalar.float_ 13830554455654793216))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 13835058055282163712) (IRList.cons IRScalar (IRScalar.float_ 13830554455654793216) (ir_vl1 (IRScalar.float_ 13830554455654793216)))))";
const SRC_IR_FRM_ON_NAN_LEFT: &str = "def ir_frm_on_nan_left : Eq IROutcome (ir_eval ir_d4 ir_frm_module ir_d0 (IRList.cons IRScalar (IRScalar.float_ 9221120237041090560) (ir_vl1 (IRScalar.float_ 4611686018427387904))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 4611686018427387904) (ir_vl1 (IRScalar.float_ 4611686018427387904)))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.float_ 4611686018427387904) (ir_vl1 (IRScalar.float_ 4611686018427387904))))";
const SRC_IR_FRS_NOT_FLOAT: &str = "def ir_frs_not_float (n : Nat) : Eq IROutcome (ir_eval ir_d4 ir_frs_module ir_d0 (ir_vl1 (IRScalar.int_ n)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_float) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_float)";

impl Specification {
    /// The float-residue micro-modules and their kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IRUnOp`/`IRBinOp`/
    /// `IRTy` syntax, the `ir_d0..ir_d16` numerals, the `ir_nd`/`ir_nd1`/
    /// `ir_bd3`/`ir_blk`/`ir_blk0`/`ir_nl0`/`ir_nl1`/`ir_nl2`/`ir_vl1`
    /// builders, `ir_mem0`, the residue evaluators (via
    /// `ir_unop_eval`/`ir_binop_eval`), and the machine (`ir_eval`,
    /// `IROutcome`, `IRFault`). Deliberately nothing from any chain stage, so
    /// the battery can register the module lines standalone into the minimal
    /// `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the
    /// machine and got a different outcome, which is a red to report, never
    /// to tune.
    pub(super) fn add_eval_ir_wfr_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_FRS_B0, "ir_frs_b0: SYNTHETIC micro-module entry (float residue, sign ops): fneg and fabs of the SAME f64 parameter, then the two-value ret — both sign-bit operations observed on one operand per row, NaN rows included (a bit operation answers on NaNs). DerivedProved, zero axiom_deps."),
            (SRC_IR_FRS_FUNC, "ir_frs_func: one parameter (SSA id 0), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRS_MODULE, "ir_frs_module: the SYNTHETIC sign-op module — authored for the float-residue differential (E2 twin tests/fixtures/synth/synth_fsign.trust-ir.txt); no producer emitted it and no lineage gate applies. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRR_B0, "ir_frr_b0: SYNTHETIC micro-module entry (float residue, rounding): ffloor, fceil and ftrunc of the SAME f64 parameter, then the three-value ret — one row observes all three rounding directions at once, which is how the away-from-zero split stays visible as a CONTRAST (floor(-1.5) = -2 beside ceil(-1.5) = -1). No NaN row by design: the rounding family REFUSES NaNs (payload), and that boundary is a kernel witness plus a grid delta, not a battery row. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRR_FUNC, "ir_frr_func: one parameter (SSA id 0), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRR_MODULE, "ir_frr_module: the SYNTHETIC rounding module — authored for the float-residue differential (E2 twin tests/fixtures/synth/synth_fround.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_FRM_B0, "ir_frm_b0: SYNTHETIC micro-module entry (float residue, minmax): fmin and fmax of the SAME two f64 parameters, then the two-value ret — the pick pair observed together, so a row shows min and max choosing OPPOSITE operands. Rows avoid the two refused cells (both-NaN, opposite zeros); those are kernel witnesses and grid deltas. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRM_FUNC, "ir_frm_func: two parameters (SSA ids 0,1), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRM_MODULE, "ir_frm_module: the SYNTHETIC minmax module — authored for the float-residue differential (E2 twin tests/fixtures/synth/synth_fminmax.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_FRS_ON_NAN, "ir_frs_on_nan: qNaN through the sign module — fneg flips the sign bit and fabs clears it, PAYLOAD PRESERVED in both: the row that shows the sign family answering where every arithmetic lane refuses. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRS_ON_MZERO, "ir_frs_on_mzero: -0.0 through the sign module — fneg(-0) = +0 and fabs(-0) = +0, the zero pair as two bit flips. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRR_ON_NEG, "ir_frr_on_neg: -1.5 through the rounding module — floor -2.0, ceil -1.0, trunc -1.0 in one execution: the away-from-zero split on the negative side, where a sign-blind rounding gets floor and ceil exchanged. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRM_ON_NAN_LEFT, "ir_frm_on_nan_left: (NaN, 2.0) through the minmax module — BOTH picks return 2.0: one NaN operand is ignored and the other operand returned, minNum/maxNum's defining rule, executed by the kernel through the full dispatch. DerivedProved, zero axiom_deps."),
            (SRC_IR_FRS_NOT_FLOAT, "ir_frs_not_float: FAULT EDGE — an integer operand halts the sign module at the FIRST unop with `type_error not_float`, at every payload n: ir_float1's coercion rejects int_ by iota on the constructor. Universally quantified, the ir_w4_fc_not_float precedent. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Clean ret-payload spine for a list of f64 bit patterns, as the
    /// witnesses spell it.
    fn float_spine(bits: &[u64]) -> String {
        let mut s = format!("(ir_vl1 (IRScalar.float_ {}))", bits[bits.len() - 1]);
        for b in bits[..bits.len() - 1].iter().rev() {
            s = format!("(IRList.cons IRScalar (IRScalar.float_ {b}) {s})");
        }
        s
    }

    /// **Every whole-program witness's ret spine is regenerated from the
    /// pinned interpreter's own formulas on host `f64`** (`eval_float_unop` /
    /// `eval_float_binop`, F64 arms: `-x`/`abs`/`floor`/`ceil`/`trunc`,
    /// `min`/`max`) and must match the const exactly — a transcription slip
    /// fails on this box instead of breaking every big-box spec build.
    #[test]
    fn test_the_witness_spines_agree_with_real_f64() {
        let b = f64::from_bits;
        let nan = b(9_221_120_237_041_090_560);
        let mzero = b(9_223_372_036_854_775_808);
        let mopf = b(13_832_806_255_468_478_464); // -1.5
        let two = b(4_611_686_018_427_387_904);

        let cases: &[(&str, Vec<u64>)] = &[
            (
                SRC_IR_FRS_ON_NAN,
                vec![(-nan).to_bits(), nan.abs().to_bits()],
            ),
            (
                SRC_IR_FRS_ON_MZERO,
                vec![(-mzero).to_bits(), mzero.abs().to_bits()],
            ),
            (
                SRC_IR_FRR_ON_NEG,
                vec![
                    mopf.floor().to_bits(),
                    mopf.ceil().to_bits(),
                    mopf.trunc().to_bits(),
                ],
            ),
            (
                SRC_IR_FRM_ON_NAN_LEFT,
                vec![nan.min(two).to_bits(), nan.max(two).to_bits()],
            ),
        ];
        for (src, bits) in cases {
            let spine = format!("(IROutcome.ret {})", float_spine(bits));
            assert_eq!(
                src.matches(&spine).count(),
                2,
                "the witness must carry the host-f64 spine twice (statement and refl term); \
                 wanted {spine} in {src}"
            );
        }
    }

    /// Each block const is exactly the generated right-nested spine — the
    /// operators in declaration order, one result id each, and the
    /// multi-value ret. Nesting checked by regeneration, not by eye.
    #[test]
    fn test_the_block_spines_are_the_generated_ones() {
        let sign = format!(
            "def ir_frs_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 {} {} {})",
            "(ir_nd1 (IRInst.unop IRUnOp.fneg (IRTy.float_ 64) ir_d0) ir_d1)",
            "(ir_nd1 (IRInst.unop IRUnOp.fabs (IRTy.float_ 64) ir_d0) ir_d2)",
            "(ir_nd (IRInst.ret (ir_nl2 ir_d1 ir_d2)))"
        );
        assert_eq!(SRC_IR_FRS_B0, sign);
        let round = format!(
            "def ir_frr_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode {} (ir_bd3 {} {} {}))",
            "(ir_nd1 (IRInst.unop IRUnOp.ffloor (IRTy.float_ 64) ir_d0) ir_d1)",
            "(ir_nd1 (IRInst.unop IRUnOp.fceil (IRTy.float_ 64) ir_d0) ir_d2)",
            "(ir_nd1 (IRInst.unop IRUnOp.ftrunc (IRTy.float_ 64) ir_d0) ir_d3)",
            "(ir_nd (IRInst.ret (IRList.cons Nat ir_d1 (ir_nl2 ir_d2 ir_d3))))"
        );
        assert_eq!(SRC_IR_FRR_B0, round);
        let minmax = format!(
            "def ir_frm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 {} {} {})",
            "(ir_nd1 (IRInst.binop IRBinOp.fmin (IRTy.float_ 64) ir_d0 ir_d1) ir_d2)",
            "(ir_nd1 (IRInst.binop IRBinOp.fmax (IRTy.float_ 64) ir_d0 ir_d1) ir_d3)",
            "(ir_nd (IRInst.ret (ir_nl2 ir_d2 ir_d3)))"
        );
        assert_eq!(SRC_IR_FRM_B0, minmax);
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_IR_FRS_B0,
            SRC_IR_FRS_FUNC,
            SRC_IR_FRS_MODULE,
            SRC_IR_FRR_B0,
            SRC_IR_FRR_FUNC,
            SRC_IR_FRR_MODULE,
            SRC_IR_FRM_B0,
            SRC_IR_FRM_FUNC,
            SRC_IR_FRM_MODULE,
            SRC_IR_FRS_ON_NAN,
            SRC_IR_FRS_ON_MZERO,
            SRC_IR_FRR_ON_NEG,
            SRC_IR_FRM_ON_NAN_LEFT,
            SRC_IR_FRS_NOT_FLOAT,
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
