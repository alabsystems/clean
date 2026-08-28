// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — the float RESIDUE band's kernel-EXECUTED witnesses, the pin on
//! its one duplicated definition, and the wave's DATED REFUSALS as
//! kernel-witnessed UNIVERSAL statements.
//!
//! Read [`super::eval_ir_float_res`]'s module doc first: it states the ground
//! truth (trust-ir `a4e81b6`), what answers, what refuses, and why. This file
//! is the evidence: every answering rule gets an executed `Eq.refl` through
//! the real dispatchers (`ir_unop_eval` / `ir_binop_eval`), every refusal is
//! a REGISTERED universal statement in the `ir_fcmp_f32_unmodelled` idiom —
//! a refusal that is silence is indistinguishable from a gap, and these are
//! not gaps — and the Rust tests below cross-check each answering witness
//! against host `f64` through the pinned interpreter's own formulas, so a
//! transcription slip fails on the authoring box before any big-box
//! registration runs.
//!
//! Registered from `add_eval_ir_ops` AFTER `add_eval_ir_compare`: the
//! executed witnesses run through the arithmetic dispatchers (declared by
//! `add_eval_ir_arith`) and the duplication pin needs the comparison band's
//! `ir_f64_ltb` (declared inside `add_eval_ir_compare`). The eight fp-cast
//! refusals live in their own registration hook at the END of
//! `add_eval_ir_cast`, beside the dispatcher they bound.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── the bit patterns, once (the eval_ir_fcmp.rs table, extended) ───────────
//   1.0   = 4607182418800017408      -1.0  = 13830554455654793216
//   2.0   = 4611686018427387904      -2.0  = 13835058055282163712
//   1.5   = 4609434218613702656      -1.5  = 13832806255468478464
//   0.5   = 4602678819172646912      -0.5  = 13826050856027422720
//   +0.0  = 0                        -0.0  = 9223372036854775808
//   +inf  = 9218868437227405312      -inf  = 18442240474082181120
//   qNaN  = 9221120237041090560      -qNaN = 18444492273895866368
//   junk  = 18446744073709551616 (2^64)
//   1.9999999999999998 = 4611686018427387903 (the ceil-carry edge)

// ── fneg / fabs: the sign-bit operations ───────────────────────────────────
const SRC_WR_FNEG_ONE: &str = "def ir_exact_fneg_one : Eq IRStepResult (ir_unop_eval IRUnOp.fneg (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.float_ 13830554455654793216)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13830554455654793216))";
const SRC_WR_FNEG_MZERO: &str = "def ir_exact_fneg_mzero : Eq IRStepResult (ir_unop_eval IRUnOp.fneg (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808)) (IRStepResult.value (IRScalar.float_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 0))";
const SRC_WR_FNEG_NAN: &str = "def ir_exact_fneg_nan : Eq IRStepResult (ir_unop_eval IRUnOp.fneg (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.float_ 18444492273895866368)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 18444492273895866368))";
const SRC_WR_FNEG_JUNK: &str = "def ir_exact_fneg_junk_refused : Eq IRStepResult (ir_unop_eval IRUnOp.fneg (IRTy.float_ 64) (IRScalar.float_ 18446744073709551616)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WR_FABS_MONE: &str = "def ir_exact_fabs_mone : Eq IRStepResult (ir_unop_eval IRUnOp.fabs (IRTy.float_ 64) (IRScalar.float_ 13830554455654793216)) (IRStepResult.value (IRScalar.float_ 4607182418800017408)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4607182418800017408))";
const SRC_WR_FABS_MZERO: &str = "def ir_exact_fabs_mzero : Eq IRStepResult (ir_unop_eval IRUnOp.fabs (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808)) (IRStepResult.value (IRScalar.float_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 0))";
const SRC_WR_FABS_NAN_NEG: &str = "def ir_exact_fabs_nan_neg : Eq IRStepResult (ir_unop_eval IRUnOp.fabs (IRTy.float_ 64) (IRScalar.float_ 18444492273895866368)) (IRStepResult.value (IRScalar.float_ 9221120237041090560)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9221120237041090560))";

// ── fmin / fmax: the NaN-ignoring minimum/maximum ──────────────────────────
const SRC_WR_FMIN_ORD: &str = "def ir_exact_fmin_ordered : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) (IRStepResult.value (IRScalar.float_ 4607182418800017408)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4607182418800017408))";
const SRC_WR_FMAX_ORD: &str = "def ir_exact_fmax_ordered : Eq IRStepResult (ir_binop_eval IRBinOp.fmax (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WR_FMIN_NEG: &str = "def ir_exact_fmin_neg_pair : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 13835058055282163712) (IRScalar.float_ 13830554455654793216)) (IRStepResult.value (IRScalar.float_ 13835058055282163712)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13835058055282163712))";
const SRC_WR_FMIN_NAN_L: &str = "def ir_exact_fmin_nan_left : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4611686018427387904)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WR_FMAX_NAN_R: &str = "def ir_exact_fmax_nan_right : Eq IRStepResult (ir_binop_eval IRBinOp.fmax (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WR_FMIN_NINF: &str = "def ir_exact_fmin_ninf : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 18442240474082181120) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.float_ 18442240474082181120)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 18442240474082181120))";
const SRC_WR_FMIN_NAN_BOTH: &str = "def ir_exact_fmin_nan_both_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 9221120237041090560)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WR_FMIN_ZPAIR: &str = "def ir_exact_fmin_zero_pair_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 64) (IRScalar.float_ 0) (IRScalar.float_ 9223372036854775808)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WR_FMAX_ZPAIR: &str = "def ir_exact_fmax_zero_pair_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fmax (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";

// ── ffloor / fceil / ftrunc: exponent-guided integer rounding ──────────────
const SRC_WR_FLOOR_POS: &str = "def ir_exact_ffloor_pos : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 4609434218613702656)) (IRStepResult.value (IRScalar.float_ 4607182418800017408)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4607182418800017408))";
const SRC_WR_FLOOR_NEG: &str = "def ir_exact_ffloor_neg : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 13832806255468478464)) (IRStepResult.value (IRScalar.float_ 13835058055282163712)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13835058055282163712))";
const SRC_WR_CEIL_NEG: &str = "def ir_exact_fceil_neg : Eq IRStepResult (ir_unop_eval IRUnOp.fceil (IRTy.float_ 64) (IRScalar.float_ 13832806255468478464)) (IRStepResult.value (IRScalar.float_ 13830554455654793216)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13830554455654793216))";
const SRC_WR_TRUNC_NEG: &str = "def ir_exact_ftrunc_neg : Eq IRStepResult (ir_unop_eval IRUnOp.ftrunc (IRTy.float_ 64) (IRScalar.float_ 13832806255468478464)) (IRStepResult.value (IRScalar.float_ 13830554455654793216)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13830554455654793216))";
const SRC_WR_FLOOR_SMALL_NEG: &str = "def ir_exact_ffloor_small_neg : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 13826050856027422720)) (IRStepResult.value (IRScalar.float_ 13830554455654793216)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 13830554455654793216))";
const SRC_WR_CEIL_SMALL_NEG: &str = "def ir_exact_fceil_small_neg_keeps_mzero : Eq IRStepResult (ir_unop_eval IRUnOp.fceil (IRTy.float_ 64) (IRScalar.float_ 13826050856027422720)) (IRStepResult.value (IRScalar.float_ 9223372036854775808)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9223372036854775808))";
const SRC_WR_TRUNC_SMALL_POS: &str = "def ir_exact_ftrunc_small_pos : Eq IRStepResult (ir_unop_eval IRUnOp.ftrunc (IRTy.float_ 64) (IRScalar.float_ 4602678819172646912)) (IRStepResult.value (IRScalar.float_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 0))";
const SRC_WR_CEIL_CARRY: &str = "def ir_exact_fceil_carry : Eq IRStepResult (ir_unop_eval IRUnOp.fceil (IRTy.float_ 64) (IRScalar.float_ 4611686018427387903)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WR_FLOOR_INT: &str = "def ir_exact_ffloor_already_int : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WR_FLOOR_MZERO: &str = "def ir_exact_ffloor_mzero : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808)) (IRStepResult.value (IRScalar.float_ 9223372036854775808)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9223372036854775808))";
const SRC_WR_FLOOR_INF: &str = "def ir_exact_ffloor_inf : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 9218868437227405312)) (IRStepResult.value (IRScalar.float_ 9218868437227405312)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9218868437227405312))";
const SRC_WR_FLOOR_NAN: &str = "def ir_exact_ffloor_nan_refused : Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";

impl Specification {
    /// The residue band's executed witnesses, the duplication pin, and the
    /// non-cast dated refusals as universal statements.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the
    /// operation and disagreed, which is a red to report, never to tune.
    pub(super) fn add_eval_ir_float_res_witnesses(&mut self) -> Result<(), SpecError> {
        // ── the duplication pin, at universally quantified operands ────
        self.add_recursive_def(
            concat!(
                "def ir_f64_ltb_pre_agrees (a : Nat) (b : Nat) : ",
                "Eq Bool (ir_f64_ltb a b) (ir_f64_ltb_pre a b) := ",
                "Eq.refl Bool (ir_f64_ltb_pre a b)",
            ),
            "THE PIN ON THE BAND'S ONE DUPLICATED DEFINITION: the residue band's value order \
             (ir_f64_ltb_pre, registered before the arithmetic dispatchers because fmin/fmax \
             need it there) and the comparison band's ir_f64_ltb are DEFINITIONALLY EQUAL at \
             every operand pair — the kernel discharges this by unfolding both spellings, so \
             any drift between the two fails every spec build rather than becoming two lanes \
             that disagree about the order. DerivedProved, zero axiom_deps.",
        )?;

        // ── fneg / fabs ────────────────────────────────────────────────
        self.add_recursive_def(SRC_WR_FNEG_ONE, "fneg 1.0 = -1.0 through the machine: the sign bit flips, nothing else moves. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FNEG_MZERO, "fneg -0.0 = +0.0: negate is exact on the zeros — the pair the arithmetic lane's signed-zero rules guard is just a bit flip here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FNEG_NAN, "fneg qNaN = -qNaN, PAYLOAD PRESERVED — the row that shows why fneg answers where fadd refuses: negate is a quiet bit operation (IEEE 754 5.5.1) with no payload freedom, so the NaN result is fully determined. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FNEG_JUNK, "fneg (2^64) is REFUSED: a junk carrier has no sign bit to flip, and flipping bit 63 of it would mint a valid-looking pattern out of garbage — the one fneg refusal, at exactly the ir_f64_is_pattern boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FABS_MONE, "fabs -1.0 = 1.0: clear the sign bit — literally ir_f64_mag. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FABS_MZERO, "fabs -0.0 = +0.0: the magnitude view collapses the format's two zeros to the positive one, which is abs's job. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FABS_NAN_NEG, "fabs -qNaN = qNaN, payload preserved: abs answers on NaNs for the same 5.5.1 reason negate does. DerivedProved, zero axiom_deps.")?;

        // ── fmin / fmax ────────────────────────────────────────────────
        self.add_recursive_def(SRC_WR_FMIN_ORD, "fmin 1.0 2.0 = 1.0: the ordered cell picks an OPERAND via the value order — minNum's basic case, executed through the typed dispatcher. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_WR_FMAX_ORD,
            "fmax 1.0 2.0 = 2.0: the mirrored pick. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_WR_FMIN_NEG, "fmin -2.0 -1.0 = -2.0: on the negative side the magnitude order reverses, and the pick follows the VALUE order — the arm a bare bit-pattern comparison would get backwards (the ir_exact_fcmp_olt_neg row's minmax twin). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMIN_NAN_L, "fmin NaN 2.0 = 2.0: one NaN operand is IGNORED and the other operand returned — minNum's defining rule (trust-ir runs host f64::min, which documents exactly this). The answer is determined, so the model answers; contrast the both-NaN row below. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMAX_NAN_R, "fmax 2.0 NaN = 2.0: the right-NaN side of the same rule, through fmax. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMIN_NINF, "fmin -inf 1.0 = -inf: infinities are ordered values and the pick transports the operand pattern. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMIN_NAN_BOTH, "fmin NaN NaN is REFUSED: with BOTH operands NaN the result is *a* NaN whose payload is implementation-defined — the arithmetic lane's exact rule, and the reason the NaN/NaN cell is the one NaN cell that does not answer. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMIN_ZPAIR, "fmin +0.0 -0.0 is REFUSED: llvm.minnum may return EITHER zero when the operands compare equal, so any answer here could be refuted by a conforming host — the tagged refusal cannot. Recorded as this wave's minmax-ambiguous-cells delta (the grid row); no battery row exists for it by design. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FMAX_ZPAIR, "fmax -0.0 +0.0 is REFUSED, the same ambiguous cell through fmax and with the operands exchanged. DerivedProved, zero axiom_deps.")?;

        // ── ffloor / fceil / ftrunc ────────────────────────────────────
        self.add_recursive_def(SRC_WR_FLOOR_POS, "ffloor 1.5 = 1.0: the mid-range arm clears the 52 fractional bits (k = 1075 - 1023). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FLOOR_NEG, "ffloor -1.5 = -2.0: a negative with a nonzero fraction rounds AWAY from zero under floor — the +2^k bump, executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_CEIL_NEG, "fceil -1.5 = -1.0: the same operand under ceil truncates instead — the away-flag split between the three operators, pinned by contrast with the row above. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_TRUNC_NEG, "ftrunc -1.5 = -1.0: truncation never rounds away, either sign. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_WR_FLOOR_SMALL_NEG,
            "ffloor -0.5 = -1.0: the |x| < 1 arm away from zero. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_WR_CEIL_SMALL_NEG, "fceil -0.5 = -0.0 — THE signed-zero rounding row: toward zero from a negative operand the result is the NEGATIVE zero (IEEE 754 keeps the operand's sign on a zero result), which is why ir_f64_rnd_small packs the operand's sign rather than producing +0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_TRUNC_SMALL_POS, "ftrunc 0.5 = +0.0: the positive half of the small arm, toward zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_CEIL_CARRY, "fceil 1.9999999999999998 = 2.0 — THE EXPONENT-CARRY ROW: the truncated significand is all ones, and the +2^k bump carries out of the significand field into the exponent, landing on exactly 2.0 because binary64 magnitudes are ordered bit patterns. The row a digit-field implementation gets wrong. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FLOOR_INT, "ffloor 2.0 = 2.0: an exact integer is returned unchanged (the zero-fraction case of the mid-range arm). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FLOOR_MZERO, "ffloor -0.0 = -0.0: a zero is its own rounding, SIGN PRESERVED — the zero-class arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FLOOR_INF, "ffloor +inf = +inf: an infinity is its own rounding — the inf-class arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WR_FLOOR_NAN, "ffloor NaN is REFUSED: the rounded result would be *a* NaN whose payload the host libm chooses — the implementation-defined-payload rule, the same boundary fadd carries and fneg does NOT (a bit operation preserves the payload; a libm operation may not). Recorded as this wave's round-nan-payload delta. DerivedProved, zero axiom_deps.")?;

        // ── the DATED REFUSALS, universally quantified (2026-08-25) ────
        self.add_recursive_def(
            concat!(
                "def ir_frem_unmodelled (t : IRTy) (a : IRScalar) (b : IRScalar) : ",
                "Eq IRStepResult (ir_binop_eval IRBinOp.frem t a b) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "frem is the tagged `unmodelled float_domain` outcome at EVERY type and operand \
             pair — the dated refusal (2026-08-25): the pinned interpreter ANSWERS f64 frem \
             (a4e81b6 eval_float_binop, `lhs % rhs`), but an exact float remainder needs the \
             quotient's significand at guard precision — the same cost class as the measured \
             fdiv-finite refusal (eval_ir_float_fin's build item) — so the honest verdict \
             stays the refusal until that build item lands. The kernel iota-reduces the \
             dispatch on the opcode, so nothing else is consulted. Recorded in \
             data/evalir_float_residue.PENDING.md and the adequacy grid \
             (frem-answers-in-e2). DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fsqrt_unmodelled (t : IRTy) (a : IRScalar) : ",
                "Eq IRStepResult (ir_unop_eval IRUnOp.fsqrt t a) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "fsqrt is the tagged `unmodelled float_domain` outcome at EVERY type and operand \
             — the dated refusal (2026-08-25) the plan itself names ('fsqrt is the hard one \
             and can carry a dated refusal'): the pinned interpreter answers it \
             (`operand.sqrt()`), but a correctly-rounded square root needs an iterated \
             guard-precision division on the substrate — the fdiv-finite cost class squared \
             — and no clean-kernel body emits one. Recorded in \
             data/evalir_float_residue.PENDING.md and the adequacy grid \
             (fsqrt-answers-in-e2). DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fdiv_fin_fin_unmodelled (a : Nat) (b : Nat) : ",
                "Eq (IROption Nat) (ir_f64_div_at a b IRF64Class.fin_ IRF64Class.fin_) ",
                "(IROption.none Nat) := ",
                "Eq.refl (IROption Nat) (IROption.none Nat)",
            ),
            "fdiv on the FINITE fragment refuses at EVERY operand pair — the existing named \
             build item (eval_ir_float_fin: the shared rounding tail's cost blow-up, \
             measured), promoted from the single-point witness \
             ir_f64_w_div_finite_finite_still_refused to the UNIVERSAL statement at the \
             table: the kernel iota-reduces ir_f64_div_at on the two fin_ constructors and \
             the cell is `none` with a and b free. A dated refusal is a theorem, not a gap. \
             DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fneg_f32_unmodelled (a : IRScalar) : ",
                "Eq IRStepResult (ir_unop_eval IRUnOp.fneg (IRTy.float_ 32) a) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "A residue unop at binary32 is the tagged `unmodelled float_domain` outcome at \
             every operand — the ir_fcmp_f32_unmodelled boundary carried to the unary \
             dispatcher: the pinned interpreter answers f32 unops (eval_float_unop's F32 \
             arm); this domain decides only binary64, and a tagged refusal can never become \
             a wrong answer. One witness per dispatcher shape (fneg here, fmin and ffloor \
             below): every residue op rides the same two width gates. DerivedProved, zero \
             axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fmin_f32_unmodelled (a : IRScalar) (b : IRScalar) : ",
                "Eq IRStepResult (ir_binop_eval IRBinOp.fmin (IRTy.float_ 32) a b) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "The binary32 boundary through the binary dispatcher's fmin arm, at every \
             operand pair. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_ffloor_f32_unmodelled (a : IRScalar) : ",
                "Eq IRStepResult (ir_unop_eval IRUnOp.ffloor (IRTy.float_ 32) a) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "The binary32 boundary through the rounding family's ffloor arm, at every \
             operand. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The eight fp-cast DATED REFUSALS as kernel-witnessed universal
    /// statements — registered at the END of `add_eval_ir_cast`, beside the
    /// dispatcher whose arms they bound.
    ///
    /// Until this wave (2026-08-25) the eight float-cast arms of
    /// `ir_cast_eval` were `ir_float_fault` with no registered statement
    /// saying so — a refusal only a source reader could see. Each now has a
    /// universal witness: the kernel iota-reduces the cast dispatch on the
    /// opcode constructor with the types and operand FREE, so each statement
    /// covers every source type, destination type and operand. The pinned
    /// interpreter ANSWERS all eight (a4e81b6 `interpret.rs:4005-4143`:
    /// `FPTrunc`/`FPExt` convert through host formats, `FPToUI`/`FPToSI`
    /// with range UB, the saturating pair, `UIToFP`/`SIToFP` rounding) — the
    /// refusal is a fragment boundary of THIS model: fp<->int conversion
    /// needs significand scaling plus rounding (the fdiv-finite cost class),
    /// and `fptrunc`/`fpext` need the binary32 format this domain does not
    /// model. Recorded in `data/evalir_float_residue.PENDING.md` and the
    /// adequacy grid (`fp-casts-answer-in-e2`).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_cast_float_refusals(&mut self) -> Result<(), SpecError> {
        for (op, name) in [
            ("fptrunc", "ir_cast_fptrunc_unmodelled"),
            ("fpext", "ir_cast_fpext_unmodelled"),
            ("fptoui", "ir_cast_fptoui_unmodelled"),
            ("fptosi", "ir_cast_fptosi_unmodelled"),
            ("uitofp", "ir_cast_uitofp_unmodelled"),
            ("sitofp", "ir_cast_sitofp_unmodelled"),
            ("fptosisat", "ir_cast_fptosisat_unmodelled"),
            ("fptouisat", "ir_cast_fptouisat_unmodelled"),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (src : IRTy) (dst : IRTy) (a : IRScalar) : \
                     Eq IRStepResult (ir_cast_eval IRCastOp.{op} src dst a) ir_float_fault := \
                     Eq.refl IRStepResult ir_float_fault"
                ),
                &format!(
                    "Cast {op} is the tagged `unmodelled float_domain` outcome at EVERY source \
                     type, destination type and operand — the dated refusal (2026-08-25) as a \
                     universal statement rather than a silent arm; see \
                     add_eval_ir_cast_float_refusals' doc for the boundary's reason and its \
                     grid row. DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every named pattern is the binary64 the comments claim.
    #[test]
    fn test_the_residue_witness_patterns_are_binary64s() {
        assert_eq!(4_607_182_418_800_017_408u64, 1.0f64.to_bits());
        assert_eq!(4_611_686_018_427_387_904u64, 2.0f64.to_bits());
        assert_eq!(4_609_434_218_613_702_656u64, 1.5f64.to_bits());
        assert_eq!(13_832_806_255_468_478_464u64, (-1.5f64).to_bits());
        assert_eq!(4_602_678_819_172_646_912u64, 0.5f64.to_bits());
        assert_eq!(13_826_050_856_027_422_720u64, (-0.5f64).to_bits());
        assert_eq!(13_830_554_455_654_793_216u64, (-1.0f64).to_bits());
        assert_eq!(13_835_058_055_282_163_712u64, (-2.0f64).to_bits());
        assert_eq!(9_223_372_036_854_775_808u64, (-0.0f64).to_bits());
        assert_eq!(9_218_868_437_227_405_312u64, f64::INFINITY.to_bits());
        assert_eq!(18_442_240_474_082_181_120u64, f64::NEG_INFINITY.to_bits());
        assert!(f64::from_bits(9_221_120_237_041_090_560u64).is_nan());
        assert_eq!(
            18_444_492_273_895_866_368u64,
            9_221_120_237_041_090_560u64 | (1u64 << 63),
            "the negated-qNaN pattern is qNaN with the sign bit set"
        );
        assert_eq!(
            4_611_686_018_427_387_903u64,
            1.999_999_999_999_999_8f64.to_bits()
        );
    }

    /// **Every answering unop witness agrees with the HARDWARE** through the
    /// pinned interpreter's own formulas (`eval_float_unop`'s F64 arm:
    /// `-x` / `abs` / `floor` / `ceil` / `trunc`), operand and result
    /// compared as BIT PATTERNS so NaN payloads and signed zeros are exact.
    #[test]
    fn test_the_answering_unop_witnesses_agree_with_real_f64() {
        let rows: &[(&str, &str, u64)] = &[
            (SRC_WR_FNEG_ONE, "fneg", 4_607_182_418_800_017_408),
            (SRC_WR_FNEG_MZERO, "fneg", 9_223_372_036_854_775_808),
            (SRC_WR_FNEG_NAN, "fneg", 9_221_120_237_041_090_560),
            (SRC_WR_FABS_MONE, "fabs", 13_830_554_455_654_793_216),
            (SRC_WR_FABS_MZERO, "fabs", 9_223_372_036_854_775_808),
            (SRC_WR_FABS_NAN_NEG, "fabs", 18_444_492_273_895_866_368),
            (SRC_WR_FLOOR_POS, "ffloor", 4_609_434_218_613_702_656),
            (SRC_WR_FLOOR_NEG, "ffloor", 13_832_806_255_468_478_464),
            (SRC_WR_CEIL_NEG, "fceil", 13_832_806_255_468_478_464),
            (SRC_WR_TRUNC_NEG, "ftrunc", 13_832_806_255_468_478_464),
            (SRC_WR_FLOOR_SMALL_NEG, "ffloor", 13_826_050_856_027_422_720),
            (SRC_WR_CEIL_SMALL_NEG, "fceil", 13_826_050_856_027_422_720),
            (SRC_WR_TRUNC_SMALL_POS, "ftrunc", 4_602_678_819_172_646_912),
            (SRC_WR_CEIL_CARRY, "fceil", 4_611_686_018_427_387_903),
            (SRC_WR_FLOOR_INT, "ffloor", 4_611_686_018_427_387_904),
            (SRC_WR_FLOOR_MZERO, "ffloor", 9_223_372_036_854_775_808),
            (SRC_WR_FLOOR_INF, "ffloor", 9_218_868_437_227_405_312),
        ];
        for (src, op, operand) in rows {
            let x = f64::from_bits(*operand);
            let want = match *op {
                "fneg" => (-x).to_bits(),
                "fabs" => x.abs().to_bits(),
                "ffloor" => x.floor().to_bits(),
                "fceil" => x.ceil().to_bits(),
                "ftrunc" => x.trunc().to_bits(),
                other => panic!("unknown unop {other}"),
            };
            let pinned = format!("(IRStepResult.value (IRScalar.float_ {want}))");
            assert!(
                src.contains(&pinned),
                "the {op} witness at operand {operand} must pin what the hardware computes: \
                 wanted {pinned} in {src}"
            );
            assert!(
                src.contains(&operand.to_string()),
                "operand {operand} missing from {src}"
            );
            assert!(
                src.contains(&format!("IRUnOp.{op} ")),
                "operator {op} missing from {src}"
            );
        }
    }

    /// **Every answering min/max witness agrees with the HARDWARE** through
    /// the pinned interpreter's own formulas (`eval_float_binop`'s F64 arm:
    /// `lhs.min(rhs)` / `lhs.max(rhs)`).
    #[test]
    fn test_the_answering_minmax_witnesses_agree_with_real_f64() {
        let rows: &[(&str, &str, u64, u64)] = &[
            (
                SRC_WR_FMIN_ORD,
                "fmin",
                4_607_182_418_800_017_408,
                4_611_686_018_427_387_904,
            ),
            (
                SRC_WR_FMAX_ORD,
                "fmax",
                4_607_182_418_800_017_408,
                4_611_686_018_427_387_904,
            ),
            (
                SRC_WR_FMIN_NEG,
                "fmin",
                13_835_058_055_282_163_712,
                13_830_554_455_654_793_216,
            ),
            (
                SRC_WR_FMIN_NAN_L,
                "fmin",
                9_221_120_237_041_090_560,
                4_611_686_018_427_387_904,
            ),
            (
                SRC_WR_FMAX_NAN_R,
                "fmax",
                4_611_686_018_427_387_904,
                9_221_120_237_041_090_560,
            ),
            (
                SRC_WR_FMIN_NINF,
                "fmin",
                18_442_240_474_082_181_120,
                4_607_182_418_800_017_408,
            ),
        ];
        for (src, op, lhs, rhs) in rows {
            let (l, r) = (f64::from_bits(*lhs), f64::from_bits(*rhs));
            let want = match *op {
                "fmin" => l.min(r).to_bits(),
                "fmax" => l.max(r).to_bits(),
                other => panic!("unknown binop {other}"),
            };
            let pinned = format!("(IRStepResult.value (IRScalar.float_ {want}))");
            assert!(
                src.contains(&pinned),
                "the {op} witness at {lhs} vs {rhs} must pin what the hardware computes: \
                 wanted {pinned} in {src}"
            );
            for v in [lhs, rhs] {
                assert!(
                    src.contains(&v.to_string()),
                    "operand {v} missing from {src}"
                );
            }
        }
    }

    /// The refusal witnesses are the TAGGED refusal, never a value — and the
    /// ambiguous minmax cells really are ambiguous on the hardware's own
    /// terms (both zeros compare equal; both operands NaN).
    #[test]
    fn test_refusals_are_tagged_not_valued() {
        for src in [
            SRC_WR_FNEG_JUNK,
            SRC_WR_FMIN_NAN_BOTH,
            SRC_WR_FMIN_ZPAIR,
            SRC_WR_FMAX_ZPAIR,
            SRC_WR_FLOOR_NAN,
        ] {
            assert!(
                src.contains("ir_float_fault"),
                "a refusal must be ir_float_fault: {src}"
            );
            assert!(!src.contains("IRStepResult.value"), "{src}");
        }
        // The zero pair compares EQUAL as values while being two patterns —
        // exactly the llvm.minnum "returns either" precondition. Through
        // from_bits so nothing here is a compile-time constant fold.
        let (pz, mz) = (f64::from_bits(0), f64::from_bits(9_223_372_036_854_775_808));
        assert!(pz == mz, "the two zeros are one value");
        assert_ne!(pz.to_bits(), mz.to_bits(), "and two patterns");
        // And min/max of two NaNs is a NaN on the host — a payload this
        // model refuses to invent.
        let nan = f64::from_bits(9_221_120_237_041_090_560);
        assert!(nan.min(nan).is_nan());
        assert!(nan.max(nan).is_nan());
    }

    /// Every refused fp cast really ANSWERS in the pinned interpreter's host
    /// semantics — the boundary is this model's, not parity — sampled where
    /// the host answer is deterministic.
    #[test]
    fn test_the_fp_casts_answer_on_the_host() {
        // fptosi/fptoui-style conversions and int->float conversions are
        // well-defined on these operands; the model still refuses them.
        // Through from_bits/runtime values so nothing constant-folds.
        let x = f64::from_bits(1.9f64.to_bits());
        assert_eq!(x as i64, 1);
        assert_eq!((-x) as i64, -1);
        let n: u64 = u64::from(7u8);
        assert_eq!(n as f64, 7.0);
        let h = f64::from_bits(4_609_434_218_613_702_656); // 1.5
        assert_eq!(h as f32, 1.5f32);
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_WR_FNEG_ONE,
            SRC_WR_FNEG_MZERO,
            SRC_WR_FNEG_NAN,
            SRC_WR_FNEG_JUNK,
            SRC_WR_FABS_MONE,
            SRC_WR_FABS_MZERO,
            SRC_WR_FABS_NAN_NEG,
            SRC_WR_FMIN_ORD,
            SRC_WR_FMAX_ORD,
            SRC_WR_FMIN_NEG,
            SRC_WR_FMIN_NAN_L,
            SRC_WR_FMAX_NAN_R,
            SRC_WR_FMIN_NINF,
            SRC_WR_FMIN_NAN_BOTH,
            SRC_WR_FMIN_ZPAIR,
            SRC_WR_FMAX_ZPAIR,
            SRC_WR_FLOOR_POS,
            SRC_WR_FLOOR_NEG,
            SRC_WR_CEIL_NEG,
            SRC_WR_TRUNC_NEG,
            SRC_WR_FLOOR_SMALL_NEG,
            SRC_WR_CEIL_SMALL_NEG,
            SRC_WR_TRUNC_SMALL_POS,
            SRC_WR_CEIL_CARRY,
            SRC_WR_FLOOR_INT,
            SRC_WR_FLOOR_MZERO,
            SRC_WR_FLOOR_INF,
            SRC_WR_FLOOR_NAN,
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
