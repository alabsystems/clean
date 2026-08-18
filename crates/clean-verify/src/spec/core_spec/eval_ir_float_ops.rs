// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the binary64 domain's machine-facing half**: the float views of
//! a value and of a type, the two fault verdicts, the typed binary dispatcher,
//! and the kernel-EXECUTED witnesses for every rule the tables encode.
//!
//! Split out of [`super::eval_ir_float`] at the commit that created it rather
//! than after the fact: with the classification, the four 4x4 tables and their
//! prose in one file the module was 710 lines against the 500-line convention,
//! and `data/paragon_ratchet.json`'s `files_over_500` is shrink-only. The
//! boundary is the natural one — that module is the VALUE DOMAIN (what a bit
//! pattern means and what the operators do to it), this one is how the MACHINE
//! reaches it (coercion, the width gate, the boundary between a value and a
//! tagged refusal) plus the evidence that the tables are right.
//!
//! Read [`super::eval_ir_float`]'s module doc first: it states exactly which
//! fragment of IEEE 754 binary64 is modelled, which is refused, and the
//! MEASURED reason for each refusal. Nothing here widens that boundary.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── kernel-EXECUTED witnesses, one per rule the tables encode ──────────
//
// The bit patterns, once, so the equations below read as numbers:
//   1.0   = 0x3FF0000000000000 = 4607182418800017408
//   -1.0  = 0xBFF0000000000000 = 13830554455654793216
//   2.0   = 0x4000000000000000 = 4611686018427387904
//   +0.0  = 0
//   -0.0  = 0x8000000000000000 = 9223372036854775808
//   +inf  = 0x7FF0000000000000 = 9218868437227405312
//   -inf  = 0xFFF0000000000000 = 18442240474082181120
//   qNaN  = 0x7FF8000000000000 = 9221120237041090560
//
// These are here rather than only in the eighth chain's module because THREE OF
// THE FOUR OPERATORS ARE NOT CHAINED. A real evaluation case nothing executes
// is a stub with better documentation, and `fadd`'s signed-zero rule is exactly
// the sort of thing that is wrong in a table nobody ran.
const SRC_WF_ADD_MM: &str = "def ir_f64_w_add_minus_zeros : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 9223372036854775808)) (IRStepResult.value (IRScalar.float_ 9223372036854775808)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9223372036854775808))";
const SRC_WF_ADD_MP: &str = "def ir_f64_w_add_mixed_zeros : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) (IRStepResult.value (IRScalar.float_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 0))";
const SRC_WF_SUB_MP: &str = "def ir_f64_w_sub_mixed_zeros : Eq IRStepResult (ir_binop_eval IRBinOp.fsub (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) (IRStepResult.value (IRScalar.float_ 9223372036854775808)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 9223372036854775808))";
const SRC_WF_ADD_NEGPAIR: &str = "def ir_f64_w_add_exact_zero_sum : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 13830554455654793216)) (IRStepResult.value (IRScalar.float_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 0))";
const SRC_WF_ADD_INF_MINF: &str = "def ir_f64_w_add_opposite_infinities_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 18442240474082181120)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WF_ADD_FIN_FIN: &str = "def ir_f64_w_add_finite_finite_answers : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.float_ 4611686018427387904)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4611686018427387904))";
const SRC_WF_ADD_FIN_TIE: &str = "def ir_f64_w_add_finite_finite_ties_to_even : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4368491638549381120)) (IRStepResult.value (IRScalar.float_ 4607182418800017408)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4607182418800017408))";
const SRC_WF_SUB_FIN_FIN: &str = "def ir_f64_w_sub_finite_finite_answers : Eq IRStepResult (ir_binop_eval IRBinOp.fsub (IRTy.float_ 64) (IRScalar.float_ 4613937818241073152) (IRScalar.float_ 4611686018427387904)) (IRStepResult.value (IRScalar.float_ 4607182418800017408)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4607182418800017408))";
const SRC_WF_MUL_FIN_FIN: &str = "def ir_f64_w_mul_finite_finite_answers : Eq IRStepResult (ir_binop_eval IRBinOp.fmul (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4613937818241073152)) (IRStepResult.value (IRScalar.float_ 4618441417868443648)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 4618441417868443648))";
const SRC_WF_DIV_FIN_FIN: &str = "def ir_f64_w_div_finite_finite_still_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fdiv (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WF_MUL_ZERO_INF: &str = "def ir_f64_w_mul_zero_by_infinity_refused : Eq IRStepResult (ir_binop_eval IRBinOp.fmul (IRTy.float_ 64) (IRScalar.float_ 0) (IRScalar.float_ 9218868437227405312)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_WF_MUL_XSIGN: &str = "def ir_f64_w_mul_sign_is_the_xor : Eq IRStepResult (ir_binop_eval IRBinOp.fmul (IRTy.float_ 64) (IRScalar.float_ 13830554455654793216) (IRScalar.float_ 9218868437227405312)) (IRStepResult.value (IRScalar.float_ 18442240474082181120)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.float_ 18442240474082181120))";
const SRC_WF_NAN_CLASS: &str = "def ir_f64_w_quiet_nan_classifies_nan : Eq IRF64Class (ir_f64_class 9221120237041090560) IRF64Class.nan_ := Eq.refl IRF64Class IRF64Class.nan_";
const SRC_WF_JUNK_CLASS: &str = "def ir_f64_w_junk_pattern_classifies_nan : Eq IRF64Class (ir_f64_class 18446744073709551616) IRF64Class.nan_ := Eq.refl IRF64Class IRF64Class.nan_";
const SRC_WF_FREM: &str = "def ir_f64_w_frem_is_still_unmodelled : Eq IRStepResult (ir_binop_eval IRBinOp.frem (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";

impl Specification {
    /// The machine-facing combinators: the float views of a value and of a
    /// type, the two fault verdicts, and the typed binary dispatcher.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_machine(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_as_float (v : IRScalar) : IROption Nat := match v with
| IRScalar.undef_ => IROption.none Nat
| IRScalar.bool_ b => IROption.none Nat
| IRScalar.int_ n => IROption.none Nat
| IRScalar.float_ n => IROption.some Nat n
| IRScalar.unit_ => IROption.none Nat
| IRScalar.ptr_ a => IROption.none Nat
| IRScalar.nullptr_ => IROption.none Nat
| IRScalar.fat_ d md => IROption.none Nat
| IRScalar.fnptr_ f => IROption.none Nat
| IRScalar.aggv sp => IROption.none Nat
| IRScalar.vnil => IROption.none Nat
| IRScalar.vcons x rest => IROption.none Nat",
            "Float view of a value. An INTEGER is deliberately not a float: the two constructors \
             carry the same Nat but under different interpretations, and reading an int_ as a bit \
             pattern would let `fdiv` accept an integer operand and answer a float. The mirror of \
             ir_as_int, and fail-closed for the same reason.",
        )?;

        self.add_recursive_def(
            r"def ir_ty_float_width (t : IRTy) : IROption Nat := match t with
| IRTy.bool_ => IROption.none Nat
| IRTy.int_ w => IROption.none Nat
| IRTy.uint_ w => IROption.none Nat
| IRTy.float_ w => IROption.some Nat w
| IRTy.ptr_ => IROption.none Nat
| IRTy.ref_ p => IROption.none Nat
| IRTy.refmut_ p => IROption.none Nat
| IRTy.rawconst_ p => IROption.none Nat
| IRTy.rawmut_ p => IROption.none Nat
| IRTy.rc_ p => IROption.none Nat
| IRTy.fatptr_ p => IROption.none Nat
| IRTy.unit_ => IROption.none Nat
| IRTy.never_ => IROption.none Nat
| IRTy.tuple_ n => IROption.none Nat
| IRTy.array_ e n => IROption.none Nat
| IRTy.struct_ n => IROption.none Nat
| IRTy.enum_ n => IROption.none Nat
| IRTy.func_ n => IROption.none Nat",
            "The bit width of a FLOAT type, and none for every other type. The exact mirror of \
             ir_ty_int_width, and load-bearing in the same way: the instruction's IRTy is \
             semantic input, so `fdiv f32` and `fdiv f64` are different operations and only one \
             of them is decided here.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_fault : IRStepResult := ",
                "IRStepResult.fault (IROutcome.unmodelled IRFault.float_domain)",
            ),
            "The verdict for every float operation OUTSIDE the modelled fragment: a NaN result \
             whose payload is implementation-defined, an invalid operation, a finite-finite \
             arithmetic that needs rounding, or any binary format but binary64. It is a tagged \
             unmodelled outcome rather than an invented number, so no theorem can rest on one. \
             \n\nMOVED here from add_eval_ir_arith on 2026-08-15, unchanged, when float stopped \
             being a single blanket verdict and became a value domain with a boundary.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_type_fault : IRStepResult := ",
                "IRStepResult.fault (IROutcome.type_error IRFault.not_float)",
            ),
            "The verdict when a float instruction meets an operand or a type that is not a float \
             at all. A TYPE ERROR and not an unmodelled outcome, and the distinction is the whole \
             reason IRFault gained not_float: `fdiv f64 <int> <int>` is ill-formed IR, while \
             `fdiv f64 <NaN> <NaN>` is well-formed IR this semantics declines to evaluate. \
             Collapsing them would make the two indistinguishable in every theorem.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float2 (f : Nat -> Nat -> IRStepResult) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (x : Nat) => IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (y : Nat) => f x y) (ir_as_float b)) ",
                "(ir_as_float a)",
            ),
            "Apply a binary float operation to two bit patterns, faulting type_error not_float \
             unless BOTH operands are floats. The mirror of ir_int2.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_result (o : IROption Nat) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_fault ",
                "(fun (k : Nat) => IRStepResult.value (IRScalar.float_ k)) o",
            ),
            "Lift a classified float answer into a step result: `some k` is the value with bit \
             pattern k, `none` is the tagged unmodelled outcome. The IROption is the boundary of \
             the modelled fragment, made structural so it cannot be forgotten at a use site.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_binop (f : Nat -> Nat -> IROption Nat) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (w : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "ir_float_fault ",
                "(ir_float2 (fun (x : Nat) (y : Nat) => ir_f64_result (f x y)) a b) ",
                "(ir_nat_eqb w 64)) ",
                "(ir_ty_float_width t)",
            ),
            "*** THE TYPED FLOAT BINARY DISPATCHER. *** A non-float type is type_error not_float; \
             a float type at any width but 64 is the tagged unmodelled outcome (binary32 and \
             binary16 are different formats with different exponent fields, and this module \
             decides only binary64); at width 64 the operands are coerced and the classified \
             table decides. \n\nThe width test is the reason the CFG gate needed a TYPE lane: \
             `fdiv f32 %1, %2` and `fdiv f64 %1, %2` differ in no other lane the gate had, and \
             they are different operations here.",
        )?;

        Ok(())
    }

    /// Kernel-executed witnesses for the rules the tables encode.
    ///
    /// Registered from `add_eval_ir_ops` AFTER `add_eval_ir_arith`, because
    /// they run through `ir_binop_eval`, which that stage declares.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_WF_ADD_MM, "(-0.0) + (-0.0) = -0.0. THE signed-zero rule: it is the ONE zero pair whose sum is negative, and the reason the zero arm of ir_f64_add_at is not the constant Nat.zero. Run by the kernel. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_ADD_MP, "(-0.0) + (+0.0) = +0.0, under roundTiesToEven (IEEE 754-2019 6.3). The companion to the witness above; together they are what a table that treated the sign of a zero as noise would fail. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_SUB_MP, "(-0.0) - (+0.0) = -0.0, where (-0.0) + (+0.0) is +0.0. Same operands, same two bit patterns, different operator, different answer -- which is the whole reason ir_f64_sub is stated as ir_f64_add of the negation rather than as a fourth copied table. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_ADD_NEGPAIR, "1.0 + (-1.0) = +0.0. The ONLY finite+finite sum IEEE 754 fixes without rounding: the result is exactly zero, and 6.3 makes an exact zero sum +0 under roundTiesToEven. Note the sign: +0, not the dividend's. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_ADD_INF_MINF, "(+inf) + (-inf) is REFUSED. An invalid operation, so the answer is a NaN whose payload is implementation-defined. The machine says so with a tagged unmodelled outcome rather than inventing a bit pattern. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_ADD_FIN_FIN, "1.0 + 1.0 = 2.0, THROUGH THE MACHINE -- and this line is where the eighth chain's most-quoted refusal was retired. It was registered as `ir_f64_w_add_finite_finite_refused` on 2026-08-15 precisely because the answer is obvious, so that the boundary would show its unflattering side; it now answers, because round-to-nearest-even over a 53-bit significand became affordable when the significand work was rewritten O(bit-length) (super::eval_ir_bits, super::eval_ir_float_fin). The refusal was a cost law of two definitions, not a wall. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_ADD_FIN_TIE, "1.0 + 2^-53 = 1.0 THROUGH THE MACHINE. A TIE -- exactly half an ulp -- resolved to the EVEN neighbour, which is downward here. Registered at this level, not only inside the fragment's own witnesses, because rounding mode is the one thing a table cannot enforce by elaboration and the only defence is an executed case whose two candidate answers differ. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_SUB_FIN_FIN, "3.0 - 2.0 = 1.0 THROUGH THE MACHINE. fsub is still ir_f64_add of the negation, so this is the finite fragment reached through the composition rather than through a fourth copied table -- which is what keeps `(-0) - (+0) = -0` and `(-0) + (+0) = +0` from drifting apart now that the fin/fin cell computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_MUL_FIN_FIN, "2.0 * 3.0 = 6.0 THROUGH THE MACHINE: an exact 106-bit product of two significands, rounded back to 53 bits. The multiplication table's fin/fin cell was a refusal for the same reason addition's was. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_DIV_FIN_FIN, "*** 2.0 / 1.0 IS STILL REFUSED, AND THIS IS NOW THE ONLY ARITHMETIC REFUSAL LEFT THAT IS ABOUT COST RATHER THAN ABOUT THE STANDARD. *** Addition, subtraction and multiplication all answer one line above; division does not, because its significand is itself a division and the shared rounding tail names its argument enough times that a 0.13 s input becomes an unbounded one -- measured, super::eval_ir_float_fin. Keeping the embarrassing case registered is the same discipline that made the addition row visible before it was fixed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_MUL_ZERO_INF, "0.0 * (+inf) is REFUSED -- an invalid operation, the multiplicative twin of inf - inf. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_MUL_XSIGN, "(-1.0) * (+inf) = -inf. The product's SIGN is the XOR of the operand signs, and that is exact for every pair of operands including the ones whose magnitude this module refuses to compute. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_NAN_CLASS, "0x7FF8000000000000 classifies as nan_: its magnitude is ABOVE the infinity boundary. The classification is what every table dispatches on, so this is the root of every refusal that mentions a NaN. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_JUNK_CLASS, "2^64 -- a Nat that is not a 64-bit pattern at all -- classifies as nan_. JUNK IS FAIL-CLOSED BY CONSTRUCTION rather than by a special case: its magnitude is at least 2^63, which exceeds 0x7FF0000000000000, so every operation on it is the tagged unmodelled outcome. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WF_FREM, "frem is STILL the blanket refusal, and the witness says so. Only the four operators that a body in clean-kernel actually emits were modelled; frem, fmin, fmax and every IRFCmpOp remain unmodelled, and no artifact in the crate lowers them (reduce_float_beq/blt/ble are `unsupported: shim: Inst::FCmp`). DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The class boundary constants are the IEEE 754 binary64 ones.
    #[test]
    fn test_the_boundary_constants_are_binary64s() {
        // 2^63 and 0x7FF0000000000000, computed here rather than restated.
        assert_eq!(9_223_372_036_854_775_808u64, 1u64 << 63);
        assert_eq!(9_218_868_437_227_405_312u64, 0x7FF0_0000_0000_0000u64);
        assert_eq!(18_442_240_474_082_181_120u64, 0xFFF0_0000_0000_0000u64);
        assert_eq!(4_607_182_418_800_017_408u64, 1.0f64.to_bits());
        assert_eq!(13_830_554_455_654_793_216u64, (-1.0f64).to_bits());
        assert_eq!(4_611_686_018_427_387_904u64, 2.0f64.to_bits());
        assert_eq!(9_223_372_036_854_775_808u64, (-0.0f64).to_bits());
        assert_eq!(9_218_868_437_227_405_312u64, f64::INFINITY.to_bits());
        assert_eq!(18_442_240_474_082_181_120u64, f64::NEG_INFINITY.to_bits());
        assert!(f64::from_bits(9_221_120_237_041_090_560u64).is_nan());
    }

    /// **Every answering witness agrees with the HARDWARE.** The one place in
    /// this repository where the classified tables are checked against `f64`
    /// itself rather than against a reading of the standard.
    #[test]
    fn test_the_answering_witnesses_agree_with_real_f64() {
        let b = f64::from_bits;
        for (x, y, want) in [
            (1.0f64, 0.0f64, f64::INFINITY.to_bits()),
            (1.0, -0.0, f64::NEG_INFINITY.to_bits()),
            (-1.0, 0.0, f64::NEG_INFINITY.to_bits()),
            (1.0, f64::INFINITY, 0.0f64.to_bits()),
            (-0.0, f64::INFINITY, (-0.0f64).to_bits()),
            (0.0, 1.0, 0.0f64.to_bits()),
        ] {
            assert_eq!(
                (x / y).to_bits(),
                want,
                "the fdiv witness at {x} / {y} must be what the hardware computes"
            );
        }
        // Through `from_bits` rather than through literals: clippy folds
        // `0.0 / 0.0` and `-1.0 * x` at the source level, and folding them is
        // precisely what this test must not do — the point is what the hardware
        // computes, at run time, on the same bit patterns the witnesses carry.
        let (pz, mz, one, mone) = (
            b(0),
            b(9_223_372_036_854_775_808),
            b(4_607_182_418_800_017_408),
            b(13_830_554_455_654_793_216),
        );
        let (pinf, minf) = (b(9_218_868_437_227_405_312), b(18_442_240_474_082_181_120));
        assert_eq!((mz + mz).to_bits(), mz.to_bits());
        assert_eq!((mz + pz).to_bits(), pz.to_bits());
        assert_eq!((mz - pz).to_bits(), mz.to_bits());
        assert_eq!((one + mone).to_bits(), pz.to_bits());
        assert_eq!((mone * pinf).to_bits(), minf.to_bits());
        // …and every REFUSED case really is a NaN or really does need rounding.
        assert!((pinf / pinf).is_nan());
        assert!((pz / pz).is_nan());
        assert!((pinf + minf).is_nan());
        assert!((pz * pinf).is_nan());
        assert!(b(9_221_120_237_041_090_560u64).is_nan());
        // ── the finite fragment, landed 2026-08-16 ────────────────────
        //
        // These four ANSWER where they used to be refused, so each one is now
        // checked against the hardware exactly like the classified rows above.
        // 1.0 + 1.0 is the row the eighth chain registered as an embarrassing
        // refusal; it is an ordinary answer now.
        assert_eq!((one + one).to_bits(), 4_611_686_018_427_387_904);
        let (two, three) = (b(4_611_686_018_427_387_904), b(4_613_937_818_241_073_152));
        let half_ulp = b(4_368_491_638_549_381_120); // 2^-53
        assert_eq!(
            (one + half_ulp).to_bits(),
            one.to_bits(),
            "a TIE goes to even"
        );
        assert_eq!((three - two).to_bits(), one.to_bits());
        assert_eq!((two * three).to_bits(), 4_618_441_417_868_443_648);
        // …and 2.0 / 1.0 is exactly 2.0 on the hardware while this semantics
        // still declines it. The assertion is the refusal's honesty: the
        // answer exists, the substrate is what cannot afford to compute it.
        assert_eq!((two / one).to_bits(), 4_611_686_018_427_387_904);
    }

    /// The refusal witnesses must be the TAGGED refusal, never a value.
    #[test]
    fn test_refusals_are_tagged_not_valued() {
        for src in [
            SRC_WF_ADD_INF_MINF,
            SRC_WF_DIV_FIN_FIN,
            SRC_WF_MUL_ZERO_INF,
            SRC_WF_FREM,
        ] {
            assert!(
                src.contains("ir_float_fault"),
                "a refusal must be ir_float_fault, i.e. IROutcome.unmodelled IRFault.float_domain"
            );
            assert!(!src.contains("IRStepResult.value"));
        }
    }

    /// Junk bit patterns are fail-closed by CONSTRUCTION, and the witness says
    /// so at a pattern that is not a 64-bit value at all.
    #[test]
    fn test_junk_is_fail_closed() {
        assert!(SRC_WF_JUNK_CLASS.contains("18446744073709551616"));
        assert_eq!(18_446_744_073_709_551_616u128, 1u128 << 64);
        assert!(SRC_WF_JUNK_CLASS.contains("IRF64Class.nan_"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_WF_ADD_MM,
            SRC_WF_ADD_MP,
            SRC_WF_SUB_MP,
            SRC_WF_ADD_NEGPAIR,
            SRC_WF_ADD_INF_MINF,
            SRC_WF_ADD_FIN_FIN,
            SRC_WF_ADD_FIN_TIE,
            SRC_WF_SUB_FIN_FIN,
            SRC_WF_MUL_FIN_FIN,
            SRC_WF_DIV_FIN_FIN,
            SRC_WF_MUL_ZERO_INF,
            SRC_WF_MUL_XSIGN,
            SRC_WF_NAN_CLASS,
            SRC_WF_JUNK_CLASS,
            SRC_WF_FREM,
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
