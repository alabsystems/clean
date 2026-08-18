// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the two finite binary64 operators**: correctly-rounded `fadd`
//! (and therefore `fsub`, which is `fadd` of the negation) and `fmul`.
//!
//! Both end in [`super::eval_ir_float_fin`]'s ONE shared rounding tail; what
//! differs is only the exact integer significand each produces and the exact
//! scale it carries. Addition's scale is the smaller operand's and is never
//! negative; multiplication's is a sum of two scales less the double bias and
//! genuinely can be, which is why the tail takes it as a `(bp, bn)` pair.
//!
//! Read [`super::eval_ir_float_fin`]'s module doc first. Split into its own
//! file because `data/paragon_ratchet.json`'s `files_over_500` is shrink-only.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Finite addition and finite multiplication.
    pub(super) fn add_eval_ir_float_ops_fin(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_f64_base (a : Nat) (b : Nat) : Nat := ir_nat_min (ir_f64_sc a) (ir_f64_sc b)",
            "The common scale two operands are aligned to: the smaller of the two, so BOTH shifts \
             are to the left and neither operand loses a bit. That is what makes the sum exact \
             before rounding, and it is why the intermediate can be 2098 bits wide. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_ma (a : Nat) (b : Nat) : Nat := ",
                "ir_nat_shl (ir_f64_sig a) (Nat.sub (ir_f64_sc a) (ir_f64_base a b))",
            ),
            "The first operand's significand at the common scale. The shift is up to 2045 places \
             — max normal against min subnormal — which is exactly the alignment `ir_nat_mul` \
             could not perform. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mb (a : Nat) (b : Nat) : Nat := ",
                "ir_nat_shl (ir_f64_sig b) (Nat.sub (ir_f64_sc b) (ir_f64_base a b))",
            ),
            "The second operand's significand at the common scale. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_msum (a : Nat) (b : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) ",
                "(Nat.add (Nat.sub (ir_f64_ma a b) (ir_f64_mb a b)) ",
                "(Nat.sub (ir_f64_mb a b) (ir_f64_ma a b))) ",
                "(Nat.add (ir_f64_ma a b) (ir_f64_mb a b)) ",
                "(ir_f64_ssign a b)",
            ),
            "THE EXACT MAGNITUDE OF THE SUM. Bool.rec minor order is (false, true): the SECOND \
             minor is same signs, an ordinary addition; the FIRST is opposite signs, where the \
             answer is the absolute difference — written as `(x - y) + (y - x)` on TRUNCATING \
             Nat.sub, which is |x - y| because exactly one of the two terms is non-zero. That is \
             not a trick to save a comparison, it is the only way to say `abs` in a substrate \
             with no integers, and it costs one extra subtraction. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_osign (a : Nat) (b : Nat) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) ",
                "(Bool.rec (fun (_ : Bool) => Bool) (ir_f64_is_neg b) (ir_f64_is_neg a) ",
                "(ir_nat_ltb (ir_f64_mb a b) (ir_f64_ma a b))) ",
                "Bool.false ",
                "(ir_nat_iszero (ir_f64_msum a b))",
            ),
            "The sign when the operands' signs DISAGREE: the larger magnitude wins, and an exact \
             zero sum is +0 (IEEE 754 §6.3 under roundTiesToEven — the one place the result's \
             sign is not either operand's). The zero test comes FIRST because it overrides. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rsign (a : Nat) (b : Nat) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) (ir_f64_osign a b) (ir_f64_is_neg a) ",
                "(ir_f64_ssign a b)",
            ),
            "The sum's sign: the shared sign when the operands agree, otherwise the larger \
             operand's — or +0. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_add_fin (a : Nat) (b : Nat) : Nat := ",
                "ir_f64_pack (ir_f64_rsign a b) ",
                "(ir_f64_magout (ir_f64_msum a b) (ir_f64_base a b) Nat.zero)",
            ),
            "*** IEEE 754 binary64 ADDITION OF TWO FINITE NON-ZERO OPERANDS, correctly rounded. \
             *** The exact aligned sum, then the shared tail at the common scale. `bn` is zero \
             because a sum's scale is the smaller operand's scale, which is already at or above \
             the subnormal floor — only multiplication can go below it. \n\nEvery structural case \
             of the standard goes through these six declarations with no further branching: \
             carry out of the significand, ties resolved to even in both directions, \
             cancellation with renormalisation, subnormal operands, a subnormal result becoming \
             normal and a normal becoming subnormal, the maximum 2045-place alignment, and \
             overflow to an infinity. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mprod (a : Nat) (b : Nat) : Nat := ",
                "ir_nat_mulb (ir_f64_sig a) (ir_f64_sig b)",
            ),
            "The EXACT product of two 53-bit significands: up to 106 bits, no rounding yet. \
             Through the shift-and-add driver, which is O(53); `ir_nat_mul` on the same operands \
             is 2^53 additions. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_msc (a : Nat) (b : Nat) : Nat := Nat.add (ir_f64_sc a) (ir_f64_sc b)",
            "The product's scale before the bias correction: exponents add. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_mbp (a : Nat) (b : Nat) : Nat := Nat.sub (ir_f64_msc a b) 1074",
            "The POSITIVE part of the product's scale. `sig a * sig b * 2^(sc a + sc b - 2148)` is \
             `m * 2^(B - 1074)` with `B = sc a + sc b - 1074`, and B is genuinely negative for \
             small operands — two subnormals multiply to something below 2^-1074 before rounding \
             — so it is carried as a difference of two Nats. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_mbn (a : Nat) (b : Nat) : Nat := Nat.sub 1074 (ir_f64_msc a b)",
            "The NEGATIVE part of the product's scale, and the reason ir_f64_rsh takes a max \
             rather than a single subtraction: when this is positive the result has to be shifted \
             right to reach the subnormal grid, whatever the significand's bit length says. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mul_fin (a : Nat) (b : Nat) : Nat := ",
                "ir_f64_pack (ir_f64_xsign a b) ",
                "(ir_f64_magout (ir_f64_mprod a b) (ir_f64_mbp a b) (ir_f64_mbn a b))",
            ),
            "*** IEEE 754 binary64 MULTIPLICATION OF TWO FINITE NON-ZERO OPERANDS, correctly \
             rounded. *** The exact 106-bit product, then the SAME tail addition uses, at a scale \
             that may be negative. The sign is the XOR and is exact on every pair. \n\nThe tail \
             being shared is not a saving, it is the claim: gradual underflow, overflow and \
             ties-to-even are the same three lines for both operators, so a case that is right \
             for one is right for the other. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}
