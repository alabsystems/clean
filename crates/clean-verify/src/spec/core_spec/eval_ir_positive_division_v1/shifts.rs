// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fixed consumers of the positive-divisor laws in the actual EvalIR shifts.
//!
//! The only input premise is the complete canonical 64-bit range. In
//! particular, arithmetic shift retains the actual sign observer and both
//! branches, including negative encodings. Both divisions use the existing
//! restoring algorithm at fuel 64, with bounds derived independently from
//! ByteV1 order laws. These are proof sources, not an alternative evaluator,
//! native authority, or a change to shift faults or divisor-zero behavior.
//!
//! Boundary applications first use the quantified operation law and reduce
//! only its restoring side; they never normalize the large subtraction loop.
//! Keep the original closed sign-fill divisor spelled `ir_nat_pow2 3` until
//! its equality rewrites it: conversion must not compute the old quotient.
//! The AShr value congruence is proved with symbolic width and amount before
//! specializing: its quotient premises are subsequently derived, not assumed
//! by either public canonical-word operation law.

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_positive_division_u64_by_three_bound_v1",
        r"def ir_positive_division_u64_by_three_bound_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Bool (ir_nat_ltb word (ir_nat_shl 8 64)) Bool.true :=
ir_byte_ltb_of_lt_v1 word (ir_nat_shl 8 64)
  (@Nat.lt_of_lt_of_le word (ir_nat_pow2 64) (ir_nat_shl 8 64)
    (ir_byte_separation_lt_of_ltb_v1 word (ir_nat_pow2 64) fits)
    (Nat.le_add_right (ir_nat_pow2 64) 129127208515966861312))",
    ),
    (
        "ir_positive_division_u64_fill_by_three_bound_v1",
        r"def ir_positive_division_u64_fill_by_three_bound_v1 :
  @Eq Bool (ir_nat_ltb (ir_nat_pow2 64) (ir_nat_shl 8 64)) Bool.true :=
ir_byte_ltb_of_lt_v1 (ir_nat_pow2 64) (ir_nat_shl 8 64)
  (Nat.le_add_right (Nat.succ (ir_nat_pow2 64)) 129127208515966861311)",
    ),
    (
        "ir_positive_division_u64_by_three_v1",
        r"def ir_positive_division_u64_by_three_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Nat (ir_nat_div word 8)
    (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))) :=
ir_div_agrees_at_fuel word 7 64
  (ir_positive_division_u64_by_three_bound_v1 word fits)",
    ),
    (
        "ir_positive_division_u64_fill_by_three_v1",
        r"def ir_positive_division_u64_fill_by_three_v1 :
  @Eq Nat (ir_nat_div (ir_nat_pow2 64) (ir_nat_pow2 3))
    (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
      (IRDivMod.mk (ir_nat_pow2 64) 0))) :=
ir_div_agrees_at_fuel (ir_nat_pow2 64) 7 64
  ir_positive_division_u64_fill_by_three_bound_v1",
    ),
    (
        "ir_positive_division_ashr_value_quotient_congr_v1",
        r"def ir_positive_division_ashr_value_quotient_congr_v1
  (width word amount quotientWord quotientFill : Nat)
  (wordEquality : @Eq Nat (ir_nat_div word (ir_nat_pow2 amount)) quotientWord)
  (fillEquality : @Eq Nat
    (ir_nat_div (ir_nat_pow2 width) (ir_nat_pow2 amount)) quotientFill) :
  @Eq Nat (ir_ashr_value width word amount)
    (@Bool.rec (fun (_ : Bool) => Nat)
      quotientWord (Nat.add quotientWord (Nat.sub (ir_nat_pow2 width) quotientFill))
      (ir_sign_bit width word)) :=
@Eq.trans Nat (ir_ashr_value width word amount)
  (@Bool.rec (fun (_ : Bool) => Nat)
    quotientWord
    (Nat.add quotientWord
      (Nat.sub (ir_nat_pow2 width)
        (ir_nat_div (ir_nat_pow2 width) (ir_nat_pow2 amount))))
    (ir_sign_bit width word))
  (@Bool.rec (fun (_ : Bool) => Nat)
    quotientWord (Nat.add quotientWord (Nat.sub (ir_nat_pow2 width) quotientFill))
    (ir_sign_bit width word))
  (ir_eq_cong Nat Nat
    (fun (quotient : Nat) => @Bool.rec (fun (_ : Bool) => Nat)
      quotient
      (Nat.add quotient
        (Nat.sub (ir_nat_pow2 width)
          (ir_nat_div (ir_nat_pow2 width) (ir_nat_pow2 amount))))
      (ir_sign_bit width word))
    (ir_nat_div word (ir_nat_pow2 amount)) quotientWord wordEquality)
  (ir_eq_cong Nat Nat
    (fun (fill : Nat) => @Bool.rec (fun (_ : Bool) => Nat)
      quotientWord (Nat.add quotientWord (Nat.sub (ir_nat_pow2 width) fill))
      (ir_sign_bit width word))
    (ir_nat_div (ir_nat_pow2 width) (ir_nat_pow2 amount)) quotientFill fillEquality)",
    ),
    (
        "ir_positive_division_ashr_i64_value_by_three_v1",
        r"def ir_positive_division_ashr_i64_value_by_three_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Nat (ir_ashr_value 64 word 3)
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
      (Nat.add
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 word)) :=
ir_positive_division_ashr_value_quotient_congr_v1 64 word 3
  (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
  (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
    (IRDivMod.mk (ir_nat_pow2 64) 0)))
  (ir_positive_division_u64_by_three_v1 word fits)
  ir_positive_division_u64_fill_by_three_v1",
    ),
    (
        "ir_byte_lshr_u64_by_three_v1",
        r"def ir_byte_lshr_u64_by_three_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64)
      (IRScalar.int_ word) (IRScalar.int_ 3))
    (IRStepResult.value (IRScalar.int_
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64)
    (IRScalar.int_ word) (IRScalar.int_ 3))
  (ir_lshr_bits 64 word (ir_wrap 64 3))
  (IRStepResult.value (IRScalar.int_
    (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))))
  (ir_eq_cong Nat IRStepResult
    (fun (input : Nat) => ir_lshr_bits 64 input (ir_wrap 64 3))
    (ir_wrap 64 word) word (ir_byte_wrap_canonical_v1 64 word fits))
  (@Eq.trans IRStepResult
    (ir_lshr_bits 64 word (ir_wrap 64 3))
    (ir_lshr_bits 64 word 3)
    (IRStepResult.value (IRScalar.int_
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))))
    (ir_eq_cong Nat IRStepResult
      (fun (amount : Nat) => ir_lshr_bits 64 word amount)
      (ir_wrap 64 3) 3
      (ir_byte_wrap_canonical_v1 64 3 (@Eq.refl Bool Bool.true)))
    (ir_eq_cong Nat IRStepResult
      (fun (quotient : Nat) => IRStepResult.value (IRScalar.int_ quotient))
      (ir_nat_div word 8)
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
      (ir_positive_division_u64_by_three_v1 word fits)))",
    ),
    (
        "ir_byte_ashr_i64_by_three_v1",
        r"def ir_byte_ashr_i64_by_three_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
      (IRScalar.int_ word) (IRScalar.int_ 3))
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.add
          (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word)))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
    (IRScalar.int_ word) (IRScalar.int_ 3))
  (ir_ashr_bits 64 word (ir_wrap 64 3))
  (IRStepResult.value (IRScalar.int_
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
      (Nat.add
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 word))))
  (ir_eq_cong Nat IRStepResult
    (fun (input : Nat) => ir_ashr_bits 64 input (ir_wrap 64 3))
    (ir_wrap 64 word) word (ir_byte_wrap_canonical_v1 64 word fits))
  (@Eq.trans IRStepResult
    (ir_ashr_bits 64 word (ir_wrap 64 3))
    (ir_ashr_bits 64 word 3)
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.add
          (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word))))
    (ir_eq_cong Nat IRStepResult
      (fun (amount : Nat) => ir_ashr_bits 64 word amount)
      (ir_wrap 64 3) 3
      (ir_byte_wrap_canonical_v1 64 3 (@Eq.refl Bool Bool.true)))
    (ir_eq_cong Nat IRStepResult
      (fun (result : Nat) => IRStepResult.value (IRScalar.int_ result))
      (ir_ashr_value 64 word 3)
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.add
          (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word))
      (ir_positive_division_ashr_i64_value_by_three_v1 word fits)))",
    ),
    (
        "ir_byte_lshr_u64_max_by_three_v1",
        r"def ir_byte_lshr_u64_max_by_three_v1 : @Eq IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64)
    (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_ 2305843009213693951)) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64)
    (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_
    (ir_dm_quot (ir_dm_go 1 18446744073709551615 64 8
      (IRDivMod.mk 18446744073709551615 0)))))
  (IRStepResult.value (IRScalar.int_ 2305843009213693951))
  (ir_byte_lshr_u64_by_three_v1 18446744073709551615 (@Eq.refl Bool Bool.true))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 2305843009213693951)))",
    ),
    (
        "ir_byte_ashr_i64_negative_one_by_three_v1",
        r"def ir_byte_ashr_i64_negative_one_by_three_v1 : @Eq IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
    (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_ 18446744073709551615)) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
    (IRScalar.int_ 18446744073709551615) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 18446744073709551615 64 8
        (IRDivMod.mk 18446744073709551615 0)))
      (Nat.add
        (ir_dm_quot (ir_dm_go 1 18446744073709551615 64 8
          (IRDivMod.mk 18446744073709551615 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 18446744073709551615))))
  (IRStepResult.value (IRScalar.int_ 18446744073709551615))
  (ir_byte_ashr_i64_by_three_v1 18446744073709551615 (@Eq.refl Bool Bool.true))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 18446744073709551615)))",
    ),
    (
        "ir_byte_ashr_i64_min_by_three_v1",
        r"def ir_byte_ashr_i64_min_by_three_v1 : @Eq IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
    (IRScalar.int_ 9223372036854775808) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_ 17293822569102704640)) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64)
    (IRScalar.int_ 9223372036854775808) (IRScalar.int_ 3))
  (IRStepResult.value (IRScalar.int_
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 9223372036854775808 64 8
        (IRDivMod.mk 9223372036854775808 0)))
      (Nat.add
        (ir_dm_quot (ir_dm_go 1 9223372036854775808 64 8
          (IRDivMod.mk 9223372036854775808 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 9223372036854775808))))
  (IRStepResult.value (IRScalar.int_ 17293822569102704640))
  (ir_byte_ashr_i64_by_three_v1 9223372036854775808 (@Eq.refl Bool Bool.true))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 17293822569102704640)))",
    ),
];
