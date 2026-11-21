// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual unsigned logical shifts agree with canonical division by a power of two.
//! Canonical operands and the original amount-in-range premise remain explicit.
pub(super) const ROOTS: &[&str] = &[
    "ir_byte_lshr_uint_canonical_v1",
    "ir_byte_lshr_uint_canonical_result_bound_v1",
];
pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_canonical_shift_pow2_positive_v1",
        r"def ir_canonical_shift_pow2_positive_v1 (exponent : Nat) : Nat.lt 0 (ir_nat_pow2 exponent) :=
@Nat.rec (fun (power : Nat) => Nat.lt 0 (ir_nat_pow2 power))
  (@Nat.zero_lt_succ 0)
  (fun (power : Nat) (ih : Nat.lt 0 (ir_nat_pow2 power)) =>
    @Nat.lt_of_lt_of_le 0 (ir_nat_pow2 power)
      (Nat.add (ir_nat_pow2 power) (ir_nat_pow2 power)) ih
      (@Nat.le_add_right (ir_nat_pow2 power) (ir_nat_pow2 power))) exponent",
    ),
    (
        "ir_lshr_div_pow2_canonical_v1",
        r"def ir_lshr_div_pow2_canonical_v1 (word amount : Nat) :
@Eq Nat (ir_nat_div word (ir_nat_pow2 amount)) (Nat.div word (Nat.pow 2 amount)) :=
@Eq.trans Nat (ir_nat_div word (ir_nat_pow2 amount)) (Nat.div word (ir_nat_pow2 amount))
  (Nat.div word (Nat.pow 2 amount))
  (ir_nat_div_canonical_nonzero_v1 word (ir_nat_pow2 amount)
    (ir_canonical_shift_pow2_positive_v1 amount))
  (ir_eq_cong Nat Nat (fun (divisor : Nat) => Nat.div word divisor)
    (ir_nat_pow2 amount) (Nat.pow 2 amount) (ir_xor_pow2_canonical_v1 amount))",
    ),
    (
        "ir_canonical_lshr_bits_in_range_v1",
        r"def ir_canonical_lshr_bits_in_range_v1 (width word amount : Nat)
  (inRange : Nat.lt amount width) : @Eq IRStepResult (ir_lshr_bits width word amount)
    (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount)))) :=
@Eq.subst Bool
  (fun (valid : Bool) => @Eq IRStepResult
    (@Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))
      (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount)))) valid)
    (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount)))))
  Bool.true (ir_nat_ltb amount width)
  (@Eq.symm Bool (ir_nat_ltb amount width) Bool.true (ir_byte_ltb_of_lt_v1 amount width inRange))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount)))))",
    ),
    (
        "ir_byte_lshr_uint_canonical_v1",
        r"def ir_byte_lshr_uint_canonical_v1 (width word amount : Nat)
  (wordBound : Nat.lt word (ir_nat_pow2 width))
  (amountBound : Nat.lt amount (ir_nat_pow2 width))
  (inRange : Nat.lt amount width) :
@Eq IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount))
  (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount)))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount))
  (ir_lshr_bits width word (ir_wrap width amount))
  (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount))))
  (ir_eq_cong Nat IRStepResult (fun (input : Nat) => ir_lshr_bits width input (ir_wrap width amount))
    (ir_wrap width word) word
    (ir_byte_wrap_canonical_v1 width word
      (ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 width) wordBound)))
  (@Eq.trans IRStepResult (ir_lshr_bits width word (ir_wrap width amount))
    (ir_lshr_bits width word amount)
    (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount))))
    (ir_eq_cong Nat IRStepResult (fun (shift : Nat) => ir_lshr_bits width word shift)
      (ir_wrap width amount) amount
      (ir_byte_wrap_canonical_v1 width amount
        (ir_byte_ltb_of_lt_v1 amount (ir_nat_pow2 width) amountBound)))
    (@Eq.trans IRStepResult (ir_lshr_bits width word amount)
      (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount))))
      (IRStepResult.value (IRScalar.int_ (Nat.div word (Nat.pow 2 amount))))
      (ir_canonical_lshr_bits_in_range_v1 width word amount inRange)
      (ir_eq_cong Nat IRStepResult (fun (result : Nat) => IRStepResult.value (IRScalar.int_ result))
        (ir_nat_div word (ir_nat_pow2 amount)) (Nat.div word (Nat.pow 2 amount))
        (ir_lshr_div_pow2_canonical_v1 word amount))))",
    ),
    (
        "ir_byte_lshr_uint_canonical_result_bound_v1",
        r"def ir_byte_lshr_uint_canonical_result_bound_v1 (width word amount : Nat)
  (wordBound : Nat.lt word (ir_nat_pow2 width)) :
Nat.lt (Nat.div word (Nat.pow 2 amount)) (ir_nat_pow2 width) :=
@Nat.lt_of_le_of_lt (Nat.div word (Nat.pow 2 amount)) word (ir_nat_pow2 width)
  (@Nat.div_le_self word (Nat.pow 2 amount)) wordBound",
    ),
];
