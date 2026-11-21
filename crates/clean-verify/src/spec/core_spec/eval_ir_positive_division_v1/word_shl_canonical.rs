// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual left-shift evaluation with canonical operands and its original range premise.
//! The result retains the real wrapped multiplication; no quotient/model substitution.
pub(super) const ROOTS: &[&str] = &["ir_byte_shl_uint_canonical_v1"];
pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_canonical_shl_bits_in_range_v1",
        r"def ir_canonical_shl_bits_in_range_v1 (width word amount : Nat)
  (inRange : Nat.lt amount width) : @Eq IRStepResult (ir_shl_bits width word amount)
    (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) :=
@Eq.subst.{1} Bool
  (fun (valid : Bool) => @Eq IRStepResult
    (@Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))
      (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) valid)
    (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))))
  Bool.true (ir_nat_ltb amount width)
  (@Eq.symm Bool (ir_nat_ltb amount width) Bool.true (ir_byte_ltb_of_lt_v1 amount width inRange))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))))",
    ),
    (
        "ir_byte_shl_uint_canonical_v1",
        r"def ir_byte_shl_uint_canonical_v1 (width word amount : Nat)
  (wordBound : Nat.lt word (ir_nat_pow2 width))
  (amountBound : Nat.lt amount (ir_nat_pow2 width))
  (inRange : Nat.lt amount width) :
@Eq IRStepResult
  (ir_binop_eval IRBinOp.shl (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount))
  (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount))))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.shl (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ amount))
  (ir_shl_bits width word (ir_wrap width amount))
  (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount)))))
  (ir_eq_cong Nat IRStepResult (fun (input : Nat) => ir_shl_bits width input (ir_wrap width amount))
    (ir_wrap width word) word
    (ir_byte_wrap_canonical_v1 width word
      (ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 width) wordBound)))
  (@Eq.trans IRStepResult (ir_shl_bits width word (ir_wrap width amount))
    (ir_shl_bits width word amount)
    (IRStepResult.value (IRScalar.int_ (ir_wrap width (ir_nat_mul word (ir_nat_pow2 amount)))))
    (ir_eq_cong Nat IRStepResult (fun (shift : Nat) => ir_shl_bits width word shift)
      (ir_wrap width amount) amount
      (ir_byte_wrap_canonical_v1 width amount
        (ir_byte_ltb_of_lt_v1 amount (ir_nat_pow2 width) amountBound)))
    (ir_canonical_shl_bits_in_range_v1 width word amount inRange))",
    ),
];
