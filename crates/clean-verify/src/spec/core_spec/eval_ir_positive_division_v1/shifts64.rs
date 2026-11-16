// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Additive checked laws for actual U64/I64 right shifts at amounts0..63.
//!
//! The word quotient uses fuel64; the full-width AShr fill uses fuel65,
//! including amount0. Public operation/range roots take only input canonicality
//! and the actual shift-range premise. Answers, output bounds, sign selection,
//! and operation equalities are never supplied by consumers. Fixed symbolic
//! dependencies retain the original evaluator and the actual restoring terms.
//! The transactional installer rechecks actual stored terms and their rooted
//! closures. This vocabulary is not native or whole-model admission evidence.

use super::{preflight, register_rows_and_check};
use crate::spec::{SpecError, Specification};

#[path = "shifts64_arithmetic.rs"]
mod shifts64_arithmetic;

pub(super) const ROOTS: &[&str] = &[
    "ir_byte_lshr_u64_in_range_v1",
    "ir_byte_ashr_i64_in_range_v1",
    "ir_byte_lshr_u64_in_range_result_bound_v1",
    "ir_byte_ashr_i64_in_range_result_bound_v1",
];

pub(super) fn laws() -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    shifts64_arithmetic::LAWS.iter().chain(LAWS).copied()
}

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_lshr_bits_in_range_v1",
        r"def ir_lshr_bits_in_range_v1 (width word amount : Nat) (inRange : Nat.lt amount width) :
  @Eq IRStepResult (ir_lshr_bits width word amount)
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
        "ir_ashr_bits_in_range_v1",
        r"def ir_ashr_bits_in_range_v1 (width word amount : Nat) (inRange : Nat.lt amount width) :
  @Eq IRStepResult (ir_ashr_bits width word amount)
    (IRStepResult.value (IRScalar.int_ (ir_ashr_value width word amount))) :=
@Eq.subst Bool
  (fun (valid : Bool) => @Eq IRStepResult
    (@Bool.rec (fun (_ : Bool) => IRStepResult)
      (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))
      (IRStepResult.value (IRScalar.int_ (ir_ashr_value width word amount))) valid)
    (IRStepResult.value (IRScalar.int_ (ir_ashr_value width word amount))))
  Bool.true (ir_nat_ltb amount width)
  (@Eq.symm Bool (ir_nat_ltb amount width) Bool.true (ir_byte_ltb_of_lt_v1 amount width inRange))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_ashr_value width word amount))))",
    ),
    (
        "ir_byte_u64_shift_amount_fits_v1",
        r"def ir_byte_u64_shift_amount_fits_v1 (amount : Nat) (inRange : Nat.lt amount 64) :
  @Eq Bool (ir_nat_ltb amount (ir_nat_pow2 64)) Bool.true :=
ir_byte_ltb_of_lt_v1 amount (ir_nat_pow2 64)
  (@Nat.lt_of_lt_of_le amount 64 (ir_nat_pow2 64) inRange
    (@Nat.le_add_right 64 18446744073709551552))",
    ),
    (
        "ir_positive_division_u64_ashr_value_v1",
        r"def ir_positive_division_u64_ashr_value_v1 (word amount : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Nat (ir_ashr_value 64 word amount)
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
      (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 word)) :=
ir_positive_division_ashr_value_quotient_congr_v1 64 word amount
  (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
  (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
    (IRDivMod.mk (ir_nat_pow2 64) 0)))
  (ir_positive_division_u64_word_shift_v1 word amount fits)
  (ir_positive_division_u64_fill_shift_v1 amount)",
    ),
    (
        "ir_byte_lshr_u64_in_range_v1",
        r"def ir_byte_lshr_u64_in_range_v1 (word amount : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true)
  (inRange : Nat.lt amount 64) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64) (IRScalar.int_ word) (IRScalar.int_ amount))
    (IRStepResult.value (IRScalar.int_
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0))))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.lshr (IRTy.uint_ 64) (IRScalar.int_ word) (IRScalar.int_ amount))
  (ir_lshr_bits 64 word (ir_wrap 64 amount))
  (IRStepResult.value (IRScalar.int_
    (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))))
  (ir_eq_cong Nat IRStepResult (fun (input : Nat) => ir_lshr_bits 64 input (ir_wrap 64 amount))
    (ir_wrap 64 word) word (ir_byte_wrap_canonical_v1 64 word fits))
  (@Eq.trans IRStepResult (ir_lshr_bits 64 word (ir_wrap 64 amount)) (ir_lshr_bits 64 word amount)
    (IRStepResult.value (IRScalar.int_
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))))
    (ir_eq_cong Nat IRStepResult (fun (shift : Nat) => ir_lshr_bits 64 word shift)
      (ir_wrap 64 amount) amount
      (ir_byte_wrap_canonical_v1 64 amount (ir_byte_u64_shift_amount_fits_v1 amount inRange)))
    (@Eq.trans IRStepResult (ir_lshr_bits 64 word amount)
      (IRStepResult.value (IRScalar.int_ (ir_nat_div word (ir_nat_pow2 amount))))
      (IRStepResult.value (IRScalar.int_
        (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))))
      (ir_lshr_bits_in_range_v1 64 word amount inRange)
      (ir_eq_cong Nat IRStepResult (fun (value : Nat) => IRStepResult.value (IRScalar.int_ value))
        (ir_nat_div word (ir_nat_pow2 amount))
        (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (ir_positive_division_u64_word_shift_v1 word amount fits))))",
    ),
    (
        "ir_byte_ashr_i64_in_range_v1",
        r"def ir_byte_ashr_i64_in_range_v1 (word amount : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true)
  (inRange : Nat.lt amount 64) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64) (IRScalar.int_ word) (IRScalar.int_ amount))
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word)))) :=
@Eq.trans IRStepResult
  (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64) (IRScalar.int_ word) (IRScalar.int_ amount))
  (ir_ashr_bits 64 word amount)
  (IRStepResult.value (IRScalar.int_
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
      (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 word))))
  (@Eq.trans IRStepResult
    (ir_binop_eval IRBinOp.ashr (IRTy.int_ 64) (IRScalar.int_ word) (IRScalar.int_ amount))
    (ir_ashr_bits 64 word (ir_wrap 64 amount)) (ir_ashr_bits 64 word amount)
    (ir_eq_cong Nat IRStepResult (fun (input : Nat) => ir_ashr_bits 64 input (ir_wrap 64 amount))
      (ir_wrap 64 word) word (ir_byte_wrap_canonical_v1 64 word fits))
    (ir_eq_cong Nat IRStepResult (fun (shift : Nat) => ir_ashr_bits 64 word shift)
      (ir_wrap 64 amount) amount
      (ir_byte_wrap_canonical_v1 64 amount (ir_byte_u64_shift_amount_fits_v1 amount inRange))))
  (@Eq.trans IRStepResult (ir_ashr_bits 64 word amount)
    (IRStepResult.value (IRScalar.int_ (ir_ashr_value 64 word amount)))
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word))))
    (ir_ashr_bits_in_range_v1 64 word amount inRange)
    (ir_eq_cong Nat IRStepResult (fun (value : Nat) => IRStepResult.value (IRScalar.int_ value))
      (ir_ashr_value 64 word amount)
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word))
      (ir_positive_division_u64_ashr_value_v1 word amount fits)))",
    ),
    (
        "ir_byte_lshr_u64_in_range_result_bound_v1",
        r"def ir_byte_lshr_u64_in_range_result_bound_v1 (word amount : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true)
  (inRange : Nat.lt amount 64) :
  @Eq Bool (ir_nat_ltb
    (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
    (ir_nat_pow2 64)) Bool.true :=
ir_byte_ltb_of_lt_v1
  (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0))) (ir_nat_pow2 64)
  (@Nat.lt_of_lt_of_le
    (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
    (ir_nat_pow2 (Nat.sub 64 amount)) (ir_nat_pow2 64)
    (ir_positive_division_u64_word_quotient_lt_v1 word amount fits (@Nat.le_of_lt amount 64 inRange))
    (ir_nat_pow2_sub_le_v1 64 amount (@Nat.le_of_lt amount 64 inRange)))",
    ),
    (
        "ir_byte_ashr_i64_in_range_result_bound_v1",
        r"def ir_byte_ashr_i64_in_range_result_bound_v1 (word amount : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true)
  (inRange : Nat.lt amount 64) :
  @Eq Bool (ir_nat_ltb
    (@Bool.rec (fun (_ : Bool) => Nat)
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
      (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64)
          (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
            (IRDivMod.mk (ir_nat_pow2 64) 0)))))
      (ir_sign_bit 64 word)) (ir_nat_pow2 64)) Bool.true :=
let negativeBound : Nat.lt
  (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
    (Nat.sub (ir_nat_pow2 64)
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
        (IRDivMod.mk (ir_nat_pow2 64) 0))))) (ir_nat_pow2 64) :=
  @Eq.subst Nat
    (fun (fill : Nat) => Nat.lt
      (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64) fill)) (ir_nat_pow2 64))
    (ir_nat_pow2 (Nat.sub 64 amount))
    (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
      (IRDivMod.mk (ir_nat_pow2 64) 0)))
    (@Eq.symm Nat
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
        (IRDivMod.mk (ir_nat_pow2 64) 0))) (ir_nat_pow2 (Nat.sub 64 amount))
      (ir_positive_division_u64_fill_quotient_v1 amount (@Nat.le_of_lt amount 64 inRange)))
    (ir_nat_add_sub_lt_of_lt_le_v1
      (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
      (ir_nat_pow2 (Nat.sub 64 amount)) (ir_nat_pow2 64)
      (ir_positive_division_u64_word_quotient_lt_v1 word amount fits (@Nat.le_of_lt amount 64 inRange))
      (ir_nat_pow2_sub_le_v1 64 amount (@Nat.le_of_lt amount 64 inRange)));
ir_byte_select_word_bound_v1 64 (ir_sign_bit 64 word)
  (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
    (Nat.sub (ir_nat_pow2 64)
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
        (IRDivMod.mk (ir_nat_pow2 64) 0)))))
  (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
  (ir_byte_ltb_of_lt_v1
    (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
      (Nat.sub (ir_nat_pow2 64)
        (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
          (IRDivMod.mk (ir_nat_pow2 64) 0))))) (ir_nat_pow2 64) negativeBound)
  (ir_byte_lshr_u64_in_range_result_bound_v1 word amount fits inRange)",
    ),
];

pub(super) fn install_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    preflight(spec, rows.clone())?;
    let mut candidate = spec.clone();
    register_rows_and_check(&mut candidate, rows, ROOTS)?;
    *spec = candidate;
    Ok(())
}

impl Specification {
    /// Extend an output-bounded shift-by-three owner with universally checked
    /// in-range U64/I64 shift operations and derived output bounds. No result
    /// proof or desired answer is supplied. Defaults and evaluators stay fixed.
    pub(crate) fn install_eval_ir_u64_in_range_shift_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_transactionally(self, laws())
    }
}
