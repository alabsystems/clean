// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Derived result ranges for the actual, bounded restoring shift consumers.
//!
//! Input canonicality is the sole public shift premise. Multiplication order,
//! quotient decomposition, and signed-fill order derive the result range;
//! callers do not provide an answer, output bound, or sign interpretation.
//! The generic arithmetic laws retain the declared `ir_nat_mul` semantics,
//! which are not definitionally identical to the prelude's `Nat.mul`.
//! Evaluators, fuel, fault behavior, defaults, and checker limits are unchanged.

use super::{preflight, register_rows_and_check};
use crate::spec::{SpecError, Specification};

pub(super) const ROOTS: &[&str] = &[
    "ir_byte_lshr_u64_by_three_result_bound_v1",
    "ir_byte_ashr_i64_by_three_result_bound_v1",
];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_nat_mul_le_right_v1",
        r"def ir_nat_mul_le_right_v1 (a b divisor : Nat) (ordered : Nat.le a b) :
  Nat.le (ir_nat_mul a divisor) (ir_nat_mul b divisor) :=
@Nat.rec
  (fun (factor : Nat) => Nat.le (ir_nat_mul a factor) (ir_nat_mul b factor))
  (@Nat.le_refl 0)
  (fun (factor : Nat)
    (ih : Nat.le (ir_nat_mul a factor) (ir_nat_mul b factor)) =>
    @Nat.add_le_add a b (ir_nat_mul a factor) (ir_nat_mul b factor) ordered ih)
  divisor",
    ),
    (
        "ir_nat_quot_lt_of_decomposition_v1",
        r"def ir_nat_quot_lt_of_decomposition_v1 (input divisor upper quotient remainder : Nat)
  (decomposition : @Eq Nat (Nat.add (ir_nat_mul quotient divisor) remainder) input)
  (bounded : Nat.lt input (ir_nat_mul upper divisor)) :
  Nat.lt quotient upper :=
let productBelowInput : Nat.le (ir_nat_mul quotient divisor) input :=
  @Eq.subst Nat
    (fun (bound : Nat) => Nat.le (ir_nat_mul quotient divisor) bound)
    (Nat.add (ir_nat_mul quotient divisor) remainder) input
    decomposition
    (@Nat.le_add_right (ir_nat_mul quotient divisor) remainder);
@Or.rec (Nat.le upper quotient) (Nat.lt quotient upper)
  (fun (_ : Or (Nat.le upper quotient) (Nat.lt quotient upper)) => Nat.lt quotient upper)
  (fun (ordered : Nat.le upper quotient) =>
    @False.elim (Nat.lt quotient upper)
      (@Nat.lt_irrefl (ir_nat_mul upper divisor)
        (@Nat.lt_of_le_of_lt (ir_nat_mul upper divisor) input (ir_nat_mul upper divisor)
          (@Nat.le_trans (ir_nat_mul upper divisor) (ir_nat_mul quotient divisor) input
            (ir_nat_mul_le_right_v1 upper quotient divisor ordered) productBelowInput)
          bounded)))
  (fun (less : Nat.lt quotient upper) => less)
  (@Nat.le_or_lt upper quotient)",
    ),
    (
        "ir_dm_quot_lt_v1",
        r"def ir_dm_quot_lt_v1 (input fuel divisor upper : Nat)
  (bounded : Nat.lt input (ir_nat_mul upper divisor)) :
  Nat.lt (ir_dm_quot (ir_dm_go 1 input fuel divisor (IRDivMod.mk input 0))) upper :=
ir_nat_quot_lt_of_decomposition_v1 input divisor upper
  (ir_dm_quot (ir_dm_go 1 input fuel divisor (IRDivMod.mk input 0)))
  (ir_dm_rem (ir_dm_go 1 input fuel divisor (IRDivMod.mk input 0)))
  (ir_dm_go_eq input fuel divisor) bounded",
    ),
    (
        "ir_nat_add_sub_lt_of_lt_le_v1",
        r"def ir_nat_add_sub_lt_of_lt_le_v1 (quotient fill limit : Nat)
  (belowFill : Nat.lt quotient fill) (fillFits : Nat.le fill limit) :
  Nat.lt (Nat.add quotient (Nat.sub limit fill)) limit :=
let notLess : @Eq Bool (ir_nat_ltb_walk limit fill) Bool.false :=
  @Eq.trans Bool (ir_nat_ltb_walk limit fill) (ir_nat_ltb limit fill) Bool.false
    (@Eq.symm Bool (ir_nat_ltb limit fill) (ir_nat_ltb_walk limit fill)
      (ir_nat_ltb_walk_eq limit fill))
    (ir_byte_allocation_ltb_false_v1 limit fill fillFits);
let fillSum : @Eq Nat (Nat.add fill (Nat.sub limit fill)) limit :=
  @Eq.trans Nat (Nat.add fill (Nat.sub limit fill))
    (Nat.add (Nat.sub limit fill) fill) limit
    (@Nat.add_comm fill (Nat.sub limit fill))
    (ir_nat_sub_add_cancel_walk fill limit notLess);
@Eq.subst Nat
  (fun (bound : Nat) => Nat.lt (Nat.add quotient (Nat.sub limit fill)) bound)
  (Nat.add fill (Nat.sub limit fill)) limit fillSum
  (@Nat.add_lt_add_right quotient fill belowFill (Nat.sub limit fill))",
    ),
    (
        "ir_positive_division_u64_fill_quotient_by_three_v1",
        r"def ir_positive_division_u64_fill_quotient_by_three_v1 :
  @Eq Nat
    (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))
    (ir_nat_pow2 61) :=
@Eq.refl Nat (ir_nat_pow2 61)",
    ),
    (
        "ir_byte_lshr_u64_by_three_result_bound_v1",
        r"def ir_byte_lshr_u64_by_three_result_bound_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Bool
    (ir_nat_ltb (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))) (ir_nat_pow2 64))
    Bool.true :=
let quotientBound : Nat.lt
  (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))) (ir_nat_pow2 61) :=
  ir_dm_quot_lt_v1 word 64 8 (ir_nat_pow2 61)
    (@Eq.subst Nat (fun (bound : Nat) => Nat.lt word bound)
      (ir_nat_pow2 64) (ir_nat_mul (ir_nat_pow2 61) 8)
      (@Eq.refl Nat (ir_nat_pow2 64))
      (ir_byte_separation_lt_of_ltb_v1 word (ir_nat_pow2 64) fits));
ir_byte_ltb_of_lt_v1 (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))) (ir_nat_pow2 64)
  (@Nat.lt_of_lt_of_le (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
    (ir_nat_pow2 61) (ir_nat_pow2 64) quotientBound
    (@Nat.le_add_right (ir_nat_pow2 61) 16140901064495857664))",
    ),
    (
        "ir_byte_ashr_i64_by_three_result_bound_v1",
        r"def ir_byte_ashr_i64_by_three_result_bound_v1 (word : Nat)
  (fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  @Eq Bool
    (ir_nat_ltb
      (@Bool.rec (fun (_ : Bool) => Nat)
        (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
          (Nat.sub (ir_nat_pow2 64)
            (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8
              (IRDivMod.mk (ir_nat_pow2 64) 0)))))
        (ir_sign_bit 64 word))
      (ir_nat_pow2 64)) Bool.true :=
let quotientBound : Nat.lt
  (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0))) (ir_nat_pow2 61) :=
  ir_dm_quot_lt_v1 word 64 8 (ir_nat_pow2 61)
    (@Eq.subst Nat (fun (bound : Nat) => Nat.lt word bound)
      (ir_nat_pow2 64) (ir_nat_mul (ir_nat_pow2 61) 8)
      (@Eq.refl Nat (ir_nat_pow2 64))
      (ir_byte_separation_lt_of_ltb_v1 word (ir_nat_pow2 64) fits));
let negativeBound : Nat.lt
  (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
    (Nat.sub (ir_nat_pow2 64)
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))))
  (ir_nat_pow2 64) :=
  @Eq.subst Nat
    (fun (fill : Nat) => Nat.lt
      (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
        (Nat.sub (ir_nat_pow2 64) fill))
      (ir_nat_pow2 64))
    (ir_nat_pow2 61)
    (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))
    (@Eq.symm Nat
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))
      (ir_nat_pow2 61)
      ir_positive_division_u64_fill_quotient_by_three_v1)
    (ir_nat_add_sub_lt_of_lt_le_v1
      (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
      (ir_nat_pow2 61) (ir_nat_pow2 64)
      quotientBound (@Nat.le_add_right (ir_nat_pow2 61) 16140901064495857664));
ir_byte_select_word_bound_v1 64 (ir_sign_bit 64 word)
  (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
    (Nat.sub (ir_nat_pow2 64)
      (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))))
  (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
  (ir_byte_ltb_of_lt_v1
    (Nat.add (ir_dm_quot (ir_dm_go 1 word 64 8 (IRDivMod.mk word 0)))
      (Nat.sub (ir_nat_pow2 64)
        (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 64 8 (IRDivMod.mk (ir_nat_pow2 64) 0)))))
    (ir_nat_pow2 64) negativeBound)
  (ir_byte_lshr_u64_by_three_result_bound_v1 word fits)",
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
    /// Add derived canonical output bounds for the existing shift-by-three
    /// consumers. The destination must have ByteV1 and the checked division
    /// and shift packages. Actual stored declarations and consumer closures
    /// are checked before the clone-once transaction becomes visible.
    ///
    /// # Errors
    /// Name collision, missing substrate, or declaration/root-check failure.
    pub(crate) fn install_eval_ir_u64_shift_by_three_output_bound_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_transactionally(self, LAWS.iter().copied())
    }

    /// A disposable factory owner needs no additional transaction clone.
    pub(crate) fn into_u64_shift_by_three_output_bounds_v1(mut self) -> Result<Self, SpecError> {
        preflight(&self, LAWS.iter().copied())?;
        register_rows_and_check(&mut self, LAWS.iter().copied(), ROOTS)?;
        Ok(self)
    }
}
