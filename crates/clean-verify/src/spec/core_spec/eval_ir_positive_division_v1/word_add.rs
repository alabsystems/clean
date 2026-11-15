// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Input-only canonical Add laws for the actual unsigned/signed evaluators.
//!
//! The exact result expression retains both the below-modulus and subtract-one-
//! modulus branches. It is not a new evaluator. Both input bounds derive the
//! wrapped result and its canonicality; no answer, sum bound, output-fit proof,
//! or chosen branch is supplied. Ordinary ByteV1 is sufficient. Definitions,
//! profiles, caches, limits, and native/model admission remain unchanged.

use super::{preflight, register_rows_and_check};
use crate::spec::{SpecError, Specification};

pub(super) const ROOTS: &[&str] = &[
    "ir_byte_add_uint_canonical_v1",
    "ir_byte_add_int_canonical_v1",
    "ir_byte_add_uint_canonical_result_bound_v1",
    "ir_byte_add_int_canonical_result_bound_v1",
];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_byte_add_le_of_ltb_false_v1",
        r"def ir_byte_add_le_of_ltb_false_v1 (a b : Nat)
  (notLess : @Eq Bool (ir_nat_ltb a b) Bool.false) : Nat.le b a :=
@Or.rec (Nat.le b a) (Nat.lt a b)
  (fun (_ : Or (Nat.le b a) (Nat.lt a b)) => Nat.le b a)
  (fun (ordered : Nat.le b a) => ordered)
  (fun (less : Nat.lt a b) => @False.elim (Nat.le b a)
    (ir_byte_world_false_true_v1
      (@Eq.trans Bool Bool.false (ir_nat_ltb a b) Bool.true
        (@Eq.symm Bool (ir_nat_ltb a b) Bool.false notLess)
        (ir_byte_ltb_of_lt_v1 a b less))))
  (@Nat.le_or_lt b a)",
    ),
    (
        "ir_byte_add_subtract_bound_v1",
        r"def ir_byte_add_subtract_bound_v1 (limit a b : Nat)
  (aBelow : Nat.lt a limit) (bFits : Nat.le b limit) :
  Nat.lt (Nat.sub (Nat.add a b) limit) limit :=
@Nat.lt_of_le_of_lt (Nat.sub (Nat.add a b) limit) a limit
  (@Eq.subst Nat
    (fun (upper : Nat) => Nat.le (Nat.sub (Nat.add a b) limit) upper)
    (Nat.sub (Nat.add a b) b) a (@Nat.add_sub_cancel a b)
    (@Nat.sub_le_sub_left (Nat.add a b) b limit bFits))
  aBelow",
    ),
    (
        "ir_byte_add_wrap_positive_once_v1",
        r"def ir_byte_add_wrap_positive_once_v1 (width sum : Nat)
  (positive : Nat.lt 0 sum)
  (first : @Eq Bool (ir_nat_ltb sum (ir_nat_pow2 width)) Bool.false)
  (rest : @Eq Bool (ir_nat_ltb (Nat.sub sum (ir_nat_pow2 width))
    (ir_nat_pow2 width)) Bool.true) :
  @Eq Nat (ir_wrap width sum) (Nat.sub sum (ir_nat_pow2 width)) :=
@Eq.subst Nat
  (fun (input : Nat) => @Eq Nat (ir_wrap width input)
    (Nat.sub input (ir_nat_pow2 width)))
  (Nat.succ (Nat.pred sum)) sum (Nat.succ_pred_of_pos sum positive)
  (ir_byte_wrap_once_v1 width (Nat.pred sum)
    (@Eq.trans Bool
      (ir_nat_ltb (Nat.succ (Nat.pred sum)) (ir_nat_pow2 width))
      (ir_nat_ltb sum (ir_nat_pow2 width)) Bool.false
      (ir_eq_cong Nat Bool (fun (input : Nat) => ir_nat_ltb input (ir_nat_pow2 width))
        (Nat.succ (Nat.pred sum)) sum (Nat.succ_pred_of_pos sum positive)) first)
    (@Eq.trans Bool
      (ir_nat_ltb (Nat.sub (Nat.succ (Nat.pred sum)) (ir_nat_pow2 width)) (ir_nat_pow2 width))
      (ir_nat_ltb (Nat.sub sum (ir_nat_pow2 width)) (ir_nat_pow2 width)) Bool.true
      (ir_eq_cong Nat Bool
        (fun (input : Nat) => ir_nat_ltb (Nat.sub input (ir_nat_pow2 width)) (ir_nat_pow2 width))
        (Nat.succ (Nat.pred sum)) sum (Nat.succ_pred_of_pos sum positive)) rest))",
    ),
    (
        "ir_byte_add_wrap_bounded_sum_v1",
        r"def ir_byte_add_wrap_bounded_sum_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq Nat (ir_wrap width (Nat.add a b))
    (@Bool.rec (fun (_ : Bool) => Nat)
      (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
      (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))) :=
@Bool.rec
  (fun (guard : Bool) => @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) guard ->
    @Eq Nat (ir_wrap width (Nat.add a b))
      (@Bool.rec (fun (_ : Bool) => Nat)
        (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b) guard))
  (fun (above : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.false) =>
    ir_byte_add_wrap_positive_once_v1 width (Nat.add a b)
      (@Nat.lt_of_lt_of_le 0 (ir_nat_pow2 width) (Nat.add a b)
        (@Nat.lt_of_le_of_lt 0 a (ir_nat_pow2 width) (@Nat.zero_le a)
          (ir_byte_separation_lt_of_ltb_v1 a (ir_nat_pow2 width) aFits))
        (ir_byte_add_le_of_ltb_false_v1 (Nat.add a b) (ir_nat_pow2 width) above))
      above
      (ir_byte_ltb_of_lt_v1 (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_pow2 width)
        (ir_byte_add_subtract_bound_v1 (ir_nat_pow2 width) a b
          (ir_byte_separation_lt_of_ltb_v1 a (ir_nat_pow2 width) aFits)
          (@Nat.le_of_lt b (ir_nat_pow2 width)
            (ir_byte_separation_lt_of_ltb_v1 b (ir_nat_pow2 width) bFits)))))
  (fun (below : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.true) =>
    ir_byte_wrap_canonical_v1 width (Nat.add a b) below)
  (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))
  (@Eq.refl Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)))",
    ),
    (
        "ir_byte_add_word_bound_v1",
        r"def ir_byte_add_word_bound_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq Bool (ir_nat_ltb
    (@Bool.rec (fun (_ : Bool) => Nat)
      (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
      (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))) (ir_nat_pow2 width)) Bool.true :=
@Bool.rec
  (fun (guard : Bool) => @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) guard ->
    @Eq Bool (ir_nat_ltb
      (@Bool.rec (fun (_ : Bool) => Nat)
        (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b) guard)
      (ir_nat_pow2 width)) Bool.true)
  (fun (_ : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.false) =>
    ir_byte_ltb_of_lt_v1 (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_pow2 width)
      (ir_byte_add_subtract_bound_v1 (ir_nat_pow2 width) a b
        (ir_byte_separation_lt_of_ltb_v1 a (ir_nat_pow2 width) aFits)
        (@Nat.le_of_lt b (ir_nat_pow2 width)
          (ir_byte_separation_lt_of_ltb_v1 b (ir_nat_pow2 width) bFits))))
  (fun (below : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.true) => below)
  (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))
  (@Eq.refl Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)))",
    ),
    (
        "ir_byte_add_uint_canonical_v1",
        r"def ir_byte_add_uint_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.add (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
        (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))))) :=
ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
  (ir_wrap width (Nat.add a b))
  (@Bool.rec (fun (_ : Bool) => Nat)
    (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
    (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)))
  (ir_byte_add_wrap_bounded_sum_v1 width a b aFits bFits)",
    ),
    (
        "ir_byte_add_int_canonical_v1",
        r"def ir_byte_add_int_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult
    (ir_binop_eval IRBinOp.add (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_
      (@Bool.rec (fun (_ : Bool) => Nat)
        (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
        (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))))) :=
ir_byte_add_uint_canonical_v1 width a b aFits bFits",
    ),
    (
        "ir_byte_add_uint_canonical_result_bound_v1",
        r"def ir_byte_add_uint_canonical_result_bound_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq Bool (ir_nat_ltb
    (@Bool.rec (fun (_ : Bool) => Nat)
      (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
      (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))) (ir_nat_pow2 width)) Bool.true :=
ir_byte_add_word_bound_v1 width a b aFits bFits",
    ),
    (
        "ir_byte_add_int_canonical_result_bound_v1",
        r"def ir_byte_add_int_canonical_result_bound_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq Bool (ir_nat_ltb
    (@Bool.rec (fun (_ : Bool) => Nat)
      (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b)
      (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))) (ir_nat_pow2 width)) Bool.true :=
ir_byte_add_uint_canonical_result_bound_v1 width a b aFits bFits",
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
    /// Add exact width-indexed wrapping Add and derived canonical result laws.
    /// Ordinary ByteV1 alone supplies the prerequisites. The clone-once
    /// transaction checks actual stored declarations and complete root closure;
    /// a failed extension leaves the whole owner untouched.
    pub(crate) fn install_eval_ir_bounded_add_laws_v1_checked(&mut self) -> Result<(), SpecError> {
        install_transactionally(self, LAWS.iter().copied())
    }
}
