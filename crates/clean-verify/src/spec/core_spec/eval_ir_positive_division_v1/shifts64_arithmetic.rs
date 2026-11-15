// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Fixed symbolic arithmetic dependencies for the additive shifts64 vocabulary.
//! These sources reuse actual EvalIR multiplication, doubling, subtraction,
//! division, and restoring declarations. There is no new evaluator or oracle.
//! Computational projection terms remain explicit rather than opaque Nat lets.

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_nat_pow2_positive_v1",
        r"def ir_nat_pow2_positive_v1 (exponent : Nat) : Nat.lt 0 (ir_nat_pow2 exponent) :=
Nat.rec (fun (power : Nat) => Nat.lt 0 (ir_nat_pow2 power))
  (@Nat.zero_lt_succ 0)
  (fun (power : Nat) (ih : Nat.lt 0 (ir_nat_pow2 power)) =>
    @Nat.lt_of_lt_of_le 0 (ir_nat_pow2 power)
      (Nat.add (ir_nat_pow2 power) (ir_nat_pow2 power)) ih
      (@Nat.le_add_right (ir_nat_pow2 power) (ir_nat_pow2 power))) exponent",
    ),
    (
        "ir_nat_shl_monotone_v1",
        r"def ir_nat_shl_monotone_v1 (fuel : Nat) :
  forall (lower upper : Nat), Nat.le lower upper ->
    Nat.le (ir_nat_shl lower fuel) (ir_nat_shl upper fuel) :=
Nat.rec
  (fun (steps : Nat) => forall (lower upper : Nat), Nat.le lower upper ->
    Nat.le (ir_nat_shl lower steps) (ir_nat_shl upper steps))
  (fun (lower upper : Nat) (ordered : Nat.le lower upper) => ordered)
  (fun (steps : Nat)
    (ih : forall (lower upper : Nat), Nat.le lower upper ->
      Nat.le (ir_nat_shl lower steps) (ir_nat_shl upper steps)) =>
    fun (lower upper : Nat) (ordered : Nat.le lower upper) =>
      ih (ir_nat_dbl lower) (ir_nat_dbl upper)
        (Eq.subst Nat (fun (bound : Nat) => Nat.le (ir_nat_dbl lower) bound)
          (Nat.add upper upper) (ir_nat_dbl upper)
          (Eq.symm Nat (ir_nat_dbl upper) (Nat.add upper upper) (ir_nat_dbl_is_add upper))
          (Eq.subst Nat (fun (value : Nat) => Nat.le value (Nat.add upper upper))
            (Nat.add lower lower) (ir_nat_dbl lower)
            (Eq.symm Nat (ir_nat_dbl lower) (Nat.add lower lower) (ir_nat_dbl_is_add lower))
            (@Nat.add_le_add lower upper lower upper ordered ordered)))) fuel",
    ),
    (
        "ir_nat_shl_pow2_add_v1",
        r"def ir_nat_shl_pow2_add_v1 (fuel exponent : Nat) :
  Eq Nat (ir_nat_shl (ir_nat_pow2 exponent) fuel) (ir_nat_pow2 (Nat.add exponent fuel)) :=
Nat.rec
  (fun (steps : Nat) => forall (power : Nat),
    Eq Nat (ir_nat_shl (ir_nat_pow2 power) steps) (ir_nat_pow2 (Nat.add power steps)))
  (fun (power : Nat) => Eq.refl Nat (ir_nat_pow2 power))
  (fun (steps : Nat)
    (ih : forall (power : Nat),
      Eq Nat (ir_nat_shl (ir_nat_pow2 power) steps) (ir_nat_pow2 (Nat.add power steps))) =>
    fun (power : Nat) =>
      Eq.trans Nat (ir_nat_shl (ir_nat_dbl (ir_nat_pow2 power)) steps)
        (ir_nat_shl (ir_nat_pow2 (Nat.succ power)) steps)
        (ir_nat_pow2 (Nat.add power (Nat.succ steps)))
        (ir_eq_cong Nat Nat (fun (value : Nat) => ir_nat_shl value steps)
          (ir_nat_dbl (ir_nat_pow2 power)) (ir_nat_pow2 (Nat.succ power))
          (ir_nat_dbl_is_add (ir_nat_pow2 power)))
        (Eq.trans Nat (ir_nat_shl (ir_nat_pow2 (Nat.succ power)) steps)
          (ir_nat_pow2 (Nat.add (Nat.succ power) steps))
          (ir_nat_pow2 (Nat.add power (Nat.succ steps))) (ih (Nat.succ power))
          (ir_eq_cong Nat Nat ir_nat_pow2 (Nat.add (Nat.succ power) steps)
            (Nat.add power (Nat.succ steps)) (nat_add_succ_left power steps)))) fuel exponent",
    ),
    (
        "ir_nat_shl_one_pow2_v1",
        r"def ir_nat_shl_one_pow2_v1 (fuel : Nat) :
  Eq Nat (ir_nat_shl 1 fuel) (ir_nat_pow2 fuel) :=
Eq.trans Nat (ir_nat_shl 1 fuel) (ir_nat_pow2 (Nat.add 0 fuel)) (ir_nat_pow2 fuel)
  (ir_nat_shl_pow2_add_v1 fuel 0)
  (ir_eq_cong Nat Nat ir_nat_pow2 (Nat.add 0 fuel) fuel (nat_add_zero_left fuel))",
    ),
    (
        "ir_nat_mul_pow2_add_v1",
        r"def ir_nat_mul_pow2_add_v1 (left right : Nat) :
  Eq Nat (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 right))
    (ir_nat_pow2 (Nat.add left right)) :=
Nat.rec
  (fun (power : Nat) => Eq Nat (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 power))
    (ir_nat_pow2 (Nat.add left power)))
  (Eq.refl Nat (ir_nat_pow2 left))
  (fun (power : Nat)
    (ih : Eq Nat (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 power))
      (ir_nat_pow2 (Nat.add left power))) =>
    Eq.trans Nat (ir_nat_mul (ir_nat_pow2 left) (Nat.add (ir_nat_pow2 power) (ir_nat_pow2 power)))
      (Nat.add (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 power))
        (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 power)))
      (Nat.add (ir_nat_pow2 (Nat.add left power)) (ir_nat_pow2 (Nat.add left power)))
      (ir_nat_mul_add_right (ir_nat_pow2 left) (ir_nat_pow2 power) (ir_nat_pow2 power))
      (ir_eq_cong Nat Nat (fun (value : Nat) => Nat.add value value)
        (ir_nat_mul (ir_nat_pow2 left) (ir_nat_pow2 power))
        (ir_nat_pow2 (Nat.add left power)) ih)) right",
    ),
    (
        "ir_nat_mul_pow2_sub_v1",
        r"def ir_nat_mul_pow2_sub_v1 (width amount : Nat) (inWidth : Nat.le amount width) :
  Eq Nat (ir_nat_mul (ir_nat_pow2 (Nat.sub width amount)) (ir_nat_pow2 amount))
    (ir_nat_pow2 width) :=
Eq.trans Nat (ir_nat_mul (ir_nat_pow2 (Nat.sub width amount)) (ir_nat_pow2 amount))
  (ir_nat_pow2 (Nat.add (Nat.sub width amount) amount)) (ir_nat_pow2 width)
  (ir_nat_mul_pow2_add_v1 (Nat.sub width amount) amount)
  (ir_eq_cong Nat Nat ir_nat_pow2 (Nat.add (Nat.sub width amount) amount) width
    (ir_nat_sub_add_cancel_walk amount width
      (Eq.trans Bool (ir_nat_ltb_walk width amount) (ir_nat_ltb width amount) Bool.false
        (Eq.symm Bool (ir_nat_ltb width amount) (ir_nat_ltb_walk width amount)
          (ir_nat_ltb_walk_eq width amount))
        (ir_byte_allocation_ltb_false_v1 width amount inWidth))))",
    ),
    (
        "ir_nat_pow2_sub_le_v1",
        r"def ir_nat_pow2_sub_le_v1 (width amount : Nat) (inWidth : Nat.le amount width) :
  Nat.le (ir_nat_pow2 (Nat.sub width amount)) (ir_nat_pow2 width) :=
Eq.subst Nat (fun (bound : Nat) => Nat.le (ir_nat_pow2 (Nat.sub width amount)) bound)
  (ir_nat_mul (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub width amount))) (ir_nat_pow2 width)
  (Eq.trans Nat (ir_nat_mul (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub width amount)))
    (ir_nat_mul (ir_nat_pow2 (Nat.sub width amount)) (ir_nat_pow2 amount)) (ir_nat_pow2 width)
    (ir_nat_mul_comm (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub width amount)))
    (ir_nat_mul_pow2_sub_v1 width amount inWidth))
  (Eq.subst Nat
    (fun (lower : Nat) => Nat.le lower
      (ir_nat_mul (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub width amount))))
    (ir_nat_mul 1 (ir_nat_pow2 (Nat.sub width amount))) (ir_nat_pow2 (Nat.sub width amount))
    (ir_nat_mul_one_left (ir_nat_pow2 (Nat.sub width amount)))
    (ir_nat_mul_le_right_v1 1 (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub width amount))
      (ir_nat_pow2_positive_v1 amount)))",
    ),
    (
        "ir_positive_divisor_agrees_v1",
        r"def ir_positive_divisor_agrees_v1 (input divisor fuel : Nat)
  (positive : Nat.lt 0 divisor)
  (bounded : Eq Bool (ir_nat_ltb input (ir_nat_shl divisor fuel)) Bool.true) :
  Eq Nat (ir_nat_div input divisor)
    (ir_dm_quot (ir_dm_go 1 input fuel divisor (IRDivMod.mk input 0))) :=
Eq.subst Nat
  (fun (denominator : Nat) =>
    Eq Bool (ir_nat_ltb input (ir_nat_shl denominator fuel)) Bool.true ->
    Eq Nat (ir_nat_div input denominator)
      (ir_dm_quot (ir_dm_go 1 input fuel denominator (IRDivMod.mk input 0))))
  (Nat.succ (Nat.pred divisor)) divisor (Nat.succ_pred_of_pos divisor positive)
  (fun (enough : Eq Bool
    (ir_nat_ltb input (ir_nat_shl (Nat.succ (Nat.pred divisor)) fuel)) Bool.true) =>
    ir_div_agrees_at_fuel input (Nat.pred divisor) fuel enough)
  bounded",
    ),
    (
        "ir_positive_pow2_divisor_agrees_v1",
        r"def ir_positive_pow2_divisor_agrees_v1 (input amount fuel : Nat)
  (bounded : Eq Bool (ir_nat_ltb input (ir_nat_shl (ir_nat_pow2 amount) fuel)) Bool.true) :
  Eq Nat (ir_nat_div input (ir_nat_pow2 amount))
    (ir_dm_quot (ir_dm_go 1 input fuel (ir_nat_pow2 amount) (IRDivMod.mk input 0))) :=
ir_positive_divisor_agrees_v1 input (ir_nat_pow2 amount) fuel
  (ir_nat_pow2_positive_v1 amount) bounded",
    ),
    (
        "ir_positive_division_u64_word_fuel_v1",
        r"def ir_positive_division_u64_word_fuel_v1 (word amount : Nat)
  (fits : Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  Eq Bool (ir_nat_ltb word (ir_nat_shl (ir_nat_pow2 amount) 64)) Bool.true :=
ir_byte_ltb_of_lt_v1 word (ir_nat_shl (ir_nat_pow2 amount) 64)
  (@Nat.lt_of_lt_of_le word (ir_nat_pow2 64) (ir_nat_shl (ir_nat_pow2 amount) 64)
    (ir_byte_separation_lt_of_ltb_v1 word (ir_nat_pow2 64) fits)
    (Eq.subst Nat (fun (lower : Nat) => Nat.le lower (ir_nat_shl (ir_nat_pow2 amount) 64))
      (ir_nat_shl 1 64) (ir_nat_pow2 64) (ir_nat_shl_one_pow2_v1 64)
      (ir_nat_shl_monotone_v1 64 1 (ir_nat_pow2 amount) (ir_nat_pow2_positive_v1 amount))))",
    ),
    (
        "ir_positive_division_u64_fill_fuel_v1",
        r"def ir_positive_division_u64_fill_fuel_v1 (amount : Nat) :
  Eq Bool (ir_nat_ltb (ir_nat_pow2 64) (ir_nat_shl (ir_nat_pow2 amount) 65)) Bool.true :=
ir_byte_ltb_of_lt_v1 (ir_nat_pow2 64) (ir_nat_shl (ir_nat_pow2 amount) 65)
  (@Nat.lt_of_lt_of_le (ir_nat_pow2 64) (ir_nat_pow2 65) (ir_nat_shl (ir_nat_pow2 amount) 65)
    (@Nat.le_add_right (Nat.succ (ir_nat_pow2 64)) 18446744073709551615)
    (Eq.subst Nat (fun (lower : Nat) => Nat.le lower (ir_nat_shl (ir_nat_pow2 amount) 65))
      (ir_nat_shl 1 65) (ir_nat_pow2 65) (ir_nat_shl_one_pow2_v1 65)
      (ir_nat_shl_monotone_v1 65 1 (ir_nat_pow2 amount) (ir_nat_pow2_positive_v1 amount))))",
    ),
    (
        "ir_positive_division_u64_word_shift_v1",
        r"def ir_positive_division_u64_word_shift_v1 (word amount : Nat)
  (fits : Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) :
  Eq Nat (ir_nat_div word (ir_nat_pow2 amount))
    (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0))) :=
ir_positive_pow2_divisor_agrees_v1 word amount 64
  (ir_positive_division_u64_word_fuel_v1 word amount fits)",
    ),
    (
        "ir_positive_division_u64_fill_shift_v1",
        r"def ir_positive_division_u64_fill_shift_v1 (amount : Nat) :
  Eq Nat (ir_nat_div (ir_nat_pow2 64) (ir_nat_pow2 amount))
    (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
      (IRDivMod.mk (ir_nat_pow2 64) 0))) :=
ir_positive_pow2_divisor_agrees_v1 (ir_nat_pow2 64) amount 65
  (ir_positive_division_u64_fill_fuel_v1 amount)",
    ),
    (
        "ir_positive_division_u64_word_quotient_lt_v1",
        r"def ir_positive_division_u64_word_quotient_lt_v1 (word amount : Nat)
  (fits : Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true)
  (inWidth : Nat.le amount 64) :
  Nat.lt (ir_dm_quot (ir_dm_go 1 word 64 (ir_nat_pow2 amount) (IRDivMod.mk word 0)))
    (ir_nat_pow2 (Nat.sub 64 amount)) :=
ir_dm_quot_lt_v1 word 64 (ir_nat_pow2 amount) (ir_nat_pow2 (Nat.sub 64 amount))
  (Eq.subst Nat (fun (bound : Nat) => Nat.lt word bound) (ir_nat_pow2 64)
    (ir_nat_mul (ir_nat_pow2 (Nat.sub 64 amount)) (ir_nat_pow2 amount))
    (Eq.symm Nat (ir_nat_mul (ir_nat_pow2 (Nat.sub 64 amount)) (ir_nat_pow2 amount))
      (ir_nat_pow2 64) (ir_nat_mul_pow2_sub_v1 64 amount inWidth))
    (ir_byte_separation_lt_of_ltb_v1 word (ir_nat_pow2 64) fits))",
    ),
    (
        "ir_positive_division_u64_fill_quotient_v1",
        r"def ir_positive_division_u64_fill_quotient_v1 (amount : Nat) (inWidth : Nat.le amount 64) :
  Eq Nat (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
    (IRDivMod.mk (ir_nat_pow2 64) 0))) (ir_nat_pow2 (Nat.sub 64 amount)) :=
Eq.symm Nat (ir_nat_pow2 (Nat.sub 64 amount))
  (ir_dm_quot (ir_dm_go 1 (ir_nat_pow2 64) 65 (ir_nat_pow2 amount)
    (IRDivMod.mk (ir_nat_pow2 64) 0)))
  (ir_dm_go_is_the_quotient (ir_nat_pow2 64) (ir_nat_pow2 amount) 65
    (ir_nat_pow2 (Nat.sub 64 amount)) 0 (ir_positive_division_u64_fill_fuel_v1 amount)
    (ir_nat_mul_pow2_sub_v1 64 amount inWidth)
    (Eq.trans Bool (ir_nat_ltb_walk 0 (ir_nat_pow2 amount))
      (ir_nat_ltb 0 (ir_nat_pow2 amount)) Bool.true
      (Eq.symm Bool (ir_nat_ltb 0 (ir_nat_pow2 amount)) (ir_nat_ltb_walk 0 (ir_nat_pow2 amount))
        (ir_nat_ltb_walk_eq 0 (ir_nat_pow2 amount)))
      (ir_byte_ltb_of_lt_v1 0 (ir_nat_pow2 amount) (ir_nat_pow2_positive_v1 amount))))",
    ),
];
