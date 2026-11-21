// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Input-only canonical AND equations for the actual signed/unsigned evaluator.
//! The actual input wraps are eliminated from bounds, never assumed successful.

pub(super) const ROOTS: &[&str] = &[
    "ir_byte_and_uint_canonical_v1",
    "ir_byte_and_int_canonical_v1",
    "ir_byte_and_canonical_result_bound_v1",
];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_and_pow2_canonical_v1",
        r"def ir_and_pow2_canonical_v1 (width : Nat) :
@Eq Nat (ir_nat_pow2 width) (Nat.pow 2 width) :=
@Nat.rec (fun (bits : Nat) => @Eq Nat (ir_nat_pow2 bits) (Nat.pow 2 bits))
  (@Eq.refl Nat 1)
  (fun (bits : Nat) (ih : @Eq Nat (ir_nat_pow2 bits) (Nat.pow 2 bits)) =>
    @Eq.trans Nat (Nat.add (ir_nat_pow2 bits) (ir_nat_pow2 bits))
      (Nat.add (Nat.pow 2 bits) (Nat.pow 2 bits)) (Nat.pow 2 (Nat.succ bits))
      (ir_eq_cong Nat Nat (fun (previous : Nat) => Nat.add previous previous)
        (ir_nat_pow2 bits) (Nat.pow 2 bits) ih)
      (@Eq.symm Nat (Nat.pow 2 (Nat.succ bits))
        (Nat.add (Nat.pow 2 bits) (Nat.pow 2 bits)) (@Nat.pow_two_succ bits)))
  width",
    ),
    (
        "ir_and_operand_bound_canonical_v1",
        r"def ir_and_operand_bound_canonical_v1 (width word : Nat)
  (bound : Nat.lt word (ir_nat_pow2 width)) : Nat.lt word (Nat.pow 2 width) :=
@Eq.subst.{1} Nat (fun (limit : Nat) => Nat.lt word limit)
  (ir_nat_pow2 width) (Nat.pow 2 width) (ir_and_pow2_canonical_v1 width) bound",
    ),
    (
        "ir_and_wrapped_inputs_canonical_v1",
        r"def ir_and_wrapped_inputs_canonical_v1 (width a b : Nat)
  (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) :
@Eq Nat (ir_nat_bitop Bool.and width a b) (ir_nat_bitop_go Bool.and width a b) :=
@Eq.trans Nat (ir_nat_bitop Bool.and width a b)
  (ir_nat_bitop_go Bool.and width a (ir_wrap width b))
  (ir_nat_bitop_go Bool.and width a b)
  (ir_eq_cong Nat Nat
    (fun (left : Nat) => ir_nat_bitop_go Bool.and width left (ir_wrap width b))
    (ir_wrap width a) a
    (ir_byte_wrap_canonical_v1 width a (ir_byte_ltb_of_lt_v1 a (ir_nat_pow2 width) aBound)))
  (ir_eq_cong Nat Nat (fun (right : Nat) => ir_nat_bitop_go Bool.and width a right)
    (ir_wrap width b) b
    (ir_byte_wrap_canonical_v1 width b (ir_byte_ltb_of_lt_v1 b (ir_nat_pow2 width) bBound)))",
    ),
    (
        "ir_and_word_canonical_v1",
        r"def ir_and_word_canonical_v1 (width a b : Nat)
  (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) :
@Eq Nat (ir_nat_bitop Bool.and width a b) (Nat.land a b) :=
@Eq.trans Nat (ir_nat_bitop Bool.and width a b)
  (ir_nat_bitop_go Bool.and width a b) (Nat.land a b)
  (ir_and_wrapped_inputs_canonical_v1 width a b aBound bBound)
  (ir_and_width_loop_canonical_v1 width a b
    (ir_and_operand_bound_canonical_v1 width a aBound)
    (ir_and_operand_bound_canonical_v1 width b bBound))",
    ),
    (
        "ir_byte_and_uint_canonical_v1",
        r"def ir_byte_and_uint_canonical_v1 (width a b : Nat)
  (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) :
@Eq IRStepResult
  (ir_binop_eval IRBinOp.and_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.int_ (Nat.land a b))) :=
ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
  (ir_nat_bitop Bool.and width a b) (Nat.land a b)
  (ir_and_word_canonical_v1 width a b aBound bBound)",
    ),
    (
        "ir_byte_and_int_canonical_v1",
        r"def ir_byte_and_int_canonical_v1 (width a b : Nat)
  (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) :
@Eq IRStepResult
  (ir_binop_eval IRBinOp.and_ (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.int_ (Nat.land a b))) :=
ir_byte_and_uint_canonical_v1 width a b aBound bBound",
    ),
    (
        "ir_byte_and_canonical_result_bound_v1",
        r"def ir_byte_and_canonical_result_bound_v1 (width a b : Nat)
  (aBound : Nat.lt a (ir_nat_pow2 width)) (bBound : Nat.lt b (ir_nat_pow2 width)) :
Nat.lt (Nat.land a b) (ir_nat_pow2 width) :=
@Eq.subst.{1} Nat (fun (limit : Nat) => Nat.lt (Nat.land a b) limit)
  (Nat.pow 2 width) (ir_nat_pow2 width)
  (@Eq.symm Nat (ir_nat_pow2 width) (Nat.pow 2 width) (ir_and_pow2_canonical_v1 width))
  (@Nat.land_lt_two_pow width a b
    (ir_and_operand_bound_canonical_v1 width a aBound)
    (ir_and_operand_bound_canonical_v1 width b bBound))",
    ),
];
