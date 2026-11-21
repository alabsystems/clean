// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Induction over the actual EvalIR bit loop, using its real division/bit basis.
//! Neither a result equality nor successful execution is an input premise.

pub(super) const ROOTS: &[&str] = &["ir_and_loop_canonical_v1", "ir_and_width_loop_canonical_v1"];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_and_digit_canonical_v1",
        r"def ir_and_digit_canonical_v1 (a b : Nat) :
@Eq Nat (ir_bool_nat (Bool.and (ir_nat_bit a) (ir_nat_bit b)))
  (Nat.ofBool (Bool.and (Nat.testBit a 0) (Nat.testBit b 0))) :=
@Eq.trans Nat
  (ir_bool_nat (Bool.and (ir_nat_bit a) (ir_nat_bit b)))
  (Nat.ofBool (Bool.and (Nat.testBit a 0) (ir_nat_bit b)))
  (Nat.ofBool (Bool.and (Nat.testBit a 0) (Nat.testBit b 0)))
  (ir_eq_cong Bool Nat
    (fun (bit : Bool) => Nat.ofBool (Bool.and bit (ir_nat_bit b)))
    (ir_nat_bit a) (Nat.testBit a 0) (ir_xor_low_bit_canonical_v1 a))
  (ir_eq_cong Bool Nat
    (fun (bit : Bool) => Nat.ofBool (Bool.and (Nat.testBit a 0) bit))
    (ir_nat_bit b) (Nat.testBit b 0) (ir_xor_low_bit_canonical_v1 b))",
    ),
    (
        "ir_and_reassemble_canonical_v1",
        r"def ir_and_reassemble_canonical_v1 (low canonicalLow tail canonicalTail : Nat)
  (lowEq : @Eq Nat low canonicalLow) (tailEq : @Eq Nat tail canonicalTail) :
@Eq Nat (Nat.add low (ir_nat_double tail))
  (Nat.add (Nat.add canonicalTail canonicalTail) canonicalLow) :=
@Eq.trans Nat (Nat.add low (ir_nat_double tail))
  (Nat.add canonicalLow (ir_nat_double tail))
  (Nat.add (Nat.add canonicalTail canonicalTail) canonicalLow)
  (ir_eq_cong Nat Nat (fun (bit : Nat) => Nat.add bit (ir_nat_double tail))
    low canonicalLow lowEq)
  (@Eq.trans Nat (Nat.add canonicalLow (ir_nat_double tail))
    (Nat.add canonicalLow (Nat.add canonicalTail canonicalTail))
    (Nat.add (Nat.add canonicalTail canonicalTail) canonicalLow)
    (ir_eq_cong Nat Nat
      (fun (rest : Nat) => Nat.add canonicalLow (Nat.add rest rest))
      tail canonicalTail tailEq)
    (@Nat.add_comm canonicalLow (Nat.add canonicalTail canonicalTail)))",
    ),
    (
        "ir_and_loop_arguments_canonical_v1",
        r"def ir_and_loop_arguments_canonical_v1 (fuel a b : Nat) :
@Eq Nat (ir_nat_bitop_go Bool.and fuel (ir_nat_div a 2) (ir_nat_div b 2))
  (ir_nat_bitop_go Bool.and fuel (Nat.div2 a) (Nat.div2 b)) :=
@Eq.trans Nat
  (ir_nat_bitop_go Bool.and fuel (ir_nat_div a 2) (ir_nat_div b 2))
  (ir_nat_bitop_go Bool.and fuel (Nat.div2 a) (ir_nat_div b 2))
  (ir_nat_bitop_go Bool.and fuel (Nat.div2 a) (Nat.div2 b))
  (ir_eq_cong Nat Nat
    (fun (left : Nat) => ir_nat_bitop_go Bool.and fuel left (ir_nat_div b 2))
    (ir_nat_div a 2) (Nat.div2 a) (ir_xor_div_two_canonical_v1 a))
  (ir_eq_cong Nat Nat
    (fun (right : Nat) => ir_nat_bitop_go Bool.and fuel (Nat.div2 a) right)
    (ir_nat_div b 2) (Nat.div2 b) (ir_xor_div_two_canonical_v1 b))",
    ),
    (
        "ir_and_loop_canonical_v1",
        r"def ir_and_loop_canonical_v1 (fuel : Nat) : forall (a b : Nat),
@Eq Nat (ir_nat_bitop_go Bool.and fuel a b) (Nat.bitwiseAux Bool.and fuel a b) :=
@Nat.rec
  (fun (steps : Nat) => forall (a b : Nat),
    @Eq Nat (ir_nat_bitop_go Bool.and steps a b) (Nat.bitwiseAux Bool.and steps a b))
  (fun (_a _b : Nat) => @Eq.refl Nat 0)
  (fun (steps : Nat)
    (ih : forall (a b : Nat), @Eq Nat (ir_nat_bitop_go Bool.and steps a b)
      (Nat.bitwiseAux Bool.and steps a b)) =>
    fun (a b : Nat) =>
    ir_and_reassemble_canonical_v1
      (ir_bool_nat (Bool.and (ir_nat_bit a) (ir_nat_bit b)))
      (Nat.ofBool (Bool.and (Nat.testBit a 0) (Nat.testBit b 0)))
      (ir_nat_bitop_go Bool.and steps (ir_nat_div a 2) (ir_nat_div b 2))
      (Nat.bitwiseAux Bool.and steps (Nat.div2 a) (Nat.div2 b))
      (ir_and_digit_canonical_v1 a b)
      (@Eq.trans Nat
        (ir_nat_bitop_go Bool.and steps (ir_nat_div a 2) (ir_nat_div b 2))
        (ir_nat_bitop_go Bool.and steps (Nat.div2 a) (Nat.div2 b))
        (Nat.bitwiseAux Bool.and steps (Nat.div2 a) (Nat.div2 b))
        (ir_and_loop_arguments_canonical_v1 steps a b)
        (ih (Nat.div2 a) (Nat.div2 b))))
  fuel",
    ),
    (
        "ir_and_width_loop_canonical_v1",
        r"def ir_and_width_loop_canonical_v1 (width a b : Nat)
  (aBound : Nat.lt a (Nat.pow 2 width)) (bBound : Nat.lt b (Nat.pow 2 width)) :
@Eq Nat (ir_nat_bitop_go Bool.and width a b) (Nat.land a b) :=
@Eq.trans Nat (ir_nat_bitop_go Bool.and width a b)
  (Nat.bitwiseAux Bool.and width a b) (Nat.land a b)
  (ir_and_loop_canonical_v1 width a b)
  (@Nat.bitwiseAux_land_eq_of_lt_two_pow width a b aBound bBound)",
    ),
];
