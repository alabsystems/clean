// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Checked, opt-in source/IR arithmetic connection; unchanged evaluator/defaults.
pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "RustSourceWord64IRV1.observe",
        r"def RustSourceWord64IRV1.observe (W : Type) (e : RustSem.SourceWord64AdditionV1.Exit W) : RustSem.SourceIdentityV1.Exit W :=
match e with
| RustSem.SourceWord64AdditionV1.Exit.returned value world trace => RustSem.SourceIdentityV1.Exit.returned W value world trace",
    ),
    (
        "RustSourceWord64IRV1.modAbove",
        r"def RustSourceWord64IRV1.modAbove (width a b : Nat)
 (ha : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
 (hb : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true)
 (above : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.false) :
 @Eq Nat (Nat.mod (Nat.add a b) (ir_nat_pow2 width)) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) :=
ir_byte_mod_unique_v1 (Nat.add a b) (ir_nat_pow2 width) 1 (Nat.sub (Nat.add a b) (ir_nat_pow2 width))
 (@Nat.lt_of_le_of_lt 0 a (ir_nat_pow2 width) (@Nat.zero_le a) (ir_byte_separation_lt_of_ltb_v1 a (ir_nat_pow2 width) ha))
 (ir_byte_add_subtract_bound_v1 (ir_nat_pow2 width) a b
   (ir_byte_separation_lt_of_ltb_v1 a (ir_nat_pow2 width) ha)
   (@Nat.le_of_lt b (ir_nat_pow2 width) (ir_byte_separation_lt_of_ltb_v1 b (ir_nat_pow2 width) hb)))
 (@Eq.symm Nat (Nat.add (Nat.mul 1 (ir_nat_pow2 width)) (Nat.sub (Nat.add a b) (ir_nat_pow2 width))) (Nat.add a b)
   (@Eq.trans Nat (Nat.add (Nat.mul 1 (ir_nat_pow2 width)) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)))
     (Nat.add (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_pow2 width)) (Nat.add a b)
     (@Eq.trans Nat (Nat.add (Nat.mul 1 (ir_nat_pow2 width)) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)))
       (Nat.add (ir_nat_pow2 width) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)))
       (Nat.add (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_pow2 width))
       (ir_eq_cong Nat Nat (fun (n : Nat) => Nat.add n (Nat.sub (Nat.add a b) (ir_nat_pow2 width)))
         (Nat.mul 1 (ir_nat_pow2 width)) (ir_nat_pow2 width) (@Nat.one_mul (ir_nat_pow2 width)))
       (@Nat.add_comm (ir_nat_pow2 width) (Nat.sub (Nat.add a b) (ir_nat_pow2 width))))
     (ir_nat_sub_add_cancel_walk (ir_nat_pow2 width) (Nat.add a b)
       (@Eq.trans Bool (ir_nat_ltb_walk (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.false
         (@Eq.symm Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) (ir_nat_ltb_walk (Nat.add a b) (ir_nat_pow2 width))
           (ir_nat_ltb_walk_eq (Nat.add a b) (ir_nat_pow2 width))) above))))",
    ),
    (
        "RustSourceWord64IRV1.modCanonical",
        r"def RustSourceWord64IRV1.modCanonical (width a b : Nat)
 (ha : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
 (hb : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
 @Eq Nat (Nat.mod (Nat.add a b) (ir_nat_pow2 width))
 (@Bool.rec (fun (_ : Bool) => Nat) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b) (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width))) :=
@Bool.rec (fun (guard : Bool) => @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) guard ->
 @Eq Nat (Nat.mod (Nat.add a b) (ir_nat_pow2 width))
 (@Bool.rec (fun (_ : Bool) => Nat) (Nat.sub (Nat.add a b) (ir_nat_pow2 width)) (Nat.add a b) guard))
 (fun (above : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.false) => RustSourceWord64IRV1.modAbove width a b ha hb above)
 (fun (below : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.true) =>
   @Nat.mod_eq_of_lt (Nat.add a b) (ir_nat_pow2 width) (ir_byte_separation_lt_of_ltb_v1 (Nat.add a b) (ir_nat_pow2 width) below))
 (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) (@Eq.refl Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)))",
    ),
];
