// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual subtraction/restoring quotients agree with canonical Nat.div.
//! Positive divisors and the original restoring-fuel bound remain explicit.
pub(super) const ROOTS: &[&str] = &[
    "ir_nat_div_canonical_positive_v1",
    "ir_nat_div_canonical_nonzero_v1",
    "ir_nat_rem_canonical_positive_v1",
    "ir_dm_quot_canonical_positive_at_fuel_v1",
];
pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_divmod_pair_canonical_positive_v1",
        r"def ir_divmod_pair_canonical_positive_v1 (word divisorPred : Nat) :
@Eq Nat
  (Nat.add (ir_nat_mul (ir_nat_div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (ir_div_rem_go (Nat.succ divisorPred) word word))
  (Nat.add (ir_nat_mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (Nat.mod word (Nat.succ divisorPred))) :=
@Eq.trans Nat
  (Nat.add (ir_nat_mul (ir_nat_div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (ir_div_rem_go (Nat.succ divisorPred) word word))
  (Nat.add (Nat.mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (Nat.mod word (Nat.succ divisorPred)))
  (Nat.add (ir_nat_mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (Nat.mod word (Nat.succ divisorPred)))
  (@Eq.trans Nat
    (Nat.add (ir_nat_mul (ir_nat_div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_div_rem_go (Nat.succ divisorPred) word word)) word
    (Nat.add (Nat.mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (Nat.mod word (Nat.succ divisorPred)))
    (ir_div_go_pair_eq (Nat.succ divisorPred) word word)
    (@Eq.symm Nat
      (Nat.add (Nat.mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
        (Nat.mod word (Nat.succ divisorPred))) word
      (@Nat.div_add_mod word (Nat.succ divisorPred))))
  (ir_eq_cong Nat Nat (fun (product : Nat) => Nat.add product (Nat.mod word (Nat.succ divisorPred)))
    (Nat.mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (ir_nat_mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (@Eq.symm Nat
      (ir_nat_mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (Nat.mul (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_nat_mul_canonical_agrees_v1 (Nat.div word (Nat.succ divisorPred)) (Nat.succ divisorPred))))",
    ),
    (
        "ir_nat_div_canonical_positive_v1",
        r"def ir_nat_div_canonical_positive_v1 (word divisorPred : Nat) :
@Eq Nat (ir_nat_div word (Nat.succ divisorPred)) (Nat.div word (Nat.succ divisorPred)) :=
ir_nat_qr_unique_q (Nat.succ divisorPred)
  (ir_nat_div word (Nat.succ divisorPred)) (Nat.div word (Nat.succ divisorPred))
  (ir_div_rem_go (Nat.succ divisorPred) word word) (Nat.mod word (Nat.succ divisorPred))
  (ir_divmod_pair_canonical_positive_v1 word divisorPred)
  (ir_div_rem_go_bound (Nat.succ divisorPred) word word (ir_div_fuel_suffices_pos word divisorPred))
  (@Eq.trans Bool
    (ir_nat_ltb_walk (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (ir_nat_ltb (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)) Bool.true
    (@Eq.symm Bool
      (ir_nat_ltb (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_nat_ltb_walk (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_nat_ltb_walk_eq (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)))
    (ir_byte_ltb_of_lt_v1 (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)
      (@Nat.mod_lt word (Nat.succ divisorPred) (@Nat.zero_lt_succ divisorPred))))",
    ),
    (
        "ir_nat_rem_canonical_positive_v1",
        r"def ir_nat_rem_canonical_positive_v1 (word divisorPred : Nat) :
@Eq Nat (ir_nat_rem word (Nat.succ divisorPred)) (Nat.mod word (Nat.succ divisorPred)) :=
@Eq.trans Nat (ir_nat_rem word (Nat.succ divisorPred))
  (ir_div_rem_go (Nat.succ divisorPred) word word) (Nat.mod word (Nat.succ divisorPred))
  (ir_nat_rem_is_residue word (Nat.succ divisorPred))
  (ir_nat_qr_unique_r (Nat.succ divisorPred)
    (ir_nat_div word (Nat.succ divisorPred)) (Nat.div word (Nat.succ divisorPred))
    (ir_div_rem_go (Nat.succ divisorPred) word word) (Nat.mod word (Nat.succ divisorPred))
    (ir_divmod_pair_canonical_positive_v1 word divisorPred)
    (ir_div_rem_go_bound (Nat.succ divisorPred) word word (ir_div_fuel_suffices_pos word divisorPred))
    (@Eq.trans Bool
    (ir_nat_ltb_walk (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
    (ir_nat_ltb (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)) Bool.true
    (@Eq.symm Bool
      (ir_nat_ltb (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_nat_ltb_walk (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred))
      (ir_nat_ltb_walk_eq (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)))
    (ir_byte_ltb_of_lt_v1 (Nat.mod word (Nat.succ divisorPred)) (Nat.succ divisorPred)
      (@Nat.mod_lt word (Nat.succ divisorPred) (@Nat.zero_lt_succ divisorPred)))))",
    ),
    (
        "ir_dm_quot_canonical_positive_at_fuel_v1",
        r"def ir_dm_quot_canonical_positive_at_fuel_v1 (word divisorPred fuel : Nat)
  (enough : @Eq Bool (ir_nat_ltb word (ir_nat_shl (Nat.succ divisorPred) fuel)) Bool.true) :
@Eq Nat
  (ir_dm_quot (ir_dm_go 1 word fuel (Nat.succ divisorPred) (IRDivMod.mk word 0)))
  (Nat.div word (Nat.succ divisorPred)) :=
@Eq.trans Nat
  (ir_dm_quot (ir_dm_go 1 word fuel (Nat.succ divisorPred) (IRDivMod.mk word 0)))
  (ir_nat_div word (Nat.succ divisorPred)) (Nat.div word (Nat.succ divisorPred))
  (@Eq.symm Nat (ir_nat_div word (Nat.succ divisorPred))
    (ir_dm_quot (ir_dm_go 1 word fuel (Nat.succ divisorPred) (IRDivMod.mk word 0)))
    (ir_div_agrees_at_fuel word divisorPred fuel enough))
  (ir_nat_div_canonical_positive_v1 word divisorPred)",
    ),
    (
        "ir_nat_div_canonical_nonzero_v1",
        r"def ir_nat_div_canonical_nonzero_v1 (word divisor : Nat)
  (positive : Nat.lt 0 divisor) : @Eq Nat (ir_nat_div word divisor) (Nat.div word divisor) :=
@Nat.rec
  (fun (d : Nat) => Nat.lt 0 d -> @Eq Nat (ir_nat_div word d) (Nat.div word d))
  (fun (impossible : Nat.lt 0 0) =>
    @False.elim (@Eq Nat (ir_nat_div word 0) (Nat.div word 0))
      (@Nat.lt_irrefl 0 impossible))
  (fun (d : Nat)
    (_ih : Nat.lt 0 d -> @Eq Nat (ir_nat_div word d) (Nat.div word d))
    (_positive : Nat.lt 0 (Nat.succ d)) => ir_nat_div_canonical_positive_v1 word d)
  divisor positive",
    ),
];
