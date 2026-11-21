// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Connect actual EvalIR division/parity operations to the canonical bit basis.
//! Quotient/remainder uniqueness supplies the bridge; neither evaluator changes.

pub(super) const ROOTS: &[&str] = &[
    "ir_xor_div_two_canonical_v1",
    "ir_xor_rem_two_canonical_v1",
    "ir_xor_low_bit_canonical_v1",
];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_xor_parity_bound_v1",
        r"def ir_xor_parity_bound_v1 (word : Nat) :
@Eq Bool (ir_nat_ltb_walk (Nat.div2Par word) 2) Bool.true :=
@Or.rec (@Eq Nat (Nat.div2Par word) 0) (@Eq Nat (Nat.div2Par word) 1)
  (fun (_ : Or (@Eq Nat (Nat.div2Par word) 0) (@Eq Nat (Nat.div2Par word) 1)) =>
    @Eq Bool (ir_nat_ltb_walk (Nat.div2Par word) 2) Bool.true)
  (fun (zero : @Eq Nat (Nat.div2Par word) 0) =>
    @Eq.subst.{1} Nat (fun (parity : Nat) => @Eq Bool (ir_nat_ltb_walk parity 2) Bool.true)
      0 (Nat.div2Par word) (@Eq.symm Nat (Nat.div2Par word) 0 zero)
      (@Eq.refl Bool Bool.true))
  (fun (one : @Eq Nat (Nat.div2Par word) 1) =>
    @Eq.subst.{1} Nat (fun (parity : Nat) => @Eq Bool (ir_nat_ltb_walk parity 2) Bool.true)
      1 (Nat.div2Par word) (@Eq.symm Nat (Nat.div2Par word) 1 one)
      (@Eq.refl Bool Bool.true))
  (@Nat.div2Par_zero_or_one word)",
    ),
    (
        "ir_xor_divmod_pair_canonical_v1",
        r"def ir_xor_divmod_pair_canonical_v1 (word : Nat) :
@Eq Nat (Nat.add (ir_nat_mul (Nat.div2 word) 2) (Nat.div2Par word)) word :=
@Eq.symm Nat word (Nat.add (Nat.add (Nat.div2 word) (Nat.div2 word)) (Nat.div2Par word))
  (@Nat.div2_rejoin word)",
    ),
    (
        "ir_xor_divmod_pair_agrees_v1",
        r"def ir_xor_divmod_pair_agrees_v1 (word : Nat) :
@Eq Nat (Nat.add (ir_nat_mul (ir_nat_div word 2) 2) (ir_div_rem_go 2 word word))
  (Nat.add (ir_nat_mul (Nat.div2 word) 2) (Nat.div2Par word)) :=
@Eq.trans Nat
  (Nat.add (ir_nat_mul (ir_nat_div word 2) 2) (ir_div_rem_go 2 word word)) word
  (Nat.add (ir_nat_mul (Nat.div2 word) 2) (Nat.div2Par word))
  (ir_div_go_pair_eq 2 word word)
  (@Eq.symm Nat (Nat.add (ir_nat_mul (Nat.div2 word) 2) (Nat.div2Par word)) word
    (ir_xor_divmod_pair_canonical_v1 word))",
    ),
    (
        "ir_xor_div_two_canonical_v1",
        r"def ir_xor_div_two_canonical_v1 (word : Nat) :
@Eq Nat (ir_nat_div word 2) (Nat.div2 word) :=
ir_nat_qr_unique_q 2 (ir_nat_div word 2) (Nat.div2 word)
  (ir_div_rem_go 2 word word) (Nat.div2Par word)
  (ir_xor_divmod_pair_agrees_v1 word)
  (ir_div_rem_go_bound 2 word word (ir_div_fuel_suffices_pos word 1))
  (ir_xor_parity_bound_v1 word)",
    ),
    (
        "ir_xor_rem_two_canonical_v1",
        r"def ir_xor_rem_two_canonical_v1 (word : Nat) :
@Eq Nat (ir_nat_rem word 2) (Nat.div2Par word) :=
@Eq.trans Nat (ir_nat_rem word 2) (ir_div_rem_go 2 word word) (Nat.div2Par word)
  (ir_nat_rem_is_residue word 2)
  (ir_nat_qr_unique_r 2 (ir_nat_div word 2) (Nat.div2 word)
    (ir_div_rem_go 2 word word) (Nat.div2Par word)
    (ir_xor_divmod_pair_agrees_v1 word)
    (ir_div_rem_go_bound 2 word word (ir_div_fuel_suffices_pos word 1))
    (ir_xor_parity_bound_v1 word))",
    ),
    (
        "ir_xor_parity_bool_canonical_v1",
        r"def ir_xor_parity_bool_canonical_v1 (word : Nat) :
@Eq Bool (ir_nat_eqb (Nat.div2Par word) 1) (Nat.toBoolPar (Nat.div2Par word)) :=
@Or.rec (@Eq Nat (Nat.div2Par word) 0) (@Eq Nat (Nat.div2Par word) 1)
  (fun (_ : Or (@Eq Nat (Nat.div2Par word) 0) (@Eq Nat (Nat.div2Par word) 1)) =>
    @Eq Bool (ir_nat_eqb (Nat.div2Par word) 1) (Nat.toBoolPar (Nat.div2Par word)))
  (fun (zero : @Eq Nat (Nat.div2Par word) 0) =>
    @Eq.subst.{1} Nat
      (fun (parity : Nat) => @Eq Bool (ir_nat_eqb parity 1) (Nat.toBoolPar parity))
      0 (Nat.div2Par word) (@Eq.symm Nat (Nat.div2Par word) 0 zero)
      (@Eq.refl Bool Bool.false))
  (fun (one : @Eq Nat (Nat.div2Par word) 1) =>
    @Eq.subst.{1} Nat
      (fun (parity : Nat) => @Eq Bool (ir_nat_eqb parity 1) (Nat.toBoolPar parity))
      1 (Nat.div2Par word) (@Eq.symm Nat (Nat.div2Par word) 1 one)
      (@Eq.refl Bool Bool.true))
  (@Nat.div2Par_zero_or_one word)",
    ),
    (
        "ir_xor_low_bit_canonical_v1",
        r"def ir_xor_low_bit_canonical_v1 (word : Nat) :
@Eq Bool (ir_nat_bit word) (Nat.testBit word 0) :=
@Eq.trans Bool (ir_nat_bit word) (ir_nat_eqb (Nat.div2Par word) 1) (Nat.testBit word 0)
  (ir_eq_cong Nat Bool (fun (parity : Nat) => ir_nat_eqb parity 1)
    (ir_nat_rem word 2) (Nat.div2Par word) (ir_xor_rem_two_canonical_v1 word))
  (ir_xor_parity_bool_canonical_v1 word)",
    ),
];
