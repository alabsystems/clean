/- EqsatTierSInt: the rules of trust-cg's saturation tier (PKG-U4c, lemma
   group e).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   One lemma per rule that only trust-cg
   `crates/trust-cg-eqsat/rules/tier_s_integer.rules` has,
   `EqsatInt.<rule> : ∀ t, Sound TierSDefs.<rule> (.int t)`, for `add_comm`,
   `mul_comm`, `add_assoc_right`, `add_assoc_left`, `mul_assoc_right`,
   `mul_assoc_left`, `distribute` and `factor`. Each is stated on the literal
   generated from that rule file (`EqsatTierSRuleDefs.lean`, namespace
   `EqsatRule.TierSDefs`). A rule with no lemma here is not proved (README,
   "Lemma names and the record term").

   The file's other two rules, `add_zero` and `mul_one`, are rules of the
   integer rule set too, written there with the same text. They get no second
   lemma: the two literals of each are one term (`EqsatTierSControls.lean`),
   so `EqsatInt.add_zero` and `EqsatInt.mul_one` (`EqsatIntSample.lean`,
   `EqsatIntArith.lean`) are proofs of the statements on `TierSDefs.add_zero`
   and `TierSDefs.mul_one`, and the gate requires Clean's entry to accept them
   as such at every integer type.

   Every lemma is one proof for all twelve integer types: the operators are
   SemR's `intBin` at the residues modulo `modulus (t.bits pb)`, and the
   arithmetic is `Nat` arithmetic modulo that modulus, whatever the width
   (the residue facts are the `tiers_*` lemmas below). No lemma uses the
   pointer-width hypothesis, and none has a side condition.

   A `_left` rule is its `_right` rule with the sides exchanged, and `factor`
   is `distribute` with the sides exchanged. An `equiv` statement is one
   common value of both sides, so each is proved from the other's lemma by
   exchanging the two equations; the kernel checks that the exchanged sides
   are the generated literal's.
-/
import EqsatBasics
import EqsatTierSRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-! ## Residue arithmetic modulo `m`

`Nat` facts the rule lemmas reduce to. `m` is any modulus (in a rule lemma,
`modulus (t.bits pb)`). -/

/-- Addition of residues is associative. -/
theorem tiers_add_assoc (m x y z : Nat) : ((x + y) % m + z) % m = (x + (y + z) % m) % m := by
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- Multiplication of residues is associative. -/
theorem tiers_mul_assoc (m x y z : Nat) : ((x * y) % m * z) % m = (x * ((y * z) % m)) % m := by
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Multiplication of residues distributes over their addition, on the left
    operand. -/
theorem tiers_add_mul (m x y z : Nat) :
    ((x + y) % m * z) % m = ((x * z) % m + (y * z) % m) % m := by
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod]

/-! ## Commutativity -/

/-- `(add ?x ?y)` is `(add ?y ?x)`, at every integer type. -/
theorem add_comm (t : IntTy) : Sound TierSDefs.add_comm (.int t) := by
  intro pb env _ hadm _
  simp only [TierSDefs.add_comm, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩ := hadm
  refine ⟨.int t ((x + y) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [TierSDefs.add_comm, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp only [intBin, liftOp, R.bind]
  · simp only [TierSDefs.add_comm, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hy hx]
    simp only [intBin, liftOp, R.bind, Nat.add_comm y x]

/-- `(mul ?x ?y)` is `(mul ?y ?x)`, at every integer type. -/
theorem mul_comm (t : IntTy) : Sound TierSDefs.mul_comm (.int t) := by
  intro pb env _ hadm _
  simp only [TierSDefs.mul_comm, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩ := hadm
  refine ⟨.int t ((x * y) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [TierSDefs.mul_comm, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp only [intBin, liftOp, R.bind]
  · simp only [TierSDefs.mul_comm, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hy hx]
    simp only [intBin, liftOp, R.bind, Nat.mul_comm y x]

/-! ## Associativity -/

/-- `(add (add ?x ?y) ?z)` is `(add ?x (add ?y ?z))`, at every integer type. -/
theorem add_assoc_right (t : IntTy) : Sound TierSDefs.add_assoc_right (.int t) := by
  intro pb env _ hadm _
  simp only [TierSDefs.add_assoc_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, z, _, rfl, hz, rfl⟩ := hadm
  refine ⟨.int t (((x + y) % modulus (t.bits pb) + z) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [TierSDefs.add_assoc_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) hz]
    simp only [intBin, liftOp, R.bind]
  · simp only [TierSDefs.add_assoc_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hy hz]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int hx (mod_modulus_lt _ _)]
    simp only [intBin, liftOp, R.bind, tiers_add_assoc]

/-- `(add ?x (add ?y ?z))` is `(add (add ?x ?y) ?z)`, at every integer type:
    `add_assoc_right` with the sides exchanged. -/
theorem add_assoc_left (t : IntTy) : Sound TierSDefs.add_assoc_left (.int t) := by
  intro pb env hpb hadm hc
  obtain ⟨v, hl, hr⟩ := add_assoc_right t pb env hpb hadm hc
  exact ⟨v, hr, hl⟩

/-- `(mul (mul ?x ?y) ?z)` is `(mul ?x (mul ?y ?z))`, at every integer type. -/
theorem mul_assoc_right (t : IntTy) : Sound TierSDefs.mul_assoc_right (.int t) := by
  intro pb env _ hadm _
  simp only [TierSDefs.mul_assoc_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, z, _, rfl, hz, rfl⟩ := hadm
  refine ⟨.int t (((x * y) % modulus (t.bits pb) * z) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [TierSDefs.mul_assoc_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) hz]
    simp only [intBin, liftOp, R.bind]
  · simp only [TierSDefs.mul_assoc_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hy hz]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int hx (mod_modulus_lt _ _)]
    simp only [intBin, liftOp, R.bind, tiers_mul_assoc]

/-- `(mul ?x (mul ?y ?z))` is `(mul (mul ?x ?y) ?z)`, at every integer type:
    `mul_assoc_right` with the sides exchanged. -/
theorem mul_assoc_left (t : IntTy) : Sound TierSDefs.mul_assoc_left (.int t) := by
  intro pb env hpb hadm hc
  obtain ⟨v, hl, hr⟩ := mul_assoc_right t pb env hpb hadm hc
  exact ⟨v, hr, hl⟩

/-! ## Distribution -/

/-- `(mul (add ?x ?y) ?z)` is `(add (mul ?x ?z) (mul ?y ?z))`, at every
    integer type. -/
theorem distribute (t : IntTy) : Sound TierSDefs.distribute (.int t) := by
  intro pb env _ hadm _
  simp only [TierSDefs.distribute, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, z, _, rfl, hz, rfl⟩ := hadm
  refine ⟨.int t (((x + y) % modulus (t.bits pb) * z) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [TierSDefs.distribute, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) hz]
    simp only [intBin, liftOp, R.bind]
  · simp only [TierSDefs.distribute, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hz]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int hy hz]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) (mod_modulus_lt _ _)]
    simp only [intBin, liftOp, R.bind, tiers_add_mul]

/-- `(add (mul ?x ?z) (mul ?y ?z))` is `(mul (add ?x ?y) ?z)`, at every
    integer type: `distribute` with the sides exchanged. -/
theorem factor (t : IntTy) : Sound TierSDefs.factor (.int t) := by
  intro pb env hpb hadm hc
  obtain ⟨v, hl, hr⟩ := distribute t pb env hpb hadm hc
  exact ⟨v, hr, hl⟩

end EqsatInt
