/- EqsatIntArith: the additive and multiplicative rules of the integer rule set
   (PKG-U2, lemma group a).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   One lemma per rule, `EqsatInt.<rule> : ∀ t, Sound Defs.<rule> (.int t)`, for
   `add_const_right`, `mul_const_right`, `sub_zero`, `sub_self`, `mul_one`,
   `mul_zero` (refines), `double_to_mul` (refines), `add_add_const` and
   `mul_mul_const`; `add_zero` is in `EqsatIntSample.lean`. A rule with no
   lemma here is not proved (README, "Lemma names and the record term").

   Every lemma is one proof for all twelve integer types: the operators are
   SemR's `intBin` at the residues modulo `modulus (t.bits pb)`, and the
   arithmetic is `Nat` arithmetic modulo that modulus, whatever the width
   (the residue facts are the `arith_*` lemmas below). No lemma uses the
   pointer-width hypothesis. The two `refines` rules are proved through the
   right disjunct (both sides are one value): `add` and `mul` are total, so
   the left side is never undefined behaviour.
-/
import EqsatBasics
import EqsatIntRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-! ## Residue arithmetic modulo `m`

`Nat` facts the rule lemmas reduce to. `m` is any modulus (in a rule lemma,
`modulus (t.bits pb)`); a hypothesis `x < m` is an admitted operand's range. -/

/-- Subtracting the literal `0`: `x - 0` is `x`. -/
theorem arith_sub_zero {m x : Nat} (hx : x < m) : (x + (m - 0 % m % m)) % m = x := by
  rw [Nat.zero_mod, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- `x - x` is `0`. -/
theorem arith_sub_self {m x : Nat} (hx : x < m) : (x + (m - x % m)) % m = 0 := by
  rw [Nat.mod_eq_of_lt hx, Nat.add_sub_cancel' (Nat.le_of_lt hx), Nat.mod_self]

/-- Multiplying by the literal `1`: `x * 1` is `x`. -/
theorem arith_mul_one {m x : Nat} (hx : x < m) : (x * (1 % m)) % m = x := by
  rw [Nat.mul_mod_mod, Nat.mul_one, Nat.mod_eq_of_lt hx]

/-- Multiplying by the literal `0`: `x * 0` is the literal `0`. -/
theorem arith_mul_zero (m x : Nat) : (x * (0 % m)) % m = 0 % m := by
  rw [Nat.zero_mod, Nat.mul_zero, Nat.zero_mod]

/-- `x + x` is `x * 2`, with `2` the literal's residue. -/
theorem arith_double (m x : Nat) : (x + x) % m = (x * (2 % m)) % m := by
  rw [Nat.mul_mod_mod, Nat.mul_two]

/-- Two additions of constants are one addition of their sum. -/
theorem arith_add_add (m x a b : Nat) : ((x + a) % m + b) % m = (x + (a + b) % m) % m := by
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-! ## The rules -/

/-- `(add (const ?c) ?x)` is `(add ?x (const ?c))`, at every integer type. -/
theorem add_const_right (t : IntTy) : Sound Defs.add_const_right (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.add_const_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t ((x + c) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [Defs.add_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hc hx]
    simp only [intBin, liftOp, R.bind, Nat.add_comm c x]
  · simp only [Defs.add_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hc]
    simp only [intBin, liftOp, R.bind]

/-- `(mul (const ?c) ?x)` is `(mul ?x (const ?c))`, at every integer type. -/
theorem mul_const_right (t : IntTy) : Sound Defs.mul_const_right (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.mul_const_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t ((x * c) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [Defs.mul_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hc hx]
    simp only [intBin, liftOp, R.bind, Nat.mul_comm c x]
  · simp only [Defs.mul_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hc]
    simp only [intBin, liftOp, R.bind]

/-- `(sub ?x (const 0))` is `?x`, at every integer type. -/
theorem sub_zero (t : IntTy) : Sound Defs.sub_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.sub_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.sub_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  simp only [intBin, liftOp, R.bind, litR, arith_sub_zero hx]

/-- `(sub ?x ?x)` is `(const 0)`, at every integer type. -/
theorem sub_self (t : IntTy) : Sound Defs.sub_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.sub_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t 0, ?_, ?_⟩
  · simp only [Defs.sub_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hx]
    simp only [intBin, liftOp, R.bind, arith_sub_self hx]
  · simp only [Defs.sub_self, Pat.eval, litVal, litR, Nat.zero_mod]

/-- `(mul ?x (const 1))` is `?x`, at every integer type. -/
theorem mul_one (t : IntTy) : Sound Defs.mul_one (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.mul_one, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.mul_one, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  simp only [intBin, liftOp, R.bind, litR, arith_mul_one hx]

/-- `(mul ?x (const 0))` refines to `(const 0)`, at every integer type (a
    one-way rule: the right disjunct of the refines statement, since `mul` is
    total and the left side is never undefined). -/
theorem mul_zero (t : IntTy) : Sound Defs.mul_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.mul_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inr ⟨.int t (litR (t.bits pb) false 0), ?_, ?_⟩
  · simp only [Defs.mul_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    simp only [intBin, liftOp, R.bind, litR, arith_mul_zero]
  · simp only [Defs.mul_zero, Pat.eval, litVal]

/-- `(add ?x ?x)` refines to `(mul ?x (const 2))`, at every integer type (a
    one-way rule: the right disjunct of the refines statement, since `add` is
    total and the left side is never undefined). -/
theorem double_to_mul (t : IntTy) : Sound Defs.double_to_mul (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.double_to_mul, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inr ⟨.int t ((x + x) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [Defs.double_to_mul, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hx]
    simp only [intBin, liftOp, R.bind]
  · simp only [Defs.double_to_mul, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    simp only [intBin, liftOp, R.bind, litR, arith_double]

/-- `(add (add ?x (const ?a)) (const ?b))` is `(add ?x (eval add ?a ?b))`, at
    every integer type, with `(eval add ?a ?b)` read as SemR's `add` on the
    two constants (premise `checker-ground-eval`). -/
theorem add_add_const (t : IntTy) : Sound Defs.add_add_const (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.add_add_const, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (((x + a) % modulus (t.bits pb) + b) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [Defs.add_add_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx ha]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) hb]
    simp only [intBin, liftOp, R.bind]
  · simp only [Defs.add_add_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int ha hb]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int hx (mod_modulus_lt _ _)]
    simp only [intBin, liftOp, R.bind, arith_add_add]

/-- `(mul (mul ?x (const ?a)) (const ?b))` is `(mul ?x (eval mul ?a ?b))`, at
    every integer type, with `(eval mul ?a ?b)` read as SemR's `mul` on the
    two constants (premise `checker-ground-eval`). -/
theorem mul_mul_const (t : IntTy) : Sound Defs.mul_mul_const (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.mul_mul_const, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t ((x * a * b) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [Defs.mul_mul_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx ha]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int (mod_modulus_lt _ _) hb]
    simp [intBin, liftOp, R.bind, Nat.mod_mul_mod]
  · simp only [Defs.mul_mul_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int ha hb]
    simp only [intBin, liftOp, R.bind]
    rw [evalBinop_int hx (mod_modulus_lt _ _)]
    simp [intBin, liftOp, R.bind, Nat.mul_mod_mod, Nat.mul_assoc]

end EqsatInt
