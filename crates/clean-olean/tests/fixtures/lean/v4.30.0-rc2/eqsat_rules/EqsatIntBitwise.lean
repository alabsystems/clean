/- EqsatIntBitwise: the bitwise rules of the integer rule set (PKG-U2, lemma
   group c).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   One lemma per rule, `EqsatInt.<rule> : ∀ t, Sound Defs.<rule> (.int t)`, for
   `and_const_right`, `or_const_right`, `xor_const_right`, `and_self`,
   `and_zero` (refines), `and_ones`, `or_self`, `or_zero`, `or_ones` (refines),
   `xor_self`, `xor_zero`, `not_not`, `and_and_const`, `or_or_const` and
   `xor_xor_const`: all fifteen, each at every integer type and every admitted
   pointer width. The `bool` instances of `and_self` and `or_self` are in
   `EqsatIntCmpSelBool.lean`. A rule with no lemma here is not proved.

   SemR's `and`, `or` and `xor` are `Nat.land`, `Nat.lor` and `Nat.xor` reduced
   modulo `2^w`; `bv_decide` and `native_decide` are not available (the
   reference entry refuses `Lean.ofReduceBool`), so each lemma is a proof over
   `Nat` bit operations at an arbitrary width: no case split on the type or
   the width, and no use of the pointer-width hypothesis.

   The helpers of this group are named `EqsatInt.bitwise_*` (the gate loads
   every module of the family into one environment, so a helper's name is the
   group's own): `bitwise_and_lt`, `bitwise_or_lt`, `bitwise_xor_lt` (the
   result of an operator on residues below `2^w` is below `2^w`),
   `bitwise_eval_and`, `bitwise_eval_or`, `bitwise_eval_xor` (so SemR's
   reduction is the identity there, stated at the value evaluator),
   `bitwise_litR_zero`, `bitwise_or_all_ones` and `bitwise_not_lt`.

   The three rules with `(eval OP ?a ?b)` on the right (`and_and_const`,
   `or_or_const`, `xor_xor_const`) are stated with the operator over the two
   constant variables and carry the named premise `checker-ground-eval`.
-/
import EqsatBasics
import EqsatIntRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-- `(xor ?x ?x)` is `(const 0)`, at every integer type. -/
theorem xor_self (t : IntTy) : Sound Defs.xor_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.xor_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t 0, ?_, ?_⟩
  · simp only [Defs.xor_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hx]
    simp [intBin, liftOp, R.bind]
  · simp [Defs.xor_self, Pat.eval, litVal, litR, Nat.zero_mod]

/-- `(and ?x (const -1))` is `?x`, at every integer type. -/
theorem and_ones (t : IntTy) : Sound Defs.and_ones (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.and_ones, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.and_ones, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  have hx' : x < 2 ^ t.bits pb := hx
  simp [intBin, liftOp, R.bind, litR_neg_one, modulus, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hx']

/-! ## The residue operators on admitted operands

`intBin` reduces `Nat.land`, `Nat.lor` and `Nat.xor` modulo `2^w`; on operands
below `2^w` the result is already below it, so the reduction is the identity.
The three `bitwise_eval_*` lemmas say so at the value evaluator, and are what every
lemma below rewrites with. -/

theorem bitwise_and_lt {w : Nat} (x : Nat) {y : Nat} (hy : y < modulus w) : x &&& y < modulus w :=
  Nat.and_lt_two_pow x hy

theorem bitwise_or_lt {w x y : Nat} (hx : x < modulus w) (hy : y < modulus w) :
    x ||| y < modulus w :=
  Nat.or_lt_two_pow hx hy

theorem bitwise_xor_lt {w x y : Nat} (hx : x < modulus w) (hy : y < modulus w) :
    x ^^^ y < modulus w :=
  Nat.xor_lt_two_pow hx hy

theorem bitwise_eval_and {pb : Nat} {t : IntTy} {x y : Nat}
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    evalBinop pb .and (.int t) (.int t x) (.int t y) = .ok (.int t (x &&& y)) := by
  rw [evalBinop_int hx hy]
  have h : Nat.land x y % modulus (t.bits pb) = x &&& y := Nat.mod_eq_of_lt (bitwise_and_lt x hy)
  simp only [intBin, liftOp, R.bind, h]

theorem bitwise_eval_or {pb : Nat} {t : IntTy} {x y : Nat}
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    evalBinop pb .or (.int t) (.int t x) (.int t y) = .ok (.int t (x ||| y)) := by
  rw [evalBinop_int hx hy]
  have h : Nat.lor x y % modulus (t.bits pb) = x ||| y := Nat.mod_eq_of_lt (bitwise_or_lt hx hy)
  simp only [intBin, liftOp, R.bind, h]

theorem bitwise_eval_xor {pb : Nat} {t : IntTy} {x y : Nat}
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    evalBinop pb .xor (.int t) (.int t x) (.int t y) = .ok (.int t (x ^^^ y)) := by
  rw [evalBinop_int hx hy]
  have h : Nat.xor x y % modulus (t.bits pb) = x ^^^ y := Nat.mod_eq_of_lt (bitwise_xor_lt hx hy)
  simp only [intBin, liftOp, R.bind, h]

/-- The literal `(const 0)` is the residue `0`. -/
theorem bitwise_litR_zero (w : Nat) : litR w false 0 = 0 := by
  simp [litR]

/-- Or with the all-ones residue is the all-ones residue. -/
theorem bitwise_or_all_ones {w x : Nat} (hx : x < 2 ^ w) : x ||| (2 ^ w - 1) = 2 ^ w - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · simp [hi]
  · have hle : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)
    simp [hi, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hle)]

/-! ## Constant to the right -/

/-- `(and (const ?c) ?x)` is `(and ?x (const ?c))`, at every integer type. -/
theorem and_const_right (t : IntTy) : Sound Defs.and_const_right (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.and_const_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x &&& c), ?_, ?_⟩
  · simp only [Defs.and_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_and hc hx, Nat.and_comm]
  · simp only [Defs.and_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_and hx hc]

/-- `(or (const ?c) ?x)` is `(or ?x (const ?c))`, at every integer type. -/
theorem or_const_right (t : IntTy) : Sound Defs.or_const_right (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.or_const_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x ||| c), ?_, ?_⟩
  · simp only [Defs.or_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_or hc hx, Nat.or_comm]
  · simp only [Defs.or_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_or hx hc]

/-- `(xor (const ?c) ?x)` is `(xor ?x (const ?c))`, at every integer type. -/
theorem xor_const_right (t : IntTy) : Sound Defs.xor_const_right (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.xor_const_right, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x ^^^ c), ?_, ?_⟩
  · simp only [Defs.xor_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_xor hc hx, Nat.xor_comm]
  · simp only [Defs.xor_const_right, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_xor hx hc]

/-! ## Idempotence, zero and all-ones -/

/-- `(and ?x ?x)` is `?x`, at every integer type. -/
theorem and_self (t : IntTy) : Sound Defs.and_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.and_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.and_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [bitwise_eval_and hx hx, Nat.and_self]

/-- `(and ?x (const 0))` refines to `(const 0)`, at every integer type (a
    one-way rule: the right disjunct of the refines statement, since the left
    side is never undefined). -/
theorem and_zero (t : IntTy) : Sound Defs.and_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.and_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inr ⟨.int t 0, ?_, ?_⟩
  · simp only [Defs.and_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [bitwise_eval_and hx (litR_lt _ _ _), bitwise_litR_zero, Nat.and_zero]
  · simp only [Defs.and_zero, Pat.eval, litVal, bitwise_litR_zero]

/-- `(or ?x ?x)` is `?x`, at every integer type. -/
theorem or_self (t : IntTy) : Sound Defs.or_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.or_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.or_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [bitwise_eval_or hx hx, Nat.or_self]

/-- `(or ?x (const 0))` is `?x`, at every integer type. -/
theorem or_zero (t : IntTy) : Sound Defs.or_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.or_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.or_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [bitwise_eval_or hx (litR_lt _ _ _), bitwise_litR_zero, Nat.or_zero]

/-- `(or ?x (const -1))` refines to `(const -1)`, at every integer type (a
    one-way rule: the right disjunct of the refines statement, since the left
    side is never undefined). -/
theorem or_ones (t : IntTy) : Sound Defs.or_ones (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.or_ones, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inr ⟨.int t (2 ^ t.bits pb - 1), ?_, ?_⟩
  · simp only [Defs.or_ones, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [bitwise_eval_or hx (litR_lt _ _ _), litR_neg_one, bitwise_or_all_ones hx]
  · simp only [Defs.or_ones, Pat.eval, litVal, litR_neg_one]

/-- `(xor ?x (const 0))` is `?x`, at every integer type. -/
theorem xor_zero (t : IntTy) : Sound Defs.xor_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.xor_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.xor_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [bitwise_eval_xor hx (litR_lt _ _ _), bitwise_litR_zero, Nat.xor_zero]

/-! ## Complement -/

/-- SemR's `not` on a residue in range: `2^w - 1 - x`, in range again. -/
theorem bitwise_not_lt (w x : Nat) : intUn .not w x < modulus w := by
  have := modulus_pos w
  simp only [intUn]
  omega

/-- `(not (not ?x))` is `?x`, at every integer type. -/
theorem not_not (t : IntTy) : Sound Defs.not_not (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.not_not, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.not_not, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalUnop_int hx]
  dsimp only
  rw [evalUnop_int (bitwise_not_lt _ _)]
  have h : intUn .not (t.bits pb) (intUn .not (t.bits pb) x) = x := by
    simp only [intUn]
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h]

/-! ## Two constants (premise `checker-ground-eval`)

The right side's `(eval OP ?a ?b)` is the same operator over the two constant
variables, read as SemR's operator; that the checker's ground evaluator
computes it is the named premise, not part of these statements. -/

/-- `(and (and ?x (const ?a)) (const ?b))` is `(and ?x (eval and ?a ?b))`, at
    every integer type. -/
theorem and_and_const (t : IntTy) : Sound Defs.and_and_const (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.and_and_const, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x &&& (a &&& b)), ?_, ?_⟩
  · simp only [Defs.and_and_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_and hx ha]
    dsimp only
    rw [bitwise_eval_and (bitwise_and_lt x ha) hb, Nat.and_assoc]
  · simp only [Defs.and_and_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_and ha hb]
    dsimp only
    rw [bitwise_eval_and hx (bitwise_and_lt a hb)]

/-- `(or (or ?x (const ?a)) (const ?b))` is `(or ?x (eval or ?a ?b))`, at
    every integer type. -/
theorem or_or_const (t : IntTy) : Sound Defs.or_or_const (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.or_or_const, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x ||| (a ||| b)), ?_, ?_⟩
  · simp only [Defs.or_or_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_or hx ha]
    dsimp only
    rw [bitwise_eval_or (bitwise_or_lt hx ha) hb, Nat.or_assoc]
  · simp only [Defs.or_or_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_or ha hb]
    dsimp only
    rw [bitwise_eval_or hx (bitwise_or_lt ha hb)]

/-- `(xor (xor ?x (const ?a)) (const ?b))` is `(xor ?x (eval xor ?a ?b))`, at
    every integer type. -/
theorem xor_xor_const (t : IntTy) : Sound Defs.xor_xor_const (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.xor_xor_const, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (x ^^^ (a ^^^ b)), ?_, ?_⟩
  · simp only [Defs.xor_xor_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_xor hx ha]
    dsimp only
    rw [bitwise_eval_xor (bitwise_xor_lt hx ha) hb, Nat.xor_assoc]
  · simp only [Defs.xor_xor_const, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [bitwise_eval_xor ha hb]
    dsimp only
    rw [bitwise_eval_xor hx (bitwise_xor_lt ha hb)]

end EqsatInt
