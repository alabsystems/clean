/- EqsatBasics: what a lemma about a rule statement stands on (PKG-U2).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   Proof helpers over `EqsatRule`, none of them part of what a rule means:
   * `admits_nil`, `admits_cons_t_int`, `admits_cons_bool`, `admits_cons_t_bool`
     turn an `Admits` hypothesis into the assignment's shape (rewrite with
     them, then `obtain` the values);
   * `evalBinop_int`, `evalBinop_bool`, `evalUnop_int`, `evalIcmp_int`,
     `evalIcmp_bool`, `selectVal_int`, `selectVal_bool` reduce SemR's value
     evaluators on admitted operands to SemR's residue operators (`intBin`,
     `boolBin`, `intUn`, `icmpR`), which is where a rule's arithmetic is;
   * `bits_cases` and `bits_pos` give the width of an instance type under
     `PbOk`; `litR_lt`, `negR_lt` and `mod_modulus_lt` the range of a literal,
     a negation and a reduced result (the operand hypotheses of the evaluator
     lemmas when an operator is applied to another's result), and
     `litR_neg_one` the all-ones residue of `(const -1)`.
   A helper more than one lemma module needs belongs here: the gate loads
   every module of the family into one environment, so two modules that
   declare one name do not load.
   `EqsatIntSample.lean` shows the proof shape these support.
-/
import EqsatRule

namespace EqsatRule
open SemR

/-- The number of variables. -/
def Sorts.len : Sorts → Nat
  | .nil => 0
  | .cons _ _ rest => rest.len + 1

theorem modulus_pos (w : Nat) : 0 < modulus w := Nat.pow_pos (by decide)

/-- A residue reduced modulo the width's modulus is in range. -/
theorem mod_modulus_lt (w x : Nat) : x % modulus w < modulus w := Nat.mod_lt _ (modulus_pos w)

theorem negR_lt (w x : Nat) : negR w x < modulus w := Nat.mod_lt _ (modulus_pos w)

theorem ty_beq_int (t : IntTy) : (Ty.int t).beq (.int t) = true := by
  cases t <;> rfl

theorem expectTy_int {pb : Nat} {t : IntTy} {x : Nat} (h : x < modulus (t.bits pb)) :
    expectTy pb (.int t x) (.int t) = .ok () := by
  simp [expectTy, Val.ty, ty_beq_int, h]

theorem expectTy_bool (pb : Nat) (b : Bool) : expectTy pb (.bool b) .bool = .ok () := rfl

theorem evalBinop_int {pb : Nat} {op : BinOp} {t : IntTy} {x y : Nat}
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    evalBinop pb op (.int t) (.int t x) (.int t y) =
      (liftOp (intBin op (t.bits pb) x y)).bind fun r => .ok (.int t r) := by
  simp [evalBinop, expectTy_int hx, expectTy_int hy, isBoolTy, expectInt, rejectPoison,
    bind, R.bind, pure]

theorem evalBinop_bool (pb : Nat) (op : BinOp) (a b : Bool) :
    evalBinop pb op .bool (.bool a) (.bool b) =
      (liftOp (boolBin op a b)).bind fun r => .ok (.bool r) := by
  simp [evalBinop, expectTy_bool, isBoolTy, expectBool, rejectPoison, bind, R.bind, pure]

theorem evalUnop_int {pb : Nat} {op : UnOp} {t : IntTy} {x : Nat}
    (hx : x < modulus (t.bits pb)) :
    evalUnop pb op (.int t) (.int t x) = .ok (.int t (intUn op (t.bits pb) x)) := by
  simp [evalUnop, expectTy_int hx, expectInt, rejectPoison, bind, R.bind, pure]

theorem evalIcmp_int {pb : Nat} {op : ICmpOp} {t : IntTy} {x y : Nat}
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    evalIcmp pb op (.int t) (.int t x) (.int t y) =
      .ok (.bool (icmpR op (t.bits pb) x y)) := by
  simp [evalIcmp, expectTy_int hx, expectTy_int hy, isBoolTy, expectInt, rejectPoison,
    bind, R.bind, pure]

theorem evalIcmp_bool (pb : Nat) (op : ICmpOp) (a b : Bool) :
    evalIcmp pb op .bool (.bool a) (.bool b) = .ok (.bool (icmpR op 1 (b2n a) (b2n b))) := by
  simp [evalIcmp, expectTy_bool, isBoolTy, expectBool, rejectPoison, bind, R.bind, pure]

theorem selectVal_int {pb : Nat} {t : IntTy} {x y : Nat} (c : Bool)
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    selectVal pb (.int t) (.bool c) (.int t x) (.int t y) =
      .ok (match c with | true => .int t x | false => .int t y) := by
  cases c <;>
    simp [selectVal, expectTy_int hx, expectTy_int hy, rejectPoison, asBool, bind, R.bind, pure]

theorem selectVal_bool (pb : Nat) (c x y : Bool) :
    selectVal pb .bool (.bool c) (.bool x) (.bool y) =
      .ok (match c with | true => .bool x | false => .bool y) := by
  cases c <;> simp [selectVal, expectTy_bool, rejectPoison, asBool, bind, R.bind, pure]

theorem admits_nil {pb : Nat} {T : STy} {env : List Val} :
    Admits pb T .nil env ↔ env = [] := by
  cases env <;> simp [Admits]

theorem admits_cons_t_int {pb : Nat} {t : IntTy} {c : Bool} {rest : Sorts} {env : List Val} :
    Admits pb (.int t) (.cons .t c rest) env ↔
      ∃ x vs, env = .int t x :: vs ∧ x < modulus (t.bits pb) ∧ Admits pb (.int t) rest vs := by
  cases env with
  | nil => simp [Admits]
  | cons v vs =>
    simp only [Admits, AdmitsVal]
    constructor
    · rintro ⟨⟨r, rfl, hr⟩, h⟩; exact ⟨r, vs, rfl, hr, h⟩
    · rintro ⟨x, vs', h, hx, hr⟩; cases h; exact ⟨⟨x, rfl, hx⟩, hr⟩

theorem admits_cons_bool {pb : Nat} {T : STy} {c : Bool} {rest : Sorts} {env : List Val} :
    Admits pb T (.cons .bool c rest) env ↔
      ∃ b vs, env = .bool b :: vs ∧ Admits pb T rest vs := by
  cases env with
  | nil => simp [Admits]
  | cons v vs =>
    simp only [Admits, AdmitsVal]
    constructor
    · rintro ⟨⟨b, rfl⟩, h⟩; exact ⟨b, vs, rfl, h⟩
    · rintro ⟨b, vs', h, hr⟩; cases h; exact ⟨⟨b, rfl⟩, hr⟩

theorem admits_cons_t_bool {pb : Nat} {c : Bool} {rest : Sorts} {env : List Val} :
    Admits pb .bool (.cons .t c rest) env ↔
      ∃ b vs, env = .bool b :: vs ∧ Admits pb .bool rest vs := by
  cases env with
  | nil => simp [Admits]
  | cons v vs =>
    simp only [Admits, AdmitsVal]
    constructor
    · rintro ⟨⟨b, rfl⟩, h⟩; exact ⟨b, vs, rfl, h⟩
    · rintro ⟨b, vs', h, hr⟩; cases h; exact ⟨⟨b, rfl⟩, hr⟩

/-- The width of an integer instance type under its pointer-width hypothesis. -/
theorem bits_cases {pb : Nat} {t : IntTy} (h : PbOk (.int t) pb) :
    t.bits pb = 8 ∨ t.bits pb = 16 ∨ t.bits pb = 32 ∨ t.bits pb = 64 ∨ t.bits pb = 128 := by
  cases t <;> simp [IntTy.bits]
  all_goals (simp only [PbOk] at h; omega)

theorem bits_pos {pb : Nat} {t : IntTy} (h : PbOk (.int t) pb) : 0 < t.bits pb := by
  have := bits_cases h; omega

theorem litR_lt (w : Nat) (neg : Bool) (mag : Nat) : litR w neg mag < modulus w := by
  cases neg <;> simp only [litR, negR] <;> exact Nat.mod_lt _ (modulus_pos w)

/-- `(const -1)` is the all-ones residue `2^w - 1`. -/
theorem litR_neg_one (w : Nat) : litR w true 1 = 2 ^ w - 1 := by
  simp only [litR, negR, modulus]
  by_cases h : 1 < 2 ^ w
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  · have h1 : 2 ^ w = 1 := by have := Nat.pow_pos (n := w) (by decide : 0 < 2); omega
    simp [h1]

end EqsatRule
