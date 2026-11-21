/- EqsatAnchors: kernel-checked statements that pin what `EqsatRule` means (PKG-U2).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `EqsatRule.Sound` is trusted as read. These theorems are what a reader can
   check it against. The gate (`crates/clean-olean/tests/eqsat_rules.rs`)
   requires every theorem of this module by name in the replayed kernel
   environment and pins a digest of its statement (`STATEMENTS` beside this
   file), so an anchor that is weakened, renamed or deleted fails the gate.

   * `admits_one_iff`: a variable admits exactly the values SemR's own checks
     accept at its type (`rejectPoison` and `expectTy`), so `Admits` neither
     lets poison in nor leaves a well-typed value out;
   * `admits_inhabited`, `pbOk_inhabited`: every variable list has an
     admitted assignment at every type and pointer width. This does not make
     the hypotheses of `Sound` satisfiable: the side conditions are a third
     hypothesis, and a rule whose conditions contradict each other is `Sound`
     for want of an assignment (`sound_of_unsatisfiable`;
     `EqsatIntControls.contradictory_is_sound`). `Satisfiable` is the
     statement that a rule's conditions can be met; it holds for nothing
     where there is no condition or the type is `Bool`
     (`satisfiable_of_no_conds`, `satisfiable_bool`), and is a lemma to be
     proved otherwise;
   * `sound_equiv_iff`, `sound_refines_iff`: the two branches of `Sound`,
     unfolded, and `equiv_gives_refines`: the equiv statement is the stronger.
     It is strictly stronger only through an operator that is not total:
     `refines_gives_equiv_of_total` is the converse for a left side of total
     operators, which is every left side the rule grammar admits;
   * `equiv_stop_never`, `refines_stop_left`, `refines_value_left`: what each
     direction says where a side is not a value;
   * `pbOk_iff`: the pointer-width hypothesis binds `isize` and `usize` only;
   * `bin_eval`, `un_eval`, `cmp_eval`, `sel_eval` and the `*_stop*`
     theorems: each operator arm of `Pat.eval` is SemR's evaluator on the
     operand values in the pattern's order, and the leftmost stop is the
     arm's; `bin_int`, `bin_int_rev`, `bin_bool`, `un_int`, `cmp_int`,
     `sel_int`, `sel_bool` take that down to SemR's residue operators;
     `bin_reads`, `un_reads`, `cmp_reads`, `sel_reads`, `stop_order` are
     concrete values that tell operands, operators, predicates and arms
     apart;
   * `const_flag_is_data`, `var_cvar_one_statement`: parts of a literal that
     do not reach the proposition;
   * `lit_*`, `getVar_*`, `cond_*`, `binTy_*`: literals, unbound variables, side
     conditions and operand types read as the checker's replay reads them.
-/
import EqsatBasics

namespace EqsatRule
open SemR

/-! ## Admission -/

/-- A single variable of sort `s` admits `v` exactly when SemR's own checks
    accept `v` as an inspected operand of the sort's type: it is not poison
    (`rejectPoison`, whatever the site label) and it has the type with its
    residue in range (`expectTy`). -/
theorem admits_one_iff (pb : Nat) (T : STy) (s : Srt) (c : Bool) (v : Val) (what : String) :
    Admits pb T (.cons s c .nil) [v] ↔
      (rejectPoison v what = .ok () ∧ expectTy pb v (s.ty T) = .ok ()) := by
  have hcode : ∀ a b : IntTy, a.code = b.code ↔ a = b := by
    intro a b; cases a <;> cases b <;> simp [IntTy.code]
  cases s <;> cases T <;> cases v <;>
    simp [Admits, AdmitsVal, Srt.ty, STy.ty, rejectPoison, expectTy, Val.ty, Ty.beq, ubR, tyR]
  rename_i t t' raw
  by_cases ht : t' = t
  · subst ht
    by_cases hr : raw < modulus (IntTy.bits pb t') <;> simp [hr]
  · have hne : t'.code ≠ t.code := fun h => ht ((hcode _ _).1 h)
    simp [ht, hne]

/-- Every variable list has an admitted assignment, at every type and pointer
    width. -/
theorem admits_inhabited (pb : Nat) (T : STy) (vars : Sorts) : ∃ env, Admits pb T vars env := by
  induction vars with
  | nil => exact ⟨[], trivial⟩
  | cons s c rest ih =>
    obtain ⟨vs, h⟩ := ih
    cases s <;> cases T
    · rename_i t; exact ⟨.int t 0 :: vs, ⟨0, rfl, modulus_pos _⟩, h⟩
    · exact ⟨.bool false :: vs, ⟨false, rfl⟩, h⟩
    · exact ⟨.bool false :: vs, ⟨false, rfl⟩, h⟩
    · exact ⟨.bool false :: vs, ⟨false, rfl⟩, h⟩

/-- An assignment has exactly one value per variable. -/
theorem admits_length {pb : Nat} {T : STy} :
    ∀ (vars : Sorts) (env : List Val), Admits pb T vars env →
      env.length = vars.len
  | .nil, [], _ => rfl
  | .nil, _ :: _, h => by simp [Admits] at h
  | .cons _ _ _, [], h => by simp [Admits] at h
  | .cons _ _ rest, _ :: vs, h => by
    simp only [Admits] at h
    simp [Sorts.len, admits_length rest vs h.2]

/-! ## Pointer width -/

/-- The pointer-width hypothesis binds `isize` and `usize` only. -/
theorem pbOk_iff (pb : Nat) (t : IntTy) :
    PbOk (.int t) pb ↔ (t.code = IntTy.isize.code ∨ t.code = IntTy.usize.code → pb = 32 ∨ pb = 64) := by
  cases t <;> simp [PbOk, IntTy.code]

theorem pbOk_bool (pb : Nat) : PbOk .bool pb := trivial

theorem pbOk_inhabited (T : STy) : PbOk T 64 := by
  cases T with
  | bool => trivial
  | int t => cases t <;> simp [PbOk]

/-- A fixed-width type has its width at every pointer width, and `isize` and
    `usize` have the pointer width. -/
theorem bits_fixed (pb : Nat) :
    IntTy.i8.bits pb = 8 ∧ IntTy.u8.bits pb = 8 ∧ IntTy.i16.bits pb = 16 ∧ IntTy.u16.bits pb = 16 ∧
    IntTy.i32.bits pb = 32 ∧ IntTy.u32.bits pb = 32 ∧ IntTy.i64.bits pb = 64 ∧ IntTy.u64.bits pb = 64 ∧
    IntTy.i128.bits pb = 128 ∧ IntTy.u128.bits pb = 128 ∧
    IntTy.isize.bits pb = pb ∧ IntTy.usize.bits pb = pb :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The two branches of `Sound` -/

theorem sound_equiv_iff (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy) :
    Sound ⟨.equiv, vars, lhs, rhs, conds⟩ T ↔
      ∀ pb env, PbOk T pb → Admits pb T vars env → CondsHold pb T env conds →
        ∃ v, lhs.eval pb T env = .ok v ∧ rhs.eval pb T env = .ok v :=
  Iff.rfl

theorem sound_refines_iff (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy) :
    Sound ⟨.refines, vars, lhs, rhs, conds⟩ T ↔
      ∀ pb env, PbOk T pb → Admits pb T vars env → CondsHold pb T env conds →
        (∃ m, lhs.eval pb T env = .stop (.ub m)) ∨
        (∃ v, lhs.eval pb T env = .ok v ∧ rhs.eval pb T env = .ok v) :=
  Iff.rfl

/-- The equiv statement is the stronger one. `EqsatIntControls.lean` shows the
    converse fails. -/
theorem equiv_gives_refines (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy)
    (h : Sound ⟨.equiv, vars, lhs, rhs, conds⟩ T) : Sound ⟨.refines, vars, lhs, rhs, conds⟩ T :=
  fun pb env hpb hadm hc => Or.inr (h pb env hpb hadm hc)

/-- An equiv statement makes both sides defined: neither is undefined
    behaviour, a type error or any other stop. -/
theorem equiv_sides_defined {l r : R Val} (h : Holds .equiv l r) :
    (∃ v, l = .ok v) ∧ (∃ v, r = .ok v) := by
  obtain ⟨v, hl, hr⟩ := h
  exact ⟨⟨v, hl⟩, ⟨v, hr⟩⟩

/-! ## Literals and variables -/

theorem lit_pos (w mag : Nat) : litR w false mag = mag % modulus w := rfl
theorem lit_neg (w mag : Nat) : litR w true mag = negR w mag := rfl

/-- `(const -1)` is all ones and `(const 255)` is itself at eight bits, and
    `(const 255)` is not `-1` at sixteen. -/
theorem lit_examples :
    litR 8 true 1 = 255 ∧ litR 8 false 255 = 255 ∧ litR 16 true 1 = 65535 ∧
    litR 16 false 255 = 255 ∧ litR 8 false 256 = 0 ∧ litR 8 true 0 = 0 := by decide

theorem lit_int (pb : Nat) (t : IntTy) (env : List Val) (neg : Bool) (mag : Nat) :
    (Pat.lit neg mag).eval pb (.int t) env = .ok (.int t (litR (t.bits pb) neg mag)) := rfl

/-- `(const INT)` is not a term at `Bool`: neither a value nor undefined
    behaviour. -/
theorem lit_bool (pb : Nat) (env : List Val) (neg : Bool) (mag : Nat) :
    (∀ v, (Pat.lit neg mag).eval pb .bool env ≠ .ok v) ∧
    (∀ m, (Pat.lit neg mag).eval pb .bool env ≠ .stop (.ub m)) := by
  constructor <;> intro _ h <;> simp [Pat.eval, litVal] at h

theorem bool_consts (pb : Nat) (T : STy) (env : List Val) :
    Pat.tt.eval pb T env = .ok (.bool true) ∧ Pat.ff.eval pb T env = .ok (.bool false) :=
  ⟨rfl, rfl⟩

/-- `?v` and `(const ?v)` both denote the value bound at the variable's rank. -/
theorem var_cvar (pb : Nat) (T : STy) (env : List Val) (i : Nat) :
    (Pat.var i).eval pb T env = getVar env i ∧ (Pat.cvar i).eval pb T env = getVar env i :=
  ⟨rfl, rfl⟩

theorem getVar_bound (v w : Val) (rest : List Val) :
    getVar (v :: w :: rest) 0 = .ok v ∧ getVar (v :: w :: rest) 1 = .ok w :=
  ⟨rfl, rfl⟩

/-- An unbound rank is not a term: neither a value nor undefined behaviour. -/
theorem getVar_unbound (i : Nat) :
    (∀ v, getVar [] i ≠ .ok v) ∧ (∀ m, getVar [] i ≠ .stop (.ub m)) := by
  constructor <;> intro _ h <;> simp [getVar] at h

/-! ## Operand types -/

/-- `band bor bxor` take `Bool` operands at every instance type; every other
    binary operator takes the instance type. -/
theorem binTy_bool_ops (T : STy) :
    binTy T .bAnd = .bool ∧ binTy T .bOr = .bool ∧ binTy T .bXor = .bool :=
  ⟨rfl, rfl, rfl⟩

theorem binTy_instance_ops (T : STy) :
    binTy T .add = T.ty ∧ binTy T .sub = T.ty ∧ binTy T .mul = T.ty ∧ binTy T .and = T.ty ∧
    binTy T .or = T.ty ∧ binTy T .xor = T.ty ∧ binTy T .rotl = T.ty ∧ binTy T .rotr = T.ty :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An integer-only operator is not a term at `Bool`: SemR refuses it. -/
theorem add_at_bool (pb : Nat) (a b : Bool) :
    ∀ v, (Pat.bin .add (.var 0) (.var 1)).eval pb .bool [.bool a, .bool b] ≠ .ok v := by
  intro v h
  simp only [Pat.eval, getVar, R.bind, binTy, STy.ty] at h
  rw [evalBinop_bool] at h
  cases h

/-! ## Side conditions -/

theorem cond_eq (pb : Nat) (t t' : IntTy) (c : Nat) (rest : List Val) (neg : Bool) (mag : Nat) :
    Cond.holds pb (.int t) (.int t' c :: rest) (.eq 0 neg mag) ↔ c = litR (t.bits pb) neg mag :=
  Iff.rfl

theorem cond_ne (pb : Nat) (t t' : IntTy) (c : Nat) (rest : List Val) (neg : Bool) (mag : Nat) :
    Cond.holds pb (.int t) (.int t' c :: rest) (.ne 0 neg mag) ↔ c ≠ litR (t.bits pb) neg mag :=
  Iff.rfl

theorem cond_pow2 (pb : Nat) (t t' : IntTy) (c : Nat) (rest : List Val) :
    Cond.holds pb (.int t) (.int t' c :: rest) (.pow2 0) ↔ ∃ k, c = 2 ^ k :=
  Iff.rfl

theorem cond_zeroModWidth (pb : Nat) (t t' : IntTy) (c : Nat) (rest : List Val) :
    Cond.holds pb (.int t) (.int t' c :: rest) (.zeroModWidth 0) ↔ c % t.bits pb = 0 :=
  Iff.rfl

/-- A side condition with no residue to test says nothing: it holds at `Bool`
    and on an unbound rank, so it never makes a statement easier. -/
theorem cond_without_residue (pb : Nat) (env : List Val) (t : IntTy) (c : Cond) :
    Cond.holds pb .bool env c ∧ Cond.holds pb (.int t) [] c := by
  cases c <;> exact ⟨trivial, trivial⟩

theorem conds_nil (pb : Nat) (T : STy) (env : List Val) : CondsHold pb T env .nil := trivial

theorem conds_cons (pb : Nat) (T : STy) (env : List Val) (c : Cond) (rest : Conds) :
    CondsHold pb T env (.cons c rest) ↔ (c.holds pb T env ∧ CondsHold pb T env rest) :=
  Iff.rfl

/-! ## Operators: each arm of `Pat.eval`, read against SemR

Two readings of each arm. The general one: on operand values the arm is SemR's
evaluator on those values, in the pattern's operand order, at the arm's
operand type; and the first operand that stops is the arm's stop. The concrete
one (`*_reads`): values that tell the operands, the operators and the
predicates apart, so an arm that swapped two operands, ignored one or read
every operator as one would not compile these. -/

theorem bin_eval {pb : Nat} {T : STy} {env : List Val} {a b : Pat} {x y : Val} (op : BinOp)
    (ha : a.eval pb T env = .ok x) (hb : b.eval pb T env = .ok y) :
    (Pat.bin op a b).eval pb T env = evalBinop pb op (binTy T op) x y := by
  simp only [Pat.eval, ha, hb, R.bind]

theorem un_eval {pb : Nat} {T : STy} {env : List Val} {a : Pat} {x : Val} (op : UnOp)
    (ha : a.eval pb T env = .ok x) :
    (Pat.un op a).eval pb T env = evalUnop pb op T.ty x := by
  simp only [Pat.eval, ha, R.bind]

theorem cmp_eval {pb : Nat} {T : STy} {env : List Val} {a b : Pat} {x y : Val} (op : ICmpOp)
    (ha : a.eval pb T env = .ok x) (hb : b.eval pb T env = .ok y) :
    (Pat.cmp op a b).eval pb T env = evalIcmp pb op T.ty x y := by
  simp only [Pat.eval, ha, hb, R.bind]

/-- `(select c a b)`: SemR's `selectVal` on the condition, the true arm `a`
    and the false arm `b`, in that order. -/
theorem sel_eval {pb : Nat} {T : STy} {env : List Val} {c a b : Pat} {cv x y : Val}
    (hc : c.eval pb T env = .ok cv) (ha : a.eval pb T env = .ok x)
    (hb : b.eval pb T env = .ok y) :
    (Pat.sel c a b).eval pb T env = selectVal pb T.ty cv x y := by
  simp only [Pat.eval, hc, ha, hb, R.bind]

/-- The first operand that stops is the pattern's stop: operands are read left
    to right, and an operator is not consulted once one has stopped. Which
    stop a side reports matters to `refines`, whose left side may be undefined
    behaviour and nothing else. -/
theorem bin_stop_left {pb : Nat} {T : STy} {env : List Val} {a : Pat} {o : Out} (op : BinOp)
    (b : Pat) (ha : a.eval pb T env = .stop o) : (Pat.bin op a b).eval pb T env = .stop o := by
  simp only [Pat.eval, ha, R.bind]

theorem bin_stop_right {pb : Nat} {T : STy} {env : List Val} {a b : Pat} {x : Val} {o : Out}
    (op : BinOp) (ha : a.eval pb T env = .ok x) (hb : b.eval pb T env = .stop o) :
    (Pat.bin op a b).eval pb T env = .stop o := by
  simp only [Pat.eval, ha, hb, R.bind]

theorem un_stop {pb : Nat} {T : STy} {env : List Val} {a : Pat} {o : Out} (op : UnOp)
    (ha : a.eval pb T env = .stop o) : (Pat.un op a).eval pb T env = .stop o := by
  simp only [Pat.eval, ha, R.bind]

theorem cmp_stop_left {pb : Nat} {T : STy} {env : List Val} {a : Pat} {o : Out} (op : ICmpOp)
    (b : Pat) (ha : a.eval pb T env = .stop o) : (Pat.cmp op a b).eval pb T env = .stop o := by
  simp only [Pat.eval, ha, R.bind]

theorem cmp_stop_right {pb : Nat} {T : STy} {env : List Val} {a b : Pat} {x : Val} {o : Out}
    (op : ICmpOp) (ha : a.eval pb T env = .ok x) (hb : b.eval pb T env = .stop o) :
    (Pat.cmp op a b).eval pb T env = .stop o := by
  simp only [Pat.eval, ha, hb, R.bind]

theorem sel_stop_cond {pb : Nat} {T : STy} {env : List Val} {c : Pat} {o : Out} (a b : Pat)
    (hc : c.eval pb T env = .stop o) : (Pat.sel c a b).eval pb T env = .stop o := by
  simp only [Pat.eval, hc, R.bind]

theorem sel_stop_true {pb : Nat} {T : STy} {env : List Val} {c a : Pat} {cv : Val} {o : Out}
    (b : Pat) (hc : c.eval pb T env = .ok cv) (ha : a.eval pb T env = .stop o) :
    (Pat.sel c a b).eval pb T env = .stop o := by
  simp only [Pat.eval, hc, ha, R.bind]

theorem sel_stop_false {pb : Nat} {T : STy} {env : List Val} {c a b : Pat} {cv x : Val} {o : Out}
    (hc : c.eval pb T env = .ok cv) (ha : a.eval pb T env = .ok x)
    (hb : b.eval pb T env = .stop o) : (Pat.sel c a b).eval pb T env = .stop o := by
  simp only [Pat.eval, hc, ha, hb, R.bind]

/-- On admitted integer operands a binary operator is SemR's residue operator
    `intBin` on the left residue, then the right. -/
theorem bin_int {pb : Nat} {t : IntTy} {x y : Nat} (op : BinOp) (hop : binTy (.int t) op = .int t)
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    (Pat.bin op (.var 0) (.var 1)).eval pb (.int t) [.int t x, .int t y] =
      (liftOp (intBin op (t.bits pb) x y)).bind fun r => .ok (.int t r) := by
  simp only [Pat.eval, getVar, R.bind, hop]
  rw [evalBinop_int hx hy]
  rfl

/-- The pattern's operand order is the operator's: with the variables written
    in the other order, the residues reach `intBin` in the other order. -/
theorem bin_int_rev {pb : Nat} {t : IntTy} {x y : Nat} (op : BinOp)
    (hop : binTy (.int t) op = .int t)
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    (Pat.bin op (.var 1) (.var 0)).eval pb (.int t) [.int t x, .int t y] =
      (liftOp (intBin op (t.bits pb) y x)).bind fun r => .ok (.int t r) := by
  simp only [Pat.eval, getVar, R.bind, hop]
  rw [evalBinop_int hy hx]
  rfl

/-- `band bor bxor` on two `Bool`s, at every instance type. -/
theorem bin_bool (pb : Nat) (T : STy) (a b : Bool) :
    (Pat.bin .bAnd (.var 0) (.var 1)).eval pb T [.bool a, .bool b] = .ok (.bool (a && b)) ∧
    (Pat.bin .bOr (.var 0) (.var 1)).eval pb T [.bool a, .bool b] = .ok (.bool (a || b)) ∧
    (Pat.bin .bXor (.var 0) (.var 1)).eval pb T [.bool a, .bool b] = .ok (.bool (a != b)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Pat.eval, getVar, R.bind, binTy] <;> rw [evalBinop_bool] <;> rfl

theorem un_int {pb : Nat} {t : IntTy} {x : Nat} (op : UnOp) (hx : x < modulus (t.bits pb)) :
    (Pat.un op (.var 0)).eval pb (.int t) [.int t x] = .ok (.int t (intUn op (t.bits pb) x)) := by
  simp only [Pat.eval, getVar, R.bind, STy.ty]
  rw [evalUnop_int hx]

/-- A comparison is SemR's `icmpR` under the pattern's own predicate, on the
    left residue, then the right; its value is a `Bool`. -/
theorem cmp_int {pb : Nat} {t : IntTy} {x y : Nat} (op : ICmpOp)
    (hx : x < modulus (t.bits pb)) (hy : y < modulus (t.bits pb)) :
    (Pat.cmp op (.var 0) (.var 1)).eval pb (.int t) [.int t x, .int t y] =
      .ok (.bool (icmpR op (t.bits pb) x y)) := by
  simp only [Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hy]

/-- `select` gives the true arm (the second operand) under `true` and the
    false arm (the third) under `false`. -/
theorem sel_int {pb : Nat} {t : IntTy} {x y : Nat} (hx : x < modulus (t.bits pb))
    (hy : y < modulus (t.bits pb)) :
    (Pat.sel (.var 0) (.var 1) (.var 2)).eval pb (.int t) [.bool true, .int t x, .int t y] =
      .ok (.int t x) ∧
    (Pat.sel (.var 0) (.var 1) (.var 2)).eval pb (.int t) [.bool false, .int t x, .int t y] =
      .ok (.int t y) := by
  refine ⟨?_, ?_⟩ <;> simp only [Pat.eval, getVar, R.bind, STy.ty] <;> rw [selectVal_int _ hx hy]

theorem sel_bool (pb : Nat) (x y : Bool) :
    (Pat.sel (.var 0) (.var 1) (.var 2)).eval pb .bool [.bool true, .bool x, .bool y] =
      .ok (.bool x) ∧
    (Pat.sel (.var 0) (.var 1) (.var 2)).eval pb .bool [.bool false, .bool x, .bool y] =
      .ok (.bool y) := by
  refine ⟨?_, ?_⟩ <;> simp only [Pat.eval, getVar, R.bind, STy.ty] <;> rw [selectVal_bool]

/-- Binary operators on values that tell the operands and the operators apart
    (`sub` and the rotations are not commutative). -/
theorem bin_reads (pb : Nat) :
    (Pat.bin .sub (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 1, .int .u8 2] = .ok (.int .u8 255) ∧
    (Pat.bin .sub (.var 1) (.var 0)).eval pb (.int .u8) [.int .u8 1, .int .u8 2] = .ok (.int .u8 1) ∧
    (Pat.bin .add (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 200, .int .u8 100] = .ok (.int .u8 44) ∧
    (Pat.bin .mul (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 16, .int .u8 17] = .ok (.int .u8 16) ∧
    (Pat.bin .and (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 12, .int .u8 10] = .ok (.int .u8 8) ∧
    (Pat.bin .or (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 12, .int .u8 10] = .ok (.int .u8 14) ∧
    (Pat.bin .xor (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 12, .int .u8 10] = .ok (.int .u8 6) ∧
    (Pat.bin .rotl (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 129, .int .u8 1] = .ok (.int .u8 3) ∧
    (Pat.bin .rotr (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 129, .int .u8 1] = .ok (.int .u8 192) ∧
    (Pat.bin .rotl (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 1, .int .u8 129] = .ok (.int .u8 2) := by
  have h : ∀ (op : BinOp) (x y : Nat), binTy (.int .u8) op = .int .u8 → x < 256 → y < 256 →
      (Pat.bin op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 x, .int .u8 y] =
        (liftOp (intBin op 8 x y)).bind fun r => .ok (.int .u8 r) :=
    fun op _ _ hop hx hy => bin_int op hop hx hy
  have h1 : (1 : Nat) < modulus (IntTy.u8.bits pb) := (by decide : (1 : Nat) < 256)
  have h2 : (2 : Nat) < modulus (IntTy.u8.bits pb) := (by decide : (2 : Nat) < 256)
  have hrev : (Pat.bin .sub (.var 1) (.var 0)).eval pb (.int .u8) [.int .u8 1, .int .u8 2] =
      (liftOp (intBin .sub 8 2 1)).bind fun r => .ok (.int .u8 r) := bin_int_rev .sub rfl h1 h2
  exact ⟨(h .sub 1 2 rfl (by decide) (by decide)).trans rfl, hrev.trans rfl,
    (h .add 200 100 rfl (by decide) (by decide)).trans rfl,
    (h .mul 16 17 rfl (by decide) (by decide)).trans rfl,
    (h .and 12 10 rfl (by decide) (by decide)).trans rfl,
    (h .or 12 10 rfl (by decide) (by decide)).trans rfl,
    (h .xor 12 10 rfl (by decide) (by decide)).trans rfl,
    (h .rotl 129 1 rfl (by decide) (by decide)).trans rfl,
    (h .rotr 129 1 rfl (by decide) (by decide)).trans rfl,
    (h .rotl 1 129 rfl (by decide) (by decide)).trans rfl⟩

/-- Every unary operator on a value that tells it from the others. -/
theorem un_reads (pb : Nat) :
    (Pat.un .neg (.var 0)).eval pb (.int .u8) [.int .u8 1] = .ok (.int .u8 255) ∧
    (Pat.un .not (.var 0)).eval pb (.int .u8) [.int .u8 1] = .ok (.int .u8 254) ∧
    (Pat.un .ctpop (.var 0)).eval pb (.int .u8) [.int .u8 7] = .ok (.int .u8 3) ∧
    (Pat.un .ctlz (.var 0)).eval pb (.int .u8) [.int .u8 1] = .ok (.int .u8 7) ∧
    (Pat.un .cttz (.var 0)).eval pb (.int .u8) [.int .u8 8] = .ok (.int .u8 3) ∧
    (Pat.un .bswap (.var 0)).eval pb (.int .u16) [.int .u16 1] = .ok (.int .u16 256) ∧
    (Pat.un .bitreverse (.var 0)).eval pb (.int .u8) [.int .u8 1] = .ok (.int .u8 128) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  rw [un_int .bswap (show (1 : Nat) < modulus (IntTy.u16.bits pb) from (by decide : (1 : Nat) < 65536))]
  simp only [IntTy.bits]
  rfl

/-- The value of each predicate on `(0, 1)`, `(1, 0)`, `(1, 1)` and
    `(255, 0)` at eight bits, where 255 is the signed `-1`. -/
def cmpRow (pb : Nat) (op : ICmpOp) : List (R Val) :=
  [(Pat.cmp op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 0, .int .u8 1],
   (Pat.cmp op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 1, .int .u8 0],
   (Pat.cmp op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 1, .int .u8 1],
   (Pat.cmp op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 255, .int .u8 0]]

def boolRow (a b c d : Bool) : List (R Val) :=
  [.ok (.bool a), .ok (.bool b), .ok (.bool c), .ok (.bool d)]

/-- The ten predicates have ten different rows, so each is read as itself and
    on its operands in order: unsigned `255 < 0` is false, signed is true. -/
theorem cmp_reads (pb : Nat) :
    cmpRow pb .eq = boolRow false false true false ∧
    cmpRow pb .ne = boolRow true true false true ∧
    cmpRow pb .ult = boolRow true false false false ∧
    cmpRow pb .ule = boolRow true false true false ∧
    cmpRow pb .ugt = boolRow false true false true ∧
    cmpRow pb .uge = boolRow false true true true ∧
    cmpRow pb .slt = boolRow true false false true ∧
    cmpRow pb .sle = boolRow true false true true ∧
    cmpRow pb .sgt = boolRow false true false false ∧
    cmpRow pb .sge = boolRow false true true false := by
  have h : ∀ (op : ICmpOp) (x y : Nat), x < 256 → y < 256 →
      (Pat.cmp op (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 x, .int .u8 y] =
        .ok (.bool (icmpR op 8 x y)) := fun op x y hx hy => cmp_int op hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cmpRow, boolRow, h _ _ _ (by decide : (0 : Nat) < 256) (by decide : (1 : Nat) < 256),
      h _ _ _ (by decide : (1 : Nat) < 256) (by decide : (0 : Nat) < 256),
      h _ _ _ (by decide : (1 : Nat) < 256) (by decide : (1 : Nat) < 256),
      h _ _ _ (by decide : (255 : Nat) < 256) (by decide : (0 : Nat) < 256)] <;>
    rfl

/-- `select` on constants: the true arm under `true`, the false arm under
    `false`. -/
theorem sel_reads (pb : Nat) :
    (Pat.sel .tt (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 0, .int .u8 1] = .ok (.int .u8 0) ∧
    (Pat.sel .ff (.var 0) (.var 1)).eval pb (.int .u8) [.int .u8 0, .int .u8 1] = .ok (.int .u8 1) ∧
    (Pat.sel .tt (.var 0) (.var 1)).eval pb .bool [.bool false, .bool true] = .ok (.bool false) ∧
    (Pat.sel .ff (.var 0) (.var 1)).eval pb .bool [.bool false, .bool true] = .ok (.bool true) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Which stop is reported, on patterns whose operands stop differently:
    `(udiv ?x ?x)` at zero is undefined behaviour and the unbound rank 9 is
    not a term. The leftmost stop wins in every arm. -/
theorem stop_order (pb : Nat) :
    (∃ m, (Pat.bin .add (.bin .udiv (.var 0) (.var 0)) (.var 9)).eval pb (.int .u8) [.int .u8 0] =
      .stop (.ub m)) ∧
    (Pat.bin .add (.var 9) (.bin .udiv (.var 0) (.var 0))).eval pb (.int .u8) [.int .u8 0] =
      .stop .outOfFuel ∧
    (∃ m, (Pat.cmp .eq (.bin .udiv (.var 0) (.var 0)) (.var 9)).eval pb (.int .u8) [.int .u8 0] =
      .stop (.ub m)) ∧
    (Pat.cmp .eq (.var 9) (.bin .udiv (.var 0) (.var 0))).eval pb (.int .u8) [.int .u8 0] =
      .stop .outOfFuel ∧
    (∃ m, (Pat.sel .tt (.bin .udiv (.var 0) (.var 0)) (.var 9)).eval pb (.int .u8) [.int .u8 0] =
      .stop (.ub m)) ∧
    (Pat.sel .tt (.var 9) (.bin .udiv (.var 0) (.var 0))).eval pb (.int .u8) [.int .u8 0] =
      .stop .outOfFuel ∧
    (Pat.sel (.var 9) (.bin .udiv (.var 0) (.var 0)) (.var 0)).eval pb (.int .u8) [.int .u8 0] =
      .stop .outOfFuel ∧
    (∃ m, (Pat.un .neg (.bin .udiv (.var 0) (.var 0))).eval pb (.int .u8) [.int .u8 0] =
      .stop (.ub m)) :=
  ⟨⟨_, rfl⟩, rfl, ⟨_, rfl⟩, rfl, ⟨_, rfl⟩, rfl, rfl, ⟨_, rfl⟩⟩

/-! ## What a direction says of a side that is not a value -/

/-- No `equiv` statement holds on an assignment where either side stops. -/
theorem equiv_stop_never (o : Out) (l r : R Val) :
    ¬ Holds .equiv (.stop o) r ∧ ¬ Holds .equiv l (.stop o) := by
  constructor
  · rintro ⟨v, h, _⟩; cases h
  · rintro ⟨v, _, h⟩; cases h

/-- A `refines` statement holds on a left side that stops exactly when the
    stop is undefined behaviour, whatever the right side is. -/
theorem refines_stop_left (o : Out) (r : R Val) :
    Holds .refines (.stop o) r ↔ ∃ m, o = .ub m := by
  constructor
  · rintro (⟨m, h⟩ | ⟨v, h, _⟩)
    · cases h; exact ⟨m, rfl⟩
    · cases h
  · rintro ⟨m, rfl⟩; exact Or.inl ⟨m, rfl⟩

/-- Where the left side is a value, a `refines` statement is that the right
    side is that value: this is the only case in which it constrains the right
    side. -/
theorem refines_value_left (v : Val) (r : R Val) : Holds .refines (.ok v) r ↔ r = .ok v := by
  constructor
  · rintro (⟨m, h⟩ | ⟨v', h, hr⟩)
    · cases h
    · cases h; exact hr
  · intro h; exact Or.inr ⟨v, rfl, h⟩

/-- An `equiv` statement between two non-terms is false: here an unbound
    variable on both sides, at every type. -/
theorem equiv_unbound_never (T : STy) : ¬ Sound ⟨.equiv, .nil, .var 0, .var 0, .nil⟩ T := by
  intro h
  obtain ⟨v, hv, _⟩ := h 64 [] (pbOk_inhabited T) trivial trivial
  cases hv

/-! ## What reaches the proposition, and what stays in the literal

The kernel binds a lemma to the proposition `Sound <literal> <type>`. These
show which parts of a literal the proposition does not see; the rule digest,
not the kernel, tells such literals apart. -/

/-- The `const` flag of a variable does not reach the proposition. -/
theorem const_flag_is_data (d : Dir) (s : Srt) (c c' : Bool) (rest : Sorts) (lhs rhs : Pat)
    (conds : Conds) (T : STy) :
    Sound ⟨d, .cons s c rest, lhs, rhs, conds⟩ T ↔ Sound ⟨d, .cons s c' rest, lhs, rhs, conds⟩ T := by
  have flag : ∀ (pb : Nat) (env : List Val) (a b : Bool),
      Admits pb T (.cons s a rest) env → Admits pb T (.cons s b rest) env := by
    intro pb env a b h
    cases env with
    | nil => exact h
    | cons v vs => exact h
  exact ⟨fun h pb env hpb hadm hc => h pb env hpb (flag pb env c' c hadm) hc,
    fun h pb env hpb hadm hc => h pb env hpb (flag pb env c c' hadm) hc⟩

/-- `?v` and `(const ?v)` give one proposition (here as a whole side; under an
    operator likewise, by `var_cvar`). -/
theorem var_cvar_one_statement (d : Dir) (vars : Sorts) (i : Nat) (rhs : Pat) (conds : Conds)
    (T : STy) :
    Sound ⟨d, vars, .var i, rhs, conds⟩ T ↔ Sound ⟨d, vars, .cvar i, rhs, conds⟩ T :=
  Iff.rfl

/-! ## Side conditions that no assignment satisfies -/

theorem condsHold_bool (pb : Nat) (env : List Val) : ∀ cs : Conds, CondsHold pb .bool env cs
  | .nil => trivial
  | .cons c rest => ⟨(cond_without_residue pb env .u8 c).1, condsHold_bool pb env rest⟩

/-- A rule with no side condition is satisfiable at every type. -/
theorem satisfiable_of_no_conds (d : Dir) (vars : Sorts) (lhs rhs : Pat) (T : STy) :
    Satisfiable ⟨d, vars, lhs, rhs, .nil⟩ T := fun pb _ =>
  let ⟨env, h⟩ := admits_inhabited pb T vars
  ⟨env, h, trivial⟩

/-- Every rule is satisfiable at `Bool`, where a side condition says nothing. -/
theorem satisfiable_bool (r : Rule) : Satisfiable r .bool := fun pb _ =>
  let ⟨env, h⟩ := admits_inhabited pb .bool r.vars
  ⟨env, h, condsHold_bool pb env r.conds⟩

/-- What `Sound` alone does not guard: a rule whose side conditions no
    admitted assignment satisfies is `Sound` whatever its direction and sides
    are. `Satisfiable` is the statement that this is not how a rule holds. -/
theorem sound_of_unsatisfiable (d : Dir) (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy)
    (h : ∀ pb env, PbOk T pb → Admits pb T vars env → ¬ CondsHold pb T env conds) :
    Sound ⟨d, vars, lhs, rhs, conds⟩ T :=
  fun pb env hpb hadm hc => absurd hc (h pb env hpb hadm)

/-- A side condition only weakens a statement. -/
theorem conds_only_weaken (d : Dir) (vars : Sorts) (lhs rhs : Pat) (c : Cond) (rest : Conds)
    (T : STy) (h : Sound ⟨d, vars, lhs, rhs, rest⟩ T) :
    Sound ⟨d, vars, lhs, rhs, .cons c rest⟩ T :=
  fun pb env hpb hadm hc => h pb env hpb hadm hc.2

/-! ## Direction, where the left side names only total operators -/

/-- The binary operators the rule grammar admits: every one but
    `udiv sdiv urem srem shl lshr ashr`, which trust-cg's registry refuses
    (`REFUSED_OPS`) because SemR answers them with undefined behaviour on
    some operands. -/
def totalOp : BinOp → Bool
  | .udiv => false
  | .sdiv => false
  | .urem => false
  | .srem => false
  | .shl => false
  | .lshr => false
  | .ashr => false
  | _ => true

/-- A pattern that names only total operators (every unary operator and
    every comparison is total). -/
def Pat.total : Pat → Bool
  | .bin op a b => totalOp op && (a.total && b.total)
  | .un _ a => a.total
  | .cmp _ a b => a.total && b.total
  | .sel c a b => c.total && (a.total && b.total)
  | _ => true

/-- A scalar value: what a variable is bound to, and what an operator gives. -/
def Scalar : Val → Prop
  | .int _ _ => True
  | .bool _ => True
  | _ => False

/-- An outcome that is a value satisfying `P`, a non-term or a type error:
    never undefined behaviour. -/
def Soft {α : Type} (P : α → Prop) (r : R α) : Prop :=
  (∃ a, r = .ok a ∧ P a) ∨ r = .stop .outOfFuel ∨ ∃ m, r = .stop (.typeError m)

theorem soft_not_ub {α : Type} {P : α → Prop} {r : R α} (h : Soft P r) (m : String) :
    r ≠ .stop (.ub m) := by
  rintro rfl
  rcases h with ⟨v, h, _⟩ | h | ⟨m', h⟩ <;> cases h

theorem soft_bind {α β : Type} {P : α → Prop} {Q : β → Prop} {r : R α} {k : α → R β}
    (h : Soft P r) (hk : ∀ a, P a → Soft Q (k a)) : Soft Q (r.bind k) := by
  rcases h with ⟨a, rfl, pa⟩ | rfl | ⟨m, rfl⟩
  · exact hk a pa
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨m, rfl⟩)

theorem expectTy_soft (pb : Nat) (v : Val) (t : Ty) : Soft (fun _ => True) (expectTy pb v t) := by
  have key : ∀ (c1 c2 : Bool) (a b : String) (r : R Unit), Soft (fun _ => True) r →
      Soft (fun _ => True) (if c1 = true then tyR a else if c2 = true then tyR b else r) := by
    intro c1 c2 a b r h
    cases c1
    · cases c2
      · exact h
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  have range : ∀ (raw limit : Nat) (message : String),
      Soft (fun _ => True) (if raw < limit then R.ok () else tyR message) := by
    intro raw limit message
    by_cases h : raw < limit
    · exact Or.inl ⟨(), if_pos h, trivial⟩
    · exact Or.inr (Or.inr ⟨_, if_neg h⟩)
  unfold expectTy
  apply key
  cases v <;>
    first
    | exact Or.inl ⟨(), rfl, trivial⟩
    | exact range _ _ _

theorem expectInt_soft {v : Val} (h : Scalar v) : Soft (fun _ => True) (expectInt v) := by
  cases v <;>
    first
    | exact Or.inl ⟨_, rfl, trivial⟩
    | exact Or.inr (Or.inr ⟨_, rfl⟩)
    | cases h

theorem expectBool_soft {v : Val} (h : Scalar v) : Soft (fun _ => True) (expectBool v) := by
  cases v <;>
    first
    | exact Or.inl ⟨_, rfl, trivial⟩
    | exact Or.inr (Or.inr ⟨_, rfl⟩)
    | cases h

theorem intBin_total {op : BinOp} (hop : totalOp op = true) (w a b : Nat) :
    ∃ r, intBin op w a b = .ok r := by
  cases op <;> first | exact ⟨_, rfl⟩ | cases hop

theorem boolBin_soft (op : BinOp) (a b : Bool) : Soft (fun _ => True) (liftOp (boolBin op a b)) := by
  cases op <;> first | exact Or.inl ⟨_, rfl, trivial⟩ | exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem evalBinop_soft {pb : Nat} {op : BinOp} (ty : Ty) {x y : Val} (hop : totalOp op = true)
    (hx : Scalar x) (hy : Scalar y) : Soft Scalar (evalBinop pb op ty x y) := by
  unfold evalBinop
  simp only [bind, pure]
  refine soft_bind (expectTy_soft pb x ty) fun _ _ => ?_
  refine soft_bind (expectTy_soft pb y ty) fun _ _ => ?_
  cases isBoolTy ty
  · refine soft_bind (expectInt_soft hx) fun p _ => ?_
    refine soft_bind (expectInt_soft hy) fun q _ => ?_
    obtain ⟨r, hr⟩ := intBin_total hop (p.1.bits pb) p.2 q.2
    exact Or.inl ⟨.int p.1 r, by simp only [hr, liftOp, R.bind], trivial⟩
  · refine soft_bind (expectBool_soft hx) fun a _ => ?_
    refine soft_bind (expectBool_soft hy) fun b _ => ?_
    exact soft_bind (boolBin_soft op a b) fun r _ => Or.inl ⟨_, rfl, trivial⟩

theorem evalUnop_soft {pb : Nat} (op : UnOp) (ty : Ty) {x : Val} (hx : Scalar x) :
    Soft Scalar (evalUnop pb op ty x) := by
  unfold evalUnop
  simp only [bind, pure]
  refine soft_bind (expectTy_soft pb x ty) fun _ _ => ?_
  exact soft_bind (expectInt_soft hx) fun p _ => Or.inl ⟨_, rfl, trivial⟩

theorem evalIcmp_soft {pb : Nat} (op : ICmpOp) (ty : Ty) {x y : Val}
    (hx : Scalar x) (hy : Scalar y) : Soft Scalar (evalIcmp pb op ty x y) := by
  unfold evalIcmp
  simp only [bind, pure]
  refine soft_bind (expectTy_soft pb x ty) fun _ _ => ?_
  refine soft_bind (expectTy_soft pb y ty) fun _ _ => ?_
  cases isBoolTy ty
  · refine soft_bind (expectInt_soft hx) fun p _ => ?_
    exact soft_bind (expectInt_soft hy) fun q _ => Or.inl ⟨_, rfl, trivial⟩
  · refine soft_bind (expectBool_soft hx) fun a _ => ?_
    exact soft_bind (expectBool_soft hy) fun b _ => Or.inl ⟨_, rfl, trivial⟩

theorem selectVal_soft {pb : Nat} (ty : Ty) {cv x y : Val}
    (hc : Scalar cv) (hx : Scalar x) (hy : Scalar y) : Soft Scalar (selectVal pb ty cv x y) := by
  have hp : rejectPoison cv "select" = .ok () := by
    cases cv <;> first | rfl | cases hc
  unfold selectVal
  simp only [bind, pure, hp, R.bind]
  refine soft_bind (expectTy_soft pb x ty) fun _ _ => ?_
  refine soft_bind (expectTy_soft pb y ty) fun _ _ => ?_
  cases cv <;> first | exact Or.inr (Or.inr ⟨_, rfl⟩) | skip
  rename_i b
  cases b
  · exact Or.inl ⟨_, rfl, hy⟩
  · exact Or.inl ⟨_, rfl, hx⟩

theorem admitsVal_scalar {pb : Nat} {T : STy} {s : Srt} {v : Val} (h : AdmitsVal pb T s v) :
    Scalar v := by
  cases s <;> cases T <;> simp only [AdmitsVal] at h
  · obtain ⟨r, rfl, _⟩ := h; trivial
  · obtain ⟨b, rfl⟩ := h; trivial
  · obtain ⟨b, rfl⟩ := h; trivial
  · obtain ⟨b, rfl⟩ := h; trivial

theorem getVar_soft {pb : Nat} {T : STy} :
    ∀ (vars : Sorts) (env : List Val) (i : Nat), Admits pb T vars env → Soft Scalar (getVar env i)
  | .nil, [], _, _ => Or.inr (Or.inl rfl)
  | .nil, _ :: _, _, h => by simp [Admits] at h
  | .cons _ _ _, [], _, h => by simp [Admits] at h
  | .cons _ _ _, v :: _, 0, h => by
    simp only [Admits] at h
    exact Or.inl ⟨v, rfl, admitsVal_scalar h.1⟩
  | .cons _ _ rest, _ :: vs, i + 1, h => by
    simp only [Admits] at h
    exact getVar_soft rest vs i h.2

/-- A pattern of total operators never evaluates to undefined behaviour on an
    admitted assignment: it is a scalar value, a non-term or a type error. -/
theorem total_soft {pb : Nat} {T : STy} {vars : Sorts} {env : List Val}
    (hadm : Admits pb T vars env) : ∀ p : Pat, p.total = true → Soft Scalar (p.eval pb T env)
  | .var i, _ => getVar_soft vars env i hadm
  | .cvar i, _ => getVar_soft vars env i hadm
  | .lit neg mag, _ => by
    cases T
    · exact Or.inl ⟨_, rfl, trivial⟩
    · exact Or.inr (Or.inl rfl)
  | .tt, _ => Or.inl ⟨_, rfl, trivial⟩
  | .ff, _ => Or.inl ⟨_, rfl, trivial⟩
  | .bin op a b, h => by
    simp only [Pat.total, Bool.and_eq_true] at h
    simp only [Pat.eval]
    exact soft_bind (total_soft hadm a h.2.1) fun x sx =>
      soft_bind (total_soft hadm b h.2.2) fun y sy => evalBinop_soft _ h.1 sx sy
  | .un op a, h => by
    simp only [Pat.total] at h
    simp only [Pat.eval]
    exact soft_bind (total_soft hadm a h) fun x sx => evalUnop_soft _ _ sx
  | .cmp op a b, h => by
    simp only [Pat.total, Bool.and_eq_true] at h
    simp only [Pat.eval]
    exact soft_bind (total_soft hadm a h.1) fun x sx =>
      soft_bind (total_soft hadm b h.2) fun y sy => evalIcmp_soft _ _ sx sy
  | .sel c a b, h => by
    simp only [Pat.total, Bool.and_eq_true] at h
    simp only [Pat.eval]
    exact soft_bind (total_soft hadm c h.1) fun cv sc =>
      soft_bind (total_soft hadm a h.2.1) fun x sx =>
        soft_bind (total_soft hadm b h.2.2) fun y sy => selectVal_soft _ sc sx sy

/-- A left side of total operators is never undefined behaviour. -/
theorem total_not_ub {pb : Nat} {T : STy} {vars : Sorts} {env : List Val} {p : Pat}
    (hadm : Admits pb T vars env) (ht : p.total = true) (m : String) :
    p.eval pb T env ≠ .stop (.ub m) :=
  soft_not_ub (total_soft hadm p ht) m

/-- Where the left side names only total operators, the `refines` statement
    gives the `equiv` statement: its undefined-behaviour disjunct is never
    the case. The rule grammar admits total operators only, so for every rule
    it can state the two directions are one statement, and a rule's direction
    is held by the rule digest and the checker's `SymOfRefines` refusal, not
    by the kernel. `EqsatIntControls.refines_does_not_give_equiv` shows the
    hypothesis is needed. -/
theorem refines_gives_equiv_of_total (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy)
    (ht : lhs.total = true) (h : Sound ⟨.refines, vars, lhs, rhs, conds⟩ T) :
    Sound ⟨.equiv, vars, lhs, rhs, conds⟩ T := by
  intro pb env hpb hadm hc
  rcases h pb env hpb hadm hc with ⟨m, hm⟩ | h
  · exact absurd hm (total_not_ub hadm ht m)
  · exact h

theorem refines_iff_equiv_of_total (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy)
    (ht : lhs.total = true) :
    Sound ⟨.refines, vars, lhs, rhs, conds⟩ T ↔ Sound ⟨.equiv, vars, lhs, rhs, conds⟩ T :=
  ⟨refines_gives_equiv_of_total vars lhs rhs conds T ht, equiv_gives_refines vars lhs rhs conds T⟩

/-- `totalOp` is the grammar's admission test, operator by operator. -/
theorem totalOp_table :
    totalOp .add = true ∧ totalOp .sub = true ∧ totalOp .mul = true ∧ totalOp .and = true ∧
    totalOp .or = true ∧ totalOp .xor = true ∧ totalOp .rotl = true ∧ totalOp .rotr = true ∧
    totalOp .bAnd = true ∧ totalOp .bOr = true ∧ totalOp .bXor = true ∧
    totalOp .udiv = false ∧ totalOp .sdiv = false ∧ totalOp .urem = false ∧
    totalOp .srem = false ∧ totalOp .shl = false ∧ totalOp .lshr = false ∧
    totalOp .ashr = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EqsatRule
