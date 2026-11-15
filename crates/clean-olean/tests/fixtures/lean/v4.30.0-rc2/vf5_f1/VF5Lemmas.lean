/-
  VF5Lemmas — the arithmetic of affine terms, scoping, and the relation
  between symbolic and concrete values that `vc_sound_F1` carries.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Calc

namespace VF5

open SemR

/-! ## Evaluation -/

theorem dot_unitVec : ∀ (i : Nat) (ρ : Nat → Int), ChkLIA.dot (unitVec i) ρ = ρ i
  | 0, ρ => by simp [unitVec, ChkLIA.dot]
  | i + 1, ρ => by
      simp only [unitVec, ChkLIA.dot, dot_unitVec i]
      simp

@[simp] theorem eval_c (n : Int) (ρ : Nat → Int) : (Aff.c n).eval ρ = n := by
  simp [Aff.c, Aff.eval, ChkLIA.dot]

@[simp] theorem eval_v (i : Nat) (ρ : Nat → Int) : (Aff.v i).eval ρ = ρ i := by
  simp [Aff.v, Aff.eval, dot_unitVec]

@[simp] theorem eval_add (a b : Aff) (ρ : Nat → Int) :
    (a.add b).eval ρ = a.eval ρ + b.eval ρ := by
  simp only [Aff.add, Aff.eval, ChkLIA.dot_addVec]; omega

@[simp] theorem eval_smul (c : Int) (a : Aff) (ρ : Nat → Int) :
    (a.smul c).eval ρ = c * a.eval ρ := by
  simp only [Aff.smul, Aff.eval, ChkLIA.dot_scale, Int.mul_add]

@[simp] theorem eval_sub (a b : Aff) (ρ : Nat → Int) :
    (a.sub b).eval ρ = a.eval ρ - b.eval ρ := by
  simp only [Aff.sub, eval_add, eval_smul]; omega

@[simp] theorem eval_addC (a : Aff) (n : Int) (ρ : Nat → Int) :
    (a.addC n).eval ρ = a.eval ρ + n := by
  simp only [Aff.addC, Aff.eval]; omega

theorem sat_le0 (e : Aff) (ρ : Nat → Int) : (le0 e).sat ρ ↔ e.eval ρ ≤ 0 := by
  simp only [le0, ChkLIA.Cons.sat, Aff.eval]; omega

theorem sat_leA (a b : Aff) (ρ : Nat → Int) : (leA a b).sat ρ ↔ a.eval ρ ≤ b.eval ρ := by
  simp only [leA, sat_le0, eval_sub]; omega

theorem sat_leAn (a : Aff) (n : Int) (b : Aff) (ρ : Nat → Int) :
    (leAn a n b).sat ρ ↔ a.eval ρ + n ≤ b.eval ρ := by
  simp only [leAn, sat_le0, eval_sub, eval_addC]; omega

theorem dot_allZero' : ∀ (a : List Int) (ρ : Nat → Int), ChkLIA.allZero a = true →
    ChkLIA.dot a ρ = 0 := fun a ρ h => ChkLIA.dot_allZero ρ h

theorem eval_isConst (e : Aff) (ρ : Nat → Int) (h : e.isConst = true) : e.eval ρ = e.k := by
  simp only [Aff.eval, dot_allZero' e.co ρ h, Int.zero_add]

/-! ## Scoping: a term reads only the variables below its length -/

def Agree (ρ ρ' : Nat → Int) (n : Nat) : Prop := ∀ i, i < n → ρ i = ρ' i

theorem Agree.refl (ρ : Nat → Int) (n : Nat) : Agree ρ ρ n := fun _ _ => rfl

theorem Agree.mono {ρ ρ' : Nat → Int} {n n' : Nat} (h : Agree ρ ρ' n') (hn : n ≤ n') :
    Agree ρ ρ' n := fun i hi => h i (Nat.lt_of_lt_of_le hi hn)

theorem Agree.trans {ρ ρ' ρ'' : Nat → Int} {n : Nat} (h : Agree ρ ρ' n) (h' : Agree ρ' ρ'' n) :
    Agree ρ ρ'' n := fun i hi => (h i hi).trans (h' i hi)

theorem dot_congr : ∀ (a : List Int) (ρ ρ' : Nat → Int), Agree ρ ρ' a.length →
    ChkLIA.dot a ρ = ChkLIA.dot a ρ'
  | [], _, _, _ => rfl
  | x :: as, ρ, ρ', h => by
      simp only [ChkLIA.dot]
      rw [h 0 (by simp), dot_congr as (fun i => ρ (i + 1)) (fun i => ρ' (i + 1))
        (fun i hi => h (i + 1) (by simp; omega))]

def Aff.Scoped (n : Nat) (e : Aff) : Prop := e.co.length ≤ n

def Cons.Scoped (n : Nat) (c : Cons) : Prop := c.coeffs.length ≤ n

theorem eval_congr {e : Aff} {n : Nat} {ρ ρ' : Nat → Int} (hs : e.Scoped n)
    (h : Agree ρ ρ' n) : e.eval ρ = e.eval ρ' := by
  simp only [Aff.eval, dot_congr e.co ρ ρ' (h.mono hs)]

theorem sat_congr {c : Cons} {n : Nat} {ρ ρ' : Nat → Int} (hs : Cons.Scoped n c)
    (h : Agree ρ ρ' n) : c.sat ρ ↔ c.sat ρ' := by
  simp only [ChkLIA.Cons.sat, dot_congr c.coeffs ρ ρ' (h.mono hs)]

theorem length_addVec : ∀ (a b : List Int),
    (ChkLIA.addVec a b).length = max a.length b.length
  | [], b => by simp [ChkLIA.addVec]
  | _ :: _, [] => by simp [ChkLIA.addVec]
  | _ :: as, _ :: bs => by simp [ChkLIA.addVec, length_addVec as bs]

theorem length_scale (c : Int) : ∀ (a : List Int), (ChkLIA.scale c a).length = a.length
  | [] => rfl
  | _ :: as => by simp [ChkLIA.scale, length_scale c as]

theorem length_unitVec : ∀ (i : Nat), (unitVec i).length = i + 1
  | 0 => rfl
  | i + 1 => by simp [unitVec, length_unitVec i]

theorem scoped_c (n : Nat) (k : Int) : (Aff.c k).Scoped n := by
  simp [Aff.Scoped, Aff.c]

theorem scoped_v {i n : Nat} (h : i < n) : (Aff.v i).Scoped n := by
  simp [Aff.Scoped, Aff.v, length_unitVec]; omega

theorem scoped_add {n : Nat} {a b : Aff} (ha : a.Scoped n) (hb : b.Scoped n) :
    (a.add b).Scoped n := by
  simp only [Aff.Scoped, Aff.add, length_addVec] at *; omega

theorem scoped_smul {n : Nat} {a : Aff} (c : Int) (ha : a.Scoped n) : (a.smul c).Scoped n := by
  simp only [Aff.Scoped, Aff.smul, length_scale] at *; exact ha

theorem scoped_sub {n : Nat} {a b : Aff} (ha : a.Scoped n) (hb : b.Scoped n) :
    (a.sub b).Scoped n := scoped_add ha (scoped_smul _ hb)

theorem scoped_addC {n : Nat} {a : Aff} (k : Int) (ha : a.Scoped n) : (a.addC k).Scoped n := ha

theorem Aff.Scoped.mono {n n' : Nat} {a : Aff} (h : a.Scoped n) (hn : n ≤ n') : a.Scoped n' :=
  Nat.le_trans h hn

theorem scoped_le0 {n : Nat} {e : Aff} (h : e.Scoped n) : Cons.Scoped n (le0 e) := h

theorem scoped_leA {n : Nat} {a b : Aff} (ha : a.Scoped n) (hb : b.Scoped n) :
    Cons.Scoped n (leA a b) := scoped_sub ha hb

theorem scoped_leAn {n : Nat} {a b : Aff} (k : Int) (ha : a.Scoped n) (hb : b.Scoped n) :
    Cons.Scoped n (leAn a k b) := scoped_sub (scoped_addC k ha) hb

/-- Update one variable. -/
def upd (ρ : Nat → Int) (n : Nat) (a : Int) : Nat → Int := fun i => if i = n then a else ρ i

theorem agree_upd (ρ : Nat → Int) (n : Nat) (a : Int) : Agree ρ (upd ρ n a) n := by
  intro i hi; simp [upd]; omega

@[simp] theorem upd_self (ρ : Nat → Int) (n : Nat) (a : Int) : upd ρ n a n = a := by simp [upd]

/-! ## Constraint lists -/

def Sat (cs : List Cons) (ρ : Nat → Int) : Prop := ∀ c ∈ cs, c.sat ρ

def CsScoped (n : Nat) (cs : List Cons) : Prop := ∀ c ∈ cs, Cons.Scoped n c

theorem Sat.append {cs ds : List Cons} {ρ : Nat → Int} (h1 : Sat cs ρ) (h2 : Sat ds ρ) :
    Sat (cs ++ ds) ρ := by
  intro c hc; rcases List.mem_append.mp hc with h | h; exact h1 c h; exact h2 c h

theorem Sat.left {cs ds : List Cons} {ρ : Nat → Int} (h : Sat (cs ++ ds) ρ) : Sat cs ρ :=
  fun c hc => h c (List.mem_append_left _ hc)

theorem Sat.right {cs ds : List Cons} {ρ : Nat → Int} (h : Sat (cs ++ ds) ρ) : Sat ds ρ :=
  fun c hc => h c (List.mem_append_right _ hc)

theorem sat_nil (ρ : Nat → Int) : Sat [] ρ := fun _ h => nomatch h

theorem sat_cons {c : Cons} {cs : List Cons} {ρ : Nat → Int} :
    Sat (c :: cs) ρ ↔ c.sat ρ ∧ Sat cs ρ := by
  constructor
  · intro h; exact ⟨h c (List.Mem.head _), fun d hd => h d (List.Mem.tail _ hd)⟩
  · intro ⟨h1, h2⟩ d hd
    cases hd with
    | head => exact h1
    | tail _ hd => exact h2 d hd

theorem Sat.congr {cs : List Cons} {n : Nat} {ρ ρ' : Nat → Int} (hs : CsScoped n cs)
    (h : Agree ρ ρ' n) (hsat : Sat cs ρ) : Sat cs ρ' :=
  fun c hc => (sat_congr (hs c hc) h).mp (hsat c hc)

theorem CsScoped.append {n : Nat} {cs ds : List Cons} (h1 : CsScoped n cs) (h2 : CsScoped n ds) :
    CsScoped n (cs ++ ds) := by
  intro c hc; rcases List.mem_append.mp hc with h | h; exact h1 c h; exact h2 c h

theorem CsScoped.mono {n n' : Nat} {cs : List Cons} (h : CsScoped n cs) (hn : n ≤ n') :
    CsScoped n' cs := fun c hc => Nat.le_trans (h c hc) hn

theorem unsat_of {p : List Cons} {ρ : Nat → Int} (hu : Unsat p) (h : Sat p ρ) : False :=
  hu ⟨ρ, h⟩

/-- The empty obligation is satisfiable: nothing discharges `FAIL`. -/
theorem not_unsat_nil : ¬ Unsat [] := fun h => h ⟨fun _ => 0, fun _ hc => nomatch hc⟩

theorem fail_refutes {P : Prop} (h : ∀ p ∈ FAIL, Unsat p) : P :=
  absurd (h [] (List.Mem.head _)) not_unsat_nil

end VF5
