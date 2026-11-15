/-
  VF5Ops — each operator's symbolic cases cover SemR's operator: for every
  in-range concrete operand pair, the branch whose constraints the operands
  meet binds the concrete result, and each undefined behaviour meets one of
  the obligations.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Lemmas

namespace VF5

open SemR

variable {m : Module}

/-! ## Widths -/

theorem modulus_pos (w : Nat) : 0 < modulus w := Nat.two_pow_pos w

theorem bits_pos (t : IntTy) : 1 ≤ t.bits := by cases t <;> decide

theorem modulus_two_half {w : Nat} (h : 1 ≤ w) : modulus w = 2 * half w := by
  simp only [modulus, half]
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp [Nat.pow_succ, Nat.mul_comm]

theorem two_le_modulus {w : Nat} (h : 1 ≤ w) : 2 ≤ modulus w := by
  have := modulus_two_half h
  have : 0 < half w := Nat.two_pow_pos _
  omega

theorem Mw_eq (w : Nat) : Mw w = ((modulus w : Nat) : Int) := rfl
theorem Hw_eq (w : Nat) : Hw w = ((half w : Nat) : Int) := rfl

theorem mod_of_lt {x M : Nat} (h : x < M) : x % M = x := Nat.mod_eq_of_lt h

theorem mod_of_lt2 {x M : Nat} (h1 : M ≤ x) (h2 : x < 2 * M) : x % M = x - M := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-! ## Symbolic and concrete values -/

def valRel (m : Module) (ρ : Nat → Int) : SV → Val → Prop
  | .int t e, v => ∃ a, v = .int t a ∧ a < modulus t.bits ∧ e.eval ρ = (a : Int)
  | .bool b, v => v = .bool b
  | .enm id ls, v => v = .enum id ls ∧ EnumOK m id ls

def SV.Scoped (n : Nat) : SV → Prop
  | .int _ e => e.Scoped n
  | .bool _ => True
  | .enm _ _ => True

theorem SV.Scoped.mono {n n' : Nat} {s : SV} (h : s.Scoped n) (hn : n ≤ n') : s.Scoped n' := by
  cases s with
  | int t e => exact Aff.Scoped.mono h hn
  | bool b => trivial
  | enm _ _ => trivial

theorem valRel_congr {ρ ρ' : Nat → Int} {n : Nat} {s : SV} {v : Val} (hs : s.Scoped n)
    (h : Agree ρ ρ' n) (hr : valRel m ρ s v) : valRel m ρ' s v := by
  cases s with
  | int t e =>
    obtain ⟨a, rfl, ha, he⟩ := hr
    exact ⟨a, rfl, ha, (eval_congr hs h).symm.trans he⟩
  | bool b => exact hr
  | enm _ _ => exact hr

theorem valRel_ty {ρ : Nat → Int} {s : SV} {v : Val} (h : valRel m ρ s v) : v.ty = s.ty := by
  cases s with
  | int t e => obtain ⟨a, rfl, _, _⟩ := h; rfl
  | bool b => cases h; rfl
  | enm _ _ => obtain ⟨rfl, _⟩ := h; rfl

theorem valRel_ok {ρ : Nat → Int} {s : SV} {v : Val} (h : valRel m ρ s v) : ValOK m v := by
  cases s with
  | int t e => obtain ⟨a, rfl, ha, _⟩ := h; exact ha
  | bool b => cases h; trivial
  | enm _ _ => obtain ⟨rfl, h⟩ := h; exact h

theorem valRel_aff {ρ : Nat → Int} {s : SV} {v : Val} (h : valRel m ρ s v) :
    s.aff.eval ρ = valInt v := by
  cases s with
  | int t e => obtain ⟨a, rfl, _, he⟩ := h; simpa [SV.aff, valInt] using he
  | bool b => cases h; cases b <;> simp [SV.aff, valInt]
  | enm _ _ => obtain ⟨rfl, _⟩ := h; simp [SV.aff, valInt]

/-- A branch's result: the constraints hold at an assignment that agrees below
    the old fresh-variable bound, the bound only grows, and the values relate. -/
def BrCovers (m : Module) (ρ : Nat → Int) (nv : Nat) (br : Br) (vs : List Val) : Prop :=
  ∃ ρ', Agree ρ ρ' nv ∧ Sat br.cs ρ' ∧ nv ≤ br.nv ∧ CsScoped br.nv br.cs ∧
    List.length br.vals = List.length vs ∧
    (∀ p ∈ br.vals.zip vs, valRel m ρ' p.1 p.2) ∧ (∀ s ∈ br.vals, s.Scoped br.nv)

/-! ## Fresh variables -/

theorem fresh_covers (ρ : Nat → Int) (nv : Nat) (t : IntTy) (c : Nat) (hc : c < modulus t.bits) :
    ∃ ρ', Agree ρ ρ' nv ∧ Sat (rangeCs t.bits (Aff.v nv)) ρ' ∧
      CsScoped (nv + 1) (rangeCs t.bits (Aff.v nv)) ∧
      valRel m ρ' (.int t (Aff.v nv)) (.int t c) ∧ (SV.int t (Aff.v nv)).Scoped (nv + 1) := by
  refine ⟨upd ρ nv c, agree_upd ρ nv c, ?_, ?_, ⟨c, rfl, hc, by simp⟩, scoped_v (by omega)⟩
  · intro x hx
    simp only [rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · rw [sat_le0]; simp
    · rw [sat_le0]; simp [Mw]; omega
  · intro x hx
    simp only [rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact scoped_le0 (scoped_smul _ (scoped_v (by omega)))
    · exact scoped_le0 (scoped_addC _ (scoped_v (by omega)))

theorem brcov_same {ρ : Nat → Int} {nv : Nat} {cs : List Cons} {t : IntTy} {e : Aff} {c : Nat}
    (h : Sat cs ρ) (hcs : CsScoped nv cs) (he : e.eval ρ = (c : Int)) (hc : c < modulus t.bits)
    (hs : e.Scoped nv) : BrCovers m ρ nv ⟨cs, [.int t e], nv⟩ [.int t c] := by
  refine ⟨ρ, Agree.refl ρ nv, h, Nat.le_refl _, hcs, rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; exact ⟨c, rfl, hc, he⟩
  · intro s hs'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
    subst hs'; exact hs

theorem brcov_fresh {ρ : Nat → Int} {nv : Nat} {pre : List Cons} {t : IntTy} {c : Nat}
    (h : Sat pre ρ) (hcs : CsScoped nv pre) (hc : c < modulus t.bits) :
    BrCovers m ρ nv ⟨pre ++ rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩ [.int t c] := by
  obtain ⟨ρ', hag, hsat, hsc, hrel, hss⟩ := fresh_covers ρ nv t c hc
  refine ⟨ρ', hag, Sat.append (Sat.congr hcs hag h) hsat, Nat.le_succ _,
    CsScoped.append (hcs.mono (Nat.le_succ _)) hsc, rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; exact hrel
  · intro s hs'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
    subst hs'; exact hss

theorem sat_one {c : Cons} {ρ : Nat → Int} (h : c.sat ρ) : Sat [c] ρ := by
  intro d hd; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd; subst hd; exact h

theorem scoped_one {n : Nat} {c : Cons} (h : Cons.Scoped n c) : CsScoped n [c] := by
  intro d hd; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd; subst hd; exact h

theorem mem2 {α : Type} {x a b : α} (h : x = a ∨ x = b) : x ∈ [a, b] := by
  rcases h with rfl | rfl <;> simp

end VF5
