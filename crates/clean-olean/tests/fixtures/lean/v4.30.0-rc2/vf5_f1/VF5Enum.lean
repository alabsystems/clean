/-
  VF5Enum — D-2(b): fieldless enums as range-restricted scalars, and B3's
  positional discriminant check.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  The calculus (`VF5Calc`) reads a fieldless enum value as known: an entry or
  a call result of a fieldless enum type forks once per variant, so the tag
  `ExtractField 0` reads is a constant, and the integer the cast after it
  makes is one of the enum's discriminants. `Valid_R` and `ClosedSafe` quantify
  over VALID enum values only (`VF5Sem.EnumOK`: the tag is the residue of one
  of the discriminants), which is Rust's validity invariant, the entry premise
  D-2(b) rests on.

  B3's positional check (`~/trust-land/d2b-placement.md`, P1–P6) binds the
  artifact's discriminant assignment to rustc's: `checkB3 bytes eid rustc repr`
  holds when SemR decodes the bytes, enum `eid` is fieldless, its positional
  list `[(i, dᵢ)]` (variant index, effective discriminant) EQUALS `rustc` in
  order — not as sets, so a swapped pair fails — and, when rustc reports an
  explicit `repr`, the artifact's tag type is that repr. The `rustc` list and
  repr are read by the producer from rustc's own evaluation (`E::Vᵢ as i128`
  and `<E as DiscriminantKind>::Discriminant`, a probe compiled by the same
  compiler without Trust), a second reader beside SemR's decoder of the
  emitted module; the kernel compares the two on literals.
-/
import VF5Mutants

set_option linter.unusedVariables false

namespace VF5
open SemR

/-- The positional discriminant list of an enum: `(variant index, effective
    discriminant)`, in variant order. -/
def positional (d : EnumDef) : List (Nat × Int) := (List.range d.discs.length).zip d.discs

def posEq : List (Nat × Int) → List (Nat × Int) → Bool
  | [], [] => true
  | (i, a) :: xs, (j, b) :: ys => i == j && a == b && posEq xs ys
  | _, _ => false

theorem posEq_sound : ∀ {xs ys : List (Nat × Int)}, posEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | (i, a) :: xs, (j, b) :: ys, h => by
    simp only [posEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [posEq_sound h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- **B3's positional check, decided.** -/
def checkB3 (bs : List Nat) (eid : Nat) (rustc : List (Nat × Int)) (repr : Option IntTy) : Bool :=
  match decode bs with
  | .ok m =>
    match findEnum m.enums eid with
    | some d =>
      isF1Enum d && posEq (positional d) rustc &&
        (match repr with
         | some t => d.tag.code == t.code
         | none => true)
    | none => false
  | .error _ => false

/-- What `checkB3` establishes. -/
def B3OK (bs : List Nat) (eid : Nat) (rustc : List (Nat × Int)) (repr : Option IntTy) : Prop :=
  ∃ m d, decode bs = .ok m ∧ findEnum m.enums eid = some d ∧ isF1Enum d = true ∧
    positional d = rustc ∧ ∀ t, repr = some t → d.tag = t

theorem checkB3_sound {bs : List Nat} {eid : Nat} {rustc : List (Nat × Int)} {repr : Option IntTy}
    (h : checkB3 bs eid rustc repr = true) : B3OK bs eid rustc repr := by
  simp only [checkB3] at h
  split at h
  · next m hm =>
    split at h
    · next d hd =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hf, hp⟩, hr⟩ := h
      refine ⟨m, d, hm, hd, hf, posEq_sound hp, fun t ht => ?_⟩
      subst ht
      simp only [beq_iff_eq] at hr
      exact code_inj hr
    · exact nomatch h
  · exact nomatch h

/-- A valid value of an enum B3 binds carries one of rustc's discriminants:
    the range a fieldless enum restricts its tag to, as rustc assigns it. -/
theorem b3_valid_tag {bs : List Nat} {eid : Nat} {rustc : List (Nat × Int)} {repr : Option IntTy}
    (h : B3OK bs eid rustc repr) {m : Module} (hm : decode bs = .ok m) {lanes : List Val}
    (hv : EnumOK m eid lanes) :
    ∃ d i disc, findEnum m.enums eid = some d ∧ (i, disc) ∈ rustc ∧
      lanes = [.int d.tag (resid d.tag.bits disc)] := by
  obtain ⟨m', d, hm', hd, _, hp, _⟩ := h
  rw [hm] at hm'; cases hm'
  obtain ⟨d', hd', _, disc, hdisc, rfl⟩ := hv
  rw [hd] at hd'; cases hd'
  obtain ⟨i, hi⟩ : ∃ i, (i, disc) ∈ positional d := by
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hdisc
    refine ⟨i, ?_⟩
    simp only [positional]
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp [hget]⟩
  exact ⟨d, i, disc, hd, hp ▸ hi, rfl⟩

/-! ### B3 over the whole artifact, and the D-2(b) row -/

/-- One B3 entry: an enum id, rustc's positional list, rustc's explicit `repr`. -/
abbrev B3Entry := Nat × List (Nat × Int) × Option IntTy

/-- B3 for EVERY enum of the artifact: each enum the module declares has an
    entry, and every entry checks against rustc's list. -/
def checkB3All (bs : List Nat) (tbl : List B3Entry) : Bool :=
  match decode bs with
  | .ok m => m.enums.all (fun d => tbl.any (fun e => e.1 == d.id)) &&
      tbl.all (fun e => checkB3 bs e.1 e.2.1 e.2.2)
  | .error _ => false

def B3All (bs : List Nat) (tbl : List B3Entry) : Prop :=
  ∃ m, decode bs = .ok m ∧ (∀ d ∈ m.enums, ∃ e ∈ tbl, e.1 = d.id) ∧
    ∀ e ∈ tbl, B3OK bs e.1 e.2.1 e.2.2

theorem checkB3All_sound {bs : List Nat} {tbl : List B3Entry} (h : checkB3All bs tbl = true) :
    B3All bs tbl := by
  simp only [checkB3All] at h
  split at h
  · next m hm =>
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
    exact ⟨m, hm, h.1, fun e he => checkB3_sound (h.2 e he)⟩
  · exact nomatch h

/-- **A D-2(b) row**: a "proved (calculus)" row over an artifact whose every
    enum's positional discriminants are rustc's (B3), so the range `Valid_R`
    reads an enum value in is the one rustc assigns. -/
def RowProvedB3 (bs : List Nat) (A : Nat → List Cons) (fid : Nat) (sym : List Nat)
    (tbl : List B3Entry) : Prop :=
  RowProved bs A fid sym ∧ B3All bs tbl

theorem rowB3_of {bs : List Nat} {A : Nat → List Cons} {cs : List (Nat × List (List ChkLIA.Step))}
    {fid : Nat} {sym : List Nat} {tbl : List B3Entry} (h : checkBlob bs A cs = true)
    (hs : rowShape bs A fid sym = true) (hb : checkB3All bs tbl = true) :
    RowProvedB3 bs A fid sym tbl :=
  ⟨row_of h hs, checkB3All_sound hb⟩

/-- A run of `fid` on `args` (any arguments, valid or not) ends `Bad`. -/
def runBad (bs : List Nat) (fid : Nat) (args : List Val) : Bool :=
  match decode bs with
  | .ok m => isBadb (runFunction m fid args 1000 64)
  | .error _ => false

end VF5
