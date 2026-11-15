/-
  VF5Check — the certificate check that turns VF4's `chk_LIA_cases` into
  F1's theorems: per function, per module, and per artifact (the blob's
  bytes, decoded by SemR's own decoder).

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Compose

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

theorem mem_zip_of_length {α β : Type} : ∀ {l : List α} {l' : List β}, l.length = l'.length →
    ∀ a ∈ l, ∃ b, (a, b) ∈ l.zip l'
  | [], [], _, a, h => nomatch h
  | x :: xs, y :: ys, hl, a, h => by
    cases h with
    | head => exact ⟨y, List.Mem.head _⟩
    | tail _ h =>
      obtain ⟨b, hb⟩ := mem_zip_of_length (by simpa using hl) a h
      exact ⟨b, List.Mem.tail _ hb⟩
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl

theorem checkVCC_sound {C : Calc} {m : Module} {A : Nat → List Cons} {fid : Nat}
    {certs : List (List ChkLIA.Step)} (h : checkVCC C m A fid certs = true) :
    ∀ p ∈ vcC C m A fid, Unsat p := by
  simp only [checkVCC, Bool.and_eq_true, beq_iff_eq] at h
  intro p hp
  obtain ⟨cert, hc⟩ := mem_zip_of_length h.1 p hp
  exact ChkLIA.chk_LIA_cases_sound _ h.2 (p, cert) hc

theorem checkVC_sound {m : Module} {A : Nat → List Cons} {fid : Nat}
    {certs : List (List ChkLIA.Step)} (h : checkVC m A fid certs = true) :
    ∀ p ∈ vc m A fid, Unsat p := checkVCC_sound h

/-- A precondition annotation from an association list (absent: none). -/
def annot (pre : List (Nat × List Cons)) (fid : Nat) : List Cons :=
  match pre.find? (fun p => p.1 == fid) with
  | some p => p.2
  | none => []

/-- The certificates of one function from an association list. -/
def certsOf (cs : List (Nat × List (List ChkLIA.Step))) (fid : Nat) : List (List ChkLIA.Step) :=
  match cs.find? (fun p => p.1 == fid) with
  | some p => p.2
  | none => []

/-- Every function of the module checks. -/
def checkModuleC (C : Calc) (m : Module) (A : Nat → List Cons)
    (cs : List (Nat × List (List ChkLIA.Step))) : Bool :=
  m.functions.all fun g => checkVCC C m A g.id (certsOf cs g.id)

def checkModule (m : Module) (A : Nat → List Cons)
    (cs : List (Nat × List (List ChkLIA.Step))) : Bool := checkModuleC stdCalc m A cs

/-- The artifact checks: SemR decodes the blob and every function checks. -/
def checkBlobC (C : Calc) (bs : List Nat) (A : Nat → List Cons)
    (cs : List (Nat × List (List ChkLIA.Step))) : Bool :=
  match decode bs with
  | .ok m => checkModuleC C m A cs
  | .error _ => false

def checkBlob (bs : List Nat) (A : Nat → List Cons)
    (cs : List (Nat × List (List ChkLIA.Step))) : Bool := checkBlobC stdCalc bs A cs

theorem checkModuleC_sound {C : Calc} {m : Module} {A : Nat → List Cons}
    {cs : List (Nat × List (List ChkLIA.Step))} (h : checkModuleC C m A cs = true) :
    ∀ g ∈ m.functions, ∀ p ∈ vcC C m A g.id, Unsat p := by
  simp only [checkModuleC, List.all_eq_true] at h
  exact fun g hg => checkVCC_sound (h g hg)

/-- **`Valid_R` of the artifact**: the module the blob's bytes decode to has
    every function `Valid_R` under `A`, and the closed program is safe. -/
def ValidBlob (bs : List Nat) (A : Nat → List Cons) : Prop :=
  ∃ m, decode bs = .ok m ∧ (∀ g ∈ m.functions, Valid_R m A g.id) ∧ ClosedSafe m A

theorem checkBlob_sound {bs : List Nat} {A : Nat → List Cons}
    {cs : List (Nat × List (List ChkLIA.Step))} (h : checkBlob bs A cs = true) : ValidBlob bs A := by
  simp only [checkBlob, checkBlobC] at h
  split at h
  · next m hm =>
    have hv := checkModuleC_sound h
    exact ⟨m, hm, fun g hg => vc_sound_F1 m A g.id (hv g hg), vc_closed m A hv⟩
  · exact nomatch h

/-! ## The row's entry premise and the row's function, decided on the decoded module

A precondition annotation is the callee-contract premise SBC R3 owns: a function
that carries one is safe only when every caller meets it. `compose_F1` checks it at
every call site INSIDE the module; nothing in the artifact says who calls from
outside (the compiler gives every Rust function external linkage and default
visibility). So a row is minted only when the module's ROOTS — the functions no
function of the module calls, which only a caller outside it can enter — carry no
precondition, and every function that carries one is reachable from a root by
direct calls. Then the roots are safe on ANY well-typed valid arguments
(`RootsSafe`), and an annotated function runs only where some call site meets its
precondition. What stays a premise, stated in the row: no caller outside the
module enters an annotated (non-root) function directly. -/

/-- The functions a body calls directly. -/
def callees (f : Func) : List Nat :=
  f.blocks.flatMap fun b => b.body.filterMap fun n =>
    match n.inst with
    | .call c _ => some c
    | _ => none

/-- The module's roots: the functions no function of the module calls. -/
def roots (m : Module) : List Nat :=
  (m.functions.filter fun g => !(m.functions.any fun h => (callees h).contains g.id)).map (·.id)

/-- One step of the call graph: the set and every direct callee of its members. -/
def reachStep (m : Module) (s : List Nat) : List Nat :=
  (s ++ (m.functions.filter fun g => s.contains g.id).flatMap callees).eraseDups

def reachFrom (m : Module) : Nat → List Nat → List Nat
  | 0, s => s
  | n + 1, s => reachFrom m n (reachStep m s)

/-- The functions reachable from a root by direct calls (as many steps as the
    module has functions: every simple call path). -/
def reachable (m : Module) : List Nat := reachFrom m m.functions.length (roots m)

/-- **The entry premise**: no root carries a precondition, and every function
    that carries one is reachable from a root. -/
def entriesOK (m : Module) (A : Nat → List Cons) : Bool :=
  (roots m).all (fun r => (A r).isEmpty) &&
    m.functions.all fun g => (A g.id).isEmpty || (reachable m).contains g.id

/-- Every root, entered from outside with ANY well-typed valid arguments, at
    every budget and call depth, never ends `Bad`. -/
def RootsSafe (m : Module) : Prop :=
  ∀ r ∈ roots m, ∀ (f : Func) (sig : FuncTy) (args : List Val) (fuel depth : Nat),
    fnOf m r = some (f, sig) → ArgsOK m sig.params args → ¬ Bad (runFunction m r args fuel depth)

theorem rootsSafe_of {m : Module} {A : Nat → List Cons} (hc : ClosedSafe m A)
    (he : entriesOK m A = true) : RootsSafe m := by
  intro r hr f sig args fuel depth hf ha
  simp only [entriesOK, Bool.and_eq_true, List.all_eq_true] at he
  have h0 : A r = [] := List.isEmpty_iff.mp (he.1 r hr)
  exact hc r f sig args fuel depth hf ha (by rw [h0]; intro c hc; exact nomatch hc)

/-- The row's shape, decided: function `fid` is in the module under the symbol
    `sym` (the artifact's own `Function.name`, the mangled path the row names),
    and the entry premise holds. -/
def rowShape (bs : List Nat) (A : Nat → List Cons) (fid : Nat) (sym : List Nat) : Bool :=
  match decode bs with
  | .ok m => m.functions.any (fun g => g.id == fid && g.name == sym) && entriesOK m A
  | .error _ => false

/-- **A "proved (calculus)" row**: the artifact decodes; function `fid` is in it
    under the symbol `sym`; that function is `Valid_R` under `A`; the closed module
    is safe from every entry meeting its precondition; the entry premise holds; and
    so every root is safe on ANY well-typed valid arguments. -/
def RowProved (bs : List Nat) (A : Nat → List Cons) (fid : Nat) (sym : List Nat) : Prop :=
  ∃ m, decode bs = .ok m ∧ (∃ g ∈ m.functions, g.id = fid ∧ g.name = sym) ∧ Valid_R m A fid ∧
    ClosedSafe m A ∧ entriesOK m A = true ∧ RootsSafe m

theorem row_of {bs : List Nat} {A : Nat → List Cons} {cs : List (Nat × List (List ChkLIA.Step))}
    {fid : Nat} {sym : List Nat} (h : checkBlob bs A cs = true) (hs : rowShape bs A fid sym = true) :
    RowProved bs A fid sym := by
  obtain ⟨m, hm, hv, hc⟩ := checkBlob_sound h
  simp only [rowShape, hm, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨g, hg, rfl, hn⟩, he⟩ := hs
  exact ⟨m, hm, ⟨g, hg, rfl, hn⟩, hv g hg, hc, he, rootsSafe_of hc he⟩

/-! ## Deciding argument facts -/

def valOKb (m : Module) : Val → Bool
  | .int t a => decide (a < modulus t.bits)
  | .bool _ => true
  | .enum id ls => enumOKb m id ls
  | _ => false

def argsOKb (m : Module) : List Ty → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => v.ty.beq t && valOKb m v && argsOKb m ts vs
  | _, _ => false

def isBadb : Out → Bool
  | .ret _ => false
  | .outOfFuel => false
  | _ => true

def preHoldsb (pre : List Cons) (args : List Val) : Bool :=
  pre.all fun c => decide (ChkLIA.dot c.coeffs (argρ args) ≤ c.bound)

theorem argsOKb_sound : ∀ {ts : List Ty} {vs : List Val}, argsOKb m ts vs = true → ArgsOK m ts vs
  | [], [], _ => trivial
  | t :: ts, v :: vs, h => by
    simp only [argsOKb, Bool.and_eq_true] at h
    refine ⟨h.1.1, ?_, argsOKb_sound h.2⟩
    have hv := h.1.2
    cases v with
    | int t a => simpa [valOKb, ValOK] using hv
    | bool b => trivial
    | enum id ls => exact enumOKb_sound (by simpa [valOKb] using hv)
    | _ => simp [valOKb] at hv
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- The precondition of function `fid` is satisfiable: `args` are well typed,
    in range, and meet it (the kernel evaluates this on literals). -/
def preWitness (bs : List Nat) (A : Nat → List Cons) (fid : Nat) (args : List Val) : Bool :=
  match decode bs with
  | .ok m =>
    match fnOf m fid with
    | some (_, sig) => argsOKb m sig.params args && preHoldsb (A fid) args
    | none => false
  | .error _ => false

theorem preWitness_sound {bs : List Nat} {A : Nat → List Cons} {fid : Nat} {args : List Val}
    (h : preWitness bs A fid args = true) :
    ∃ m f sig, decode bs = .ok m ∧ fnOf m fid = some (f, sig) ∧ ArgsOK m sig.params args ∧
      PreHolds (A fid) args := by
  simp only [preWitness] at h
  split at h
  · next m hm =>
    split at h
    · next f sig hf =>
      simp only [Bool.and_eq_true] at h
      refine ⟨m, f, sig, hm, hf, argsOKb_sound h.1, ?_⟩
      intro c hc
      simp only [preHoldsb, List.all_eq_true, decide_eq_true_eq] at h
      exact h.2 c hc
    · exact nomatch h
  · exact nomatch h

end VF5
