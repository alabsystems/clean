/-
  VF5Spec — the statement pins of F1's theorems.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  * `vc_sound_pin`, `compose_pin` and `row_pin` restate `vc_sound_F1`,
    `compose_F1` and `row_of` verbatim, so this module stops compiling when a
    statement changes.
  * `Failed` spells the bad verdicts out apart from `Bad` (a weakened `Bad`,
    say `fun _ => False`, would make `ClosedSafe` true of every program);
    `bad_iff` is the bridge, and `spec_closed` is the closed-program claim in
    SemR's own words: `runFunction`'s verdict is not `Failed`.
  * `failed_nonvacuous` and `closed_nonvacuous` show neither is trivial: a
    panic is `Failed`, and `divModule` (an unguarded division) is not
    `ClosedSafe` by a kernel-evaluated run.
  * `ForgedVcSound` and `ForgedClosed` are what premise-free versions of the
    two theorems would state; both are refuted here, and the test offers the
    real proofs for them and requires a refusal.

  This is the family's last module: it imports every other.
-/
import VF5Rows
import VF5MutantRows
import VF7Rows
import VF5AtermRows
import VF5D2bRows1
import VF5D2bRows2
import VF5D2bRows3
import VF5D2bRows4
import VF5D2bRows5
import VF5D2bRows6
import VF5D2bRows7
import VF5D2bRows8
import VF5D2bRows9
import VF5D2bRows10
import VF5PM1Rows1
import VF5PM1Rows2
import VF5PM1Rows3
import VF5PM1Rows4
import VF5PM1Rows5
import VF5PM1Rows6

namespace VF5Spec

open SemR VF5

variable {m : Module}

/-- The verdicts that are failures, written apart from `VF5.Bad`. -/
def Failed : Out → Prop
  | .panic _ => True
  | .ub _ => True
  | .typeError _ => True
  | .unsupported _ => True
  | .outOfMemory => True
  | .ret _ => False
  | .outOfFuel => False

theorem bad_iff (o : Out) : VF5.Bad o ↔ Failed o := by cases o <;> simp [VF5.Bad, Failed]

theorem vc_sound_pin : ∀ (m : Module) (A : Nat → List Cons) (fid : Nat),
    (∀ p ∈ vc m A fid, Unsat p) → Valid_R m A fid :=
  vc_sound_F1

theorem compose_pin : ∀ (m : Module) (A : Nat → List Cons),
    (∀ g ∈ m.functions, Valid_R m A g.id) → ClosedSafe m A :=
  compose_F1

theorem row_pin : ∀ {bs : List Nat} {A : Nat → List Cons} {cs : List (Nat × List (List ChkLIA.Step))}
    {fid : Nat} {sym : List Nat}, checkBlob bs A cs = true → rowShape bs A fid sym = true →
    RowProved bs A fid sym :=
  row_of

/-- **What a row is, spelled out** (`RowProved` unfolded by hand): a weakened
    `RowProved` stops this module compiling, as a weakened `Bad` stops `bad_iff`. -/
theorem row_means : ∀ {bs : List Nat} {A : Nat → List Cons} {fid : Nat} {sym : List Nat},
    RowProved bs A fid sym →
    ∃ m, decode bs = .ok m ∧ (∃ g ∈ m.functions, g.id = fid ∧ g.name = sym) ∧
      Valid_R m A fid ∧ ClosedSafe m A ∧ entriesOK m A = true ∧ RootsSafe m :=
  fun h => h

/-- A D-2(b) row, spelled out: the row, and B3 for every enum of the artifact. -/
theorem row_b3_means : ∀ {bs : List Nat} {A : Nat → List Cons} {fid : Nat} {sym : List Nat}
    {tbl : List B3Entry}, RowProvedB3 bs A fid sym tbl →
    RowProved bs A fid sym ∧ ∃ m, decode bs = .ok m ∧ (∀ d ∈ m.enums, ∃ e ∈ tbl, e.1 = d.id) ∧
      ∀ e ∈ tbl, B3OK bs e.1 e.2.1 e.2.2 :=
  fun h => h

/-- **The closed-program claim, in SemR's words.** Refuted obligations for
    every function of the module: then every run of SemR's machine, from any
    function entered with well-typed in-range arguments meeting its
    precondition, at every budget and call depth, ends in a return or out of
    budget — never a panic, undefined behaviour, a type error or an
    unsupported construct. -/
theorem spec_closed (m : Module) (A : Nat → List Cons)
    (h : ∀ g ∈ m.functions, ∀ p ∈ vc m A g.id, ¬ ∃ ρ : Nat → Int, ∀ c ∈ p, c.sat ρ) :
    ∀ (fid : Nat) (f : Func) (sig : FuncTy) (args : List Val) (fuel depth : Nat),
      fnOf m fid = some (f, sig) → ArgsOK m sig.params args →
      (∀ c ∈ A fid, c.sat (argρ args)) → ¬ Failed (runFunction m fid args fuel depth) :=
  fun fid f sig args fuel depth hf ha hp hfail =>
    vc_closed m A h fid f sig args fuel depth hf ha hp ((bad_iff _).mpr hfail)

/-- **A row's claim, in SemR's words.** The artifact decodes to a module in which
    function `fid` carries the symbol `sym`; every root of the module (a function
    no function of it calls), entered with ANY well-typed valid arguments, and
    every function entered with arguments meeting its precondition, at every
    budget and call depth, ends in a return or out of budget. -/
theorem row_spec {bs : List Nat} {A : Nat → List Cons} {fid : Nat} {sym : List Nat}
    (h : RowProved bs A fid sym) :
    ∃ m, decode bs = .ok m ∧ (∃ g ∈ m.functions, g.id = fid ∧ g.name = sym) ∧
      (∀ r ∈ roots m, ∀ (f : Func) (sig : FuncTy) (args : List Val) (fuel depth : Nat),
        fnOf m r = some (f, sig) → ArgsOK m sig.params args →
        ¬ Failed (runFunction m r args fuel depth)) ∧
      (∀ (g : Nat) (f : Func) (sig : FuncTy) (args : List Val) (fuel depth : Nat),
        fnOf m g = some (f, sig) → ArgsOK m sig.params args →
        (∀ c ∈ A g, c.sat (argρ args)) → ¬ Failed (runFunction m g args fuel depth)) := by
  obtain ⟨m, hm, hg, _, hc, _, hr⟩ := row_means h
  exact ⟨m, hm, hg,
    fun r hr' f sig args fuel depth hf ha hfail => hr r hr' f sig args fuel depth hf ha ((bad_iff _).mpr hfail),
    fun g f sig args fuel depth hf ha hp hfail => hc g f sig args fuel depth hf ha hp ((bad_iff _).mpr hfail)⟩

theorem failed_nonvacuous : Failed (.panic "attempt to divide by zero") := trivial

/-- `ClosedSafe` is not true of every program. -/
theorem closed_nonvacuous : ∃ m A, ¬ ClosedSafe m A := ⟨divModule, fun _ => [], divModule_unsafe⟩

/-! ## The statements the negative controls forge

`vf5_f1_reference.rs` offers `vc_sound_F1`'s proof for `ForgedVcSound` and
`compose_F1`'s for `ForgedClosed`, and requires the entry to refuse both; the
refutations below are admitted beside them, so neither forgery is true. -/

/-- What a premise-free `vc_sound_F1` would say: every function is valid. -/
def ForgedVcSound : Prop := ∀ (m : Module) (A : Nat → List Cons) (fid : Nat), Valid_R m A fid

/-- What a premise-free `compose_F1` would say: every program is safe. -/
def ForgedClosed : Prop := ∀ (m : Module) (A : Nat → List Cons), ClosedSafe m A

theorem forged_vc_sound_fails : ¬ ForgedVcSound := by
  intro h
  obtain ⟨_, _, f, sig, hf, _⟩ := h { funcTys := [], enums := [], functions := [] } (fun _ => []) 0
  simp [fnOf] at hf

theorem forged_closed_fails : ¬ ForgedClosed := fun h => divModule_unsafe (h _ _)

/-- No precondition anywhere: the annotation the controls swap in. -/
def noAnnot : Nat → List Cons := annot []

/-! ## F1's explicit target boundary

SemR executes both widths. F1's current symbolic integer calculus is 64-bit:
the checker refuses a 32-bit module rather than reading its `usize` as 64-bit.
These controls use the SAME body and signature, changing only target metadata.
-/

def identityModule : Module :=
  { funcTys := [{ params := [.int .usize], returns := [.int .usize], vararg := false }],
    enums := [], functions := [{ id := 0, ty := 0, entry := 0, blocks := [
      { id := 0, params := [(0, .int .usize)], body := [{ inst := .ret [0], results := [] }] }] }] }

def width32Target : TargetInfo :=
  { triple := "wasm32-unknown-unknown".toList.map Char.toNat,
    pointerSize := 4, bigEndian := false, abi := none, structPassing := 0 }

def width64Target : TargetInfo :=
  { triple := "aarch64-apple-darwin".toList.map Char.toNat,
    pointerSize := 8, bigEndian := false, abi := none, structPassing := 0 }

def width32Module : Module := { identityModule with target := some width32Target }

def width64Module : Module := { identityModule with target := some width64Target }

theorem non64_vc_refused (C : Calc) (m : Module) (A : Nat → List Cons) (fid : Nat)
    (hw : m.pointerBits ≠ 64) : vcC C m A fid = FAIL := by simp [vcC, hw]

theorem nonexec_vc_refused (C : Calc) (m : Module) (A : Nat → List Cons) (fid : Nat)
    (he : m.executableTarget = false) : vcC C m A fid = FAIL := by simp [vcC, he]

theorem width32_vc_refused : vc width32Module noAnnot 0 = FAIL := rfl

theorem width32_check_refused : checkModule width32Module noAnnot [(0, [])] = false := rfl

theorem width32_not_valid : ¬ Valid_R width32Module noAnnot 0 := by
  intro h
  have hw : (32 : Nat) = 64 := h.1
  exact (by decide : (32 : Nat) ≠ 64) hw

/-- Refusing F1 certification does not disable SemR's 32-bit execution. -/
theorem width32_run : runFunction width32Module 0 [.int .usize 7] 10 8 = .ret [.int .usize 7] := rfl

/-- The range check that prevents a 64-bit residue entering 32-bit `usize`. -/
theorem width32_range_refused :
    expectTy 32 (.int .usize (2 ^ 32)) (.int .usize) =
      .stop (.typeError "TypeError: integer value is out of range for the target width") := rfl

theorem width64_check_accepted : checkModule width64Module noAnnot [(0, [])] = true := rfl

theorem width64_run :
    runFunction width64Module 0 [.int .usize (2 ^ 32)] 10 8 = .ret [.int .usize (2 ^ 32)] := rfl

theorem width64_valid : Valid_R width64Module noAnnot 0 :=
  vc_sound_F1 _ _ _ (by intro p hp; exact nomatch hp)

theorem targetless_check_accepted : checkModule identityModule noAnnot [(0, [])] = true := rfl

/-- Every successful F1 theorem states its admitted target in the conclusion. -/
theorem valid_target_pin {m : Module} {A : Nat → List Cons} {fid : Nat}
    (h : Valid_R m A fid) : m.pointerBits = 64 ∧ m.executableTarget = true := ⟨h.1, h.2.1⟩

end VF5Spec
