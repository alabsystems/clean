/-
  VF5Mutants — three mutant calculi, each refuted by a kernel-checked
  counterexample: a program whose every mutant obligation the kernel refutes
  (so the mutant would call it safe) and whose SemR run, evaluated by the
  kernel, panics or reaches undefined behaviour.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  * `mutWrap` (wrap on overflow): the checked trio's flag is never set, so a
    wrapped sum passes its `Assert`.
  * `mutSign` (flipped signedness): `slt`/`sle`/`sgt`/`sge` read the residues
    as unsigned; `mutSignAt o`: only `o` read so.
  * `mutDiv` (a missing div-by-zero arm): `udiv`/`urem`/`sdiv`/`srem` emit no
    divisor-zero obligation.

  The counterexamples live in `VF5MutantRows` (generated: the compiler's blobs
  and the mutants' certificates); this module states what a refutation is.
-/
import VF5Check

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

/-- The flag of every checked-trio branch cleared. -/
def clearFlag : SV → SV
  | .bool _ => .bool false
  | v => v

def mutWrap : Calc :=
  { stdCalc with ovf := fun op t ea eb nv =>
      (ovfCases op t ea eb nv).map fun b => { b with vals := b.vals.map clearFlag } }

def unsignedOf : ICmpOp → ICmpOp
  | .slt => .ult
  | .sle => .ule
  | .sgt => .ugt
  | .sge => .uge
  | op => op

def mutSign : Calc :=
  { stdCalc with cmp := fun op w ea eb => cmpCases (unsignedOf op) w ea eb }

/-- `o` read unsigned when it is `op`; every other comparison as it is. -/
def unsignedAt : ICmpOp → ICmpOp → ICmpOp
  | .slt, .slt => .ult
  | .sle, .sle => .ule
  | .sgt, .sgt => .ugt
  | .sge, .sge => .uge
  | _, op => op

/-- The narrow mutants: ONE signed comparison read unsigned, the other three
    signed. Each has its own witness (`VF5MutantRows`), so a calculus that
    flips any one of the four is refuted, not only one that flips all four. -/
def mutSignAt (o : ICmpOp) : Calc :=
  { stdCalc with cmp := fun op w ea eb => cmpCases (unsignedAt o op) w ea eb }

def mutDiv : Calc :=
  { stdCalc with bin := fun op t ea eb nv cs =>
      match op with
      | .udiv | .urem | .sdiv | .srem => (binCases op t ea eb nv cs).map fun (ubs, bs) => (ubs.drop 1, bs)
      | _ => binCases op t ea eb nv cs }

/-! ## VF7's mutant calculi (R206): one bit-level encoding wrong each -/

/-- An arithmetic shift right that zero-fills: `ashr` read as `lshr` (the
    `bvashr` zero-fill mutant `ay/LIMITATIONS.md` names). -/
def mutAshr : Calc :=
  { stdCalc with bin := fun op t ea eb nv cs =>
      match op with
      | .ashr => binCases .lshr t ea eb nv cs
      | _ => binCases op t ea eb nv cs }

/-- `^` read as `|`: the bit `1 ^ 1` taken for `1`. -/
def mutXor : Calc :=
  { stdCalc with bin := fun op t ea eb nv cs =>
      match op with
      | .xor => binCases .or t ea eb nv cs
      | _ => binCases op t ea eb nv cs }

/-- A narrowing cast that keeps the value: `trunc` without the wrap. -/
def mutTrunc : Calc :=
  { stdCalc with cast := fun op t dst e nv cs =>
      match op, dst with
      | .trunc, .int t' => if isF1Int t' then some [⟨[], [.int t' e], nv⟩] else none
      | _, _ => castCases op t dst e nv cs }

/-- What a calculus claims: refuted obligations for every function make the
    closed program safe. `vc_closed` is this for `stdCalc`. -/
def CalcSound (C : Calc) : Prop :=
  ∀ (m : Module) (A : Nat → List Cons), (∀ g ∈ m.functions, ∀ p ∈ vcC C m A g.id, Unsat p) →
    ClosedSafe m A

theorem stdCalc_sound : CalcSound stdCalc := fun m A h => vc_closed m A h

/-! ## Deciding a bad run -/

/-- A run of `fid` on `args`, entered under its precondition, ends `Bad`. -/
def badRun (m : Module) (A : Nat → List Cons) (fid : Nat) (args : List Val) (fuel depth : Nat) : Bool :=
  match fnOf m fid with
  | some (_, sig) => argsOKb m sig.params args && preHoldsb (A fid) args &&
      isBadb (runFunction m fid args fuel depth)
  | none => false

theorem badRun_sound {m : Module} {A : Nat → List Cons} {fid : Nat} {args : List Val}
    {fuel depth : Nat} (h : badRun m A fid args fuel depth = true) : ¬ ClosedSafe m A := by
  intro hs
  simp only [badRun] at h
  split at h
  · next f sig hf =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hp⟩, hb⟩ := h
    have hpre : PreHolds (A fid) args := by
      intro c hc
      simp only [preHoldsb, List.all_eq_true, decide_eq_true_eq] at hp
      exact hp c hc
    apply hs fid f sig args fuel depth hf (argsOKb_sound ha) hpre
    revert hb
    cases runFunction m fid args fuel depth <;> simp [isBadb, Bad]
  · exact nomatch h

/-- A mutant calculus is refuted by a module, an annotation and certificates
    the kernel accepts for every mutant obligation, and a bad run. -/
theorem refute {C : Calc} {m : Module} {A : Nat → List Cons}
    {cs : List (Nat × List (List ChkLIA.Step))} {fid : Nat} {args : List Val} {fuel depth : Nat}
    (hc : checkModuleC C m A cs = true) (hb : badRun m A fid args fuel depth = true) :
    ¬ CalcSound C :=
  fun hs => badRun_sound hb (hs m A (checkModuleC_sound hc))

def badRunBlob (bs : List Nat) (A : Nat → List Cons) (fid : Nat) (args : List Val)
    (fuel depth : Nat) : Bool :=
  match decode bs with
  | .ok m => badRun m A fid args fuel depth
  | .error _ => false

/-- The same refutation over an artifact: SemR decodes the blob. -/
theorem refuteBlob {C : Calc} {bs : List Nat} {A : Nat → List Cons}
    {cs : List (Nat × List (List ChkLIA.Step))} {fid : Nat} {args : List Val} {fuel depth : Nat}
    (hc : checkBlobC C bs A cs = true) (hb : badRunBlob bs A fid args fuel depth = true) :
    ¬ CalcSound C := by
  simp only [checkBlobC] at hc
  simp only [badRunBlob] at hb
  split at hc
  · next m hm => rw [hm] at hb; exact refute hc hb
  · exact nomatch hc

/-- The blob's program is unsafe: no sound calculus certifies it. -/
theorem unsafeBlob {bs : List Nat} {A : Nat → List Cons} {fid : Nat} {args : List Val}
    {fuel depth : Nat} (hb : badRunBlob bs A fid args fuel depth = true) :
    ∀ m, decode bs = .ok m → ¬ ClosedSafe m A := by
  intro m hm
  simp only [badRunBlob, hm] at hb
  exact badRun_sound hb

/-- The module of the `mutDiv` counterexample, built directly (Rust guards
    every division with an `Assert`, so no compiled body divides unguarded):
    `fn(x: u32, d: u32) -> u32 { udiv x d }`. -/
def divModule : Module :=
  { funcTys := [{ params := [.int .u32, .int .u32], returns := [.int .u32], vararg := false }],
    enums := [],
    functions := [{ id := 0, ty := 0, entry := 0, blocks := [
      { id := 0, params := [(0, .int .u32), (1, .int .u32)],
        body := [{ inst := .binop .udiv (.int .u32) 0 1, results := [2] },
                 { inst := .ret [2], results := [] }] }] }] }

/-- The mutant emits no obligation for the unguarded division. -/
theorem divModule_mutDiv_checks : checkModuleC mutDiv divModule (fun _ => []) [(0, [])] = true := rfl

/-- SemR runs it to undefined behaviour at `d = 0`. -/
theorem divModule_ub :
    runFunction divModule 0 [.int .u32 7, .int .u32 0] 100 8 = .ub "unsigned division by zero" := rfl

/-- **`mutDiv` is unsound.** -/
theorem mutDiv_refuted : ¬ CalcSound mutDiv :=
  refute (fid := 0) (args := [.int .u32 7, .int .u32 0]) (fuel := 100) (depth := 8)
    divModule_mutDiv_checks rfl

/-- F1's own calculus does not certify the same module: its division
    obligation (`d ≤ 0` under `0 ≤ d`) is satisfiable, so no certificate
    exists, and the bad run shows no sound calculus could. -/
theorem divModule_unsafe : ¬ ClosedSafe divModule (fun _ => []) :=
  badRun_sound (fid := 0) (args := [.int .u32 7, .int .u32 0]) (fuel := 100) (depth := 8) rfl

end VF5
