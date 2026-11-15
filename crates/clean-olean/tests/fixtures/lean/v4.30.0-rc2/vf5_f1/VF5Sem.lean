/-
  VF5Sem — what F1's theorems are about, stated on SemR alone: `Bad`, the
  frame-local reading of a body under its callees' contracts (`LStep`,
  `LBad`), `Valid_R`, and the closed-program statement `compose_F1` proves.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  Nothing here mentions the calculus: these definitions use SemR's own
  `execNode`, `getVs`, `bindResults`, `checkSig`, `start` and `runFunction`.

  * `Bad o`: a verdict other than a return or running out of budget — a
    panic (a failed `Assert`), undefined behaviour, a type error or an
    unsupported construct.
  * `LStep`/`LBad`: one function body read frame by frame. A node of the
    frame-local fragment steps by SemR's `execNode`; a `call` is read through
    the callee's contract: it is BAD unless the arguments meet the callee's
    precondition `A callee` and enter its body, and otherwise steps to the
    next node with ANY well-typed, in-range results. A `ret` is bad when its
    values miss the signature; the frame-binding instructions are outside
    the fragment and bad.
  * `Valid_R m A fid`: every frame state reachable from any well-typed
    valid entry meeting `A fid`, under any outer context (call stack,
    depth, open binding frames), is not bad and holds valid values. A valid
    value is an integer residue of its width, a `Bool`, or a fieldless enum
    value whose tag is one of its discriminants (Rust's validity invariant:
    the entry premise D-2(b) rests on).
  * `ClosedSafe m A`: every run of every function entered with well-typed
    in-range arguments meeting its precondition never ends `Bad`, for every
    budget and call depth (`runFunction`, SemR's whole machine, callees run
    for real on its call stack).
-/
import SemR
import ChkLIACases

namespace VF5

open SemR

/-- F1's present calculus uses the 64-bit reference integer widths. SemR also
    executes 32-bit modules; admitting those requires a target-aware calculus. -/
abbrev F1Target (m : Module) : Prop := m.pointerBits = 64

def Bad : Out → Prop
  | .ret _ => False
  | .outOfFuel => False
  | _ => True

/-- A fieldless enum F1 reads (D-2(b)): every variant without fields, one
    effective discriminant per variant, a tag of at most 64 bits. -/
def isF1Enum (d : EnumDef) : Bool :=
  d.variants.all (fun v => v.fields.isEmpty) && d.variants.length == d.discs.length &&
    decide (d.tag.bits ≤ 64)

/-- A VALID fieldless enum value (Rust's validity invariant, the entry premise
    D-2(b) rests on): its one lane is the tag, at the enum's tag type, and the
    tag is the residue of one of the enum's discriminants. -/
def EnumOK (m : Module) (id : Nat) (lanes : List Val) : Prop :=
  ∃ d, findEnum m.enums id = some d ∧ isF1Enum d = true ∧
    ∃ disc ∈ d.discs, lanes = [.int d.tag (resid d.tag.bits disc)]

/-- An F1 value: an integer residue of its width, a `Bool`, or a valid
    fieldless enum value. -/
def ValOK (m : Module) : Val → Prop
  | .int t a => a < modulus t.bits
  | .bool _ => True
  | .enum id lanes => EnumOK m id lanes
  | _ => False

def EnvOK (m : Module) (env : List (Nat × Val)) : Prop := ∀ p ∈ env, ValOK m p.2

/-- Well-typed (`checkSig`'s type test) and valid. -/
def ArgsOK (m : Module) : List Ty → List Val → Prop
  | [], [] => True
  | t :: ts, v :: vs => v.ty.beq t = true ∧ ValOK m v ∧ ArgsOK m ts vs
  | _, _ => False

/-- The integer reading of a value: a residue, or a `Bool`'s 0/1. -/
def valInt : Val → Int
  | .int _ a => (a : Int)
  | .bool b => if b then 1 else 0
  | _ => 0

/-- Argument `i` as variable `i`. -/
def argρ (args : List Val) (i : Nat) : Int :=
  match nth? args i with
  | some v => valInt v
  | none => 0

/-- The precondition `pre` (constraints over the parameter variables) holds of `args`. -/
def PreHolds (pre : List ChkLIA.Cons) (args : List Val) : Prop :=
  ∀ c ∈ pre, c.sat (argρ args)

/-- The nodes `execNode` runs inside one frame. -/
def isLocal : Inst → Bool
  | .binop .. | .unop .. | .overflow .. | .icmp .. | .const .. | .copy .. | .select ..
  | .extractField .. | .insertField .. | .nullPtr | .unreachable | .assert .. | .br ..
  | .condBr .. | .cast .. | .switch .. => true
  | _ => false

def isOkR {α : Type} : R α → Bool
  | .ok _ => true
  | .stop _ => false

/-- The function `id` names and its signature, as `execNode`'s `call` arm and
    `start` find them. -/
def fnOf (m : Module) (id : Nat) : Option (Func × FuncTy) :=
  match m.functions.find? (fun f => f.id == id) with
  | none => none
  | some f =>
    match nth? m.funcTys f.ty with
    | none => none
    | some sig => some (f, sig)

/-- A call enters its callee's body (`execNode`'s `call` arm with call depth
    left), and its node binds as many results as the callee returns. -/
def entersOk (m : Module) (f : Func) (sig : FuncTy) (vs : List Val) (node : Node) : Bool :=
  !sig.vararg && isOkR (checkSig m.pointerBits vs sig.params) && !f.blocks.isEmpty &&
    (match findBlock f.blocks f.entry with
     | none => false
     | some b => isOkR (bindParams m.pointerBits [] b.params vs)) &&
    node.results.length == sig.returns.length

/-- Results a callee may return: well-typed, valid. -/
def RetsOK (m : Module) (ts : List Ty) (vs : List Val) : Prop := ArgsOK m ts vs

/-- One frame-local step. -/
inductive LStep (m : Module) (A : Nat → List ChkLIA.Cons) : Core → Core → Prop where
  | exec (k k' : Core) (node : Node) :
      nth? k.block.body k.pc = some node → isLocal node.inst = true →
      execNode m k node = .cont k' → LStep m A k k'
  | call (k k' : Core) (node : Node) (callee : Nat) (args : List Nat) (vs : List Val)
      (f : Func) (sig : FuncTy) (rs : List Val) :
      nth? k.block.body k.pc = some node → node.inst = .call callee args →
      getVs k args = .ok vs → fnOf m callee = some (f, sig) →
      RetsOK m sig.returns rs → bindResults (next k) node rs = .ok k' → LStep m A k k'

/-- A frame state that goes wrong. -/
inductive LBad (m : Module) (A : Nat → List ChkLIA.Cons) : Core → Prop where
  | missing (k : Core) : nth? k.block.body k.pc = none → LBad m A k
  | exec (k : Core) (node : Node) (o : Out) :
      nth? k.block.body k.pc = some node → isLocal node.inst = true →
      execNode m k node = .done o → Bad o → LBad m A k
  | outside (k : Core) (node : Node) :
      nth? k.block.body k.pc = some node → isLocal node.inst = false →
      (∀ callee args, node.inst ≠ .call callee args) → (∀ xs, node.inst ≠ .ret xs) → LBad m A k
  | callArgs (k : Core) (node : Node) (callee : Nat) (args : List Nat) (o : Out) :
      nth? k.block.body k.pc = some node → node.inst = .call callee args →
      getVs k args = .stop o → LBad m A k
  | callFn (k : Core) (node : Node) (callee : Nat) (args : List Nat) (vs : List Val) :
      nth? k.block.body k.pc = some node → node.inst = .call callee args →
      getVs k args = .ok vs → fnOf m callee = none → LBad m A k
  | callEnter (k : Core) (node : Node) (callee : Nat) (args : List Nat) (vs : List Val)
      (f : Func) (sig : FuncTy) :
      nth? k.block.body k.pc = some node → node.inst = .call callee args →
      getVs k args = .ok vs → fnOf m callee = some (f, sig) →
      entersOk m f sig vs node = false → LBad m A k
  | callPre (k : Core) (node : Node) (callee : Nat) (args : List Nat) (vs : List Val)
      (f : Func) (sig : FuncTy) :
      nth? k.block.body k.pc = some node → node.inst = .call callee args →
      getVs k args = .ok vs → fnOf m callee = some (f, sig) →
      ¬ PreHolds (A callee) vs → LBad m A k
  | retArgs (k : Core) (node : Node) (xs : List Nat) (o : Out) :
      nth? k.block.body k.pc = some node → node.inst = .ret xs →
      getVs k xs = .stop o → LBad m A k
  | retSig (k : Core) (node : Node) (xs : List Nat) (vs : List Val) (o : Out) :
      nth? k.block.body k.pc = some node → node.inst = .ret xs →
      getVs k xs = .ok vs → checkSig m.pointerBits vs k.sig.returns = .stop o → LBad m A k

inductive LStar (m : Module) (A : Nat → List ChkLIA.Cons) : Core → Core → Prop where
  | refl (k : Core) : LStar m A k k
  | step (k k' k'' : Core) : LStep m A k k' → LStar m A k' k'' → LStar m A k k''

/-- `k` placed in `c`'s outer context: its call depth, call stack and binding
    frames. -/
def withCtx (k c : Core) : Core :=
  { k with depth := c.depth, stack := c.stack, openFrames := c.openFrames, nextFrame := c.nextFrame,
           cells := c.cells, nextCell := c.nextCell }

/-- **`Valid_R`**: function `fid` of the decoded module `m`, under the
    precondition annotation `A`, read frame-locally with its callees through
    their contracts. This F1 calculus admits only the executable 64-bit domain;
    these facts are conclusions of `vc_sound_F1`, never caller assumptions. -/
def Valid_R (m : Module) (A : Nat → List ChkLIA.Cons) (fid : Nat) : Prop :=
  F1Target m ∧ m.executableTarget = true ∧ ∃ f sig, fnOf m fid = some (f, sig) ∧
    ∀ (args : List Val) (depth : Nat), ArgsOK m sig.params args → PreHolds (A fid) args →
      ∃ k0, start m fid args depth = .ok k0 ∧
        ∀ (c k : Core), LStar m A (withCtx k0 c) k → ¬ LBad m A k ∧ EnvOK m k.env

/-- **The closed-program statement**: SemR's whole machine never ends `Bad`
    from an entry meeting its precondition. -/
def ClosedSafe (m : Module) (A : Nat → List ChkLIA.Cons) : Prop :=
  ∀ (fid : Nat) (f : Func) (sig : FuncTy) (args : List Val) (fuel depth : Nat),
    fnOf m fid = some (f, sig) → ArgsOK m sig.params args → PreHolds (A fid) args →
    ¬ Bad (runFunction m fid args fuel depth)

/-- A conjunction of constraints no integer assignment satisfies. -/
def Unsat (p : List ChkLIA.Cons) : Prop := ¬ ∃ ρ : Nat → Int, ∀ c ∈ p, c.sat ρ

end VF5
