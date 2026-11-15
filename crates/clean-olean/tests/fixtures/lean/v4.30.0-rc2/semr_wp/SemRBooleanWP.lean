/-
  Weakest-precondition rules over SemR's actual scalar Boolean instructions.
  No alternate program syntax, evaluator, or assumption-bearing summary.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemR

namespace SemRBooleanWP
open SemR

/-- The state substitution performed by a one-result Boolean instruction. -/
def writeBool (k : Core) (dst : Nat) (value : Bool) : Core :=
  { next k with env := (dst, .bool value) :: k.env }

def constNode (dst : Nat) (value : Bool) : Node :=
  { inst := .const .bool (.bool value), results := [dst] }

def copyNode (dst src : Nat) : Node :=
  { inst := .copy .bool src, results := [dst] }

def selectNode (dst cond yes no : Nat) : Node :=
  { inst := .select .bool cond yes no, results := [dst] }

/-- This is a predicate substitution, not an assertion about a solver. -/
def constWP (dst : Nat) (value : Bool) (Q : Core → Prop) (k : Core) : Prop :=
  Q (writeBool k dst value)

def copyWP (dst src : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  ∃ b, lookupEnv k.env src = some (.bool b) ∧ Q (writeBool k dst b)

def selectWP (dst cond yes no : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  ∃ c t e, lookupEnv k.env cond = some (.bool c) ∧
    lookupEnv k.env yes = some (.bool t) ∧ lookupEnv k.env no = some (.bool e) ∧
    Q (writeBool k dst (if c then t else e))

theorem const_step (m : Module) (k : Core) (dst : Nat) (b : Bool) :
    execNode m k (constNode dst b) = .cont (writeBool k dst b) := by
  rfl

theorem copy_step (m : Module) (k : Core) (dst src : Nat) (b : Bool)
    (h : lookupEnv k.env src = some (.bool b)) :
    execNode m k (copyNode dst src) = .cont (writeBool k dst b) := by
  simp [execNode, copyNode, copyStep, getV, h, expectTy, Val.ty,
    bindResults, writeBool, next, ok_bind] <;> rfl

theorem select_step (m : Module) (k : Core) (dst cond yes no : Nat) (c t e : Bool)
    (hc : lookupEnv k.env cond = some (.bool c))
    (ht : lookupEnv k.env yes = some (.bool t))
    (he : lookupEnv k.env no = some (.bool e)) :
    execNode m k (selectNode dst cond yes no) =
      .cont (writeBool k dst (if c then t else e)) := by
  cases c <;> simp [execNode, selectNode, selectStep, getV, hc, ht, he,
    rejectPoison, expectTy, Val.ty, selectOn, asBool, bindResults, writeBool, next, ok_bind] <;> rfl

/-- A proved instruction WP authorizes a step of SemR's independent relation
    only when this exact instruction is the one at the current program point. -/
theorem at_pc (m : Module) (k : Core) (node : Node) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some node)
    (h : ∃ k', execNode m k node = .cont k' ∧ Q k') :
    ∃ k', Step m k (.cont k') ∧ Q k' := by
  obtain ⟨k', hs, hq⟩ := h
  refine ⟨k', ?_, hq⟩
  have he : stepCore m k = .cont k' := by simp [stepCore, hat, hs]
  rw [← he]
  exact step_complete m k

theorem const_wp_sound (m : Module) (k : Core) (dst : Nat) (b : Bool) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some (constNode dst b))
    (h : constWP dst b Q k) : ∃ k', Step m k (.cont k') ∧ Q k' := by
  exact at_pc m k _ Q hat ⟨writeBool k dst b, const_step m k dst b, h⟩

theorem copy_wp_sound (m : Module) (k : Core) (dst src : Nat) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some (copyNode dst src))
    (h : copyWP dst src Q k) : ∃ k', Step m k (.cont k') ∧ Q k' := by
  obtain ⟨b, hb, hq⟩ := h
  exact at_pc m k _ Q hat ⟨writeBool k dst b, copy_step m k dst src b hb, hq⟩

theorem select_wp_sound (m : Module) (k : Core) (dst cond yes no : Nat) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some (selectNode dst cond yes no))
    (h : selectWP dst cond yes no Q k) : ∃ k', Step m k (.cont k') ∧ Q k' := by
  obtain ⟨c, t, e, hc, ht, he, hq⟩ := h
  exact at_pc m k _ Q hat
    ⟨writeBool k dst (if c then t else e), select_step m k dst cond yes no c t e hc ht he, hq⟩

def returnNode (src : Nat) : Node := { inst := .ret [src], results := [] }

theorem return_step (m : Module) (k : Core) (src : Nat) (b : Bool)
    (h : lookupEnv k.env src = some (.bool b)) (hs : k.stack = [])
    (ht : k.sig.returns = [.bool]) :
    execNode m k (returnNode src) = .done (.ret [.bool b]) := by
  simp [execNode, returnNode, retStep, getVs, getV, h, ht,
    returnTo, hs, ofR, ok_bind] <;> rfl

def returnWP (src : Nat) (Q : List Val → Prop) (k : Core) : Prop :=
  k.stack = [] ∧ k.sig.returns = [.bool] ∧
    ∃ b, lookupEnv k.env src = some (.bool b) ∧ Q [.bool b]

theorem return_wp_sound (m : Module) (k : Core) (src : Nat) (Q : List Val → Prop)
    (hat : nth? k.block.body k.pc = some (returnNode src)) (h : returnWP src Q k) :
    ∃ vs, Step m k (.done (.ret vs)) ∧ Q vs := by
  obtain ⟨hs, ht, b, hb, hq⟩ := h
  refine ⟨[.bool b], ?_, hq⟩
  have he : stepCore m k = .done (.ret [.bool b]) := by
    simp [stepCore, hat, return_step m k src b hb hs ht]
  rw [← he]
  exact step_complete m k

/-- Block arguments are read in the predecessor state and fed to SemR's
    own simultaneous parameter binding. No second binding semantics enters. -/
theorem branch_step (m : Module) (k k' : Core) (target : Nat) (args : List Nat)
    (vs : List Val) (hv : getVs k args = .ok vs)
    (hj : jump m.pointerBits k target vs = .ok k') :
    execNode m k { inst := .br target args, results := [] } = .cont k' := by
  simp [execNode, brStep, hv, hj, ofR, ok_bind]

theorem conditional_step (m : Module) (k k' : Core) (cond tt et : Nat)
    (ta ea : List Nat) (c : Bool) (vs : List Val)
    (hc : lookupEnv k.env cond = some (.bool c))
    (hv : getVs k (if c then ta else ea) = .ok vs)
    (hj : jump m.pointerBits k (if c then tt else et) vs = .ok k') :
    execNode m k { inst := .condBr cond tt ta et ea, results := [] } = .cont k' := by
  cases c <;> simp_all [execNode, condBrStep, getV, rejectPoison, branchOn, asBool, ofR, ok_bind]

/-- WPs compose over the real run relation, preserving the exact postcondition. -/
theorem compose (m : Module) (k : Core) (fuel : Nat) (out : Out) (Q : Core → Prop)
    (hfirst : ∃ k', Step m k (.cont k') ∧ Q k')
    (hrest : ∀ k', Q k' → Exec m fuel k' out) : Exec m (fuel + 1) k out := by
  obtain ⟨k', hs, hq⟩ := hfirst
  exact Exec.step fuel k k' out hs (hrest k' hq)

def negateBlock : Block :=
  { id := 0, params := [(0, .bool)], body :=
    [constNode 1 false, constNode 2 true, selectNode 3 0 1 2,
      { inst := .ret [3], results := [] }] }

def negateModule : Module :=
  { funcTys := [{ params := [.bool], returns := [.bool], vararg := false }],
    enums := [], functions :=
      [{ id := 0, ty := 0, entry := 0, blocks := [negateBlock], name := [110, 101, 103, 97, 116, 101] }] }

/-- A real parameterized four-instruction program, not a constant goal. -/
theorem negate_correct (b : Bool) (depth : Nat) :
    runFunction negateModule 0 [.bool b] 4 depth = .ret [.bool (!b)] := by
  cases b <;> rfl

def WrongPostcondition : Prop := ∀ (b : Bool) (depth : Nat),
  runFunction negateModule 0 [.bool b] 4 depth = .ret [.bool b]

/-- The old scalar-Not admission cannot satisfy even one actual SemR step. -/
theorem scalar_not_is_type_error (m : Module) (k : Core) (dst src : Nat) (b : Bool)
    (h : lookupEnv k.env src = some (.bool b)) :
    execNode m k { inst := .unop .not .bool src, results := [dst] } =
      .done (.typeError "TypeError: expected integer value") := by
  simp [execNode, unopStep, getV, h, evalUnop, expectTy, Val.ty,
    expectInt, rejectPoison, tyR, ofR, ok_bind] <;> rfl

end SemRBooleanWP
