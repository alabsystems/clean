/- Copyright 2026 Andrew Yates. Apache-2.0.
   Integer assignment/substitution rules for the existing canonical SemR.
   Values are arbitrary exact Nat residues. No evaluator, decoder, solver
   assumption or alternative program syntax is introduced here. -/
import SemR

namespace SemRUnsignedSelect
open SemR

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

/-- The one-result SSA update already performed by SemR.bindResults/next.
    Selection and equality are residue operations, so the rules also apply
    to a signed IntTy without interpreting its residue as a signed number. -/
def writeUInt (k : Core) (dst : Nat) (t : IntTy) (raw : Nat) : Core :=
  { next k with env := (dst, .int t raw) :: k.env }

def writeBoolResult (k : Core) (dst : Nat) (value : Bool) : Core :=
  { next k with env := (dst, .bool value) :: k.env }

def constUInt (dst : Nat) (t : IntTy) (pattern : Nat) : Node :=
  { inst := .const (.int t) (.int pattern), results := [dst] }

def copyUInt (dst src : Nat) (t : IntTy) : Node :=
  { inst := .copy (.int t) src, results := [dst] }

def selectUInt (dst cond yes no : Nat) (t : IntTy) : Node :=
  { inst := .select (.int t) cond yes no, results := [dst] }

def icmpEqUInt (dst lhs rhs : Nat) (t : IntTy) : Node :=
  { inst := .icmp .eq (.int t) lhs rhs, results := [dst] }

def returnUInt (src : Nat) : Node := { inst := .ret [src], results := [] }

theorem checkedUInt (pointerBits : Nat) (t : IntTy) (raw : Nat)
    (bound : raw < modulus (t.bits pointerBits)) :
    expectTy pointerBits (.int t raw) (.int t) = .ok () := by
  simp [expectTy, Val.ty, Ty.beq, bound]

/-- Constants retain SemR's own modulo conversion, including the full U64
    domain; this rule does not route their bit patterns through host Int64. -/
theorem constUInt_step (m : Module) (k : Core) (dst : Nat) (t : IntTy) (pattern : Nat) :
    execNode m k (constUInt dst t pattern) =
      .cont (writeUInt k dst t (pattern % modulus (t.bits m.pointerBits))) := by
  rfl

theorem copyUInt_step (m : Module) (k : Core) (dst src : Nat) (t : IntTy) (raw : Nat)
    (value : getV k src = .ok (.int t raw))
    (bound : raw < modulus (t.bits m.pointerBits)) :
    execNode m k (copyUInt dst src t) = .cont (writeUInt k dst t raw) := by
  simp [execNode, copyUInt, copyStep, value, checkedUInt _ _ _ bound,
    bindResults, writeUInt, next, ofR, ok_bind] <;> rfl

/-- Both values are read and checked in the predecessor state, even when one
    arm is unselected. The Boolean is an actual non-poison SemR value. -/
theorem selectUInt_step (m : Module) (k : Core) (dst cond yes no : Nat) (t : IntTy)
    (c : Bool) (a b : Nat)
    (condition : getV k cond = .ok (.bool c))
    (left : getV k yes = .ok (.int t a))
    (right : getV k no = .ok (.int t b))
    (leftBound : a < modulus (t.bits m.pointerBits))
    (rightBound : b < modulus (t.bits m.pointerBits)) :
    execNode m k (selectUInt dst cond yes no t) =
      .cont (writeUInt k dst t (if c then a else b)) := by
  cases c <;> simp [execNode, selectUInt, selectStep, condition, left, right,
    checkedUInt _ _ _ leftBound, checkedUInt _ _ _ rightBound,
    rejectPoison, selectOn, asBool, bindResults, writeUInt, next, ofR, ok_bind] <;> rfl

theorem icmpEqUInt_step (m : Module) (k : Core) (dst lhs rhs : Nat) (t : IntTy)
    (a b : Nat) (left : getV k lhs = .ok (.int t a))
    (right : getV k rhs = .ok (.int t b))
    (leftBound : a < modulus (t.bits m.pointerBits))
    (rightBound : b < modulus (t.bits m.pointerBits)) :
    execNode m k (icmpEqUInt dst lhs rhs t) =
      .cont (writeBoolResult k dst (a == b)) := by
  simp [execNode, icmpEqUInt, icmpStep, left, right, evalIcmp,
    checkedUInt _ _ _ leftBound, checkedUInt _ _ _ rightBound,
    expectInt, rejectPoison, isBoolTy, icmpR, bindResults,
    writeBoolResult, next, ofR, ok_bind] <;> rfl

theorem returnUInt_step (m : Module) (k : Core) (src : Nat) (t : IntTy) (raw : Nat)
    (value : getV k src = .ok (.int t raw))
    (bound : raw < modulus (t.bits m.pointerBits))
    (stack : k.stack = []) (signature : k.sig.returns = [.int t]) :
    execNode m k (returnUInt src) = .done (.ret [.int t raw]) := by
  simp [execNode, returnUInt, retStep, getVs, value, signature, pure_ok, checkSig,
    rejectPoison, Val.ty, Ty.beq, checkedUInt _ _ _ bound,
    returnTo, stack, ofR, ok_bind] <;> rfl

/-- Establish only a step of the actual instruction at the actual PC. -/
theorem at_pc (m : Module) (k k' : Core) (node : Node)
    (hat : nth? k.block.body k.pc = some node)
    (executed : execNode m k node = .cont k') : Step m k (.cont k') := by
  have h : stepCore m k = .cont k' := by simp [stepCore, hat, executed]
  rw [← h]
  exact step_complete m k

def constUIntWP (m : Module) (dst : Nat) (t : IntTy) (pattern : Nat)
    (Q : Core → Prop) (k : Core) : Prop :=
  Q (writeUInt k dst t (pattern % modulus (t.bits m.pointerBits)))

def copyUIntWP (m : Module) (dst src : Nat) (t : IntTy)
    (Q : Core → Prop) (k : Core) : Prop :=
  ∃ raw, getV k src = .ok (.int t raw) ∧ raw < modulus (t.bits m.pointerBits) ∧
    Q (writeUInt k dst t raw)

/-- Guarded predicate substitution, with the actual eager operand checks.
    This precondition contains no execution or translation-soundness premise. -/
def selectUIntWP (m : Module) (dst cond yes no : Nat) (t : IntTy)
    (Q : Core → Prop) (k : Core) : Prop :=
  ∃ (c : Bool) (a b : Nat), getV k cond = .ok (.bool c) ∧
    getV k yes = .ok (.int t a) ∧ getV k no = .ok (.int t b) ∧
    a < modulus (t.bits m.pointerBits) ∧ b < modulus (t.bits m.pointerBits) ∧
    (c = true → Q (writeUInt k dst t a)) ∧
    (c = false → Q (writeUInt k dst t b))

def icmpEqUIntWP (m : Module) (dst lhs rhs : Nat) (t : IntTy)
    (Q : Core → Prop) (k : Core) : Prop :=
  ∃ (a b : Nat), getV k lhs = .ok (.int t a) ∧ getV k rhs = .ok (.int t b) ∧
    a < modulus (t.bits m.pointerBits) ∧ b < modulus (t.bits m.pointerBits) ∧
    Q (writeBoolResult k dst (a == b))

def returnUIntWP (m : Module) (src : Nat) (t : IntTy)
    (Q : List Val → Prop) (k : Core) : Prop :=
  k.stack = [] ∧ k.sig.returns = [.int t] ∧
    ∃ raw, getV k src = .ok (.int t raw) ∧ raw < modulus (t.bits m.pointerBits) ∧
      Q [.int t raw]

theorem constUInt_wp_step (m : Module) (k : Core) (dst : Nat) (t : IntTy)
    (pattern : Nat) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some (constUInt dst t pattern))
    (wp : constUIntWP m dst t pattern Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  exact ⟨_, at_pc m k _ _ hat (constUInt_step m k dst t pattern), rfl, rfl, wp⟩

theorem copyUInt_wp_step (m : Module) (k : Core) (dst src : Nat) (t : IntTy)
    (Q : Core → Prop) (hat : nth? k.block.body k.pc = some (copyUInt dst src t))
    (wp : copyUIntWP m dst src t Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  obtain ⟨raw, value, bound, hq⟩ := wp
  exact ⟨_, at_pc m k _ _ hat (copyUInt_step m k dst src t raw value bound), rfl, rfl, hq⟩

theorem selectUInt_wp_step (m : Module) (k : Core) (dst cond yes no : Nat) (t : IntTy)
    (Q : Core → Prop) (hat : nth? k.block.body k.pc = some (selectUInt dst cond yes no t))
    (wp : selectUIntWP m dst cond yes no t Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  obtain ⟨c, a, b, hc, ha, hb, hab, hbb, hyes, hno⟩ := wp
  refine ⟨_, at_pc m k _ _ hat (selectUInt_step m k dst cond yes no t c a b hc ha hb hab hbb),
    rfl, rfl, ?_⟩
  cases c with
  | false => exact hno rfl
  | true => exact hyes rfl

theorem icmpEqUInt_wp_step (m : Module) (k : Core) (dst lhs rhs : Nat) (t : IntTy)
    (Q : Core → Prop) (hat : nth? k.block.body k.pc = some (icmpEqUInt dst lhs rhs t))
    (wp : icmpEqUIntWP m dst lhs rhs t Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  obtain ⟨a, b, ha, hb, hab, hbb, hq⟩ := wp
  exact ⟨_, at_pc m k _ _ hat (icmpEqUInt_step m k dst lhs rhs t a b ha hb hab hbb),
    rfl, rfl, hq⟩

theorem returnUInt_wp_step (m : Module) (k : Core) (src : Nat) (t : IntTy)
    (Q : List Val → Prop) (hat : nth? k.block.body k.pc = some (returnUInt src))
    (wp : returnUIntWP m src t Q k) :
    ∃ vs, Step m k (.done (.ret vs)) ∧ Q vs := by
  obtain ⟨stack, signature, raw, value, bound, hq⟩ := wp
  refine ⟨[.int t raw], ?_, hq⟩
  have executed := returnUInt_step m k src t raw value bound stack signature
  have hs : stepCore m k = .done (.ret [.int t raw]) := by simp [stepCore, hat, executed]
  rw [← hs]
  exact step_complete m k

end SemRUnsignedSelect
