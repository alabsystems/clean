/-
  Unsigned comparison normalization and selection over canonical SemR.
  No alternative instruction decoder or execution relation.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanWPMemory
import SemRMemory

namespace SemRUnsignedSelect
open SemR SemRBooleanWP

/-- The admitted machine domains of the source-clause select reader. -/
def Supported (t : IntTy) : Prop := t = .u8 ∨ t = .u16 ∨ t = .u32 ∨ t = .u64

theorem ugt_not_ule (width a b : Nat) :
    icmpR .ugt width a b = !(icmpR .ule width a b) := by
  by_cases h : a ≤ b
  · have hn : ¬ b < a := Nat.not_lt.mpr h
    simp [icmpR, h, hn]
  · have hg : b < a := Nat.lt_of_not_ge h
    simp [icmpR, h, hg]

theorem uge_not_ult (width a b : Nat) :
    icmpR .uge width a b = !(icmpR .ult width a b) := by
  by_cases h : a < b
  · have hn : ¬ b ≤ a := Nat.not_le.mpr h
    simp [icmpR, h, hn]
  · have hg : b ≤ a := Nat.le_of_not_gt h
    simp [icmpR, h, hg]

/-- Negating the condition requires swapping BOTH operands, at every type. -/
theorem selectOn_not_swap (k : Core) (node : Node) (yes no : Val) (c : Bool) :
    selectOn k node yes no (.bool (!c)) = selectOn k node no yes (.bool c) := by
  cases c <;> rfl

theorem ugt_select_swap (k : Core) (node : Node) (yes no : Val) (width a b : Nat) :
    selectOn k node yes no (.bool (icmpR .ugt width a b)) =
      selectOn k node no yes (.bool (icmpR .ule width a b)) := by
  rw [ugt_not_ule]
  exact selectOn_not_swap k node yes no _

theorem uge_select_swap (k : Core) (node : Node) (yes no : Val) (width a b : Nat) :
    selectOn k node yes no (.bool (icmpR .uge width a b)) =
      selectOn k node no yes (.bool (icmpR .ult width a b)) := by
  rw [uge_not_ult]
  exact selectOn_not_swap k node yes no _

theorem expect_int (pointerBits : Nat) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits pointerBits)) :
    expectTy pointerBits (.int t a) (.int t) = .ok () := by
  simp [expectTy, Val.ty, Ty.beq, ha]

theorem eval_ugt (pointerBits : Nat) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits pointerBits))
    (hb : b < modulus (t.bits pointerBits)) :
    evalIcmp pointerBits .ugt (.int t) (.int t a) (.int t b) =
      .ok (.bool (!(icmpR .ule (t.bits pointerBits) a b))) := by
  simp [evalIcmp, expect_int, ha, hb, isBoolTy, expectInt, rejectPoison, ugt_not_ule, pure, ok_bind]

theorem eval_uge (pointerBits : Nat) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits pointerBits))
    (hb : b < modulus (t.bits pointerBits)) :
    evalIcmp pointerBits .uge (.int t) (.int t a) (.int t b) =
      .ok (.bool (!(icmpR .ult (t.bits pointerBits) a b))) := by
  simp [evalIcmp, expect_int, ha, hb, isBoolTy, expectInt, rejectPoison, uge_not_ult, pure, ok_bind]

/-- The exact state update made by SemR's one-result integer select. -/
def writeInt (k : Core) (dst : Nat) (t : IntTy) (a : Nat) : Core :=
  { next k with env := (dst, .int t a) :: k.env }

def selectNode (t : IntTy) (dst condition yes no : Nat) : Node :=
  ⟨.select (.int t) condition yes no, [dst]⟩

theorem select_step (m : Module) (k : Core) (t : IntTy)
    (dst condition yes no : Nat) (c : Bool) (a b : Nat)
    (hc : lookupEnv k.env condition = some (.bool c))
    (hy : lookupEnv k.env yes = some (.int t a))
    (hn : lookupEnv k.env no = some (.int t b))
    (ha : a < modulus (t.bits m.pointerBits))
    (hb : b < modulus (t.bits m.pointerBits)) :
    execNode m k (selectNode t dst condition yes no) =
      .cont (writeInt k dst t (if c then a else b)) := by
  cases c <;>
    simp [execNode, selectNode, selectStep, getV, hc, hy, hn, rejectPoison,
      expect_int, ha, hb, selectOn, asBool, ofR, bindResults, writeInt, next, ok_bind]

theorem ugt_select_min (width a b : Nat) :
    (if icmpR .ugt width a b then b else a) = min a b := by
  by_cases h : a ≤ b
  · simp [icmpR, Nat.not_lt.mpr h, Nat.min_eq_left h]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [icmpR, Nat.lt_of_not_ge h, Nat.min_eq_right hba]

theorem uge_select_min (width a b : Nat) :
    (if icmpR .uge width a b then b else a) = min a b := by
  by_cases h : b ≤ a
  · simp [icmpR, h, Nat.min_eq_right h]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [icmpR, h, Nat.min_eq_left hab]

theorem clamp_bounds (a bound : Nat) : min a bound ≤ bound ∧ min a bound ≤ a :=
  ⟨Nat.min_le_right _ _, Nat.min_le_left _ _⟩

theorem clamp_width_bounds (w : Nat) : min w 64 ≤ 64 ∧ min w 64 ≤ w :=
  clamp_bounds w 64

theorem clamp_to_max_bounds (n maximum : Nat) :
    min n maximum ≤ maximum ∧ min n maximum ≤ n := clamp_bounds n maximum


theorem const_int_step (m : Module) (k : Core) (dst : Nat) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits m.pointerBits)) :
    execNode m k ⟨.const (.int t) (.int a), [dst]⟩ = .cont (writeInt k dst t a) := by
  simp [execNode, constStep, constVal, Nat.mod_eq_of_lt ha, ofR, bindResults, writeInt, next, pure, ok_bind]

theorem copy_int_step (m : Module) (k : Core) (dst src : Nat) (t : IntTy) (a : Nat)
    (h : lookupEnv k.env src = some (.int t a))
    (ha : a < modulus (t.bits m.pointerBits)) :
    execNode m k ⟨.copy (.int t) src, [dst]⟩ = .cont (writeInt k dst t a) := by
  simp [execNode, copyStep, getV, h, expect_int, ha, ofR, bindResults, writeInt, next, ok_bind]

theorem icmp_int_step (m : Module) (k : Core) (dst lhs rhs : Nat) (op : ICmpOp)
    (t : IntTy) (a b : Nat)
    (hl : lookupEnv k.env lhs = some (.int t a))
    (hr : lookupEnv k.env rhs = some (.int t b))
    (ha : a < modulus (t.bits m.pointerBits))
    (hb : b < modulus (t.bits m.pointerBits)) :
    execNode m k ⟨.icmp op (.int t) lhs rhs, [dst]⟩ =
      .cont (writeBool k dst (icmpR op (t.bits m.pointerBits) a b)) := by
  simp [execNode, icmpStep, getV, hl, hr, evalIcmp, expect_int, ha, hb,
    isBoolTy, expectInt, rejectPoison, ofR, bindResults, writeBool, next, ok_bind, pure]

theorem assume_true_step (m : Module) (k : Core) (condition : Nat)
    (h : lookupEnv k.env condition = some (.bool true)) :
    execNode m k ⟨.assume condition, []⟩ = .cont (next k) := by
  simp [execNode, getV, h, expectBool, rejectPoison, assumeOn, ofR, bindResults, next, pure, ok_bind]

theorem return_int_step (m : Module) (k : Core) (src : Nat) (t : IntTy) (a : Nat)
    (h : lookupEnv k.env src = some (.int t a))
    (ha : a < modulus (t.bits m.pointerBits)) (hs : k.stack = [])
    (ht : k.sig.returns = [.int t]) :
    execNode m k ⟨.ret [src], []⟩ = .done (.ret [.int t a]) := by
  simp [execNode, retStep, getVs, getV, h, hs, ht, checkSig, expect_int, ha,
    rejectPoison, returnTo, ofR, Val.ty, Ty.beq, pure, ok_bind]

def storedInt (k : Core) (index offset : Nat) (al : Alloc) (t : IntTy) (a : Nat)
    (pointerBits : Nat) : Core :=
  { next k with mem := written k.mem index offset al (leBytes (t.bytes pointerBits) a) }

theorem store_int_step (m : Module) (k : Core) (ptr src index offset : Nat)
    (al : Alloc) (t : IntTy) (a : Nat)
    (hp : lookupEnv k.env ptr = some (.ptr index offset))
    (hv : lookupEnv k.env src = some (.int t a))
    (ha : a < modulus (t.bits m.pointerBits))
    (hal : checkAlign (t.bytes m.pointerBits) = .ok (t.bytes m.pointerBits))
    (hac : accessAt k.mem "Store" index offset (t.bytes m.pointerBits) (t.bytes m.pointerBits) = .ok al) :
    execNode m k ⟨.store (.int t) ptr src false none, []⟩ =
      .cont (storedInt k index offset al t a m.pointerBits) := by
  simp [execNode, storeStep, getV, hp, hv, scalarLayout, storeImage, expect_int, ha,
    encodeVal, hal, expectPtr, rejectPoison, hac, ofR, storedInt, bindResults, next, pure, ok_bind]

theorem load_stored_int_step (m : Module) (k : Core) (dst ptr index offset : Nat)
    (al : Alloc) (data : List AByte) (t : IntTy) (a : Nat)
    (hp : lookupEnv k.env ptr = some (.ptr index offset))
    (ha : a < modulus (t.bits m.pointerBits))
    (hal : checkAlign (t.bytes m.pointerBits) = .ok (t.bytes m.pointerBits))
    (hdata : al.data = writeBytes data offset (leBytes (t.bytes m.pointerBits) a))
    (hac : accessAt k.mem "Load" index offset (t.bytes m.pointerBits) (t.bytes m.pointerBits) = .ok al)
    (hbits : m.pointerBits = 32 ∨ m.pointerBits = 64) :
    execNode m k ⟨.load (.int t) ptr false none, [dst]⟩ = .cont (writeInt k dst t a) := by
  simp only [execNode, loadStep, getV, hp, scalarLayout, hal, Option.getD_none,
    expectPtr, rejectPoison, hac, pure, ok_bind, hdata, ofR]
  rw [readOut_after_store_target m.pointerBits hbits k _ t false data offset a ha]
  rfl


theorem at_node (m : Module) (k : Core) (node : Node) (result : StepR)
    (hat : nth? k.block.body k.pc = some node) (he : execNode m k node = result) :
    Step m k result := by
  have h : stepCore m k = result := by simp only [stepCore, hat, he]
  rw [← h]
  exact step_complete m k


theorem ugt_clamp_step (m : Module) (k : Core) (t : IntTy) (_supported : Supported t)
    (dst condition yes no a b : Nat)
    (hc : lookupEnv k.env condition = some (.bool (icmpR .ugt (t.bits m.pointerBits) a b)))
    (hy : lookupEnv k.env yes = some (.int t b))
    (hn : lookupEnv k.env no = some (.int t a))
    (ha : a < modulus (t.bits m.pointerBits)) (hb : b < modulus (t.bits m.pointerBits)) :
    execNode m k (selectNode t dst condition yes no) = .cont (writeInt k dst t (min a b)) := by
  simpa only [ugt_select_min] using select_step m k t dst condition yes no _ b a hc hy hn hb ha

theorem uge_clamp_step (m : Module) (k : Core) (t : IntTy) (_supported : Supported t)
    (dst condition yes no a b : Nat)
    (hc : lookupEnv k.env condition = some (.bool (icmpR .uge (t.bits m.pointerBits) a b)))
    (hy : lookupEnv k.env yes = some (.int t b))
    (hn : lookupEnv k.env no = some (.int t a))
    (ha : a < modulus (t.bits m.pointerBits)) (hb : b < modulus (t.bits m.pointerBits)) :
    execNode m k (selectNode t dst condition yes no) = .cont (writeInt k dst t (min a b)) := by
  simpa only [uge_select_min] using select_step m k t dst condition yes no _ b a hc hy hn hb ha

end SemRUnsignedSelect
