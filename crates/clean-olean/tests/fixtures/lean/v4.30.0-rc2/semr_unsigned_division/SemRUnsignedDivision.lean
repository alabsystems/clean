/-
  Positive-constant unsigned division in the canonical SemR execution.
  The 1048576 specialization is the retained raw_megabytes native body.
  This is a return relation, not a caller/source publication authority.
-/
import SemRUnsignedSelect

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SemRUnsignedDivision
open SemR SemRUnsignedSelect SemRBooleanWP

theorem udiv_step (m : Module) (k : Core) (dst lhs rhs : Nat)
    (t : IntTy) (x d : Nat)
    (hl : lookupEnv k.env lhs = some (.int t x))
    (hr : lookupEnv k.env rhs = some (.int t d))
    (hx : x < modulus (t.bits m.pointerBits))
    (hd : d < modulus (t.bits m.pointerBits)) (positive : 0 < d) :
    execNode m k ⟨.binop .udiv (.int t) lhs rhs, [dst]⟩ =
      .cont (writeInt k dst t (x / d)) := by
  have nz : d ≠ 0 := Nat.ne_of_gt positive
  simp [execNode, binopStep, getV, hl, hr, evalBinop, expect_int, hx, hd,
    isBoolTy, expectInt, rejectPoison, intBin, nz, liftOp, ofR, bindResults,
    writeInt, next, pure, ok_bind]

theorem assert_true_step (m : Module) (k : Core) (condition : Nat) (kind : AssertKind)
    (h : lookupEnv k.env condition = some (.bool true)) :
    execNode m k ⟨.assert condition kind, []⟩ = .cont (next k) := by
  simp [execNode, assertStep, getV, h, rejectPoison, assertOn, asBool, ofR, pure, ok_bind]

def target : TargetInfo :=
  ⟨[97,97,114,99,104,54,52,45,97,112,112,108,101,45,100,97,114,119,105,110],8,false,none,2⟩

def blocks (d : Nat) : List Block :=
  [{ id := 0, params := [(0, .int .u64)], body :=
      [⟨.const (.int .u64) (.int 0), [3]⟩,
       ⟨.icmp .uge (.int .u64) 0 3, [4]⟩,
       ⟨.const (.int .u64) (.int 18446744073709551615), [5]⟩,
       ⟨.icmp .ule (.int .u64) 0 5, [6]⟩,
       ⟨.const .bool (.bool false), [7]⟩,
       ⟨.select .bool 4 6 7, [8]⟩,
       ⟨.assume 8, []⟩,
       ⟨.const (.int .u64) (.int d), [10]⟩,
       ⟨.const (.int .u64) (.int 0), [11]⟩,
       ⟨.icmp .eq (.int .u64) 10 11, [9]⟩,
       ⟨.const .bool (.bool false), [12]⟩,
       ⟨.icmp .eq .bool 9 12, [13]⟩,
       ⟨.assert 13 .divByZero, []⟩,
       ⟨.br 1 [], []⟩] },
   { id := 1, params := [], body :=
      [⟨.const (.int .u64) (.int d), [15]⟩,
       ⟨.binop .udiv (.int .u64) 0 15, [14]⟩,
       ⟨.ret [14], []⟩] }]

def module (d : Nat) : Module :=
  { funcTys := [⟨[.int .u64], [.int .u64], false⟩], enums := [],
    functions := [⟨0,0,0,blocks d,[114,97,119,95,109,101,103,97,98,121,116,101,115]⟩],
    target := some target }

def initial (x d depth : Nat) : Core :=
  { fn := (module d).functions[0]'(by simp [module]), sig := (module d).funcTys[0]'(by simp [module]),
    block := (blocks d)[0]'(by simp [blocks]), pc := 0, env := [(0,.int .u64 x)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

/-- The actual guard, assertion and division execute for every in-range input.
    A positive divisor excludes unsigned division by zero. No multiplication,
    signed division or overflow assumption is used. -/
theorem division_correct (x d depth : Nat) (hx : x < 18446744073709551616)
    (positive : 0 < d) (hd : d < 18446744073709551616) :
    runFunction (module d) 0 [.int .u64 x] 17 depth = .ret [.int .u64 (x / d)] := by
  have hxle : x ≤ 18446744073709551615 := by omega
  have nz : d ≠ 0 := Nat.ne_of_gt positive
  have zeroCmp : (d == 0) = false := beq_eq_false_iff_ne.mpr nz
  have zrange : 0 < modulus (IntTy.u64.bits (module d).pointerBits) := by change 0 < 18446744073709551616; decide
  have mrange : 18446744073709551615 < modulus (IntTy.u64.bits (module d).pointerBits) := by change 18446744073709551615 < 18446744073709551616; decide
  have quotient : x / d < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self x d) hx
  let k0 := initial x d depth
  let k1 := writeInt k0 3 .u64 0
  let k2 := writeBool k1 4 true
  let k3 := writeInt k2 5 .u64 18446744073709551615
  let k4 := writeBool k3 6 true
  let k5 := writeBool k4 7 false
  let k6 := writeBool k5 8 true
  let k7 := next k6
  let k8 := writeInt k7 10 .u64 d
  let k9 := writeInt k8 11 .u64 0
  let k10 := writeBool k9 9 false
  let k11 := writeBool k10 12 false
  let k12 := writeBool k11 13 true
  let k13 := next k12
  let k14 : Core := {k13 with block := (blocks d)[1]'(by simp [blocks]), pc := 0}
  let k15 := writeInt k14 15 .u64 d
  let k16 := writeInt k15 14 .u64 (x / d)
  have s1 : Step (module d) k0 (.cont k1) := at_node _ _ _ _ (by rfl) (const_int_step _ _ _ _ _ zrange)
  have s2 : Step (module d) k1 (.cont k2) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, Nat.zero_le, decide_true] using
      icmp_int_step (module d) k1 4 0 3 .uge .u64 x 0 (by rfl) (by rfl) hx zrange
  have s3 : Step (module d) k2 (.cont k3) := at_node _ _ _ _ (by rfl) (const_int_step _ _ _ _ _ mrange)
  have s4 : Step (module d) k3 (.cont k4) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, hxle, decide_true] using
      icmp_int_step (module d) k3 6 0 5 .ule .u64 x 18446744073709551615 (by rfl) (by rfl) hx mrange
  have s5 : Step (module d) k4 (.cont k5) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.const_step _ _ _ _)
  have s6 : Step (module d) k5 (.cont k6) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.select_step _ _ 8 4 6 7 true true false (by rfl) (by rfl) (by rfl))
  have s7 : Step (module d) k6 (.cont k7) := at_node _ _ _ _ (by rfl) (assume_true_step _ _ _ (by rfl))
  have s8 : Step (module d) k7 (.cont k8) := at_node _ _ _ _ (by rfl) (const_int_step _ _ _ _ _ hd)
  have s9 : Step (module d) k8 (.cont k9) := at_node _ _ _ _ (by rfl) (const_int_step _ _ _ _ _ zrange)
  have s10 : Step (module d) k9 (.cont k10) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, zeroCmp] using
      icmp_int_step (module d) k9 9 10 11 .eq .u64 d 0 (by rfl) (by rfl) hd zrange
  have s11 : Step (module d) k10 (.cont k11) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.const_step _ _ _ _)
  have s12 : Step (module d) k11 (.cont k12) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWPMemory.eq_step _ _ 13 9 12 false false (by rfl) (by rfl))
  have s13 : Step (module d) k12 (.cont k13) := at_node _ _ _ _ (by rfl) (assert_true_step _ _ _ _ (by rfl))
  have s14 : Step (module d) k13 (.cont k14) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.branch_step _ _ _ 1 [] [] (by rfl) (by rfl))
  have s15 : Step (module d) k14 (.cont k15) := at_node _ _ _ _ (by rfl) (const_int_step _ _ _ _ _ hd)
  have s16 : Step (module d) k15 (.cont k16) := at_node _ _ _ _ (by rfl)
    (udiv_step _ _ 14 0 15 .u64 x d (by rfl) (by rfl) hx hd positive)
  have sr : Step (module d) k16 (.done (.ret [.int .u64 (x / d)])) := at_node _ _ _ _ (by rfl)
    (return_int_step _ _ 14 .u64 (x / d) (by rfl) quotient (by rfl) (by rfl))
  have ex : Exec (module d) 17 k0 (.ret [.int .u64 (x / d)]) :=
    Exec.step 16 k0 k1 _ s1 (Exec.step 15 k1 k2 _ s2 (Exec.step 14 k2 k3 _ s3
    (Exec.step 13 k3 k4 _ s4 (Exec.step 12 k4 k5 _ s5 (Exec.step 11 k5 k6 _ s6
    (Exec.step 10 k6 k7 _ s7 (Exec.step 9 k7 k8 _ s8 (Exec.step 8 k8 k9 _ s9
    (Exec.step 7 k9 k10 _ s10 (Exec.step 6 k10 k11 _ s11 (Exec.step 5 k11 k12 _ s12
    (Exec.step 4 k12 k13 _ s13 (Exec.step 3 k13 k14 _ s14 (Exec.step 2 k14 k15 _ s15
    (Exec.step 1 k15 k16 _ s16 (Exec.done 0 k16 _ sr))))))))))))))))
  have exty : expectTy 64 (.int .u64 x) (.int .u64) = .ok () := expect_int 64 .u64 x hx
  have start_ok : start (module d) 0 [.int .u64 x] depth = .ok k0 := by
    simp [start, module, blocks, initial, k0, target, Module.executableTarget,
      Module.pointerBits, checkSig, exty, bindParams, findBlock, nth?,
      rejectPoison, Val.ty, Ty.beq, IntTy.code, pure, ok_bind]
  simpa only [runFunction, start_ok] using run_complete (module d) 17 k0 _ ex

theorem raw_megabytes_correct (x depth : Nat) (hx : x < 18446744073709551616) :
    runFunction (module 1048576) 0 [.int .u64 x] 17 depth =
      .ret [.int .u64 (x / 1048576)] :=
  division_correct x 1048576 depth hx (by decide) (by decide)

end SemRUnsignedDivision
