/-
  The actual retained clamp instruction sequences, in canonical SemR.
  The binary regression binds these quotations to the unmodified native IR.
  Source-to-IR translation is a separate trusted compiler boundary.
-/
import SemRUnsignedSelect

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SemRUnsignedClamp
open SemR SemRUnsignedSelect SemRBooleanWP

def target : TargetInfo := ⟨[97,97,114,99,104,54,52,45,97,112,112,108,101,45,100,97,114,119,105,110],8,false,none,2⟩

def widthBlocks : List Block :=
  [{ id := 0, params := [(0, .int .u32)], body :=
      [⟨.alloca (.int .u32) none none, [3]⟩,
       ⟨.const (.int .u32) (.int 0), [4]⟩,
       ⟨.icmp .uge (.int .u32) 0 4, [5]⟩,
       ⟨.const (.int .u32) (.int 4294967295), [6]⟩,
       ⟨.icmp .ule (.int .u32) 0 6, [7]⟩,
       ⟨.const .bool (.bool false), [8]⟩,
       ⟨.select .bool 5 7 8, [9]⟩,
       ⟨.assume 9, []⟩,
       ⟨.const (.int .u32) (.int 64), [11]⟩,
       ⟨.icmp .ugt (.int .u32) 0 11, [10]⟩,
       ⟨.const .bool (.bool false), [12]⟩,
       ⟨.icmp .eq .bool 10 12, [13]⟩,
       ⟨.condBr 13 2 [] 1 [], []⟩] },
   { id := 1, params := [], body :=
      [⟨.const (.int .u32) (.int 64), [14]⟩,
       ⟨.copy (.int .u32) 14, [15]⟩,
       ⟨.store (.int .u32) 3 15 false none, []⟩,
       ⟨.br 3 [], []⟩] },
   { id := 2, params := [], body :=
      [⟨.copy (.int .u32) 0, [16]⟩,
       ⟨.store (.int .u32) 3 16 false none, []⟩,
       ⟨.br 3 [], []⟩] },
   { id := 3, params := [], body :=
      [⟨.load (.int .u32) 3 false none, [17]⟩,
       ⟨.ret [17], []⟩] }]

def widthModule : Module :=
  { funcTys := [⟨[.int .u32], [.int .u32], false⟩], enums := [],
    functions := [⟨0,0,0,widthBlocks,[99,108,97,109,112,95,119,105,100,116,104]⟩],
    target := some target }


def maximumBlocks : List Block :=
  [{id:=0,params:=[(0,(.int .u64)),(1,(.int .u64))],body:=[
      ⟨.alloca (.int .u64) none none, [4]⟩,
      ⟨.const (.int .u64) (.int 0), [5]⟩,
      ⟨.icmp .uge (.int .u64) 0 5, [6]⟩,
      ⟨.const (.int .u64) (.int 18446744073709551615), [7]⟩,
      ⟨.icmp .ule (.int .u64) 0 7, [8]⟩,
      ⟨.const .bool (.bool false), [9]⟩,
      ⟨.select .bool 6 8 9, [10]⟩,
      ⟨.assume 10, []⟩,
      ⟨.const (.int .u64) (.int 0), [11]⟩,
      ⟨.icmp .uge (.int .u64) 1 11, [12]⟩,
      ⟨.const (.int .u64) (.int 18446744073709551615), [13]⟩,
      ⟨.icmp .ule (.int .u64) 1 13, [14]⟩,
      ⟨.const .bool (.bool false), [15]⟩,
      ⟨.select .bool 12 14 15, [16]⟩,
      ⟨.assume 16, []⟩,
      ⟨.icmp .ugt (.int .u64) 0 1, [17]⟩,
      ⟨.const .bool (.bool false), [18]⟩,
      ⟨.icmp .eq .bool 17 18, [19]⟩,
      ⟨.condBr 19 2 [] 1 [], []⟩]},
   {id:=1,params:=[],body:=[
      ⟨.copy (.int .u64) 1, [20]⟩,
      ⟨.store (.int .u64) 4 20 false none, []⟩,
      ⟨.br 3 [], []⟩]},
   {id:=2,params:=[],body:=[
      ⟨.copy (.int .u64) 0, [21]⟩,
      ⟨.store (.int .u64) 4 21 false none, []⟩,
      ⟨.br 3 [], []⟩]},
   {id:=3,params:=[],body:=[
      ⟨.load (.int .u64) 4 false none, [22]⟩,
      ⟨.ret [22], []⟩]}]

def maximumModule : Module :=
  {funcTys := [⟨[.int .u64,.int .u64],[.int .u64],false⟩], enums:=[],
   functions := [⟨0,0,0,maximumBlocks,[99,108,97,109,112,95,116,111,95,109,97,120]⟩],target:=some target}

def widthInitial (w depth : Nat) : Core :=
  { fn := widthModule.functions[0], sig := widthModule.funcTys[0],
    block := widthBlocks[0], pc := 0, env := [(0,.int .u32 w)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

theorem width_correct (w depth : Nat) (hw : w < 4294967296) :
    runFunction widthModule 0 [.int .u32 w] 19 depth = .ret [.int .u32 (min w 64)] := by
  have hwle : w ≤ 4294967295 := by omega
  let c := icmpR .ugt 32 w 64
  let slot : Alloc := {base:=1024,size:=4,align:=4,live:=true,data:=[]}
  let k0 := widthInitial w depth
  let k1 : Core := { next k0 with env := (3,.ptr 0 0)::k0.env, mem := {allocs:=[slot],nextAddr:=1028} }
  let k2 := writeInt k1 4 .u32 0
  let k3 := writeBool k2 5 true
  let k4 := writeInt k3 6 .u32 4294967295
  let k5 := writeBool k4 7 true
  let k6 := writeBool k5 8 false
  let k7 := writeBool k6 9 true
  let k8 := next k7
  let k9 := writeInt k8 11 .u32 64
  let k10 := writeBool k9 10 c
  let k11 := writeBool k10 12 false
  let k12 := writeBool k11 13 (!c)
  let k13 : Core := { k12 with block := if c then widthBlocks[1] else widthBlocks[2], pc := 0 }
  have s1 : Step widthModule k0 (.cont k1) := at_node _ _ _ _ (by rfl) (by
    simp [execNode, allocaStep, getCount, layoutOf, allocSize, checkAlign, isPow2,
      allocAt, k1, k0, widthInitial, widthModule, next, target, Module.pointerBits,
      Mem.empty, slot, addrSpace, alignUp, IntTy.bytes, bindResults, ofR, pure, ok_bind])
  have s2 : Step widthModule k1 (.cont k2) := at_node _ _ _ _ (by rfl)
    (const_int_step _ _ _ _ _ (by decide))
  have s3 : Step widthModule k2 (.cont k3) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, Nat.zero_le, decide_true] using
      icmp_int_step widthModule k2 5 0 4 .uge .u32 w 0 (by rfl) (by rfl) hw (by decide)
  have s4 : Step widthModule k3 (.cont k4) := at_node _ _ _ _ (by rfl)
    (const_int_step _ _ _ _ _ (by decide))
  have s5 : Step widthModule k4 (.cont k5) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, hwle, decide_true] using
      icmp_int_step widthModule k4 7 0 6 .ule .u32 w 4294967295 (by rfl) (by rfl) hw (by decide)
  have s6 : Step widthModule k5 (.cont k6) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.const_step _ _ _ _)
  have s7 : Step widthModule k6 (.cont k7) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.select_step _ _ 9 5 7 8 true true false (by rfl) (by rfl) (by rfl))
  have s8 : Step widthModule k7 (.cont k8) := at_node _ _ _ _ (by rfl)
    (assume_true_step _ _ _ (by rfl))
  have s9 : Step widthModule k8 (.cont k9) := at_node _ _ _ _ (by rfl)
    (const_int_step _ _ _ _ _ (by decide))
  have s10 : Step widthModule k9 (.cont k10) := at_node _ _ _ _ (by rfl)
    (icmp_int_step _ _ 10 0 11 .ugt .u32 w 64 (by rfl) (by rfl) hw (by decide))
  have s11 : Step widthModule k10 (.cont k11) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.const_step _ _ _ _)
  have s12 : Step widthModule k11 (.cont k12) := by
    apply at_node _ _ _ _ (by rfl)
    have e := SemRBooleanWPMemory.eq_step widthModule k11 13 10 12 c false (by rfl) (by rfl)
    cases hc : c <;> simpa only [k12, SemRBooleanWPMemory.eqNode, hc, Bool.not_false, Bool.not_true, Bool.false_beq, Bool.true_beq] using e
  have hj : jump widthModule.pointerBits k12 (if !c then 2 else 1) [] = .ok k13 := by
    cases hc : c <;> simp only [k13, hc, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false] <;> rfl
  have s13 : Step widthModule k12 (.cont k13) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.conditional_step _ _ _ 13 2 1 [] [] (!c) [] (by rfl) (by simp only [ite_self]; rfl) hj)
  have ew : expectTy 64 (.int .u32 w) (.int .u32) = .ok () := expect_int 64 .u32 w hw
  have hs : start widthModule 0 [.int .u32 w] depth = .ok k0 := by
    simp [start, widthModule, widthBlocks, widthInitial, k0, target, Module.executableTarget,
      Module.pointerBits, checkSig, ew, bindParams, findBlock, nth?, rejectPoison, Val.ty, Ty.beq, IntTy.code, pure, ok_bind]
  by_cases h : w ≤ 64
  · have hc : c = false := by simp [c, icmpR, Nat.not_lt.mpr h]
    let k14 := writeInt k13 16 .u32 w
    have s14 : Step widthModule k13 (.cont k14) := at_node _ _ _ _ (by first | (simp only [k13, hc, writeInt, storedInt, next]; rfl) | rfl) (copy_int_step _ _ 16 0 .u32 w (by rfl) hw)
    let k15 := storedInt k14 0 0 slot .u32 w 64
    have s15 : Step widthModule k14 (.cont k15) := at_node _ _ _ _ (by first | (simp only [k13, hc, k14, writeInt, storedInt, next]; rfl) | rfl) (store_int_step _ _ 3 16 0 0 slot .u32 w (by rfl) (by rfl) hw (by rfl) (by change accessAt {allocs:=[slot],nextAddr:=1028} "Store" 0 0 4 4 = .ok slot; simp [accessAt,accessAlloc,slot,nth?,addrSpace]))
    let k16 : Core := { k15 with block := widthBlocks[3], pc := 0 }
    have s16 : Step widthModule k15 (.cont k16) := at_node _ _ _ _ (by first | (simp only [k13, hc, k14, k15, writeInt, storedInt, next]; rfl) | rfl) (SemRBooleanWP.branch_step _ _ _ 3 [] [] (by rfl) (by rfl))
    let k17 := writeInt k16 17 .u32 w
    have s17 : Step widthModule k16 (.cont k17) := at_node _ _ _ _ (by rfl) (load_stored_int_step _ _ 17 3 0 0 {slot with data:=writeBytes [] 0 (leBytes 4 w)} [] .u32 w (by rfl) hw (by rfl) (by rfl) (by change accessAt {allocs:=[{slot with data:=writeBytes [] 0 (leBytes 4 w)}],nextAddr:=1028} "Load" 0 0 4 4 = .ok {slot with data:=writeBytes [] 0 (leBytes 4 w)}; simp [accessAt,accessAlloc,slot,nth?,addrSpace]) (Or.inr rfl))
    have sr : Step widthModule k17 (.done (.ret [.int .u32 w])) := at_node _ _ _ _ (by rfl) (return_int_step _ _ 17 .u32 w (by rfl) hw (by rfl) (by rfl))
    have he : Exec widthModule 19 k0 (.ret [.int .u32 w]) := Exec.step 18 k0 k1 (.ret [.int .u32 w]) s1 (Exec.step 17 k1 k2 (.ret [.int .u32 w]) s2 (Exec.step 16 k2 k3 (.ret [.int .u32 w]) s3 (Exec.step 15 k3 k4 (.ret [.int .u32 w]) s4 (Exec.step 14 k4 k5 (.ret [.int .u32 w]) s5 (Exec.step 13 k5 k6 (.ret [.int .u32 w]) s6 (Exec.step 12 k6 k7 (.ret [.int .u32 w]) s7 (Exec.step 11 k7 k8 (.ret [.int .u32 w]) s8 (Exec.step 10 k8 k9 (.ret [.int .u32 w]) s9 (Exec.step 9 k9 k10 (.ret [.int .u32 w]) s10 (Exec.step 8 k10 k11 (.ret [.int .u32 w]) s11 (Exec.step 7 k11 k12 (.ret [.int .u32 w]) s12 (Exec.step 6 k12 k13 (.ret [.int .u32 w]) s13 (Exec.step 5 k13 k14 (.ret [.int .u32 w]) s14 (Exec.step 4 k14 k15 (.ret [.int .u32 w]) s15 (Exec.step 3 k15 k16 (.ret [.int .u32 w]) s16 (Exec.step 2 k16 k17 (.ret [.int .u32 w]) s17 (Exec.done 1 k17 (.ret [.int .u32 w]) sr)))))))))))))))))
    simpa only [runFunction, hs, Nat.min_eq_left h] using run_complete widthModule 19 k0 (.ret [.int .u32 w]) he
  · have hc : c = true := by simp [c, icmpR, Nat.lt_of_not_ge h]
    let k14 := writeInt k13 14 .u32 64
    have s14 : Step widthModule k13 (.cont k14) := at_node _ _ _ _ (by first | (simp only [k13, hc, writeInt, storedInt, next]; rfl) | rfl) (const_int_step _ _ _ _ _ (by decide))
    let k15 := writeInt k14 15 .u32 64
    have s15 : Step widthModule k14 (.cont k15) := at_node _ _ _ _ (by first | (simp only [k13, hc, k14, writeInt, storedInt, next]; rfl) | rfl) (copy_int_step _ _ 15 14 .u32 64 (by rfl) (by decide))
    let k16 := storedInt k15 0 0 slot .u32 64 64
    have s16 : Step widthModule k15 (.cont k16) := at_node _ _ _ _ (by first | (simp only [k13, hc, k14, k15, writeInt, storedInt, next]; rfl) | rfl) (store_int_step _ _ 3 15 0 0 slot .u32 64 (by rfl) (by rfl) (by decide) (by rfl) (by change accessAt {allocs:=[slot],nextAddr:=1028} "Store" 0 0 4 4 = .ok slot; simp [accessAt,accessAlloc,slot,nth?,addrSpace]))
    let k17 : Core := { k16 with block := widthBlocks[3], pc := 0 }
    have s17 : Step widthModule k16 (.cont k17) := at_node _ _ _ _ (by first | (simp only [k13, hc, k14, k15, k16, writeInt, storedInt, next]; rfl) | rfl) (SemRBooleanWP.branch_step _ _ _ 3 [] [] (by rfl) (by rfl))
    let k18 := writeInt k17 17 .u32 64
    have s18 : Step widthModule k17 (.cont k18) := at_node _ _ _ _ (by rfl) (load_stored_int_step _ _ 17 3 0 0 {slot with data:=writeBytes [] 0 (leBytes 4 64)} [] .u32 64 (by rfl) (by decide) (by rfl) (by rfl) (by change accessAt {allocs:=[{slot with data:=writeBytes [] 0 (leBytes 4 64)}],nextAddr:=1028} "Load" 0 0 4 4 = .ok {slot with data:=writeBytes [] 0 (leBytes 4 64)}; simp [accessAt,accessAlloc,slot,nth?,addrSpace]) (Or.inr rfl))
    have sr : Step widthModule k18 (.done (.ret [.int .u32 64])) := at_node _ _ _ _ (by rfl) (return_int_step _ _ 17 .u32 64 (by rfl) (by decide) (by rfl) (by rfl))
    have he : Exec widthModule 19 k0 (.ret [.int .u32 64]) := Exec.step 18 k0 k1 (.ret [.int .u32 64]) s1 (Exec.step 17 k1 k2 (.ret [.int .u32 64]) s2 (Exec.step 16 k2 k3 (.ret [.int .u32 64]) s3 (Exec.step 15 k3 k4 (.ret [.int .u32 64]) s4 (Exec.step 14 k4 k5 (.ret [.int .u32 64]) s5 (Exec.step 13 k5 k6 (.ret [.int .u32 64]) s6 (Exec.step 12 k6 k7 (.ret [.int .u32 64]) s7 (Exec.step 11 k7 k8 (.ret [.int .u32 64]) s8 (Exec.step 10 k8 k9 (.ret [.int .u32 64]) s9 (Exec.step 9 k9 k10 (.ret [.int .u32 64]) s10 (Exec.step 8 k10 k11 (.ret [.int .u32 64]) s11 (Exec.step 7 k11 k12 (.ret [.int .u32 64]) s12 (Exec.step 6 k12 k13 (.ret [.int .u32 64]) s13 (Exec.step 5 k13 k14 (.ret [.int .u32 64]) s14 (Exec.step 4 k14 k15 (.ret [.int .u32 64]) s15 (Exec.step 3 k15 k16 (.ret [.int .u32 64]) s16 (Exec.step 2 k16 k17 (.ret [.int .u32 64]) s17 (Exec.step 1 k17 k18 (.ret [.int .u32 64]) s18 (Exec.done 0 k18 (.ret [.int .u32 64]) sr))))))))))))))))))
    simpa only [runFunction, hs, Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using run_complete widthModule 19 k0 (.ret [.int .u32 64]) he


def maximumInitial (n maximum depth : Nat) : Core :=
  { fn := maximumModule.functions[0], sig := maximumModule.funcTys[0],
    block := maximumBlocks[0], pc := 0,
    env := [(1,.int .u64 maximum),(0,.int .u64 n)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

theorem maximum_correct (n maximum depth : Nat)
    (hn : n < 18446744073709551616) (hb : maximum < 18446744073709551616) :
    runFunction maximumModule 0 [.int .u64 n,.int .u64 maximum] 24 depth =
      .ret [.int .u64 (min n maximum)] := by
  have hnle : n ≤ 18446744073709551615 := by omega
  have hble : maximum ≤ 18446744073709551615 := by omega
  let c := icmpR .ugt 64 n maximum
  let slot : Alloc := {base:=1024,size:=8,align:=8,live:=true,data:=[]}
  let k0 := maximumInitial n maximum depth
  let k1 : Core := {next k0 with env := (4,.ptr 0 0)::k0.env, mem := {allocs:=[slot],nextAddr:=1032}}
  let k2 := writeInt k1 5 .u64 0
  let k3 := writeBool k2 6 true
  let k4 := writeInt k3 7 .u64 18446744073709551615
  let k5 := writeBool k4 8 true
  let k6 := writeBool k5 9 false
  let k7 := writeBool k6 10 true
  let k8 := next k7
  let k9 := writeInt k8 11 .u64 0
  let k10 := writeBool k9 12 true
  let k11 := writeInt k10 13 .u64 18446744073709551615
  let k12 := writeBool k11 14 true
  let k13 := writeBool k12 15 false
  let k14 := writeBool k13 16 true
  let k15 := next k14
  let k16 := writeBool k15 17 c
  let k17 := writeBool k16 18 false
  let k18 := writeBool k17 19 (!c)
  let k19 : Core := {k18 with block:=if c then maximumBlocks[1] else maximumBlocks[2],pc:=0}
  have s1 : Step maximumModule k0 (.cont k1) := at_node _ _ _ _ (by rfl) (by
    simp [execNode, allocaStep, getCount, layoutOf, allocSize, checkAlign, isPow2,
      allocAt, k1, k0, maximumInitial, maximumModule, next, target, Module.pointerBits,
      Mem.empty, slot, addrSpace, alignUp, IntTy.bytes, bindResults, ofR, pure, ok_bind])
  have s2 : Step maximumModule k1 (.cont k2) := at_node _ _ _ _ (by rfl) (const_int_step _ _ 5 .u64 0 (by decide))
  have s4 : Step maximumModule k3 (.cont k4) := at_node _ _ _ _ (by rfl) (const_int_step _ _ 7 .u64 18446744073709551615 (by decide))
  have s9 : Step maximumModule k8 (.cont k9) := at_node _ _ _ _ (by rfl) (const_int_step _ _ 11 .u64 0 (by decide))
  have s11 : Step maximumModule k10 (.cont k11) := at_node _ _ _ _ (by rfl) (const_int_step _ _ 13 .u64 18446744073709551615 (by decide))
  have s3 : Step maximumModule k2 (.cont k3) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, Nat.zero_le, decide_true] using
      icmp_int_step maximumModule k2 6 0 5 .uge .u64 n 0 (by rfl) (by rfl) hn (by decide)
  have s5 : Step maximumModule k4 (.cont k5) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, hnle, decide_true] using
      icmp_int_step maximumModule k4 8 0 7 .ule .u64 n 18446744073709551615 (by rfl) (by rfl) hn (by decide)
  have s10 : Step maximumModule k9 (.cont k10) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, Nat.zero_le, decide_true] using
      icmp_int_step maximumModule k9 12 1 11 .uge .u64 maximum 0 (by rfl) (by rfl) hb (by decide)
  have s12 : Step maximumModule k11 (.cont k12) := by
    apply at_node _ _ _ _ (by rfl)
    simpa only [icmpR, hble, decide_true] using
      icmp_int_step maximumModule k11 14 1 13 .ule .u64 maximum 18446744073709551615 (by rfl) (by rfl) hb (by decide)
  have s6 : Step maximumModule k5 (.cont k6) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.const_step _ _ 9 false)
  have s13 : Step maximumModule k12 (.cont k13) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.const_step _ _ 15 false)
  have s17 : Step maximumModule k16 (.cont k17) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.const_step _ _ 18 false)
  have s7 : Step maximumModule k6 (.cont k7) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.select_step _ _ 10 6 8 9 true true false (by rfl) (by rfl) (by rfl))
  have s14 : Step maximumModule k13 (.cont k14) := at_node _ _ _ _ (by rfl) (SemRBooleanWP.select_step _ _ 16 12 14 15 true true false (by rfl) (by rfl) (by rfl))
  have s8 : Step maximumModule k7 (.cont k8) := at_node _ _ _ _ (by rfl) (assume_true_step _ _ 10 (by rfl))
  have s15 : Step maximumModule k14 (.cont k15) := at_node _ _ _ _ (by rfl) (assume_true_step _ _ 16 (by rfl))
  have s16 : Step maximumModule k15 (.cont k16) := at_node _ _ _ _ (by rfl)
    (icmp_int_step _ _ 17 0 1 .ugt .u64 n maximum (by rfl) (by rfl) hn hb)
  have s18 : Step maximumModule k17 (.cont k18) := by
    apply at_node _ _ _ _ (by rfl)
    have e := SemRBooleanWPMemory.eq_step maximumModule k17 19 17 18 c false (by rfl) (by rfl)
    cases hc : c <;> simpa only [k18, SemRBooleanWPMemory.eqNode, hc, Bool.not_false, Bool.not_true, Bool.false_beq, Bool.true_beq] using e
  have hj : jump maximumModule.pointerBits k18 (if !c then 2 else 1) [] = .ok k19 := by
    cases hc : c <;> simp only [k19,hc,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false] <;> rfl
  have s19 : Step maximumModule k18 (.cont k19) := at_node _ _ _ _ (by rfl)
    (SemRBooleanWP.conditional_step _ _ _ 19 2 1 [] [] (!c) [] (by rfl) (by simp only [ite_self]; rfl) hj)
  have en : expectTy 64 (.int .u64 n) (.int .u64) = .ok () := expect_int 64 .u64 n hn
  have eb : expectTy 64 (.int .u64 maximum) (.int .u64) = .ok () := expect_int 64 .u64 maximum hb
  have hs : start maximumModule 0 [.int .u64 n,.int .u64 maximum] depth = .ok k0 := by
    simp [start,maximumModule,maximumBlocks,maximumInitial,k0,target,Module.executableTarget,
      Module.pointerBits,checkSig,en,eb,bindParams,findBlock,nth?,rejectPoison,Val.ty,Ty.beq,IntTy.code,pure,ok_bind]
  by_cases h : n ≤ maximum
  · have hc : c = false := by simp [c,icmpR,Nat.not_lt.mpr h]
    let k20 := writeInt k19 21 .u64 n
    let k21 := storedInt k20 0 0 slot .u64 n 64
    let k22 : Core := {k21 with block:=maximumBlocks[3],pc:=0}
    let k23 := writeInt k22 22 .u64 n
    have s20 : Step maximumModule k19 (.cont k20) := at_node _ _ _ _ (by first | (simp only [k19, hc, writeInt, storedInt, next]; rfl) | rfl) (copy_int_step _ _ 21 0 .u64 n (by rfl) hn)
    have s21 : Step maximumModule k20 (.cont k21) := at_node _ _ _ _ (by first | (simp only [k19, hc, k20, writeInt, storedInt, next]; rfl) | rfl) (store_int_step _ _ 4 21 0 0 slot .u64 n (by rfl) (by rfl) hn (by rfl) (by change accessAt {allocs:=[slot],nextAddr:=1032} "Store" 0 0 8 8 = .ok slot; simp [accessAt,accessAlloc,slot,nth?,addrSpace]))
    have s22 : Step maximumModule k21 (.cont k22) := at_node _ _ _ _ (by first | (simp only [k19, hc, k20, k21, writeInt, storedInt, next]; rfl) | rfl) (SemRBooleanWP.branch_step _ _ _ 3 [] [] (by rfl) (by rfl))
    have s23 : Step maximumModule k22 (.cont k23) := at_node _ _ _ _ (by rfl) (load_stored_int_step _ _ 22 4 0 0 {slot with data:=writeBytes [] 0 (leBytes 8 n)} [] .u64 n (by rfl) hn (by rfl) (by rfl) (by change accessAt {allocs:=[{slot with data:=writeBytes [] 0 (leBytes 8 n)}],nextAddr:=1032} "Load" 0 0 8 8 = .ok {slot with data:=writeBytes [] 0 (leBytes 8 n)}; simp [accessAt,accessAlloc,slot,nth?,addrSpace]) (Or.inr rfl))
    have sr : Step maximumModule k23 (.done (.ret [.int .u64 n])) := at_node _ _ _ _ (by rfl) (return_int_step _ _ 22 .u64 n (by rfl) hn (by rfl) (by rfl))
    have he : Exec maximumModule 24 k0 (.ret [.int .u64 n]) := Exec.step 23 k0 k1 (.ret [.int .u64 n]) s1 (Exec.step 22 k1 k2 (.ret [.int .u64 n]) s2 (Exec.step 21 k2 k3 (.ret [.int .u64 n]) s3 (Exec.step 20 k3 k4 (.ret [.int .u64 n]) s4 (Exec.step 19 k4 k5 (.ret [.int .u64 n]) s5 (Exec.step 18 k5 k6 (.ret [.int .u64 n]) s6 (Exec.step 17 k6 k7 (.ret [.int .u64 n]) s7 (Exec.step 16 k7 k8 (.ret [.int .u64 n]) s8 (Exec.step 15 k8 k9 (.ret [.int .u64 n]) s9 (Exec.step 14 k9 k10 (.ret [.int .u64 n]) s10 (Exec.step 13 k10 k11 (.ret [.int .u64 n]) s11 (Exec.step 12 k11 k12 (.ret [.int .u64 n]) s12 (Exec.step 11 k12 k13 (.ret [.int .u64 n]) s13 (Exec.step 10 k13 k14 (.ret [.int .u64 n]) s14 (Exec.step 9 k14 k15 (.ret [.int .u64 n]) s15 (Exec.step 8 k15 k16 (.ret [.int .u64 n]) s16 (Exec.step 7 k16 k17 (.ret [.int .u64 n]) s17 (Exec.step 6 k17 k18 (.ret [.int .u64 n]) s18 (Exec.step 5 k18 k19 (.ret [.int .u64 n]) s19 (Exec.step 4 k19 k20 (.ret [.int .u64 n]) s20 (Exec.step 3 k20 k21 (.ret [.int .u64 n]) s21 (Exec.step 2 k21 k22 (.ret [.int .u64 n]) s22 (Exec.step 1 k22 k23 (.ret [.int .u64 n]) s23 (Exec.done 0 k23 (.ret [.int .u64 n]) sr)))))))))))))))))))))))
    simpa only [runFunction,hs,Nat.min_eq_left h] using run_complete maximumModule 24 k0 (.ret [.int .u64 n]) he
  · have hc : c = true := by simp [c,icmpR,Nat.lt_of_not_ge h]
    let k20 := writeInt k19 20 .u64 maximum
    let k21 := storedInt k20 0 0 slot .u64 maximum 64
    let k22 : Core := {k21 with block:=maximumBlocks[3],pc:=0}
    let k23 := writeInt k22 22 .u64 maximum
    have s20 : Step maximumModule k19 (.cont k20) := at_node _ _ _ _ (by first | (simp only [k19, hc, writeInt, storedInt, next]; rfl) | rfl) (copy_int_step _ _ 20 1 .u64 maximum (by rfl) hb)
    have s21 : Step maximumModule k20 (.cont k21) := at_node _ _ _ _ (by first | (simp only [k19, hc, k20, writeInt, storedInt, next]; rfl) | rfl) (store_int_step _ _ 4 20 0 0 slot .u64 maximum (by rfl) (by rfl) hb (by rfl) (by change accessAt {allocs:=[slot],nextAddr:=1032} "Store" 0 0 8 8 = .ok slot; simp [accessAt,accessAlloc,slot,nth?,addrSpace]))
    have s22 : Step maximumModule k21 (.cont k22) := at_node _ _ _ _ (by first | (simp only [k19, hc, k20, k21, writeInt, storedInt, next]; rfl) | rfl) (SemRBooleanWP.branch_step _ _ _ 3 [] [] (by rfl) (by rfl))
    have s23 : Step maximumModule k22 (.cont k23) := at_node _ _ _ _ (by rfl) (load_stored_int_step _ _ 22 4 0 0 {slot with data:=writeBytes [] 0 (leBytes 8 maximum)} [] .u64 maximum (by rfl) hb (by rfl) (by rfl) (by change accessAt {allocs:=[{slot with data:=writeBytes [] 0 (leBytes 8 maximum)}],nextAddr:=1032} "Load" 0 0 8 8 = .ok {slot with data:=writeBytes [] 0 (leBytes 8 maximum)}; simp [accessAt,accessAlloc,slot,nth?,addrSpace]) (Or.inr rfl))
    have sr : Step maximumModule k23 (.done (.ret [.int .u64 maximum])) := at_node _ _ _ _ (by rfl) (return_int_step _ _ 22 .u64 maximum (by rfl) hb (by rfl) (by rfl))
    have he : Exec maximumModule 24 k0 (.ret [.int .u64 maximum]) := Exec.step 23 k0 k1 (.ret [.int .u64 maximum]) s1 (Exec.step 22 k1 k2 (.ret [.int .u64 maximum]) s2 (Exec.step 21 k2 k3 (.ret [.int .u64 maximum]) s3 (Exec.step 20 k3 k4 (.ret [.int .u64 maximum]) s4 (Exec.step 19 k4 k5 (.ret [.int .u64 maximum]) s5 (Exec.step 18 k5 k6 (.ret [.int .u64 maximum]) s6 (Exec.step 17 k6 k7 (.ret [.int .u64 maximum]) s7 (Exec.step 16 k7 k8 (.ret [.int .u64 maximum]) s8 (Exec.step 15 k8 k9 (.ret [.int .u64 maximum]) s9 (Exec.step 14 k9 k10 (.ret [.int .u64 maximum]) s10 (Exec.step 13 k10 k11 (.ret [.int .u64 maximum]) s11 (Exec.step 12 k11 k12 (.ret [.int .u64 maximum]) s12 (Exec.step 11 k12 k13 (.ret [.int .u64 maximum]) s13 (Exec.step 10 k13 k14 (.ret [.int .u64 maximum]) s14 (Exec.step 9 k14 k15 (.ret [.int .u64 maximum]) s15 (Exec.step 8 k15 k16 (.ret [.int .u64 maximum]) s16 (Exec.step 7 k16 k17 (.ret [.int .u64 maximum]) s17 (Exec.step 6 k17 k18 (.ret [.int .u64 maximum]) s18 (Exec.step 5 k18 k19 (.ret [.int .u64 maximum]) s19 (Exec.step 4 k19 k20 (.ret [.int .u64 maximum]) s20 (Exec.step 3 k20 k21 (.ret [.int .u64 maximum]) s21 (Exec.step 2 k21 k22 (.ret [.int .u64 maximum]) s22 (Exec.step 1 k22 k23 (.ret [.int .u64 maximum]) s23 (Exec.done 0 k23 (.ret [.int .u64 maximum]) sr)))))))))))))))))))))))
    simpa only [runFunction,hs,Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using run_complete maximumModule 24 k0 (.ret [.int .u64 maximum]) he


/-- These statements take the independently supplied original bytes. A proof
    packet cannot choose another input or replace the canonical body question. -/
def DecodesWidth (bytes : List Nat) : Prop := decode bytes = .ok widthModule
def DecodesMaximum (bytes : List Nat) : Prop := decode bytes = .ok maximumModule
def ReturnsWidth (bytes : List Nat) : Prop := ∀ w depth : Nat,
  w < 4294967296 → runBlob bytes 0 [.int .u32 w] 19 depth =
    .ok (.ret [.int .u32 (min w 64)])
def ReturnsMaximum (bytes : List Nat) : Prop := ∀ n bound depth : Nat,
  n < 18446744073709551616 → bound < 18446744073709551616 →
  runBlob bytes 0 [.int .u64 n, .int .u64 bound] 24 depth =
    .ok (.ret [.int .u64 (min n bound)])

end SemRUnsignedClamp
