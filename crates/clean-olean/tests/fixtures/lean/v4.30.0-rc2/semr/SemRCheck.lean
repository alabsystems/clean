/-
  SemRCheck — what Clean's reference entry checks of SemR beyond its own
  theorems: runs and decodes of a real trust-ir artifact, evaluated by the
  kernel (`rfl`; no `native_decide`, no `decide` instance), instances of the
  MiniRust operator lemma, and the statements the negative controls forge.

  `subBlob` is the binary image `trust_ir::binary::serialize_module` writes for
  `fn sub(a: i32, b: i32) -> i32 { a - b }` (trust-ir
  `crates/trust-ir-conformance/tests/lean_exec_differential.rs`, the SemR
  mutation control's module), byte for byte.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import SemRMemory
import ClosureConstruction
import MetadataCheck
import U64AdditionConsumer
import U64ScalarProfile

namespace SemRCheck

/-- Scalar v63 support grants no MakeClosure instruction admission. -/
def ForgedClosureWire : Prop :=
  SemR.inst 63 #[] [70,0,0,0] ≠ .err (.unsupported "inst.make_closure")

theorem forged_closure_wire_fails : ¬ ForgedClosureWire := by
  intro h
  exact h SemR.construction_instruction_v63_refused


open SemR

def subBlob : List Nat :=
  [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 2, 8, 115, 101, 109, 114, 95, 115, 117, 98, 3, 115, 117, 98, 0, 1, 2, 2, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 2, 1, 2, 2, 0, 1, 2, 0, 1, 1, 2, 0, 0, 0, 0, 20, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A run of `sub` on two `i32` residues, the reference interpreter's budgets. -/
def subRun (a b : Nat) : Except DErr Out :=
  runBlob subBlob 0 [.int .i32 a, .int .i32 b] 10000 64

/-- The claim a kernel-evaluated run is checked against: it returns `r`. -/
def RunIs (a b r : Nat) : Prop := subRun a b = .ok (.ret [.int .i32 r])

theorem sub_5_3 : RunIs 5 3 2 := rfl
theorem sub_3_5 : RunIs 3 5 4294967294 := rfl
theorem sub_min_1 : RunIs 2147483648 1 2147483647 := rfl

/- These are the upstream kernel's exact closures for the merged executor.
   Keep them checked beside the independent ReferenceKernel expectations. -/
/-- info: 'SemRCheck.sub_5_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_5_3
/-- info: 'SemRCheck.sub_3_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_3_5
/-- info: 'SemRCheck.sub_min_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_min_1

/-- The decoder's verdict as a `Bool`: the blob decodes. -/
def decodes (bs : List Nat) : Bool :=
  match decode bs with
  | .ok _ => true
  | .error _ => false

theorem blob_decodes : decodes subBlob = true := rfl
theorem bad_magic_refused : decodes (0 :: subBlob.drop 1) = false := rfl
theorem trailing_byte_refused : decodes (subBlob ++ [0]) = false := rfl
theorem truncated_refused : decodes (subBlob.take (subBlob.length - 1)) = false := rfl

/-- The statement a forged `run_sound` would need: every run is out of fuel. -/
def ForgedRunSound : Prop := ∀ (m : Module) (b : Nat) (k : Core), Exec m b k .outOfFuel

/-- A one-node body that returns nothing, in the empty module. -/
def retBlock : Block := { id := 0, params := [], body := [{ inst := .ret [], results := [] }] }

def retCore : Core :=
  { fn := { id := 0, ty := 0, entry := 0, blocks := [retBlock] },
    sig := { params := [], returns := [], vararg := false },
    block := retBlock, pc := 0, env := [], depth := 64, stack := [],
    openFrames := [], nextFrame := 0, mem := Mem.empty }

def emptyModule : Module := { funcTys := [], enums := [], functions := [] }

/-- `Exec` is not vacuous: the one-step run of `retCore` returns, so it is
    not out of fuel, and `ForgedRunSound` is false. -/
theorem forged_run_sound_fails : ¬ ForgedRunSound := by
  intro h
  have e := run_complete emptyModule 1 retCore _ (h emptyModule 1 retCore)
  have r : run emptyModule 1 retCore = .ret [] := rfl
  rw [r] at e
  exact Out.noConfusion e

/-- The statement a forged step relation would need: every state steps to
    "out of fuel". -/
def ForgedStep : Prop := ∀ (m : Module) (k : Core), Step m k (.done .outOfFuel)

/-- `Step` is not vacuous either: `retCore`'s one step returns, and
    `step_sound` ties every step of the relation to the executable's, so
    `ForgedStep` is false. -/
theorem forged_step_fails : ¬ ForgedStep := by
  intro h
  have e := step_sound emptyModule retCore _ (h emptyModule retCore)
  have r : stepCore emptyModule retCore = .done (.ret []) := rfl
  rw [r] at e
  exact StepR.noConfusion e (fun h => Out.noConfusion h)

/-- The operator lemma at `i8`: MiniRust's generated `Div` on `MIN / -1` is
    undefined behaviour, as SemR's `sdiv` says. -/
theorem i8_min_div_neg_one (fuel : Nat) (M : MR_Machine) :
    mrBinOn fuel M .Div true .i8 128 255 = mrUb "overflow in division" := by
  rw [sdiv_mr fuel M .i8 128 255 (by decide) (by decide)]
  rfl

/-- And at `u8`: MiniRust's `Sub` wraps `3 - 5` to `254`. -/
theorem u8_sub_wraps (fuel : Nat) (M : MR_Machine) :
    mrBinOn fuel M .Sub false .u8 3 5 = mrVal false .u8 254 :=
  sub_mr fuel M .u8 3 5 (by decide) (by decide) false

/-- The statement a forged operator layer would need: MiniRust's `i8`
    `MIN / -1` is a value. -/
def ForgedSdiv : Prop :=
  ∃ (fuel : Nat) (M : MR_Machine), mrBinOn fuel M .Div true .i8 128 255 = mrVal true .i8 128

theorem forged_sdiv_fails : ¬ ForgedSdiv := by
  intro ⟨fuel, M, h⟩
  rw [i8_min_div_neg_one] at h
  have h2 := SOut.ok.inj h
  cases h2

/-- The signed bitwise arm: MiniRust's `BitAnd` on the `i8`s `-1` and `-128`
    (residues 255, 128) is `-128`, as SemR's `and` says. -/
theorem i8_and_signed (fuel : Nat) (M : MR_Machine) :
    mrBinOn fuel M .BitAnd true .i8 255 128 = mrVal true .i8 128 :=
  band_mr fuel M .i8 255 128 (by decide) (by decide) true

/-- The statement a forged signed `and` would need: `-1 & -128` is `0`. -/
def ForgedAndSigned : Prop :=
  ∃ (fuel : Nat) (M : MR_Machine), mrBinOn fuel M .BitAnd true .i8 255 128 = mrVal true .i8 0

theorem forged_and_signed_fails : ¬ ForgedAndSigned := by
  intro ⟨fuel, M, h⟩
  rw [i8_and_signed] at h
  have h1 := MR_Value.Int.inj (Prod.mk.inj (SRes.ok.inj (SOut.ok.inj h))).1
  have h2 := readAt_inj true (IntTy.i8.bits 64) 128 0 (by decide) (by decide) h1
  cases h2

/-- `ctpop`: MiniRust's `CountOnes` of the `i8` `-1` counts eight ones (typed
    `u32`), as SemR's `ctpop` says. -/
theorem i8_ctpop_neg_one (fuel : Nat) (M : MR_Machine) :
    mrUnOn fuel M .CountOnes true .i8 255 =
      SOut.ok (SRes.ok (.Int (Int.ofNat 8), .Int (mrIntTy false .u32))) :=
  ctpop_minirust fuel M true .i8 255 (by decide)

/-- The statement a forged bit count would need: seven ones. -/
def ForgedCtpop : Prop :=
  ∃ (fuel : Nat) (M : MR_Machine), mrUnOn fuel M .CountOnes true .i8 255 =
    SOut.ok (SRes.ok (.Int (Int.ofNat 7), .Int (mrIntTy false .u32)))

theorem forged_ctpop_fails : ¬ ForgedCtpop := by
  intro ⟨fuel, M, h⟩
  rw [i8_ctpop_neg_one] at h
  have h1 := Int.ofNat.inj (MR_Value.Int.inj (Prod.mk.inj (SRes.ok.inj (SOut.ok.inj h))).1)
  cases h1

/-- Pointer-sized layout and images use the actual target; fixed u64 stays eight bytes. -/
def UsizeFootprint (bits bytes : Nat) : Prop := scalarLayout bits (.int .usize) = .ok bytes

theorem usize32_footprint : UsizeFootprint 32 4 := rfl
theorem usize64_footprint : UsizeFootprint 64 8 := rfl
theorem u64_on32_footprint : scalarLayout 32 (.int .u64) = .ok 8 := rfl
theorem usize32_image : encodeVal 32 (.int .usize 1144201745) =
    .ok [.init 17, .init 34, .init 51, .init 68] := rfl

def WrongUsize32Image : Prop := encodeVal 32 (.int .usize 1144201745) =
  .ok [.init 17, .init 34, .init 51, .init 68, .init 0, .init 0, .init 0, .init 0]
theorem wrong_usize32_image_refused : ¬ WrongUsize32Image := by
  intro h
  cases h

def WrongUsize32Footprint : Prop := UsizeFootprint 32 8
theorem wrong_usize32_footprint_refused : ¬ WrongUsize32Footprint := by
  intro h
  cases h

/-- Zero-sized operations keep the interpreter's u64 count/index arithmetic. -/
theorem unit_u64_count32 : allocSize 32 0 (some (.int .u64 4294967296)) = .ok 0 := rfl
theorem unit_u64_index32 : gepDelta 32 0 [.int .u64 4294967296] 0 = .ok 0 := rfl

def memoryNode : Node := { inst := .alloca (.int .u8) none none, results := [0] }
def allocationNext (bits size : Nat) : Option Nat :=
  match allocAt bits retCore memoryNode size 1 with
  | .ok next => some next.mem.nextAddr
  | .stop _ => none

theorem last_byte32_allocates : allocationNext 32 4294966272 = some 4294967296 := rfl
theorem past_last_byte32_refuses : allocationNext 32 4294967296 = none := rfl
theorem same_allocation64_fits : allocationNext 64 4294967296 = some 4294968320 := rfl

def WrongAllocation32 : Prop := allocationNext 32 4294967296 = some 4294968320
theorem wrong_allocation32_refused : ¬ WrongAllocation32 := by
  intro h
  cases h

/-- Instantiate the actual target-aware memory law with its real width premise. -/
theorem usize32_store_load (a : Nat) (within : a < modulus 32) :
    readOut retCore memoryNode (.int .usize) true 0
      (readBytes (writeBytes [] 0 (leBytes 4 a)) 0 4) =
        bindResults (next retCore) memoryNode [.int .usize a] :=
  readOut_after_store_target 32 (Or.inl rfl) retCore memoryNode .usize true [] 0 a within
/-! ### The first memory slice (RM4c) -/

/-- `memBlob` is the binary image `trust_ir::binary::serialize_module` writes for
    trust-ir's memory check module (`semr_memory_check_module` in
    `crates/trust-ir-conformance/tests/lean_exec_differential.rs`, whose
    `semr_memory_check_blob_is_pinned` pins the same bytes): `fn 0` stores its
    `i32` argument in a fresh slot and loads it back; `fn 1` loads after the
    slot's `StorageDead`; `fn 2` loads one `i32` past the slot; `fn 3` loads
    an `i32` at address 1025; `fn 4` stores a `u32` and loads its byte 1. -/
def memBlob : List Nat :=
  [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 6, 17, 115, 101, 109, 114, 95, 109, 101, 109, 111, 114, 121, 95, 99, 104, 101, 99, 107, 9, 114, 111, 117, 110, 100, 116, 114, 105, 112, 18, 108, 111, 97, 100, 95, 97, 102, 116, 101, 114, 95, 100, 101, 97, 108, 108, 111, 99, 13, 112, 97, 115, 116, 95, 116, 104, 101, 95, 115, 108, 111, 116, 10, 109, 105, 115, 97, 108, 105, 103, 110, 101, 100, 8, 98, 121, 116, 101, 95, 111, 110, 101, 0, 5, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 7, 1, 5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 0, 1, 0, 2, 4, 8, 2, 0, 0, 1, 1, 0, 0, 0, 0, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 20, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 5, 8, 2, 0, 0, 1, 1, 0, 0, 0, 0, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 39, 1, 0, 0, 0, 0, 0, 6, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 20, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 0, 1, 0, 1, 0, 2, 5, 8, 2, 0, 0, 1, 1, 0, 0, 0, 0, 25, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 2, 1, 1, 2, 0, 1, 3, 0, 0, 0, 0, 6, 2, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 3, 0, 1, 0, 1, 0, 2, 5, 8, 3, 0, 0, 1, 1, 0, 0, 0, 0, 25, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 0, 1, 1, 2, 0, 1, 3, 0, 0, 0, 0, 6, 2, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 4, 0, 1, 0, 1, 0, 7, 6, 8, 7, 0, 0, 1, 1, 0, 0, 0, 0, 7, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 25, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 5, 1, 1, 2, 0, 1, 3, 0, 0, 0, 0, 6, 5, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A run of the memory module's function `f`, the interpreter's budgets. -/
def memRun (f : Nat) (args : List Val) : Except DErr Out :=
  runBlob memBlob f args 10000 64

/-- The claim a kernel-evaluated memory run is checked against. -/
def MemIs (f : Nat) (args : List Val) (o : Out) : Prop := memRun f args = .ok o

set_option maxRecDepth 100000 in
theorem mem_blob_decodes : (match decode memBlob with | .ok _ => true | .error _ => false) = true := rfl
set_option maxRecDepth 100000 in
theorem mem_roundtrip : MemIs 0 [.int .i32 7] (.ret [.int .i32 7]) := rfl
set_option maxRecDepth 100000 in
theorem mem_load_after_dealloc : MemIs 1 [.int .i32 7] (.ub "Load: use after dealloc") := rfl
set_option maxRecDepth 100000 in
theorem mem_past_the_slot :
    MemIs 2 [.int .i32 7] (.ub "Load: access [4..8) is out of bounds for allocation size 4") := rfl
set_option maxRecDepth 100000 in
theorem mem_misaligned :
    MemIs 3 [.int .i32 7] (.ub "Load: pointer address 1025 is not aligned to 4") := rfl
set_option maxRecDepth 100000 in
theorem mem_byte_one : MemIs 4 [.int .u32 3735928559] (.ret [.int .u8 190]) := rfl

def ForgedUseAfterFree : Prop := MemIs 1 [.int .i32 7] (.ret [.int .i32 7])

theorem forged_use_after_free_fails : ¬ ForgedUseAfterFree := by
  intro h
  have e := h.symm.trans mem_load_after_dealloc
  exact Out.noConfusion (Except.ok.inj e)

def ForgedBigEndian : Prop := MemIs 4 [.int .u32 3735928559] (.ret [.int .u8 173])

theorem forged_big_endian_fails : ¬ ForgedBigEndian := by
  intro h
  have e := List.cons.inj (Out.ret.inj (Except.ok.inj (h.symm.trans mem_byte_one)))
  have e2 := Val.int.inj e.1
  exact absurd e2.2 (by decide)

theorem u32_encode :
    SEndian.encode .LittleEndian (sgnOf false) (Int.ofNat 4) (readAt false 32 16909060) =
      SOut.ok (some [4, 3, 2, 1]) :=
  encode_minirust false .u32 16909060 (by decide)

def ForgedEncode : Prop :=
  SEndian.encode .LittleEndian (sgnOf false) (Int.ofNat 4) (readAt false 32 16909060) =
    SOut.ok (some [1, 2, 3, 4])

theorem forged_encode_fails : ¬ ForgedEncode := by
  intro h
  have e := h.symm.trans u32_encode
  have e2 := Option.some.inj (SOut.ok.inj e)
  exact absurd e2 (by decide)

/-! ### MiniRust's decode, alignment and access checks (RM4c review) -/

/-- MiniRust's little-endian decode of the bytes SemR stores for the `i32`
    residue `2^32 - 1` is the integer that residue stands for (`-1`). -/
theorem i32_decode :
    SEndian.decode .LittleEndian (sgnOf true) (byteInts (leBytes 4 4294967295)) =
      SOut.ok (readAt true 32 4294967295) :=
  decode_minirust true .i32 4294967295 (by decide)

def ForgedDecode : Prop :=
  SEndian.decode .LittleEndian (sgnOf true) (byteInts (leBytes 4 4294967295)) =
    SOut.ok (Int.ofNat 4294967295)

theorem forged_decode_fails : ¬ ForgedDecode := by
  intro h
  have e := SOut.ok.inj (h.symm.trans i32_decode)
  exact absurd e (by decide)

/-- Address 1025 is not aligned to 4, in MiniRust's `Align::is_aligned` as in
    SemR. -/
theorem misaligned_1025 :
    SAlign.is_aligned (Int.ofNat 4) (Int.ofNat 1025) = SOut.ok false :=
  aligned_minirust 1025 4 (by decide)

def ForgedAligned : Prop := SAlign.is_aligned (Int.ofNat 4) (Int.ofNat 1025) = SOut.ok true

theorem forged_aligned_fails : ¬ ForgedAligned := by
  intro h
  exact Bool.noConfusion (SOut.ok.inj (h.symm.trans misaligned_1025))

/-- A dead four-byte slot at 1024, as SemR and MiniRust each record it. -/
def semrDeadSlot : Alloc := { base := 1024, size := 4, align := 4, live := false, data := [] }
def mrDeadSlot : MR_Allocation :=
  ⟨[.Uninit, .Uninit, .Uninit, .Uninit], 1024, 4, .Stack, false, ()⟩
def mrDeadMem : MR_BasicMemory := ⟨[mrDeadSlot], ()⟩

/-- MiniRust's `check_ptr` of a load through the dead slot is undefined
    behaviour, as SemR's access is (`accessAlloc_minirust`). -/
theorem dead_slot_check_ptr :
    MRf.BasicMemory.check_ptr 2 mrDeadMem ⟨Int.ofNat (1024 + 0), some (⟨Int.ofNat 0⟩, ())⟩
        (Int.ofNat 4) =
      SOut.ok (SRes.err (MR_TerminationInfo.Ub "dereferencing pointer to dead allocation")) :=
  ((accessAlloc_minirust "Load" 0 mrDeadMem 0 0 4 4 semrDeadSlot mrDeadSlot rfl ⟨rfl, rfl, rfl⟩
    (by decide) (by decide)).1 rfl).2

def ForgedDeadAccess : Prop :=
  MRf.BasicMemory.check_ptr 2 mrDeadMem ⟨Int.ofNat (1024 + 0), some (⟨Int.ofNat 0⟩, ())⟩
      (Int.ofNat 4) =
    SOut.ok (SRes.ok (some (⟨Int.ofNat 0⟩, (), Int.ofNat 0)))

theorem forged_dead_access_fails : ¬ ForgedDeadAccess := by
  intro h
  have e := SOut.ok.inj (h.symm.trans dead_slot_check_ptr)
  cases e

end SemRCheck

#print axioms SemR.pow_bytes_target
#print axioms SemR.decodeVal_encodeVal_int_target
#print axioms SemR.readOut_after_store_target
#print axioms SemR.step_load_after_dealloc
#print axioms SemR.step_store_after_dealloc
#print axioms SemR.alloc_fresh
#print axioms SemR.encode_minirust
#print axioms SemR.decode_minirust
#print axioms SemR.accessAlloc_minirust
#print axioms SemRCheck.usize32_footprint
#print axioms SemRCheck.usize64_footprint
#print axioms SemRCheck.u64_on32_footprint
#print axioms SemRCheck.usize32_image
#print axioms SemRCheck.wrong_usize32_image_refused
#print axioms SemRCheck.wrong_usize32_footprint_refused
#print axioms SemRCheck.unit_u64_count32
#print axioms SemRCheck.unit_u64_index32
#print axioms SemRCheck.last_byte32_allocates
#print axioms SemRCheck.past_last_byte32_refuses
#print axioms SemRCheck.same_allocation64_fits
#print axioms SemRCheck.wrong_allocation32_refused
#print axioms SemRCheck.usize32_store_load

-- Keep main's RM4c closures observable beside the target-width controls.
#print axioms SemR.readBytes_writeBytes
#print axioms SemR.readBytes_writeBytes_disjoint
#print axioms SemR.fromLE_leBytes
#print axioms SemR.decodeVal_encodeVal_int
#print axioms SemR.readOut_after_store
#print axioms SemR.accessAt_dead
#print axioms SemR.accessAt_oob
#print axioms SemR.accessAt_ok
#print axioms SemR.step_double_dealloc
#print axioms SemR.load_decode_minirust
#print axioms SemR.leBytes_fromLE
#print axioms SemR.isPow2_minirust
#print axioms SemR.checkAlign_minirust
#print axioms SemR.aligned_minirust
#print axioms SemR.check_ptr_eq
#print axioms SemR.alignUp_aligned
#print axioms SemR.below_empty
#print axioms SemR.below_setNth
#print axioms SemRCheck.mem_blob_decodes
#print axioms SemRCheck.mem_roundtrip
#print axioms SemRCheck.mem_load_after_dealloc
#print axioms SemRCheck.mem_past_the_slot
#print axioms SemRCheck.mem_misaligned
#print axioms SemRCheck.mem_byte_one
#print axioms SemRCheck.forged_use_after_free_fails
#print axioms SemRCheck.forged_big_endian_fails
#print axioms SemRCheck.u32_encode
#print axioms SemRCheck.forged_encode_fails
#print axioms SemRCheck.i32_decode
#print axioms SemRCheck.forged_decode_fails
#print axioms SemRCheck.misaligned_1025
#print axioms SemRCheck.forged_aligned_fails
#print axioms SemRCheck.dead_slot_check_ptr
#print axioms SemRCheck.forged_dead_access_fails
