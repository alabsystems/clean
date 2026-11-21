/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/
import Init.Data.BitVec
import Init.Omega

/- Qualification INPUT produced by official Lean4.31. It grants no Clean
   admission. The state/read/write definitions and frame lemmas below are
   literal Trust-CG source excerpts bound in source-book.json. -/
namespace Trust.A64

abbrev Reg := Fin 32

structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr

/-- A64 machine state for the integer subset. -/
structure MachState where
  /-- X0..X30. -/
  x : Fin 31 → BitVec 64
  sp : BitVec 64
  pc : BitVec 64
  nzcv : NZCV
  /-- Byte-addressed little-endian memory. -/
  mem : BitVec 64 → BitVec 8

namespace MachState

/-- `X[r]` where register 31 is the zero register. -/
def readX (s : MachState) (r : Reg) : BitVec 64 :=
  if h : r.val < 31 then s.x ⟨r.val, h⟩ else 0

/-- `X[r]` where register 31 is SP. -/
def readXSP (s : MachState) (r : Reg) : BitVec 64 :=
  if h : r.val < 31 then s.x ⟨r.val, h⟩ else s.sp

/-- `X[r] = v` where register 31 is the zero register (the write is discarded). -/
def writeX (s : MachState) (r : Reg) (v : BitVec 64) : MachState :=
  if h : r.val < 31 then { s with x := fun i => if i = ⟨r.val, h⟩ then v else s.x i } else s

/-- `X[r] = v` where register 31 is SP. -/
def writeXSP (s : MachState) (r : Reg) (v : BitVec 64) : MachState :=
  if h : r.val < 31 then { s with x := fun i => if i = ⟨r.val, h⟩ then v else s.x i }
  else { s with sp := v }

/-- Fall through to the next instruction. -/
def advance (s : MachState) : MachState := { s with pc := s.pc + 4 }

/-- Read `k` bytes little-endian at `addr` (wrapping) as a natural number. -/
def readMem (s : MachState) (addr : BitVec 64) : Nat → Nat
  | 0 => 0
  | k + 1 => (s.mem addr).toNat + 256 * s.readMem (addr + 1) k

/-- Write the low `k` bytes of `v` little-endian at `addr` (wrapping). -/
def writeMem (s : MachState) (addr : BitVec 64) (v : Nat) : Nat → MachState
  | 0 => s
  | k + 1 =>
    let s' : MachState :=
      { s with mem := fun a => if a = addr then BitVec.ofNat 8 v else s.mem a }
    s'.writeMem (addr + 1) (v / 256) k

end MachState

theorem byteAddress_add (base : BitVec 64) (i j : Nat) :
    base + BitVec.ofNat 64 i + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem differentByteOffsets {base : BitVec 64} {i j : Nat}
    (iBound : i < 2 ^ 64) (jBound : j < 2 ^ 64) (different : i ≠ j) :
    base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j := by
  intro same
  have nat := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp same)
  apply different
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt iBound, Nat.mod_eq_of_lt jBound] using nat

theorem MachState.writeMem_frame (s : MachState) (base addr : BitVec 64) (value count : Nat)
    (outside : ∀ i, i < count → addr ≠ base + BitVec.ofNat 64 i) :
    (s.writeMem base value count).mem addr = s.mem addr := by
  induction count generalizing s base value with
  | zero => rfl
  | succ count ih =>
    have first : addr ≠ base := by
      simpa using outside 0 (Nat.succ_pos count)
    simp only [MachState.writeMem]
    rw [ih]
    · simp [first]
    · intro i within
      change addr ≠ base + BitVec.ofNat 64 1 + BitVec.ofNat 64 i
      rw [byteAddress_add]
      exact outside (1 + i) (by omega)

/-- Original 64-bit byte increment, without a Nat-address port. -/
theorem next64_toNat (a : BitVec 64) :
    (a + BitVec.ofNat 64 1).toNat = (a.toNat + 1) % 18446744073709551616 := by
  simpa only [BitVec.toNat_ofNat] using BitVec.toNat_add a (BitVec.ofNat 64 1)

/-- Original second-eight-byte-store address. -/
theorem secondStore64_toNat (a : BitVec 64) :
    (a + BitVec.ofNat 64 8).toNat = (a.toNat + 8) % 18446744073709551616 := by
  simpa only [BitVec.toNat_ofNat] using BitVec.toNat_add a (BitVec.ofNat 64 8)

/-- The copied divisor survives the subsequent constant write to X0. -/
theorem divisorCopySurvives (s : MachState) :
    ((s.writeX 1 (s.readX 0)).writeX 0 1000).readX 1 = s.readX 0 := by
  simp [MachState.readX, MachState.writeX]

/-- Memory part of s21's actual STP X29,X30,[SP,#-16]!, using original writeMem. -/
def s21StorePair (s : MachState) : MachState :=
  let base := s.sp - 16
  (s.writeMem base (s.readX 29).toNat 8).writeMem (base + 8) (s.readX 30).toNat 8

theorem s21StorePair_frame (s : MachState) (address : BitVec 64)
    (separate : ∀ i, i < 16 → address ≠ (s.sp - 16) + BitVec.ofNat 64 i) :
    (s21StorePair s).mem address = s.mem address := by
  unfold s21StorePair
  rw [MachState.writeMem_frame, MachState.writeMem_frame]
  · exact fun i hi => separate i (by omega)
  · intro i hi
    change address ≠ (s.sp - 16) + BitVec.ofNat 64 8 + BitVec.ofNat 64 i
    rw [byteAddress_add]
    exact separate (8 + i) (by omega)

theorem s21StorePair_text (s : MachState) (codeBase : BitVec 64)
    (separate : ∀ i, i < 88 → ∀ j, j < 16 →
      codeBase + BitVec.ofNat 64 i ≠ (s.sp - 16) + BitVec.ofNat 64 j)
    (i : Nat) (within : i < 88) :
    (s21StorePair s).mem (codeBase + BitVec.ofNat 64 i) =
      s.mem (codeBase + BitVec.ofNat 64 i) :=
  s21StorePair_frame s _ (separate i within)

def overlapState : MachState :=
  { x := fun r => if r.val = 29 then 5 else 0
    sp := 48, pc := 0, nzcv := ⟨false, false, false, false⟩, mem := fun _ => 0 }

theorem overlapChangesByte : (s21StorePair overlapState).mem 32 = 5 := by decide

end Trust.A64

#print axioms Trust.A64.MachState.writeMem_frame
#print axioms Trust.A64.next64_toNat
#print axioms Trust.A64.secondStore64_toNat
#print axioms Trust.A64.divisorCopySurvives
#print axioms Trust.A64.s21StorePair_frame
#print axioms Trust.A64.s21StorePair_text
#print axioms Trust.A64.overlapChangesByte
