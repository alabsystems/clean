/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/
import MachineMemory431

namespace Trust.A64

theorem MachState.readMem_congr_bytes (s t : MachState) (base : BitVec 64) (count : Nat)
    (same : ∀ i, i < count → s.mem (base + BitVec.ofNat 64 i) = t.mem (base + BitVec.ofNat 64 i)) :
    s.readMem base count = t.readMem base count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
    have head : s.mem base = t.mem base := by simpa using same 0 (Nat.succ_pos count)
    simp only [MachState.readMem, head]
    rw [ih (base + 1)]
    intro i within
    change s.mem (base + BitVec.ofNat 64 1 + BitVec.ofNat 64 i) =
      t.mem (base + BitVec.ofNat 64 1 + BitVec.ofNat 64 i)
    rw [byteAddress_add]
    exact same (1 + i) (by omega)

/-- Preserve the exact original four-byte fetch after the s21 pair store. -/
theorem s21StorePair_fetch4 (s : MachState) (pc : BitVec 64)
    (separate : ∀ i, i < 4 → ∀ j, j < 16 →
      pc + BitVec.ofNat 64 i ≠ (s.sp - 16) + BitVec.ofNat 64 j) :
    (s21StorePair s).readMem pc 4 = s.readMem pc 4 := by
  apply MachState.readMem_congr_bytes
  intro i within
  exact s21StorePair_frame s _ (separate i within)

end Trust.A64

#print axioms Trust.A64.MachState.readMem_congr_bytes
#print axioms Trust.A64.s21StorePair_fetch4
