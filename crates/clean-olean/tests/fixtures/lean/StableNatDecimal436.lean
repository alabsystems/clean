import Init.Data.Repr
import Init.Data.UInt.Lemmas
import Init.Data.Array.Lemmas
import Init.Data.List.Range

set_option maxRecDepth 8192 in
theorem originalNatDecimal (n : Nat) :
    Nat.reprFast n = String.ofList (Nat.toDigits 10 n) := by
  let words := (List.range 128).map (fun i => i.toUSize.repr)
  let table : Array String := ⟨words⟩
  change (if h : n < table.size then table.getInternal n h else
    if h : n < USize.size then (USize.ofNatLT n h).repr
    else String.ofList (Nat.toDigits 10 n)) = _
  split
  · rename_i h
    have small : n < 128 := by simpa [table, words] using h
    have native : n < USize.size :=
      Nat.lt_of_lt_of_le small (Nat.le_trans (by decide : 128 ≤ UInt8.size) UInt8.size_le_usizeSize)
    change words[n] = _
    simp only [words, List.getElem_map, List.getElem_range, USize.repr]
    rw [show n.toUSize.toNat = n from USize.toNat_ofNat_of_lt native]
  · split
    · rfl
    · rfl

theorem originalNatReprImplementsFast : Nat.repr = Nat.reprFast := by
  funext n
  exact (originalNatDecimal n).symm

#print axioms originalNatDecimal
#print axioms originalNatReprImplementsFast
