import Init.Data.Repr
import Init.Data.UInt.Lemmas
import Init.Data.Array.Lemmas
import Init.Data.List.Range

theorem errorCodeReprFast (x : UInt32) :
    Nat.reprFast x.toNat = x.toUSize.repr := by
  let words := (List.range 128).map (fun n => n.toUSize.repr)
  let table : Array String := ⟨words⟩
  change (if h : x.toNat < table.size then table.getInternal x.toNat h else
    if h : x.toNat < USize.size then (USize.ofNatLT x.toNat h).repr
    else String.ofList (Nat.toDigits 10 x.toNat)) = _
  split
  · rename_i h
    change words[x.toNat] = _
    simp only [words, List.getElem_map, List.getElem_range]
    congr 1
    apply USize.toNat_inj.mp
    simp
  · simp only [dite_eq_left x.toNat_lt_usizeSize]
    rfl
theorem errorCodeRepr (x : UInt32) :
    Nat.repr x.toNat = x.toUSize.repr := by
  simp only [Nat.repr, USize.repr, UInt32.toNat_toUSize]

#print axioms errorCodeReprFast
#print axioms errorCodeRepr
