def decodeAllowed (version flags : Option Nat) : Option Nat := do
  let v ← version
  let bits ← flags
  let allocated := 7 + (if 20 ≤ v then 24 else 0) + (if 45 ≤ v then 96 else 0)
  if Nat.land bits (255 - allocated) != 0 then none
  if Nat.land bits 96 == 96 then none
  pure allocated

theorem before20 : decodeAllowed (some 19) (some 8) = none := rfl
theorem at20 : decodeAllowed (some 20) (some 8) = some 31 := rfl
theorem at45 : decodeAllowed (some 45) (some 64) = some 127 := rfl
theorem conflicting : decodeAllowed (some 45) (some 96) = none := rfl
