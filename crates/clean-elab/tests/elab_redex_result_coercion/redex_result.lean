-- Lean 4.8.0 accepts every theorem here (`lean <file>`, exit 0, measured 2026-10-29).
-- A β-redex whose head's body settles a GROUND result type, under a different ground
-- expected type, is coerced as a whole (`ensureHasType` after `elabAppArgs`).
theorem eq0 : (((fun y => y - (7 : Nat)) 1 : Int)) = (0) := by decide
theorem eq2 : (((fun k => -k + 0) 5 : Int)) = (-5) := by decide
theorem eq4 : (((fun k => k - 7) 5 : Int)) = (-2) := by decide
theorem eq5 : (((fun (k : Nat) => k - 7) 5 : Int)) = (0) := by decide
theorem eq6 : (((fun y => y * (2 : Nat) - 9) 1 : Int)) = (0) := by decide
theorem eq9 : (((fun y => (y : Nat) - 3) 1 : Int)) = (0) := by decide
theorem eq10 : (((fun y => Nat.sub y 3) 1 : Int)) = (0) := by decide
theorem eq11 : (((fun y => y.succ - 3) 1 : Int)) = (-1) := by decide
theorem eq12 : (((fun y => y - (3 : Nat)) 1 + 0 : Int)) = (0) := by decide
theorem eq13 : ((id ((fun y => y - (7 : Nat)) 1) : Int)) = (0) := by decide
theorem eq14 : (((fun y => y - (7 : Nat)) 1 - 0 : Int)) = (0) := by decide
theorem eq16 : (((fun y => y - (7 : Nat)) 1 : Nat)) = (0) := by decide
theorem eq17 : (((fun y => (y - (7 : Nat) : Int)) 1 : Int)) = (-6) := by decide
theorem eq18 : (((fun y => y - (7 : Int)) 1 : Int)) = (-6) := by decide
theorem eq19 : (((fun y => y - (7 : Nat)) (1 : Nat) : Int) + 0) = (0) := by decide
theorem eq21 : (((fun y => y + (7 : Fin 5)) 2 : Nat)) = (4) := by decide
theorem eq22 : (((fun y => y - (2 : Nat)) 1 : Int) - ((fun y => y - (2 : Nat)) 1 : Int)) = (0) := by decide
theorem eq24 : (((fun x => x / (2 : Nat) - 3) 5 : Int)) = (0) := by decide
theorem eq25 : (((fun x => (x - 3, x)) (1 : Nat)).1) = (0) := by decide
