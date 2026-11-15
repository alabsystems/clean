-- Lean 4.8.0 accepts every theorem here (`lean <file>`, exit 0, measured 2026-10-29).
-- A later operand whose result is an open `outParam` (`HAdd.hAdd (1 : Nat) 0`, `xs[0]!`)
-- defaults every pending numeral, so an earlier operand whose type only its numerals
-- decide is `Nat` and is coerced; an operand before it, one whose instance is found, or a
-- `match` (Lean postpones it past the defaulting) is not.
def nN : Nat := 1
theorem dl0 : ((id (1 - 7) + HAdd.hAdd (1 : Nat) 0 : Int)) = (1) := by decide
theorem dl1 : ((id (1 - 7) + HPow.hPow (2 : Nat) 2 : Int)) = (4) := by decide
theorem dl2 : (((if true then 1 - 7 else 0) + HMod.hMod (7 : Nat) 4 : Int)) = (3) := by decide
theorem dl3 : ((id (1 - 7) + [(1 : Nat), 2][0]! : Int)) = (1) := by decide
theorem dl4 : (((some (1 - 7)).getD 0 + [(1 : Nat), 2][0]! : Int)) = (1) := by decide
theorem dl5 : ((-(id (1 - 7)) + -(HSub.hSub (1 : Nat) 7) : Int)) = (0) := by decide
theorem dl6 : (([1 - 7].headD 0 + (HAdd.hAdd (1 : Nat) 0 : Nat) : Int)) = (1) := by decide
theorem dl7 : ((id (1 - 7) - (HAdd.hAdd (1 : Nat) 0 : Nat) : Int)) = (-1) := by decide
theorem dl8 : ((HAdd.hAdd (1 : Nat) 0 + id (1 - 7) : Int)) = (-5) := by decide
theorem dl9 : ((id (1 - 7) + HAdd.hAdd (1 : Nat) (0 : Nat) : Int)) = (-5) := by decide
theorem dl10 : ((id (1 - 7) * 2 + HAdd.hAdd (1 : Nat) 0 : Int)) = (1) := by decide
theorem dl11 : ((id (nN - 7) + HAdd.hAdd (1 : Nat) 0 : Int)) = (1) := by decide
theorem dl12 : ((id (2 - 5) - [(1 : Nat), 2][1]! : Int)) = (-2) := by decide
theorem dl13 : (((match 0 with | _ => 1 - 7) + (HAdd.hAdd (1 : Nat) 0 : Nat) : Int)) = (-5) := by decide
