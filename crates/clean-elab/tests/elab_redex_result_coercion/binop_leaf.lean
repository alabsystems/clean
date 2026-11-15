-- Lean 4.8.0 accepts every theorem here (`lean <file>`, exit 0, measured 2026-10-29).
-- A compound operand of an arithmetic operator is elaborated with no expected type and
-- coerced (`binop%`), an identity-like head meets the expected type before its argument
-- (`propagateExpectedType`), and a field-notation receiver's numerals wait.
def nN : Nat := 1
theorem leaf0 : (((3 : Nat) - 5 : Int)) = (-2) := by decide
theorem leaf1 : ((nN - 7 : Int)) = (-6) := by decide
theorem leaf2 : ((id nN - 7 : Int)) = (-6) := by decide
theorem leaf3 : ((id (1 : Nat) - 7 : Int)) = (-6) := by decide
theorem leaf4 : ((Nat.succ 0 - 7 : Int)) = (-6) := by decide
theorem leaf5 : ((nN.succ - 7 : Int)) = (-5) := by decide
theorem leaf6 : (((nN + 0) - 7 : Int)) = (-6) := by decide
theorem leaf7 : (((nN, 0).1 - 7 : Int)) = (-6) := by decide
theorem leaf8 : (([nN].headD 0 - 7 : Int)) = (-6) := by decide
theorem leaf9 : (((some nN).getD 0 - 7 : Int)) = (-6) := by decide
theorem leaf10 : ((max nN 0 - 7 : Int)) = (-6) := by decide
theorem leaf11 : (((fun z => z) nN - 7 : Int)) = (-6) := by decide
theorem leaf12 : ((id (nN - 7) : Int)) = (-6) := by decide
theorem leaf13 : ((id (1 - 7) : Int)) = (-6) := by decide
theorem leaf15 : (((some (1 - 7)).getD 0 : Int)) = (-6) := by decide
theorem leaf16 : (([1 - 7].headD 0 : Int)) = (-6) := by decide
theorem leaf17 : ((max (1 - 7) 0 : Int)) = (0) := by decide
theorem leaf18 : ((min (1 - 7) 9 : Int)) = (-6) := by decide
theorem leaf19 : ((if true then 1 - 7 else 0 : Int)) = (-6) := by decide
theorem leaf20 : ((if 1 = 1 then 0 - 2 else 3 : Int)) = (-2) := by decide
theorem leaf21 : (([if 1 = 1 then 0 - 2 else 3].headD 0 : Int)) = (-2) := by decide
theorem leaf22 : (((· - 7) 1 : Int)) = (-6) := by decide
theorem leaf24 : (((fun z => z) (1 - 7) : Int)) = (-6) := by decide
theorem leaf25 : (((fun z => z) (Nat.succ 0 - 7) : Int)) = (-6) := by decide
theorem leaf26 : ((Id.run (pure (1 - 7)) : Int)) = (-6) := by decide
theorem leaf27 : ((Function.const Nat (1 - 7) 3 : Int)) = (-6) := by decide
theorem leaf28 : ((match 0 with | _ => 1 - 7 : Int)) = (-6) := by decide
theorem leaf29 : ((let z := 1 - 7; z : Int)) = (-6) := by decide
theorem leaf30 : ((7 - id (Nat.succ 0 - 7) : Int)) = (7) := by decide
theorem leaf31 : ((id ((1 : Nat) - 7) - 7 : Int)) = (-7) := by decide
theorem leaf32 : ((id (nN - 7) - (3 : Nat) : Int)) = (-3) := by decide
theorem leaf33 : (((if nN < 5 then nN - 3 else 0) - 3 : Int)) = (-3) := by decide
theorem leaf34 : ((min (min 1 9 - 5) 9 - 5 : Int)) = (-9) := by decide
theorem leaf35 : (((some (1 / 2 - 1)).getD 0 : Int)) = (-1) := by decide
theorem recv9 : ((((some (1 - 7)).map (· + 1)).getD 0 : Int)) = (-5) := by decide
theorem recv11 : (([1 - 7, 2].getD 0 5 : Int)) = (-6) := by decide
theorem recv13 : (((some (nN - 7)).getD 0 : Int)) = (0) := by decide
theorem recv14 : (((some (1 - 7)).getD (0 : Nat) : Int)) = (-6) := by decide
theorem recv22 : (((some (1 - 7)).getD 0 * 2 : Int)) = (-12) := by decide
theorem recv26 : (((some (5 : Nat)).getD 0 - 7 : Int)) = (-2) := by decide
theorem more1 : ((((fun z => z - 7) 1) - 7 : Int)) = (-13) := by decide
theorem more3 : ((-(id (nN - 7)) : Int)) = (0) := by decide
theorem more4 : ((-((if nN < 5 then nN - 3 else 0)) : Int)) = (0) := by decide
theorem more5 : ((-((let z := nN; z - 7)) : Int)) = (0) := by decide
