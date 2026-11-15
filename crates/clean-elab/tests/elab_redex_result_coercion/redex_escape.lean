-- Lean 4.8.0 accepts every theorem here (`lean <file>`, exit 0, measured 2026-10-29).
-- A β-redex whose head queues an instance goal over its binder (`Decidable (y = 1)`).
def nN : Nat := 1
theorem re0 : (((fun y => if y = 1 then (0 : Nat) - 1 else 2) (nN - 7) : Int)) = (2) := by decide
theorem re1 : (((fun y => if y = 1 then (0 : Nat) - 1 else 2) 1 : Int)) = (0) := by decide
theorem re2 : (((fun y => if y = 1 then (0 : Nat) - 1 else 2) (nN - 7) : Nat)) = (2) := by decide
theorem re3 : (((fun y => if y = 1 then (0 : Nat) - 1 else 2) (Nat.succ 0 - 7) : Int)) = (2) := by decide
theorem re4 : (((fun y => if y = 0 then 5 else (0 : Nat) - 1) 1 : Int)) = (0) := by decide
