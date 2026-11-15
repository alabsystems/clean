theorem byCases (n : Nat) : n + 0 = n := by
  cases n with
  | zero => rfl
  | succ k => exact congrArg Nat.succ (byCases k)

-- Lean's well-founded proof uses these foundational axioms; Clean's
-- structural proof is axiom-free. The message difference remains a gap.
/-- info: 'byCases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms byCases
