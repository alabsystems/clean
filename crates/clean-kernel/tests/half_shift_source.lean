namespace Trust.Kernel.HalfShift

/-- The actual native halving declaration is definitionally a right shift by one. -/
theorem half_is_shift (n : Nat) : Nat.div2 n = Nat.shiftRight n 1 := by
  rfl

/-- Reconstruct the parity carry using the actual constructive rejoin proof. -/
theorem parity_from_rejoin (n : Nat) :
    Nat.div2Par n = n - (Nat.div2 n + Nat.div2 n) := by
  have h := Nat.div2_rejoin n
  have c := Nat.add_comm (Nat.div2 n + Nat.div2 n) (Nat.div2Par n)
  have s := Nat.add_sub_cancel (Nat.div2Par n) (Nat.div2 n + Nat.div2 n)
  exact Eq.symm (Eq.trans (congrArg (fun k : Nat => k - (Nat.div2 n + Nat.div2 n)) (Eq.trans h c)) s)

end Trust.Kernel.HalfShift
