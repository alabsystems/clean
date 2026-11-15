-- G70 twin: `simp only` with an empty list does not use `injEq`
-- (Lean: "simp made no progress").
theorem inj_only (a b : Nat) (h : (a, 1) = (b, 1)) : a = b := by
  simp only [] at h
  exact h.1
