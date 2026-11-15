theorem rwa_implicit_local_empty (h : {n : Nat} → n = n) : {n : Nat} → n = n := by
  rwa [] at h
