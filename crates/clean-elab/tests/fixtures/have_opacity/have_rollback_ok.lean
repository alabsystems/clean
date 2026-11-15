theorem opaque_have_rollback_ok : True := by
  have h : Nat := 7
  have k : h = h := by
    first
    | exact Eq.refl 7
    | rfl
  exact True.intro
