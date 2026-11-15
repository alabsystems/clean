-- Consumer module for the partial-`end` producer: references the declaration
-- by the name Lean 4.30.0-rc2 gives it, `Bundle.after_partial`.
theorem uses_partial : Bundle.after_partial = 2 := rfl

theorem uses_partial_inner : Bundle.Pretriv.inner = 1 := rfl
