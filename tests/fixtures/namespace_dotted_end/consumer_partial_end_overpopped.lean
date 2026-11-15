-- The negative control for the partial-`end` producer: the name minted when
-- `end Pretriv` is treated as closing BOTH components. Lean 4.30.0-rc2 rejects
-- it with `Unknown identifier `after_partial``, so Clean must reject it too.
theorem uses_overpopped : after_partial = 2 := rfl
