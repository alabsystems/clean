-- The negative control: the name the one-component pop used to mint. Lean
-- 4.30.0-rc2 rejects it with `Unknown identifier `Alpha.Gamma.g_inside``, so
-- Clean must reject it too. If this ever elaborates, the leak is back.
theorem uses_leaked : Alpha.Gamma.g_inside = 2 := rfl
