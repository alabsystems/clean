-- Consumer module: references the producer's declarations by the names Lean
-- 4.30.0-rc2 gives them. Elaborated against the producer's environment with a
-- FRESH file context, which is what an `import` is -- and is why the leaked
-- prefix cannot self-cancel here the way an in-file reference does.
theorem uses_gamma : Gamma.g_inside = 2 := rfl

theorem uses_alpha_beta : Alpha.Beta.b_inside = 1 := rfl

theorem uses_root : after_everything = 3 := rfl
