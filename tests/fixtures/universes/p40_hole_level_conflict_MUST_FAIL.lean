-- MUST FAIL — a genuine universe conflict at a hole stays LOUD.
--
-- The second half of the p37 guard. p39 pins that a forced assignment to a
-- RIGID parameter is still refused; this pins that a forced assignment to an
-- incompatible CONCRETE level is still refused, i.e. that making the hole's
-- universe a metavariable did not make it a wildcard.
--
-- `f` demands `γ : Prop` (`Sort 0`); `b : β : Type` (`Sort 1`). Filling the
-- hole with `β` needs `Sort 1 ≤ Sort 0`, which cumulativity does not grant, so
-- `unify_meta`'s concrete-level branch must reject:
--
--     universe level conflict: Zero vs Succ(Zero)
--
-- Cumulativity in the licensed direction is still allowed and is covered by
-- p37's `polyProp` row (a `Sort 0` value in a `Sort 1` position passes).

theorem holeLevelConflict (f : ∀ (γ : Prop), γ → True) (β : Type) (b : β) : True := f _ b
