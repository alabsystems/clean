-- MUST FAIL — the rigid refusal survives the p37/p38 hole repair.
--
-- p37 removed a hardcoded `Sort 1` from the hole's type metavariable, which is
-- exactly the kind of change that can turn a refusal into an acceptance. This
-- is the pin that says it did not.
--
-- Here the hole's universe is GENUINELY forced: `f` demands `γ : Type`, so the
-- hole must be a `Sort 1`, and `a : α : Sort u` is the only thing that can fill
-- it. Solving that requires `u := 1` — and `u` is a DECLARED parameter of
-- `rigidHole`, so assigning it would silently monomorphize the declaration.
-- `add_level_constraint`'s rigid refusal (`unify/meta_state/levels.rs`) must
-- still fire:
--
--     cannot assign rigid universe parameter u := 1
--
-- Note the message is character-for-character the one the BUG produced in
-- `tests/fixtures/pattern_lambda/anon_ctor_dependent_exists_universe_u.lean`
-- before the repair. That is the point: the diagnosis was never wrong, the
-- premise was. There the `Sort 1` was invented by `elab_hole` and nothing
-- forced it; here `f`'s own signature forces it, and the refusal is correct.
--
-- The in-family control that MUST pass is `okHoleAgreeing`, in p37's companion
-- position — see `polyRigid` (p37), the same shape where the callee's binder is
-- `Sort u` rather than `Type` and the hole solves without touching `u`.

universe u

theorem rigidHole {α : Sort u} (f : ∀ (γ : Type), γ → True) (a : α) : True := f _ a
