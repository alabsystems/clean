-- p52: simp must not bind a `Prop`-declared lemma binder to a `Sort u` term.
--
-- Simp mints one metavariable per lemma binder with the PLACEHOLDER type
-- `Expr::type_()` (`simp/pattern.rs`) and `MetaState::assign` never type-checks,
-- so `capRhs`'s binder `(p : Prop)` used to capture `γ : Sort v`. Nothing
-- downstream objected: `lhs_inst ≡ expr` holds (it is the same term) and
-- `proof_matches_rewrite` runs the non-checking `infer_type`. The ill-typed
-- `@capRhs γ` reached `close_goal`'s `infer_type_strict` and killed the whole
-- declaration with `TypeMismatch { expected: Sort(Zero), inferred: Sort(Param v) }`.
--
-- The third declaration is the one that matters: BOTH lemmas are offered, and
-- the honest universe-polymorphic one only gets its turn if the ill-typed match
-- is refused first.

axiom capRhs : ∀ (p : Prop), (p → True) = p

axiom capU : ∀ {α : Sort u}, (α → True) = True

-- CONTROL: a genuine `Prop` still matches the `Prop` binder. The guard must be
-- restrictive only where the binding is actually ill-typed.
theorem prop_binder_control {γ : Prop} : (γ → True) = γ := by
  simp only [capRhs]

-- CONTROL: the universe-polymorphic lemma matches `Sort v` on its own, so the
-- level-solving path (`expr.rs`, telescope walk) keeps working.
theorem sort_binder_control {γ : Sort v} : (γ → True) = True := by
  simp only [capU]

-- THE DEFECT: `capRhs` is offered first and matches `γ : Sort v` against its
-- `(p : Prop)` binder. Refusing that match is what lets `capU` fire.
theorem prop_binder_must_not_hijack {γ : Sort v} : (γ → True) = True := by
  simp only [capRhs, capU]
