-- A bare constructor application must infer its implicit arguments from
-- the EXPECTED TYPE, as Lean's propagateExpectedType does (Elab/App.lean).
-- Equivalence.mk's `refl` slot is `∀ x : ?a, ?r x x` -- a FLEX APPLICATION
-- (metavariable in head position). No argument can ever pin ?r: matching
-- against it is a Miller-pattern problem the unifier rejects as a rigid
-- shape clash, so the result type must be unified with the expected type
-- FIRST. All three spellings below must elaborate.
def trivRel (_ _ : Nat) : Prop := True
-- the WORKING spellings
theorem ok_at : Equivalence trivRel :=
  @Equivalence.mk Nat trivRel (fun _ => True.intro)
    (fun {_ _} _ => True.intro) (fun {_ _ _} _ _ => True.intro)
theorem ok_anon : Equivalence trivRel :=
  ⟨fun _ => True.intro, fun {_ _} _ => True.intro, fun {_ _ _} _ _ => True.intro⟩
-- the FAILING spelling (bare ctor, implicits from expected type)
theorem bare : Equivalence trivRel :=
  Equivalence.mk (fun _ => True.intro)
    (fun {_ _} _ => True.intro) (fun {_ _ _} _ _ => True.intro)
