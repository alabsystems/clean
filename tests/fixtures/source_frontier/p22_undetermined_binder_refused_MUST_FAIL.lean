-- p22 — CLASS I hygiene: a telescope binder the GOAL does not determine.
--
-- PROVES: opening a local's ∀-telescope allocates one metavariable per
-- binder. `MyDConst α := (x : α) → MyD True` concludes in `MyD True`, which
-- unifies with the goal `MyD True` while telling us NOTHING about `x`. The
-- candidate-side match applies the same hygiene check the global candidate
-- loop already applies — every telescope metavariable must end DETERMINED by
-- the goal — and refuses the candidate instead of emitting `h ?x`.
--
-- WHY THIS MATTERS BEYOND TASTE: an unassigned metavariable is carried as a
-- tagged free variable. Emitting one would not be caught here; it would
-- surface far from its cause as the kernel's fail-closed "Declaration
-- contains free variables". A capability-adding change that manufactured
-- kernel free-variable leaks would be a net loss.
--
-- CONTROL: p23 — the SAME class, the SAME telescope machinery, over a local
-- whose conclusion DOES determine both binders, passes. So this failure is
-- undeterminedness and not "telescoped locals are unusable".
class MyD (p : Prop) where
  ev : Nat

def MyDConst (α : Type) : Type := (x : α) → MyD True

def evAt (p : Prop) [MyD p] : Nat := MyD.ev

def undetermined {α : Type} [MyDConst α] : Nat := evAt True
