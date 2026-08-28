-- p25 — CLASS I, FRONTIER STAGE I-2: the refusal that makes p24 mean
-- something. The goal telescope must be solved for an ARBITRARY argument.
--
-- PROVES: `resolve_pi_goal_by_abstraction` opens the goal's ∀-telescope over
-- rigid LOCALS, not over metavariables. The distinction is the whole
-- soundness of the stage. `MyDEq Bool` δ-unfolds to
-- `(x y : Bool) → MyD (Eq Bool x y)`, and the only instance in the file
-- covers exactly one pair of arguments, `MyD (true = true)`. Opening the
-- telescope with metavariables would let the conclusion's search ASSIGN
-- `?x := true`, `?y := true`, "succeed", and hand back
-- `fun x y => trueMyD` — a term whose body has the wrong type for all but one
-- of its own arguments. Opening it with rigid locals makes that unification
-- fail, and the candidate is refused.
--
-- IN-FILE CONTROL (`bodyAtTrue`): `MyD (true = true)` resolves on its own,
-- so the refusal below is not "the instance is unreachable" or "`MyD` is
-- broken" — the ONE argument the instance covers is answerable today. What
-- is refused is generalising it to every argument.
--
-- CONTROL: p24 — the same shape whose conclusion IS solvable for an
-- arbitrary argument passes. So the pair distinguishes a precise refusal
-- from a blanket one: p25 alone could not.
class MyD (p : Prop) where
  ev : Nat

instance trueMyD : MyD (true = true) := ⟨7⟩

def MyDEq (α : Type) : Type := (x : α) → (y : α) → MyD (x = y)

def callee {α : Type} [MyDEq α] (a : α) : Nat := 0

def bodyAtTrue : Nat := (inferInstance : MyD (true = true)).ev

def useBool (a : Bool) : Nat := callee a
