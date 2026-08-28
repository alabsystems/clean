-- p18 — CLASS I, the GOAL side: the alias goal whose answer must be BUILT.
--
-- RE-PINNED 2026-08-26 (FRONTIER STAGE I-2): FAIL -> PASS, 2/1 -> 3/0.
-- Renamed from `p18_goal_side_still_open_MUST_FAIL.lean`. The flip is this
-- stage's exit criterion; the file is unchanged, only its pinned verdict
-- moved.
--
-- WHAT IT PINNED BEFORE: stage I-1's candidate-side repair matches a
-- `def`-based class alias against LOCAL instance binders. It did not
-- TELESCOPE the goal, so a Pi-shaped alias goal with no local of that type in
-- scope still failed, even though the BODY of that Pi was answerable from the
-- global table. `callee` is applied at the concrete carrier `Nat`,
-- `[DecidableEq Nat]` is δ-unfolded by the caller to
-- `(n n1 : Nat) → Decidable (Eq Nat n n1)`, and there is no local to match it
-- against:
--   FailedToSynthesizeInstance { goal: "(n : Nat) -> (n1 : Nat) ->
--                                       Decidable (Eq {1} Nat n n1)" }
--
-- WHAT IT PINS NOW: `ElabCtx::resolve_pi_goal_by_abstraction` opens the
-- goal's ∀-telescope over fresh rigid LOCALS, resolves the conclusion as an
-- ordinary instance goal, and re-abstracts the locals into lambdas —
-- `fun n n1 => <that instance> n n1`. This is §4.3 point 2 of the recon
-- (telescope a Pi goal, solve the body, re-abstract), and it is the one thing
-- no candidate-side match can do: the answer is not in scope to be found.
--
-- IN-FILE CONTROL (`bodyIsSolvable`): the Pi's body — `Decidable (a = b)` at
-- `Nat` — resolved from the global table on its own before this stage and
-- resolves now. So what moved is the ABSTRACTION, not the body and not a
-- `Nat` instance.
--
-- WHAT IT DOES NOT ESTABLISH: that the goal side works in general. Both
-- declarations here run through the hand-written `Decidable (@Eq α a b)`
-- bridge. p24 is the probe that removes the bridge from the picture, and
-- p25/p26 are the refusals that keep the new capability from being a blanket.
--
-- CONTROL: p09 — the SAME shape with `[DecidableEq α]` in scope passed at
-- stage I-1 already, so what this file measured was never the alias.
def callee {α : Type} [DecidableEq α] (a : α) : Nat := 0

def bodyIsSolvable (a b : Nat) : Bool := if a = b then true else false

def useNat (a : Nat) : Nat := callee a
