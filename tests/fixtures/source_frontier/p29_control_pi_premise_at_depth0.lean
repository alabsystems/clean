-- DISCRIMINATOR for p28, and the fixture that localizes its cause.
--
-- `needsPiPremise` demands EXACTLY the premise p28's `piLE` cannot get -- the
-- Pi-shaped instance goal `forall k, MyLE (p k)` -- but demands it as the
-- ELABORATOR'S OWN top-level goal. Here it RESOLVES, from the same
-- `[forall k, MyPre (p k)]` and the same `myPreToLE`, so the capability to
-- build a Pi-shaped instance by opening its binder plainly exists:
-- `ElabCtx::resolve_pi_goal_by_abstraction` (crates/clean-elab/src/infer/instance.rs:551).
--
-- p28 differs in ONE way: there the same premise is a CANDIDATE's `[inst]`
-- sub-goal, reached at depth >= 1, and the call site gates the abstraction on
-- `depth == 0` (instance.rs:257). That guard is deliberate and documented --
-- without it a candidate's sub-goal could be answered by the goal-side
-- telescope and silently change the TERM of goals that already resolve, which
-- `test_goal_side_is_not_applied_to_an_internal_subgoal` pins.
--
-- So the pair p29/p28 is a controlled experiment: same premise, same context,
-- same instances, differing only in the depth at which the premise is raised.
-- Keep them together; p28's header states the conclusion they license.
universe u

class MyLE (a : Type u) where
  le : a -> a -> Prop

class MyPre (a : Type u) where
  toMyLE : MyLE a

instance myPreToLE (a : Type u) [p : MyPre a] : MyLE a := MyPre.toMyLE

def needsPiPremise (i : Type u) (p : i -> Type u) [hh : forall k, MyLE (p k)] : Prop := True

def depth0Resolves (i : Type u) (p : i -> Type u) [h : forall k, MyPre (p k)] : Prop :=
  needsPiPremise i p
