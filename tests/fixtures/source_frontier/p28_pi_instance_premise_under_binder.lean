-- CLOSED 2026-09-16. This file was `..._MUST_FAIL.lean` and pinned a refusal;
-- it is now a PASS pin, which is the outcome its own header was written to
-- demand ("pinned rather than skipped so the day the capability lands this
-- fixture FAILS and is read"). It failed, it was read, and the capability
-- landed: the `depth == 0` restriction at the call site of
-- `resolve_pi_goal_by_abstraction` was lifted, so the goal-side telescope now
-- answers a CANDIDATE's `[inst]` premise, which is where `∀ i, LE (π i)`
-- appears. Measured on landing: `Mathlib/Order/Basic.lean` 65/206 -> 70/206,
-- all five regressed declarations recovered BY NAME, zero residual
-- `failed to synthesize instance LE ((x ...` errors in the file.
--
-- The history below is kept verbatim because the SHAPE is the lesson, and
-- because a closed class still has to say what it closed.
--
-- WAS (open class, measured 2026-09-15): instance synthesis cannot discharge a
-- FORALL-QUANTIFIED instance premise by applying another instance UNDER the
-- binder.
--
-- The goal is `MyLE (forall k, p k)`. `piLE` is registered and IS offered as a
-- candidate -- the error message lists it -- but its own premise
-- `forall k, MyLE (p k)` has to be built from `[forall k, MyPre (p k)]` by
-- going under the `k` binder and applying `myPreToLE` there.
--
-- CORRECTION (2026-09-15, same day): this header first said "nothing does that
-- ... a missing capability". THAT IS FALSE, and it was reached by grepping
-- `instance_synthesis.rs` and `instance_resolution.rs` -- neither of which is
-- the engine. The engine is `crates/clean-elab/src/infer/instance.rs`, and
-- `resolve_pi_goal_by_abstraction` (:551) does exactly this: it opens a
-- Pi-shaped goal's telescope over fresh LOCALS, resolves the conclusion, and
-- re-abstracts into lambdas.
--
-- The real mechanism is a DEPTH GATE, and p29 is the controlled experiment that
-- shows it. The call site (instance.rs:257) runs that abstraction only when
-- `depth == 0`, so it answers the elaborator's own goal and never a CANDIDATE's
-- `[inst]` sub-goal. `piLE`'s premise is precisely such a sub-goal. p29 demands
-- the IDENTICAL premise at depth 0, from the same context and the same
-- instances, and it RESOLVES; this file raises it at depth >= 1 and it does
-- not. Same premise, same everything, one difference.
--
-- The guard is deliberate, not an oversight: its comment records that without
-- it a candidate's sub-goal could be answered by the goal-side telescope and
-- silently change the TERM of goals that already resolve, and
-- `test_goal_side_is_not_applied_to_an_internal_subgoal` pins that boundary. So
-- lifting it is "a separate increment with its own argument", exactly as
-- `resolve_pi_goal_by_abstraction`'s own docstring anticipates for the
-- `[inst]`-binder case -- NOT a one-line relaxation.
--
-- WHERE IT BITES, and why this fixture exists rather than a note: it is the
-- whole of `Mathlib/Order/Basic.lean`'s 72 -> 67 regression, recorded in
-- data/source_elab_ratchet.json `_audit_r17_remeasurement_2026_09_02`. Diffed
-- per declaration against the armed report, the -5 is THREE declarations that
-- hit this class directly -- le_of_strongLT (line 588),
-- strongLT_of_strongLT_of_le (596) and le_update_iff (613), each
-- `failed to synthesize instance LE ((x : fvar#0) -> fvar#2 x)` -- plus TWO
-- pure cascades that are `alias`es of the first two and report
-- `Unknown identifier`. One cause, not five. Upstream the shape is
-- `instance Pi.hasLe [forall i, LE (pi i)] : LE (forall i, pi i)` at
-- Order/Basic:531 used under `variable [forall i, Preorder (pi i)]`, so the
-- binder-crossing step is `Preorder.toLE`; here it is `myPreToLE`, which keeps
-- the fixture free of any Mathlib dependency.
--
-- MEASURED COST AND BENEFIT OF LIFTING IT (2026-09-16, a probe -- reverted, NOT
-- landed): reports/source-frontier/2026-09-16-depth-gate-lift-probe.json.
-- Removing `&& depth == 0` at instance.rs:257 makes this fixture pass 5/5, takes
-- Mathlib/Order/Basic.lean from 65/206 to 70/206 on a corpus whose decl_count for
-- that file equals the armed one, recovers all five regressed declarations BY
-- NAME and leaves ZERO `failed to synthesize instance LE ((x...` errors in it.
-- The cost is exactly one test -- `test_goal_side_is_not_applied_to_an_internal_subgoal`,
-- which encodes the contract itself -- out of 534 in the instance-synthesis
-- suite, and the decEq/goal-side fixtures the guard's comment names as at risk
-- (p08, p09, p11, p18, p24) all hold at their exact declaration counts. What is
-- still unmeasured is the rest of clean-elab's lib suite, which does not finish
-- under bare cargo here (timed out at 50 and at 90 minutes).
--
-- So the open question is not "does it work" but "is the contract re-decided" --
-- the fix and that test want opposite things, and that is an owner's call.
--
-- Pinned rather than skipped so the day the capability lands this fixture FAILS
-- and is read. Its control is p27: if p27 ever stops passing, this refusal has
-- stopped measuring what it names.
universe u

class MyLE (a : Type u) where
  le : a -> a -> Prop

class MyPre (a : Type u) where
  toMyLE : MyLE a

instance myPreToLE (a : Type u) [p : MyPre a] : MyLE a := MyPre.toMyLE

instance piLE (i : Type u) (p : i -> Type u) [h : forall k, MyLE (p k)] :
    MyLE (forall k, p k) where
  le x y := forall k, MyLE.le (x k) (y k)

-- TARGET ASSERTION, written beside the refusal: when the capability lands this
-- must elaborate, exactly as `Mathlib/Order/Basic.lean`'s le_of_strongLT does.
def subjectViaParent (i : Type u) (p : i -> Type u) [h : forall k, MyPre (p k)]
    (a b : forall k, p k) : Prop := MyLE.le a b
