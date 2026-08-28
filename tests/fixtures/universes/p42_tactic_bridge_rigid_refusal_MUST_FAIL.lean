-- U2 stage 1 MUST-FAIL twin of p41 — a genuinely conflicting tactic-level
-- equation stays a LOUD refusal after the bridge fix (2026-08-25).
--
-- `tsymm` is monomorphic at `Type` (Sort 1). `apply tsymm` against a goal
-- whose carrier is the DECLARED rigid `Sort u` forces the unifier to solve
-- `u := 1`, which the ProofState's seeded rigid set now refuses INSIDE the
-- tactic block exactly as the declaration layer always has (the
-- p06/p30/p31/p39 discipline). Before stage 1a the ProofState's rigid set
-- was empty: the same equation was accepted into the tactic's own level
-- state and the declaration died downstream as an opaque Sort mismatch.
-- The pinned fragment is the rigid-refusal message itself — if this ever
-- degrades back into a raw `Sort(Param(..)) vs Sort(..)` mismatch, the
-- bridge has regressed to level-blind checking.

universe u

def tsymm {α : Type} (a b : α) (h : a = b) : b = a := Eq.symm h

theorem probe_rigid_conflict {α : Sort u} (a b : α) (h : a = b) : b = a := by
  apply tsymm
  exact h
