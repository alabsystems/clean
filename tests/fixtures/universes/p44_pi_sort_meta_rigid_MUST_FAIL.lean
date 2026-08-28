-- P44 — U2 stage 2 MUST-FAIL twin of p43's `monoSolve`: the newly-generated
-- Pi-level equation refuses LOUDLY when it needs a rigid parameter
-- (2026-08-25).
--
-- `tid`'s argument lives in `Type` (Sort 1), so `bad` forces
-- `max(succ u, succ v) =?= 1`, i.e. `u := 0 ∧ v := 0` — and `u`/`v` here are
-- DECLARED universe parameters, rigid by the p06/p30/p31/p39 discipline.
-- Before stage 2 this equation was never generated and the declaration died
-- downstream at the kernel re-check as an opaque
-- `expected Sort(Succ(Zero)), got Sort(Max(Succ(..), Succ(..)))`. Now the
-- solver sees the equation and the rigid refusal fires at the constraint
-- site, with the same message the declaration layer has always used. If this
-- fragment ever degrades back into a raw Sort mismatch, the Pi arm of
-- `infer_level_for_type` has regressed to generating nothing.

universe u v

def tid (γ : Type) (c : γ) : γ := c

def bad {α : Type u} {β : Type v} (f : α → β) : α → β := tid _ f
