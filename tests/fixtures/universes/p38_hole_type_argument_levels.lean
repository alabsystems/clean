-- U2 — THE HOLE THAT STANDS FOR A TYPE: its callee's universe must be SOLVED,
-- not left free and generalized.
--
-- This is the Mathlib-source frontier's first failure, reduced. Measured
-- 2026-08-21 (docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md),
-- `Mathlib/Logic/Basic.lean:513`:
--
--     variable {α β : Sort*} {p : α → Prop}
--     theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _
--
--     Type mismatch: expected Sort(Param(u_3)), got Sort(Param(u_2))
--       in declaration 'forall_true_iff', at body of lambda
--
-- The frontier map read that as `Sort*` minting a fresh `u_n` per reference,
-- so the statement and the value placed `α` in different params. That is
-- REFUTED by `forallTrueIffExplicit` below and by the `Sort*` rows of p37:
-- `Sort*` is elaborated exactly once per declaration and works. Swapping the
-- `_` for an explicit `α` made every variant pass — `Sort*` in a section,
-- `Sort*` as a plain binder, and `universe u` / `Sort u` alike — and keeping
-- the `_` made every variant fail INCLUDING a fully concrete `{α : Type}`,
-- where the level cannot vary at all:
--
--     expected Sort(Param(u_1)), got Sort(Succ(Zero))
--
-- So the hole is the whole cause, and the level was not mis-solved — it was
-- never constrained. `elab_hole` mints `?h : ?t`, so `?h`'s recorded type is
-- the bare `FVar(?t)` even after `?t` stands for a real `Sort u_1`.
-- `unify_meta` matched that RAW type: `FVar` is not `Sort(_)` and carries no
-- level param, so neither the Sort arm nor `propagate_meta_type_levels` fired,
-- `impTrue`'s `u_1` stayed free of `α`'s `u_2`, `finalize_level_params`
-- generalized BOTH, and the kernel rejected the pair it was handed.
--
-- Fix: resolve the metavariable's type before dispatching on it (Lean's
-- `checkTypesAndAssign` runs on `instantiateMVars mvarType`).

theorem impTrue (α : Sort u) : (α → True) ↔ True :=
  Iff.intro (fun _ => True.intro) (fun _ _ => True.intro)

-- The frontier declaration, verbatim in shape: section variable + `_`.
section
variable {α β : Sort*} {p : α → Prop}

theorem forallTrueIff : (α → True) ↔ True := impTrue _
end

-- The control that isolated the cause: identical but for the explicit
-- argument. This one ALWAYS passed, which is what refuted the `Sort*`-mints-
-- twice reading.
section
variable {α : Sort*}

theorem forallTrueIffExplicit : (α → True) ↔ True := impTrue α
end

-- The concrete witness: no `Sort*`, no section, nothing polymorphic about the
-- binder — and it still failed, because the callee's level was unconstrained.
theorem forallTrueIffConcrete {α : Type} : (α → True) ↔ True := impTrue _

-- A declared rigid parameter through the same hole.
universe v
theorem forallTrueIffRigid {α : Sort v} : (α → True) ↔ True := impTrue _
