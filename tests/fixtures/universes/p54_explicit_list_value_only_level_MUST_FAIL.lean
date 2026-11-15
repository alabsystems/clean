-- P54 — a universe level left undetermined only in a declaration's VALUE is
-- refused when the declaration wrote a `.{...}` list, as Lean refuses it.
-- Added 2026-10-19 as p21's MUST_FAIL twin.
--
-- Lean generalizes a leftover level metavariable into an extra parameter only
-- when the declaration's TYPE mentions it (`levelMVarToParamTypesPreDecls`,
-- `Lean/Elab/MutualDef.lean:1406`); one left in the body is an error.
-- Measured on the pinned v4.30.0-rc2 `lean`:
--
--   error: declaration `useZ` contains universe level metavariables at the
--   expression z.{?u.23 + 1} (Sort ?u.23) in the declaration body
--
-- `z` itself is the control and passes. Lean refuses the same body with no
-- written list too; Clean still generalizes it there (the OPEN half of
-- `docs/FRONTEND_CLASS_LEDGER.md` class (164)), so this probe writes one.
def z.{v} (x : Sort v) : Nat := 0

def useZ.{u} (A : Type u) : Nat := z (Sort _)
