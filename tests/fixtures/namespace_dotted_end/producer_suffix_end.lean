-- Producer module for the MULTI-component partial `end`: `end B.C` against
-- `namespace A.B.C` closes exactly TWO of the three components.
--
-- This is the fixture that separates Lean's real rule from the convenient
-- approximation "a partial `end` closes its leaf". Under that approximation
-- `end B.C` would close only `C` and `mid` would register as `A.B.mid`.
--
-- Ground truth, Lean 4.30.0-rc2 (`set_option pp.fullNames true`):
--
--   A.B.C.deep : Nat
--   A.mid : Nat
--
-- The shape is live in Mathlib: `Mathlib/Tactic/LinearCombination/Lemmas.lean`
-- opens `Mathlib.Tactic.LinearCombination` at line 24 and closes it at line 196
-- with `end Tactic.LinearCombination`, leaving `Mathlib` open for what follows.
namespace A.B.C

def deep : Nat := 1

end B.C

def mid : Nat := 2

end A
