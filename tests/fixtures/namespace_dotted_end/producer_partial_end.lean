-- Producer module for the PARTIAL `end` half of the namespace-pop defect.
--
-- Ground truth, Lean 4.30.0-rc2: the `end` NAME's component count sets the pop
-- width, not the `namespace` name's. `namespace Bundle.Pretriv` opens two
-- scopes; `end Pretriv` closes exactly ONE, so `Bundle` stays open and
-- `after_partial` registers as `Bundle.after_partial`:
--
--   $ lean p1.lean          -- set_option pp.fullNames true
--   Bundle.Pretriv.inner : Nat
--   Bundle.after_partial : Nat
--
-- Restoring the whole pre-`namespace` prefix (the root, here) registers a bare
-- `after_partial` instead -- which Lean rejects with
-- `Unknown identifier `after_partial``.
--
-- This shape is live in Mathlib: `Mathlib/Topology/VectorBundle/Basic.lean:78`
-- opens `Bundle.Pretrivialization`, closes it at line 152 with
-- `end Pretrivialization`, and declares 27 further declarations against the
-- `Bundle` that stays open.
namespace Bundle.Pretriv

def inner : Nat := 1

end Pretriv

def after_partial : Nat := 2

end Bundle
