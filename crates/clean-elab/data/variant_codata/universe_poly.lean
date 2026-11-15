-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- UNIVERSE-POLYMORPHIC variant codata (`codata T.{u}`), with the whole
-- coinductive tier.
--
-- VC-1 refused this until 2026-08-29 ("outside the VC1 envelope — VC1 is
-- monomorphic `Type`"). The seed library was ALREADY the two-universe
-- `.{u, v}` sibling, designed to be instantiated at `v := u` for exactly
-- this lane, so the lift is a re-spelling of pinned levels rather than new
-- machinery: `PUnit.{1}` -> `PUnit.{u+1}`, `PEmpty.{1}` -> `PEmpty.{u+1}`,
-- `Type` -> `Type u`, plus stamping `.{u}` on every generated head.
--
-- NO `Codata.*` reference carries a universe pin. The level solver derives
-- `?u := u, ?v := u` from the `PUnit.{u+1}` index and the `Type u` families.
--
-- THE ANTI-VACUITY BAR. Instantiating only at `Nat` would prove nothing: a
-- fresh level metavariable that silently solves to 0 yields a well-typed,
-- kernel-accepted, but strictly WEAKER declaration — the same hazard that
-- made `elab_hole` pin every `_` to `Sort 1` (CLAUDE.md, 75ce06eaa). So the
-- carrier is instantiated at a TYPE-valued parameter below, which is
-- impossible in the monomorphic lane.
--
-- Replayed by `codata_variant_coind_tests::test_universe_polymorphic_fixture`.

codata St.{u} (A : Type u) where
  | Nil : St A
  | Cons : A → St A → St A
deriving Coind

-- `St.{1} Type` — the carrier at `Type 1`, unreachable monomorphically.
def bigNil : St.{1} Type := St.Nil.{1} Type

theorem big_cases : St.CasesP.{1} Type bigNil := St.cases.{1} Type bigNil

-- the eta law, at `u := 0`
theorem cons_eta (A : Type) (a : A) (t : St.{0} A) :
    St.Cons A a t = St.Cons A a (St.ConsChild A (St.Cons A a t) a rfl) :=
  St.Cons_eta A (St.Cons A a t) a rfl

-- ANTI-VACUITY: a corec-built infinite value, and its unfolding proved ONLY
-- through the eta law. `rfl` does not prove this (the approximation towers
-- differ), so the coinduction tier is doing real work at `.{u}` too.
def forever.{u} (A : Type u) (a : A) : St.{u} A :=
  St.corec.{u} A PUnit.{u+1}
    (fun j s => St.step_Cons.{u} A PUnit.{u+1} j a s) PUnit.unit

theorem forever_unfolds.{u} (A : Type u) (a : A) :
    forever.{u} A a = St.Cons A a (forever.{u} A a) :=
  St.Cons_eta A (forever.{u} A a) a rfl

-- ── The `T.{u}` SELF-REFERENCE spelling, which is the natural one to write
-- under `codata T.{u}` and was refused until 2026-08-29. Two defects sat
-- behind that: `is_self_at_params` wanted a bare `Ident` head, and — the one
-- that actually produced the confusing message — `walk` did not descend into
-- a `UniverseInst`, so `mentions(T.{u} A, "T")` was FALSE and a recursive
-- argument written that way was classified as a PAYLOAD. The declaration was
-- then refused for "no constructor has a recursive argument", which names
-- the wrong problem entirely.
codata Sf.{u} (A : Type u) where
  | Nil : Sf.{u} A
  | Cons : A → Sf.{u} A → Sf.{u} A
deriving Coind

theorem sf_cases.{u} (A : Type u) (s : Sf.{u} A) : Sf.CasesP.{u} A s :=
  Sf.cases.{u} A s

-- and the two spellings mix freely within one declaration
codata Mixed.{u} (A : Type u) where
  | C : A → Mixed A → Mixed.{u} A
deriving Coind

theorem mixed_cases.{u} (A : Type u) (m : Mixed.{u} A) : Mixed.CasesP.{u} A m :=
  Mixed.cases.{u} A m
