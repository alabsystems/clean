-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- VC-6/VC-6b corner shapes the ITr fixture does NOT reach.
--
-- ITr's four constructors cover the four POSITION shapes, but every one of
-- them has at most one payload and at least one recursive argument. Two
-- corners were therefore reasoned about and never exercised:
--
--   Nil  -- NULLARY: no payload and no child, so its `CasesP` disjunct is a
--           bare equation with no existential at all, and its eta law has
--           no extractor.
--   Stream1 -- a SINGLE-constructor codata. `cases_tower` takes a wholly
--              different branch: with one constructor there is no `Sum` at
--              all, so no `sumCases` is emitted and the head equation is
--              `rfl` rather than a folded chain of injections.
--   Tri.Three -- the LAST constructor of a 3-way codata, carrying PAYLOADS.
--              ITr's last constructor (`Br`) has none, so the last-leaf
--              projection path had only ever run at payload arity 0.
--   Pair -- TWO payloads: `Pₖ` is a right-nested `PProd`, so the `T.cases`
--           leaf must recover each payload by PROJECTION and the head
--           equation it hands the eta law is `tag (PProd.mk p.1 p.2)`
--           against a bound `p`. That step relies on structure eta holding
--           definitionally in the kernel -- which it does, and this fixture
--           is what says so.
--
-- Replayed by `codata_variant_coind_tests::test_corner_shapes_check`.

codata Two (A : Type) (B : Type) where
  | Nil : Two A B
  | Pair : A → B → Two A B → Two A B
deriving Coind

theorem Two.nil_cases (A : Type) (B : Type) : Two.CasesP A B (Two.Nil A B) :=
  Two.cases A B (Two.Nil A B)

theorem Two.pair_cases (A : Type) (B : Type) (a : A) (b : B) (t : Two A B) :
    Two.CasesP A B (Two.Pair A B a b t) :=
  Two.cases A B (Two.Pair A B a b t)

theorem Two.pair_eta_used (A : Type) (B : Type) (a : A) (b : B) (t : Two A B) :
    Two.Pair A B a b t
      = Two.Pair A B a b (Two.PairChild A B (Two.Pair A B a b t) a b rfl) :=
  Two.Pair_eta A B (Two.Pair A B a b t) a b rfl

-- ── single-constructor codata: no `Sum`, so no `sumCases` and an `rfl` head
codata Stream1 (A : Type) where
  | Cons : A → Stream1 A → Stream1 A
deriving Coind

theorem Stream1.cases_used (A : Type) (s : Stream1 A) : Stream1.CasesP A s :=
  Stream1.cases A s

theorem Stream1.eta_used (A : Type) (a : A) (t : Stream1 A) :
    Stream1.Cons A a t
      = Stream1.Cons A a (Stream1.ConsChild A (Stream1.Cons A a t) a rfl) :=
  Stream1.Cons_eta A (Stream1.Cons A a t) a rfl

-- ── three constructors whose LAST one carries payloads
codata Tri (A : Type) where
  | One : Tri A → Tri A
  | Two : A → Tri A → Tri A
  | Three : A → A → Tri A → Tri A
deriving Coind

theorem Tri.cases_used (A : Type) (t : Tri A) : Tri.CasesP A t :=
  Tri.cases A t

theorem Tri.three_eta_used (A : Type) (a : A) (b : A) (t : Tri A) :
    Tri.Three A a b t
      = Tri.Three A a b (Tri.ThreeChild A (Tri.Three A a b t) a b rfl) :=
  Tri.Three_eta A (Tri.Three A a b t) a b rfl
