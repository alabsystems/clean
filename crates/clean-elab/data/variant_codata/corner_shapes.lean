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
