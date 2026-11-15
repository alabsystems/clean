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

-- ── REGRESSION PINS for the two generator bugs found 2026-08-29 (§12).
-- Both were pre-existing, both hit ordinary shapes, and neither had
-- anything to do with the k-fold/indexed-family shape that VC-6 had
-- (wrongly) refused.

-- Bug 1 — a single constructor whose FIRST argument is recursive. The case
-- tower's `Exists.intro` had its predicate left implicit; with the goal
-- behind the `CasesP` definition and the witness a compound extractor
-- application, `?p` is not a Miller pattern and the unifier poisoned it.
-- Multi-constructor codata escaped only because `Or.inl` pinned the shape
-- first. This is the minimal case, and it is an ordinary infinite chain.
codata Sc (A : Type) where
  | C : Sc A → Sc A
deriving Coind

theorem Sc.cases_used (A : Type) (t : Sc A) : Sc.CasesP A t := Sc.cases A t

-- the same bug at k-fold arity, with an INDEXED FAMILY summand: the exact
-- shape VC-6 used to refuse as "no worked precedent". It works.
codata Mx (A : Type) where
  | Mix : Mx A → (A → Mx A) → Mx A
deriving Coind

theorem Mx.cases_used (A : Type) (t : Mx A) : Mx.CasesP A t := Mx.cases A t

theorem Mx.eta_used (A : Type) (l : Mx A) (k : A → Mx A) :
    Mx.Mix A l k
      = Mx.Mix A (Mx.MixChild0 A (Mx.Mix A l k) rfl)
          (Mx.MixChild1 A (Mx.Mix A l k) rfl) :=
  Mx.Mix_eta A (Mx.Mix A l k) rfl

-- Bug 2 — a payload AFTER a recursive argument. The existential binder
-- rebound the payload under its primary name and CAPTURED it inside the
-- already-built child-extractor witness, so the extractor got the bound
-- variable where the lemma's binder was meant.
codata Cp (A : Type) where
  | C : Cp A → A → Cp A
deriving Coind

theorem Cp.cases_used (A : Type) (t : Cp A) : Cp.CasesP A t := Cp.cases A t

-- payload BETWEEN two children, so the capture is not merely a tail case
codata Iv (A : Type) where
  | C : Iv A → A → Iv A → Iv A
deriving Coind

theorem Iv.cases_used (A : Type) (t : Iv A) : Iv.CasesP A t := Iv.cases A t

-- a family domain that MENTIONS a payload, with the payload first: the
-- control for the re-spelling rule (`source` vs `in_alt`) that the capture
-- fix introduced — get it wrong and this stops elaborating.
codata Dv (E : Type) (Ans : E → Type) where
  | V : (e : E) → (Ans e → Dv E Ans) → Dv E Ans → Dv E Ans
deriving Coind

theorem Dv.cases_used (E : Type) (Ans : E → Type) (t : Dv E Ans) :
    Dv.CasesP E Ans t :=
  Dv.cases E Ans t
