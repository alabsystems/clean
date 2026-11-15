-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- VC-7's first obstacle, CLOSED and pinned.
--
-- ITreeEco's ITree carrier is hand-rolled (predating the `codata` command).
-- The question that decides whether VC-7 is a redefinition or a rewrite is
-- whether the GENERATED descriptor is DEFINITIONALLY equal to it. It was
-- not: ITreeEco declared its own empty inductive `NoPos` where the
-- generator emits `PEmpty`, and two distinct inductives are not defeq
-- however similar (designs/2026-08-28-variant-codata-surface.md §14).
--
-- ITreeEco now uses `PEmpty` (mapping `NoPos.{u}` -> `PEmpty.{u+1}`, and
-- correspondingly `NoPos.rec.{v, u}` -> `PEmpty.rec.{v, u+1}` at the three
-- sites carrying explicit universes). It still checks — 716 declarations,
-- one fewer than before because the `inductive NoPos` line is gone.
--
-- This fixture pins the PAYOFF: the generated position functor and the
-- generated carrier are definitionally equal to ITreeEco's, so the 716
-- declarations built on that carrier would survive a redefinition. If
-- either side drifts, `rfl` stops checking here.
--
-- Replayed by `codata_variant_coind_tests::test_itree_carrier_is_defeq`.

codata ITr.{u} (E : Type u) (R : Type u) (Ans : E → Type u) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
deriving Coind

-- ITreeEco's descriptor AFTER the NoPos -> PEmpty substitution
def itreeShape.{u} (E : Type u) (R : Type u) : Type u := Sum R (Sum PUnit.{u+1} E)

def itreePos.{u} (E : Type u) (R : Type u) (Ans : E → Type u) :
    itreeShape E R → Type u :=
  fun s =>
    @Sum.rec R (Sum PUnit.{u+1} E) (fun _ => Type u)
      (fun _ => PEmpty.{u+1})
      (fun s2 =>
        @Sum.rec PUnit.{u+1} E (fun _ => Type u) (fun _ => PUnit.{u+1}) (fun e => Ans e) s2)
      s

-- THE QUESTION: is the generated position functor now definitionally equal
-- to the hand-rolled one, pointwise?
theorem pos_agrees.{u} (E : Type u) (R : Type u) (Ans : E → Type u)
    (s : ITr.shapeF.{u} E R Ans PUnit.unit) :
    ITr.posF.{u} E R Ans PUnit.unit s = itreePos.{u} E R Ans s := rfl

-- and the carrier itself
def ITree'.{u} (E : Type u) (Ans : E → Type u) (R : Type u) : Type u :=
  @Codata.IMIntl PUnit.{u+1} (fun _ => itreeShape.{u} E R)
    (fun _ s => itreePos.{u} E R Ans s) (fun _ _ _ => PUnit.unit) PUnit.unit

theorem carrier_agrees.{u} (E : Type u) (Ans : E → Type u) (R : Type u) :
    ITr.{u} E R Ans = ITree'.{u} E Ans R := rfl
