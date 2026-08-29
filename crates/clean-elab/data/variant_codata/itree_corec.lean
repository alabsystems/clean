-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- The ANTI-VACUITY fixture of brick VC-4
-- (designs/2026-08-28-variant-codata-surface.md SS4).
--
-- The codata is DECLARED; `ITr.Step`, `ITr.step_Ret/Tau/Vis/Br`, `ITr.corec`
-- and the corecursor's computation laws are all GENERATED. Everything below
-- the declaration is hand-written and cites only generated names.
--
-- WHY IT EXISTS. `ITr.head_spin` alone proves nothing about corecursion: a
-- `corec` that ignored its coalgebra and returned a FINITE `Tau` chain would
-- satisfy it, because the head of `Tau x` is the `Tau` tag whatever `x` is.
-- The law that separates them is `ITr.child_spin` -- the child of `spin` is
-- `spin` ITSELF, by `rfl`. A finite chain's child is one layer shorter, so it
-- fails. (MEASURED against the hand-written target's own corecursor: with
-- `ITr.Tau (ITr.Tau x)` in place of `spin`, the head law still kernel-checks
-- and the child law fails with a `Subtype.mk ... = Subtype.mk ...` type
-- mismatch on the approximation stream.)
--
-- `ITr.visLoop` covers the second half of the brick: a step builder that
-- carries a PAYLOAD and whose child function is indexed by a
-- payload-dependent position type (`Ans e -> S`), rather than the one-point
-- position `spin` uses.
--
-- Replayed by
-- `codata_variant_generate_tests::test_generated_corecursor_builds_an_infinite_value`.

codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
  | Br : ITr E R Ans → ITr E R Ans → ITr E R Ans

-- an infinite Tau chain: one-point state, `Tau` forever
def ITr.spin (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s) PUnit.unit

theorem ITr.head_spin (E : Type) (R : Type) (Ans : E → Type) :
    ITr.head E R Ans (ITr.spin E R Ans) = Sum.inr (Sum.inl PUnit.unit) := rfl

-- THE anti-vacuity law: unfolding never terminates, definitionally.
theorem ITr.child_spin (E : Type) (R : Type) (Ans : E → Type)
    (b : ITr.posF E R Ans PUnit.unit (Sum.inr (Sum.inl PUnit.unit))) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.spin E R Ans) b = ITr.spin E R Ans := rfl

-- the same, routed through the GENERATED generic law rather than by `rfl`
theorem ITr.child_spin_via_law (E : Type) (R : Type) (Ans : E → Type)
    (b : ITr.posF E R Ans PUnit.unit
      (ITr.head E R Ans
        (ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s)
          PUnit.unit))) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.spin E R Ans) b = ITr.spin E R Ans :=
  ITr.child_corec E R Ans PUnit.{1} (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s)
    PUnit.unit b

-- a payload-carrying corecursion whose positions are `Ans e`
def ITr.visLoop (E : Type) (R : Type) (Ans : E → Type) (e : E) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Vis E R Ans PUnit.{1} j e (fun _ => s))
    PUnit.unit

theorem ITr.head_visLoop (E : Type) (R : Type) (Ans : E → Type) (e : E) :
    ITr.head E R Ans (ITr.visLoop E R Ans e) = Sum.inr (Sum.inr (Sum.inl e)) := rfl

theorem ITr.child_visLoop (E : Type) (R : Type) (Ans : E → Type) (e : E) (a : Ans e) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.visLoop E R Ans e) a = ITr.visLoop E R Ans e := rfl

-- spin is not a Ret, by the generated head laws. Hand-written rather than
-- cited from VC-5, so that this file measures VC-4 on its own: `spin` is not
-- a constructor, so no generated `_ne_` theorem mentions it.
def ITr.isInl {X : Type} {Y : Type} (v : Sum X Y) : Prop :=
  @Sum.rec X Y (fun _ => Prop) (fun _ => True) (fun _ => False) v

theorem ITr.Ret_ne_spin (E : Type) (R : Type) (Ans : E → Type) (r : R)
    (h : ITr.Ret E R Ans r = ITr.spin E R Ans) : False :=
  @Eq.rec (ITr.shapeF E R Ans PUnit.unit) (Sum.inl r) (fun v _ => ITr.isInl v) True.intro
    (Sum.inr (Sum.inl PUnit.unit))
    (Eq.trans (Eq.symm (ITr.head_Ret E R Ans r))
      (Eq.trans (congrArg (fun z : ITr E R Ans => ITr.head E R Ans z) h)
        (ITr.head_spin E R Ans)))
