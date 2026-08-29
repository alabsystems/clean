-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- The TARGET output of the variant-codata generator, hand-written.
--
-- This is what `codata ITr (E R : Type) (Ans : E -> Type) where
--   | Ret : R -> ITr E R Ans
--   | Tau : ITr E R Ans -> ITr E R Ans
--   | Vis : (e : E) -> (Ans e -> ITr E R Ans) -> ITr E R Ans
--   | Br  : ITr E R Ans -> ITr E R Ans -> ITr E R Ans
-- must lower to (designs/2026-08-28-variant-codata-surface.md SS3). It is the
-- rank-9 hand-rolled ITree carrier
-- (data/graduation/clean-mtype/proof/ITreeEco.lean:754-855) with the names
-- abstracted, plus a fourth constructor so all FOUR position shapes appear in
-- one file:
--
--   Ret  ->  PEmpty.{1}            zero children
--   Tau  ->  PUnit.{1}             one child
--   Vis  ->  Ans e                 payload-DEPENDENT children
--   Br   ->  Sum PUnit.{1} PUnit.{1}   k children
--
-- Every declaration goes through the ordinary parse -> elaborate -> kernel
-- pipeline against the UNMODIFIED `Codata.*` seed; the leading record codata
-- is only there to trigger the lazy seed injection.
--
-- The `_ne_` theorems are the ANTI-VACUITY check: a lowering that collapsed
-- two constructor tags would still satisfy every `rfl` computation law above
-- and would fail only there. The corecursor tier carries its own:
-- `ITr.child_spin` is the law a FINITE value cannot satisfy.
--
-- Replayed by `codata_variant_tests::test_variant_lowering_target_kernel_checks`.

codata CodataSeeder (A : Type) where
  head : A
  tail : CodataSeeder A

def ITr.shapeF (E : Type) (R : Type) (Ans : E → Type) : PUnit.{1} → Type :=
  fun _ => Sum R (Sum PUnit.{1} (Sum E PUnit.{1}))

def ITr.posF (E : Type) (R : Type) (Ans : E → Type) :
    (i : PUnit.{1}) → ITr.shapeF E R Ans i → Type :=
  fun _ s =>
    @Sum.rec R (Sum PUnit.{1} (Sum E PUnit.{1})) (fun _ => Type)
      (fun _ => PEmpty.{1})
      (fun s2 =>
        @Sum.rec PUnit.{1} (Sum E PUnit.{1}) (fun _ => Type)
          (fun _ => PUnit.{1})
          (fun s3 =>
            @Sum.rec E PUnit.{1} (fun _ => Type)
              (fun e => Ans e)
              (fun _ => Sum PUnit.{1} PUnit.{1})
              s3)
          s2)
      s

def ITr.tgtF (E : Type) (R : Type) (Ans : E → Type) :
    (i : PUnit.{1}) → (a : ITr.shapeF E R Ans i) → ITr.posF E R Ans i a → PUnit.{1} :=
  fun _ _ _ => PUnit.unit

def ITr (E : Type) (R : Type) (Ans : E → Type) : Type :=
  @Codata.IMIntl PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit

def ITr.mkStep (E : Type) (R : Type) (Ans : E → Type)
    (a : ITr.shapeF E R Ans PUnit.unit)
    (f : (b : ITr.posF E R Ans PUnit.unit a) →
      Codata.IMIntl (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
        (ITr.tgtF E R Ans PUnit.unit a b)) :
    Codata.isigmaStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      (Codata.IMIntl (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)) PUnit.unit :=
  Sigma.mk a f

def ITr.Ret (E : Type) (R : Type) (Ans : E → Type) (r : R) : ITr E R Ans :=
  @Codata.IMmk PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit
    (ITr.mkStep E R Ans (Sum.inl r) (fun b => @PEmpty.rec (fun _ => ITr E R Ans) b))

def ITr.Tau (E : Type) (R : Type) (Ans : E → Type) (t0 : ITr E R Ans) : ITr E R Ans :=
  @Codata.IMmk PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit
    (ITr.mkStep E R Ans (Sum.inr (Sum.inl PUnit.unit)) (fun _ => t0))

def ITr.Vis (E : Type) (R : Type) (Ans : E → Type) (e : E) (k : Ans e → ITr E R Ans) :
    ITr E R Ans :=
  @Codata.IMmk PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit
    (ITr.mkStep E R Ans (Sum.inr (Sum.inr (Sum.inl e))) k)

def ITr.Br (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans) (r : ITr E R Ans) :
    ITr E R Ans :=
  @Codata.IMmk PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit
    (ITr.mkStep E R Ans (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))
      (fun b => @Sum.rec PUnit.{1} PUnit.{1} (fun _ => ITr E R Ans)
        (fun _ => l) (fun _ => r) b))

def ITr.head (E : Type) (R : Type) (Ans : E → Type) (x : ITr E R Ans) :
    ITr.shapeF E R Ans PUnit.unit :=
  @Codata.IMhead PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) PUnit.unit x

theorem ITr.head_Ret (E : Type) (R : Type) (Ans : E → Type) (r : R) :
    ITr.head E R Ans (ITr.Ret E R Ans r) = Sum.inl r := rfl

theorem ITr.head_Tau (E : Type) (R : Type) (Ans : E → Type) (t0 : ITr E R Ans) :
    ITr.head E R Ans (ITr.Tau E R Ans t0) = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem ITr.head_Vis (E : Type) (R : Type) (Ans : E → Type) (e : E) (k : Ans e → ITr E R Ans) :
    ITr.head E R Ans (ITr.Vis E R Ans e k) = Sum.inr (Sum.inr (Sum.inl e)) := rfl

theorem ITr.head_Br (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans) (r : ITr E R Ans) :
    ITr.head E R Ans (ITr.Br E R Ans l r) = Sum.inr (Sum.inr (Sum.inr PUnit.unit)) := rfl

theorem ITr.child_Tau (E : Type) (R : Type) (Ans : E → Type) (t0 : ITr E R Ans)
    (b : ITr.posF E R Ans PUnit.unit (Sum.inr (Sum.inl PUnit.unit))) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.Tau E R Ans t0) b = t0 := rfl

theorem ITr.child_Vis (E : Type) (R : Type) (Ans : E → Type) (e : E) (k : Ans e → ITr E R Ans)
    (b : Ans e) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.Vis E R Ans e k) b = k b := rfl

theorem ITr.child_Br_left (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans)
    (r : ITr E R Ans) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.Br E R Ans l r) (Sum.inl PUnit.unit) = l := rfl

theorem ITr.child_Br_right (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans)
    (r : ITr E R Ans) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.Br E R Ans l r) (Sum.inr PUnit.unit) = r := rfl

-- ── the corecursor tier (VC-4) ──
-- `Step` names the coalgebra's codomain in the codata's own vocabulary; each
-- `step_C` is the CONSTRUCTOR with the carrier replaced by the state, over
-- `umkStep` instead of `IMmk ∘ mkStep`; `corec` is `ucorec` at this container.

def ITr.Step (E : Type) (R : Type) (Ans : E → Type) (S : Type) (j : PUnit.{1}) : Type :=
  Codata.isigmaStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) (Codata.uFam S) j

def ITr.step_Ret (E : Type) (R : Type) (Ans : E → Type) (S : Type) (j : PUnit.{1}) (r : R) :
    ITr.Step E R Ans S j :=
  @Codata.umkStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) S j
    (Sum.inl r) (fun b => @PEmpty.rec (fun _ => S) b)

def ITr.step_Tau (E : Type) (R : Type) (Ans : E → Type) (S : Type) (j : PUnit.{1}) (t0 : S) :
    ITr.Step E R Ans S j :=
  @Codata.umkStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) S j
    (Sum.inr (Sum.inl PUnit.unit)) (fun _ => t0)

def ITr.step_Vis (E : Type) (R : Type) (Ans : E → Type) (S : Type) (j : PUnit.{1}) (e : E)
    (k : Ans e → S) : ITr.Step E R Ans S j :=
  @Codata.umkStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) S j
    (Sum.inr (Sum.inr (Sum.inl e))) k

def ITr.step_Br (E : Type) (R : Type) (Ans : E → Type) (S : Type) (j : PUnit.{1}) (l : S) (r : S) :
    ITr.Step E R Ans S j :=
  @Codata.umkStep (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) S j
    (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))
    (fun b => @Sum.rec PUnit.{1} PUnit.{1} (fun _ => S) (fun _ => l) (fun _ => r) b)

def ITr.corec (E : Type) (R : Type) (Ans : E → Type) (S : Type)
    (g : (j : PUnit.{1}) → S → ITr.Step E R Ans S j) (st : S) : ITr E R Ans :=
  @Codata.ucorec (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans) S g st

theorem ITr.head_corec (E : Type) (R : Type) (Ans : E → Type) (S : Type)
    (g : (j : PUnit.{1}) → S → ITr.Step E R Ans S j) (st : S) :
    ITr.head E R Ans (ITr.corec E R Ans S g st) = (g PUnit.unit st).1 := rfl

theorem ITr.child_corec (E : Type) (R : Type) (Ans : E → Type) (S : Type)
    (g : (j : PUnit.{1}) → S → ITr.Step E R Ans S j) (st : S)
    (b : ITr.posF E R Ans PUnit.unit (ITr.head E R Ans (ITr.corec E R Ans S g st))) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.corec E R Ans S g st) b
      = ITr.corec E R Ans S g ((g PUnit.unit st).2 b) := rfl

-- the divergent computation: an infinite Tau chain, by corecursion over the
-- one-point state. THE anti-vacuity value of this brick — the head law below
-- would also hold of a finite `Tau` chain, the child law would not.
def ITr.spin (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s) PUnit.unit

theorem ITr.head_spin (E : Type) (R : Type) (Ans : E → Type) :
    ITr.head E R Ans (ITr.spin E R Ans) = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem ITr.child_spin (E : Type) (R : Type) (Ans : E → Type)
    (b : ITr.posF E R Ans PUnit.unit (Sum.inr (Sum.inl PUnit.unit))) :
    @Codata.IMchild PUnit.{1} (ITr.shapeF E R Ans) (ITr.posF E R Ans) (ITr.tgtF E R Ans)
      PUnit.unit (ITr.spin E R Ans) b = ITr.spin E R Ans := rfl

def ITr.sumIsInl {X : Type} {Y : Type} (v : Sum X Y) : Prop :=
  @Sum.rec X Y (fun _ => Prop) (fun _ => True) (fun _ => False) v

theorem ITr.inl_ne_inr {X : Type} {Y : Type} (a : X) (b : Y)
    (h : @Sum.inl X Y a = @Sum.inr X Y b) : False :=
  @Eq.rec (Sum X Y) (Sum.inl a) (fun v _ => ITr.sumIsInl v) True.intro (Sum.inr b) h

theorem ITr.Ret_ne_Tau (E : Type) (R : Type) (Ans : E → Type) (r : R) (x : ITr E R Ans)
    (h : ITr.Ret E R Ans r = ITr.Tau E R Ans x) : False :=
  ITr.inl_ne_inr r (Sum.inl PUnit.unit)
    (Eq.trans (Eq.symm (ITr.head_Ret E R Ans r))
      (Eq.trans (congrArg (fun z : ITr E R Ans => ITr.head E R Ans z) h)
        (ITr.head_Tau E R Ans x)))

theorem ITr.Ret_ne_spin (E : Type) (R : Type) (Ans : E → Type) (r : R)
    (h : ITr.Ret E R Ans r = ITr.spin E R Ans) : False :=
  ITr.inl_ne_inr r (Sum.inl PUnit.unit)
    (Eq.trans (Eq.symm (ITr.head_Ret E R Ans r))
      (Eq.trans (congrArg (fun z : ITr E R Ans => ITr.head E R Ans z) h)
        (ITr.head_spin E R Ans)))
