-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- The ANTI-VACUITY fixture of bricks VC-3 and VC-5
-- (designs/2026-08-28-variant-codata-surface.md SS4).
--
-- The codata is DECLARED and everything above the `--` rule is GENERATED:
-- `ITr`, `ITr.shapeF/posF/tgtF`, `ITr.mkStep`, the five constructors,
-- `ITr.head`, every `rfl` law, the corecursor tier, the five head classifiers
-- `ITr.isRet` ... `ITr.isDelay`, all TEN disjointness theorems
-- `ITr.Cj_ne_Ck`, and the payload retraction + injectivity of `Ret` and `Vis`.
-- Everything below is hand-written and cites only generated names.
--
-- WHY IT EXISTS. A degenerate `shapeF` -- one that mapped every constructor to
-- the SAME tag -- would satisfy every generated `rfl` computation law, because
-- each law is stated against the very tag the generator chose. All of
-- `head_Ret`, `head_Tau`, `head_Vis`, `head_Br`, `head_Delay`, `child_Tau`,
-- `child_Vis`, `child_Br_0`, `child_Br_1`, `child_Delay` would still
-- kernel-check. Only DISJOINTNESS fails: `ITr.Cj x = ITr.Ck y -> False` needs
-- the two heads to be provably different tags.
--
-- `Tau` and `Delay` are DELIBERATELY the same shape -- one bare child, no
-- payload -- so their P and Q are literally identical types. That is the pair a
-- degenerate tag assignment could collapse without any type error anywhere, and
-- `ITr.Tau_ne_Delay` is the only declaration that would notice. (MEASURED at
-- VC-3: collapsing `Delay`'s tag onto `Tau`'s leaves all five head laws, both
-- child laws and the whole container kernel-checking.)
--
-- Replayed by
-- `codata_variant_generate_tests::test_generated_family_proves_constructor_disjointness`.

codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
  | Br : ITr E R Ans → ITr E R Ans → ITr E R Ans
  | Delay : ITr E R Ans → ITr E R Ans

-- ── consumers: the generated companions used, not merely registered ──

-- the same-shaped pair, in `Not` form
theorem ITr.tau_not_delay (E : Type) (R : Type) (Ans : E → Type) (x : ITr E R Ans) :
    Not (ITr.Tau E R Ans x = ITr.Delay E R Ans x) :=
  fun h => ITr.Tau_ne_Delay E R Ans x x h

-- a two-tag-deep pair (inr-inl vs inr-inr-inl)
theorem ITr.tau_not_vis (E : Type) (R : Type) (Ans : E → Type) (x : ITr E R Ans) (e : E)
    (k : Ans e → ITr E R Ans) : Not (ITr.Tau E R Ans x = ITr.Vis E R Ans e k) :=
  fun h => ITr.Tau_ne_Vis E R Ans x e k h

-- symmetry is derivable from the generated (ordered) statement
theorem ITr.br_not_ret (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans)
    (m : ITr E R Ans) (r : R) : Not (ITr.Br E R Ans l m = ITr.Ret E R Ans r) :=
  fun h => ITr.Ret_ne_Br E R Ans r l m (Eq.symm h)

-- payload injectivity, used to move an equation backwards through `Ret`
theorem ITr.ret_eq_of_eq (E : Type) (R : Type) (Ans : E → Type) (a : R) (b : R)
    (h : ITr.Ret E R Ans a = ITr.Ret E R Ans b) : b = a :=
  Eq.symm (ITr.Ret_inj E R Ans a b h)

-- `Vis`'s payload is its event; the continuation is NOT recoverable this way
-- (its type moves with the event), which is exactly the boundary VC-5 draws.
theorem ITr.vis_event_inj (E : Type) (R : Type) (Ans : E → Type) (e : E)
    (k : Ans e → ITr E R Ans) (e0 : E) (k0 : Ans e0 → ITr E R Ans)
    (h : ITr.Vis E R Ans e k = ITr.Vis E R Ans e0 k0) : e = e0 :=
  ITr.Vis_inj E R Ans e k e0 k0 h
