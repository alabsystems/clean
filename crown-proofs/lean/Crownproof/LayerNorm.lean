/-
  LayerNorm CROWN-relaxation END-TO-END SOUNDNESS, formalized in Lean 4 over
  the rationals, using mathlib and the three supporting modules of this project.

  Pipeline of one LayerNorm output coordinate
  -------------------------------------------
  Given a (centered) input feature `c` and the normalizer

        t = rsqrt(var + eps) = 1 / √(var + eps),

  the LayerNorm output coordinate is the affine-after-bilinear

        y = gamma * (c * t) + beta.

  CROWN relaxes this exactly the way `crown_bridge` (see `Bridge.lean`) relaxes a
  ReLU layer: every nonlinearity is replaced by a pair of sound linear bounds and
  the genuine value is treated as a BOUNDED VARIABLE constrained to its envelope
  interval.  Here there are two nonlinear ingredients:

    * the normalizer `t`, whose value lies in the rsqrt envelope interval
      `[tl, th]` produced by the secant/tangent bounds of `Crownproof.Rsqrt`
      (`rsqrt_lower` / `rsqrt_upper`).  On a genuine execution `t` is the true
      `rsqrt(var+eps)` and `tl ≤ t ≤ th` holds; we carry that interval as the
      `t`-box premises.  (The rational endpoints `tl, th` are exactly what the
      certificate emitter computes from the real-valued envelopes; their
      soundness is `Rsqrt.rsqrt_lower`/`rsqrt_upper`, and here they enter as the
      validity hypothesis `htlo`/`hthi` on the genuine state.)

    * the bilinear product `p = c * t`, relaxed by the four McCormick planes of
      `Crownproof.McCormick`.  These four are PROVEN sound on every genuine
      state directly from `mccormick_lower1/2` and `mccormick_upper1/2`.

  The output `y = gamma * p + beta` is affine, so — exactly as in `crown_bridge`
  — the verifier folds the affine equalities in directly and the Farkas
  certificate is a choice of non-negative multipliers combining the premise LHSs
  to `-(y) - c0`.

  `layernorm_bridge` is then `farkas_to_interval` for this LayerNorm coordinate,
  proven sorry-free by reduction to `farkas_premise_combination`, with the eight
  premises packed into a `Fin 8` family — EXACTLY the `crown_bridge` pattern.

  What is PROVEN vs. what is HYPOTHESIS
  -------------------------------------
  * PROVEN here, sorry-free: the four McCormick product premises are sound on
    every genuine state (reusing the imported McCormick lemmas); the box premises
    are sound; the abstract Farkas combination yields the certified bound.
  * HYPOTHESIS on the genuine state: that the true normalizer `t` lies in the
    rational envelope interval `[tl, th]`.  This is precisely the content of
    `Rsqrt.rsqrt_lower`/`rsqrt_upper` (proven sorry-free over ℝ in `Rsqrt.lean`);
    we consume it as the interval membership `tl ≤ st.t ≤ th` so the whole bridge
    stays in ℚ and is sorry-free.  Likewise `cl ≤ st.c ≤ ch` is the (input) box.
-/

import Crownproof.Rsqrt
import Crownproof.McCormick
import Crownproof.Variance
import Crownproof.Bridge
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof

open Finset

/-! ## 1. The LayerNorm coordinate state.

A genuine execution of one LayerNorm output coordinate carries:
  c : the centered input feature       (bounded, `cl ≤ c ≤ ch`)
  t : the normalizer `rsqrt(var+eps)`  (bounded by its rsqrt envelope, `tl ≤ t ≤ th`)
  p : the product `c * t`              (relaxed by McCormick, `p = c * t`)
  y : the output `gamma*p + beta`      (affine) -/
structure LNState where
  c : ℚ
  t : ℚ
  p : ℚ
  y : ℚ

/-- A `LNState` is a *genuine LayerNorm execution* for parameters
    `(gamma, beta)` on the boxes `c ∈ [cl,ch]`, `t ∈ [tl,th]` iff the two box
    memberships hold, the product is exact (`p = c*t`), and the output is the
    affine map (`y = gamma*p + beta`).

    The `t`-box membership is exactly the soundness conclusion of the rsqrt
    secant/tangent envelopes (`Crownproof.Rsqrt.rsqrt_lower`/`rsqrt_upper`),
    transported to the rational envelope endpoints `tl, th`. -/
def LNState.valid (gamma beta cl ch tl th : ℚ) (st : LNState) : Prop :=
  cl ≤ st.c ∧ st.c ≤ ch ∧
  tl ≤ st.t ∧ st.t ≤ th ∧
  st.p = st.c * st.t ∧
  st.y = gamma * st.p + beta

/-! ## 2. The eight relaxed-LayerNorm premises (each `lhs ≤ 0`).

Indexed by `Fin 8`:
  0  box_c_lo :  cl - c                       ≤ 0
  1  box_c_hi :  c - ch                        ≤ 0
  2  box_t_lo :  tl - t                        ≤ 0     (rsqrt lower envelope endpoint)
  3  box_t_hi :  t - th                        ≤ 0     (rsqrt upper envelope endpoint)
  4  mcc_lo1  :  (cl*t + c*tl - cl*tl) - p     ≤ 0     McCormick lower 1
  5  mcc_lo2  :  (ch*t + c*th - ch*th) - p     ≤ 0     McCormick lower 2
  6  mcc_up1  :  p - (ch*t + c*tl - ch*tl)     ≤ 0     McCormick upper 1
  7  mcc_up2  :  p - (cl*t + c*th - cl*th)     ≤ 0     McCormick upper 2 -/
def lnPremiseFun (cl ch tl th : ℚ) : Fin 8 → LNState → ℚ
  | 0, st => cl - st.c
  | 1, st => st.c - ch
  | 2, st => tl - st.t
  | 3, st => st.t - th
  | 4, st => (cl * st.t + st.c * tl - cl * tl) - st.p
  | 5, st => (ch * st.t + st.c * th - ch * th) - st.p
  | 6, st => st.p - (ch * st.t + st.c * tl - ch * tl)
  | 7, st => st.p - (cl * st.t + st.c * th - cl * th)

/-- Soundness of each LayerNorm premise on genuine executions.  The four
    McCormick product premises are discharged by the imported
    `mccormick_lower1/2` / `mccormick_upper1/2`; the box premises are immediate. -/
theorem lnPremiseFun_sound
    (gamma beta cl ch tl th : ℚ) :
    ∀ i : Fin 8, ∀ st : LNState,
      LNState.valid gamma beta cl ch tl th st →
        lnPremiseFun cl ch tl th i st ≤ 0 := by
  intro i st hv
  obtain ⟨hcl, hch, htl, hth, hpeq, hyeq⟩ := hv
  fin_cases i
  · -- box_c_lo
    simp only [lnPremiseFun]; linarith
  · -- box_c_hi
    simp only [lnPremiseFun]; linarith
  · -- box_t_lo
    simp only [lnPremiseFun]; linarith
  · -- box_t_hi
    simp only [lnPremiseFun]; linarith
  · -- mcc_lo1 :  (McCormick lower 1) - p ≤ 0,  using p = c*t
    simp only [lnPremiseFun]
    rw [hpeq]
    have := mccormick_lower1 (a := st.c) (b := st.t)
              (al := cl) (bl := tl) (ah := ch) (bh := th) hcl htl
    linarith
  · -- mcc_lo2 :  (McCormick lower 2) - p ≤ 0,  using p = c*t
    simp only [lnPremiseFun]
    rw [hpeq]
    have := mccormick_lower2 (a := st.c) (b := st.t)
              (al := cl) (bl := tl) (ah := ch) (bh := th) hch hth
    linarith
  · -- mcc_up1 :  p - (McCormick upper 1) ≤ 0,  using p = c*t
    simp only [lnPremiseFun]
    rw [hpeq]
    have := mccormick_upper1 (a := st.c) (b := st.t)
              (al := cl) (bl := tl) (ah := ch) (bh := th) hch htl
    linarith
  · -- mcc_up2 :  p - (McCormick upper 2) ≤ 0,  using p = c*t
    simp only [lnPremiseFun]
    rw [hpeq]
    have := mccormick_upper2 (a := st.c) (b := st.t)
              (al := cl) (bl := tl) (ah := ch) (bh := th) hcl hth
    linarith

/-! ## 3. The LayerNorm end-to-end bridge.

Same shape as `crown_bridge`: a non-negative multiplier vector that combines the
eight relaxed-LayerNorm premises into `-(y) - c0` (as a function of the state)
certifies `y ≥ -c0` on every genuine execution.  Proven by reduction to
`farkas_premise_combination`, packing the eight multipliers/premises into a
`Fin 8` family. -/
theorem layernorm_bridge
    (gamma beta cl ch tl th c0 : ℚ)
    (m_cl m_ch m_tl m_th m_l1 m_l2 m_u1 m_u2 : ℚ)
    (h_cl : 0 ≤ m_cl) (h_ch : 0 ≤ m_ch)
    (h_tl : 0 ≤ m_tl) (h_th : 0 ≤ m_th)
    (h_l1 : 0 ≤ m_l1) (h_l2 : 0 ≤ m_l2)
    (h_u1 : 0 ≤ m_u1) (h_u2 : 0 ≤ m_u2)
    -- Farkas certificate identity: the μ-combination of premise LHSs IS -(y) - c0.
    (hcert : ∀ st : LNState,
        m_cl * (cl - st.c)
      + m_ch * (st.c - ch)
      + m_tl * (tl - st.t)
      + m_th * (st.t - th)
      + m_l1 * ((cl * st.t + st.c * tl - cl * tl) - st.p)
      + m_l2 * ((ch * st.t + st.c * th - ch * th) - st.p)
      + m_u1 * (st.p - (ch * st.t + st.c * tl - ch * tl))
      + m_u2 * (st.p - (cl * st.t + st.c * th - cl * th))
        = -(st.y) - c0) :
    ∀ st : LNState, LNState.valid gamma beta cl ch tl th st → -c0 ≤ st.y := by
  refine farkas_premise_combination (S := LNState) (ι := Fin 8)
        (premises := Finset.univ)
        (g := lnPremiseFun cl ch tl th)
        (out := fun st => st.y)
        (μ := ![m_cl, m_ch, m_tl, m_th, m_l1, m_l2, m_u1, m_u2]) (c := c0)
        (valid := LNState.valid gamma beta cl ch tl th)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _
    fin_cases i
    · simpa using h_cl
    · simpa using h_ch
    · simpa using h_tl
    · simpa using h_th
    · simpa using h_l1
    · simpa using h_l2
    · simpa using h_u1
    · simpa using h_u2
  case hg =>
    intro i _ st hv
    exact lnPremiseFun_sound gamma beta cl ch tl th i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_eight, lnPremiseFun, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.cons_val]
    have h := hcert st
    linarith [h]

/-! ## 4. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms lnPremiseFun_sound
#print axioms layernorm_bridge

end Crownproof
