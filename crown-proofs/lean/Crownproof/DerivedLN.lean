/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WAVE-6 PROGRAM 2 — GENUINE rsqrt(variance) LayerNorm, DERIVED not assumed.

Every previous block (TinyBlock, Block2, SoftmaxBridge, StackTwo) carried the
LayerNorm normalizer

      t = rsqrt(var + eps)   ∈ [tl, th]

as a HYPOTHESIS on the genuine state (the conclusion of `Rsqrt.lean`, transported
to rational endpoints).  The variance that t normalizes by was never connected to
the residual stream: the model multiplied `h * t` with `t ∈ [1/2,1]` ASSUMED.

This module closes that caveat.  It builds a transformer block whose LayerNorm
normalizer `t` is a CONSEQUENCE of the residual-stream box, through the COMPOSITION
of the two proven bridges:

  (i)  Variance.lean : from the residual-stream box `hvec j ∈ [hl, hh]` it derives
       the population variance interval

           0 ≤ var(hvec) ≤ B,    B = (hh − hl)^2

       via `Crownproof.var_nonneg` (left endpoint) and
       `Crownproof.var_upper_box_uniform` (right endpoint, the sum-of-squares /
       mean-spread relaxation).

  (ii) Rsqrt.lean : the reciprocal-square-root `t = rsqrt eps v = 1/√(v+eps)` is
       ANTITONE on `v ≥ 0` (`Crownproof.rsqrt_antitone`), so it maps the variance
       interval `[0, B]` to the t-interval

           rsqrt eps B  ≤  t  ≤  rsqrt eps 0.

So the t-box is `[tl, th] = [rsqrt eps B, rsqrt eps 0]`, and BOTH endpoints are
DERIVED from the h-box through Variance + Rsqrt — NOT assumed.  The carried
hypothesis `tl ≤ t ≤ th` of all earlier blocks is here a THEOREM
(`t_box_derived`).

The LayerNorm product `p_i = centered_i · t` is then McCormick-bounded exactly as
before (`mccormick_*_R`), and a small ReLU-MLP tail closes a concrete numeric
block bound `o ∈ [ol, oh]` via the abstract Farkas core
(`farkas_premise_combination_R`).

What is PROVEN vs. what is CARRIED
----------------------------------
DERIVED here, sorry-free (the whole point of this run):
  * the variance interval  0 ≤ var(hvec) ≤ B  — `var_box_derived`, from Variance;
  * the normalizer interval  rsqrt eps B ≤ t ≤ rsqrt eps 0  — `t_box_derived`,
    from Rsqrt (antitonicity), with `t = rsqrt eps (var hvec)` the GENUINE value;
  * the centered-feature box, the McCormick product box, the ReLU envelopes, and
    the composed block bound.
CARRIED real-analysis facts (used, all PROVEN sorry-free in the imported bridges):
  * `rsqrt_antitone` (rsqrt is decreasing) — proven in Rsqrt.lean from the implicit
    identity `t^2(v+eps)=1`, itself from `Real.sq_sqrt`;
  * `var_nonneg`, `var_upper_box_uniform`, `mean_mem_box`, `centered_sq_le_spread`
    — proven in Variance.lean by ordered-field / Finset reasoning.
NO fact about t is assumed: t is literally `rsqrt eps (var hvec)`.

`#print axioms` at the bottom must show exactly [propext, Classical.choice,
Quot.sound] and NEVER sorryAx.
-/

import Crownproof.Rsqrt          -- rsqrt, rsqrt_pos, rsqrt_antitone (ℝ)
import Crownproof.Variance       -- var, mean, centered, var_nonneg, var_upper_box_uniform (ℚ)
import Crownproof.GeluFull       -- mccormick_lower_R / upper1_R / upper2_R (ℝ)
import Crownproof.Block2         -- farkas_premise_combination_R (ℝ)
import Crownproof.Bridge         -- relu, relu_lower, relu_upper (ℚ → reused over ℝ? see below)
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof.DerivedLN

open Crownproof Crownproof.Block2 Finset Real

/-! ## 0. ReLU over ℝ (the MLP tail nonlinearity).

We need a ReLU and its two envelopes over ℝ to close the block tail.  Define them
locally and prove the two standard CROWN envelopes (lower slope-α line through 0,
upper secant chord) sorry-free. -/

/-- Real ReLU (`max 0 z`, matching the `Basic.relu` convention). -/
noncomputable def reluR (z : ℝ) : ℝ := max 0 z

/-- ReLU lower envelope over ℝ: `α·z ≤ relu z` for any slope `α ∈ [0,1]`.
    (The real-valued copy of `Basic.relu_lower`.) -/
theorem reluR_lower (alpha z : ℝ) (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    alpha * z ≤ reluR z := by
  unfold reluR
  rcases le_or_gt 0 z with hz | hz
  · have hmax : max 0 z = z := max_eq_right hz
    rw [hmax]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - alpha) hz]
  · have hmax : max 0 z = 0 := max_eq_left (le_of_lt hz)
    rw [hmax]
    exact mul_nonpos_of_nonneg_of_nonpos h0 (le_of_lt hz)

/-- ReLU upper chord over ℝ on `[l, u]` with `l < 0 < u` and chord slope
    `s = u/(u − l)` (passed via `s*(u−l)=u`): `relu z ≤ s·(z − l)`.
    (The real-valued copy of `Basic.relu_upper`.) -/
theorem reluR_upper (l u s z : ℝ)
    (hl : l < 0) (hu : 0 < u) (hs : s * (u - l) = u)
    (hzl : l ≤ z) (hzu : z ≤ u) : reluR z ≤ s * (z - l) := by
  have hul : 0 < u - l := by linarith
  have hs_nonneg : 0 ≤ s := by
    by_contra hneg
    rw [not_le] at hneg
    have hle : s * (u - l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hul)
    rw [hs] at hle; linarith
  unfold reluR
  rcases le_or_gt 0 z with hz | hz
  · have hmax : max 0 z = z := max_eq_right hz
    rw [hmax]
    have hlu : l * (u - z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hl) (by linarith)
    nlinarith [hs, hul, hlu]
  · have hmax : max 0 z = 0 := max_eq_left (le_of_lt hz)
    rw [hmax]
    exact mul_nonneg hs_nonneg (by linarith)

/-! ## 1. The residual-stream → variance → rsqrt-normalizer DERIVATION.

This is the KEY content of the run.  We fix a residual-stream width `n > 0`, a
uniform residual-stream box `[hl, hh]`, and a LayerNorm `eps > 0`.  We then prove:

  * `var_box_derived` : `0 ≤ var(hvec) ≤ (hh − hl)^2` for any `hvec` whose
    coordinates lie in `[hl, hh]`.  (Variance bridge.)

  * `t_box_derived` : the GENUINE normalizer `t = rsqrt eps (↑(var hvec))` lies in
    `[rsqrt eps ((hh−hl)^2), rsqrt eps 0]`.  (Rsqrt antitonicity over the derived
    variance interval.)  NOTHING about `t` is assumed: `t` is defined as the real
    `rsqrt` of the rational variance, cast to ℝ. -/

variable (n : ℕ) (eps hl hh : ℚ)

/-- The DERIVED variance upper endpoint `B = (hh − hl)^2`. -/
def varB : ℚ := (hh - hl) ^ 2

/-- **Variance interval, DERIVED from the residual-stream box.**
    For any `hvec` with every coordinate in `[hl, hh]`, the population variance
    of the residual stream lies in `[0, B]`, `B = (hh−hl)^2`.  Left endpoint is
    `var_nonneg`; right endpoint is `var_upper_box_uniform` (the sum-of-squares /
    mean-spread relaxation of Variance.lean). -/
theorem var_box_derived (hn : 0 < n) (hvec : Fin n → ℚ)
    (hlo : ∀ j, hl ≤ hvec j) (hhi : ∀ j, hvec j ≤ hh) :
    0 ≤ var n hvec ∧ var n hvec ≤ varB hl hh := by
  refine ⟨var_nonneg n hn hvec, ?_⟩
  simpa [varB] using var_upper_box_uniform n hn hvec hl hh hlo hhi

/-- The GENUINE LayerNorm normalizer for this residual stream:
    `t = rsqrt eps (var hvec) = 1 / √(var hvec + eps)`, a real number computed
    from the actual rational variance (cast to ℝ).  This is NOT a free variable:
    it is the value `Rsqrt.lean` proves the secant/tangent envelopes around. -/
noncomputable def tNorm (hvec : Fin n → ℚ) : ℝ := rsqrt (eps : ℝ) ((var n hvec : ℚ) : ℝ)

/-- The DERIVED rational t-interval endpoints, as REALS:
    `tl = rsqrt eps B`  (from the variance upper endpoint),
    `th = rsqrt eps 0`  (from the variance lower endpoint). -/
noncomputable def tLo : ℝ := rsqrt (eps : ℝ) ((varB hl hh : ℚ) : ℝ)
noncomputable def tHi : ℝ := rsqrt (eps : ℝ) (0 : ℝ)

/-- **Normalizer interval, DERIVED through Variance + Rsqrt.**
    The genuine normalizer `t = rsqrt eps (var hvec)` satisfies

        rsqrt eps B  ≤  t  ≤  rsqrt eps 0,

    i.e. `tLo ≤ tNorm ≤ tHi`.  This is the carried-hypothesis-turned-THEOREM: the
    t-box is a CONSEQUENCE of the residual-stream box via
      Variance (`var ∈ [0,B]`) ∘ Rsqrt (`rsqrt` antitone).
    The two `rsqrt_antitone` calls supply the only real-analysis content (rsqrt is
    decreasing), itself proven sorry-free in Rsqrt.lean. -/
theorem t_box_derived (heps : 0 < eps) (hn : 0 < n) (hvec : Fin n → ℚ)
    (hlo : ∀ j, hl ≤ hvec j) (hhi : ∀ j, hvec j ≤ hh) :
    tLo eps hl hh ≤ tNorm n eps hvec ∧ tNorm n eps hvec ≤ tHi eps := by
  obtain ⟨hv0, hvB⟩ := var_box_derived n hl hh hn hvec hlo hhi
  -- cast the rational variance bounds to ℝ
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hv0R : (0 : ℝ) ≤ ((var n hvec : ℚ) : ℝ) := by exact_mod_cast hv0
  have hvBR : ((var n hvec : ℚ) : ℝ) ≤ ((varB hl hh : ℚ) : ℝ) := by exact_mod_cast hvB
  -- domain positivity:  v + eps > 0  at the three points 0, var, B
  have dom0  : (0 : ℝ) < (0 : ℝ) + (eps : ℝ) := by linarith
  have domV  : (0 : ℝ) < ((var n hvec : ℚ) : ℝ) + (eps : ℝ) := by linarith
  have domB  : (0 : ℝ) < ((varB hl hh : ℚ) : ℝ) + (eps : ℝ) := by linarith
  constructor
  · -- tLo = rsqrt eps B ≤ rsqrt eps (var)  since var ≤ B  (antitone)
    exact rsqrt_antitone (eps : ℝ) ((var n hvec : ℚ) : ℝ) ((varB hl hh : ℚ) : ℝ)
      domV domB hvBR
  · -- rsqrt eps (var) ≤ rsqrt eps 0 = tHi  since 0 ≤ var  (antitone)
    exact rsqrt_antitone (eps : ℝ) (0 : ℝ) ((var n hvec : ℚ) : ℝ) dom0 domV hv0R

/-! ## 2. Concrete numeric t-box: pin the DERIVED real endpoints to rationals.

We now fix the concrete LayerNorm `eps = 1` and residual-stream box `[0, 1]` of
width `n = 2`, so the DERIVED variance upper endpoint is `B = (1−0)^2 = 1`, and the
DERIVED normalizer endpoints are

    tHi = rsqrt 1 0 = 1/√1     = 1            (exact)
    tLo = rsqrt 1 1 = 1/√2     ∈ [7/10, 1].

We prove the rational ENCLOSURE `7/10 ≤ tNorm ≤ 1` for the genuine normalizer of
ANY residual stream in the box.  This is the sound rational t-box the McCormick
LayerNorm product and the Farkas certificate consume — and crucially it is DERIVED
(its endpoints come from the variance interval through `rsqrt_antitone`), not
assumed. -/

/-- `tHi` at `eps = 1` is exactly `1`. -/
theorem tHi_one : tHi (1 : ℚ) = 1 := by
  unfold tHi rsqrt
  norm_num [Real.sqrt_one]

/-- `7/10 ≤ tLo` at `eps = 1`, `hl = 0`, `hh = 1` (i.e. `7/10 ≤ 1/√2`).  Proven
    from `(√2)^2 = 2` and `√2 ≤ 1.42`. -/
theorem tLo_ge : (7 : ℝ) / 10 ≤ tLo (1 : ℚ) (0 : ℚ) (1 : ℚ) := by
  unfold tLo varB
  have harg : (((((1:ℚ) - 0) ^ 2 : ℚ) : ℝ) + ((1:ℚ) : ℝ)) = 2 := by push_cast; norm_num
  unfold rsqrt
  rw [harg]
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := by rw [Real.sq_sqrt (by norm_num)]
  have hub : Real.sqrt 2 ≤ 142/100 := by nlinarith [hsq, h2]
  rw [le_div_iff₀ h2]; nlinarith [hub, h2]

/-- **The CONCRETE genuine normalizer enclosure, fully DERIVED.**
    For any width-2 residual stream `hvec` with every coordinate in `[0,1]`, the
    genuine LayerNorm normalizer `t = rsqrt 1 (var hvec) = 1/√(var hvec + 1)`
    satisfies the rational box

        7/10  ≤  t  ≤  1.

    BOTH endpoints are DERIVED through Variance + Rsqrt: the upper endpoint is
    `tHi = rsqrt 1 0 = 1` (variance ≥ 0), the lower endpoint is bounded below by
    `tLo = rsqrt 1 1 = 1/√2 ≥ 7/10` (variance ≤ B = 1).  This is the
    carried-hypothesis-turned-THEOREM that all previous blocks assumed. -/
theorem tNorm_box_concrete (hvec : Fin 2 → ℚ)
    (hlo : ∀ j, (0:ℚ) ≤ hvec j) (hhi : ∀ j, hvec j ≤ 1) :
    (7:ℝ)/10 ≤ tNorm 2 (1:ℚ) hvec ∧ tNorm 2 (1:ℚ) hvec ≤ 1 := by
  obtain ⟨hL, hH⟩ := t_box_derived 2 (1:ℚ) (0:ℚ) (1:ℚ) (by norm_num) (by norm_num)
    hvec hlo hhi
  refine ⟨le_trans tLo_ge hL, ?_⟩
  rw [tHi_one] at hH; exact hH

/-- **The centered-feature box, DERIVED from the residual-stream box.**
    For the width-2 residual stream in `[0,1]`, the LayerNorm-centered coordinate-0
    feature `c = hvec 0 − mean` lies in `[−1, 1]`: with `hvec 0 ∈ [0,1]` and (by
    `mean_mem_box`) `mean ∈ [0,1]`, the gap `hvec 0 − mean ∈ [−1,1]`. -/
theorem centered0_box (hvec : Fin 2 → ℚ)
    (hlo : ∀ j, (0:ℚ) ≤ hvec j) (hhi : ∀ j, hvec j ≤ 1) :
    (-1:ℚ) ≤ centered 2 hvec 0 ∧ centered 2 hvec 0 ≤ 1 := by
  obtain ⟨hml, hmu⟩ := mean_mem_box 2 (by norm_num) hvec 0 1 hlo hhi
  unfold centered
  exact ⟨by linarith [hlo 0, hmu], by linarith [hhi 0, hml]⟩

/-! ## 3. The concrete block with GENUINE rsqrt(variance) LayerNorm.

The block (single LayerNorm output coordinate, width-2 residual stream):

      hvec : Fin 2 → ℚ    residual stream,  hvec j ∈ [0,1]      (input box)
      c    = hvec 0 − mean(hvec)            LayerNorm centering   (DERIVED box [−1,1])
      t    = rsqrt 1 (var hvec)             GENUINE normalizer    (DERIVED box [7/10,1])
      p    = c · t                          LayerNorm product     (McCormick)
      ln   = 1·p + 0                        LayerNorm affine      (γ=1, β=0)
      z    = 1·ln + (−1/2)                  MLP pre-activation
      mr   = relu z                         MLP ReLU              (unstable, z∈[−3/2,1/2])
      o    = 1·mr + 0                       MLP output

The ENTIRE novelty over TinyBlock/Block2/StackTwo: `c` and `t` are not assumed
inside `valid`; they are the actual `centered`/`tNorm` of the residual stream, and
their boxes are the DERIVED theorems above.  `valid` carries only the input box on
`hvec` and the structural equalities — the LayerNorm normalizer interval is a
CONSEQUENCE, not a premise. -/

structure BState where
  hvec : Fin 2 → ℚ      -- residual stream (the real LayerNorm input)
  c    : ℝ              -- centered coord-0 feature (= ↑(centered 2 hvec 0))
  t    : ℝ              -- GENUINE normalizer (= tNorm 2 1 hvec = rsqrt 1 (var hvec))
  p    : ℝ              -- LN product   p = c · t
  ln   : ℝ              -- LN affine     ln = p
  z    : ℝ              -- MLP pre-act   z = ln − 1/2
  mr   : ℝ              -- MLP ReLU      mr = relu z
  o    : ℝ              -- MLP output    o = mr

/-- A genuine execution.  CRUCIALLY:
    * the only "input" assumption is the residual-stream box `hvec j ∈ [0,1]`;
    * `c` IS the LayerNorm-centered feature `centered 2 hvec 0` (cast to ℝ);
    * `t` IS the genuine normalizer `tNorm 2 1 hvec = rsqrt 1 (var hvec)` — NOT a
      free bounded variable.  There is NO `tl ≤ t ≤ th` premise: that interval is
      derived from these definitions in `t_genuine_box`. -/
def BState.valid (st : BState) : Prop :=
  (∀ j, (0:ℚ) ≤ st.hvec j) ∧ (∀ j, st.hvec j ≤ 1) ∧
  st.c = ((centered 2 st.hvec 0 : ℚ) : ℝ) ∧
  st.t = tNorm 2 (1:ℚ) st.hvec ∧
  st.p = st.c * st.t ∧
  st.ln = (1:ℝ) * st.p + 0 ∧
  st.z = (1:ℝ) * st.ln + (-1/2) ∧
  st.mr = reluR st.z ∧
  st.o = (1:ℝ) * st.mr + 0

/-! ### DERIVED interval facts on a genuine execution. -/

/-- The centered feature box `c ∈ [−1,1]`, DERIVED (`centered0_box`). -/
theorem c_genuine_box (st : BState) (hv : st.valid) :
    (-1:ℝ) ≤ st.c ∧ st.c ≤ 1 := by
  obtain ⟨hlo, hhi, hceq, _⟩ := hv
  obtain ⟨hcl, hcu⟩ := centered0_box st.hvec hlo hhi
  rw [hceq]
  exact ⟨by exact_mod_cast hcl, by exact_mod_cast hcu⟩

/-- **The GENUINE normalizer box `t ∈ [7/10, 1]`, DERIVED through Variance + Rsqrt.**
    This is the carried-hypothesis-turned-THEOREM: on a genuine execution
    `t = rsqrt 1 (var hvec)` and the interval comes from `tNorm_box_concrete`. -/
theorem t_genuine_box (st : BState) (hv : st.valid) :
    (7:ℝ)/10 ≤ st.t ∧ st.t ≤ 1 := by
  obtain ⟨hlo, hhi, _, hteq, _⟩ := hv
  rw [hteq]
  exact tNorm_box_concrete st.hvec hlo hhi

/-- The MLP pre-activation box `z ∈ [−3/2, 1/2]`, DERIVED from the McCormick range
    of `p = c·t` (`c∈[−1,1]`, `t∈[7/10,1]`) and `z = p − 1/2`. -/
theorem z_genuine_box (st : BState) (hv : st.valid) :
    (-3/2:ℝ) ≤ st.z ∧ st.z ≤ 1/2 := by
  obtain ⟨hcl, hcu⟩ := c_genuine_box st hv
  obtain ⟨htl, htu⟩ := t_genuine_box st hv
  obtain ⟨_, _, _, _, hpeq, hlneq, hzeq, _, _⟩ := hv
  have hplo := mccormick_lower_R (a := st.c) (b := st.t)
      (al := (-1:ℝ)) (bl := (7/10:ℝ)) hcl htl
  have hpup := mccormick_upper2_R (a := st.c) (b := st.t)
      (al := (-1:ℝ)) (bh := (1:ℝ)) hcl htu
  rw [hzeq, hlneq, hpeq]
  constructor
  · nlinarith [hplo, hcl, hcu, htl, htu]
  · nlinarith [hpup, hcl, hcu, htl, htu]

/-! ## 4. The block premise family (`Fin 14`, each `lhs ≤ 0`).

The nonlinear premises are the DERIVED centered box (`centered0_box`), the DERIVED
rsqrt-variance box (`t_genuine_box`), the McCormick LayerNorm product planes
(`mccormick_lower_R` lower-1, `mccormick_upper1_R` upper-1, at `(c,t)`), and the
two ReLU envelopes (`reluR_lower` α=0, `reluR_upper` chord slope 1/4 on
`z∈[−3/2,1/2]`).  The affine equalities are split into `±`-pairs.

  idx  premise                                       source
  ---  --------------------------------------------  -----------------------------
   0   (−1) − c                          ≤ 0         centered box lo   (DERIVED)
   1   c − 1                             ≤ 0         centered box hi   (DERIVED)
   2   (7/10) − t                        ≤ 0         rsqrt-var box lo  (DERIVED)
   3   t − 1                             ≤ 0         rsqrt-var box hi  (DERIVED)
   4   ((−1)t + c(7/10) − (−1)(7/10)) − p ≤ 0        McCormick lower-1 (p=c·t)
   5   p − (1·t + c(7/10) − 1·(7/10))    ≤ 0         McCormick upper-1 (p=c·t)
   6   0·z − mr                          ≤ 0         ReLU lower (α=0)
   7   mr − (1/4)(z − (−3/2))            ≤ 0         ReLU upper chord (z∈[−3/2,1/2])
   8   ln − p                            ≤ 0         LN affine  (E≤0)   ln=p
   9   −(ln − p)                         ≤ 0         LN affine  (−E≤0)
  10   z − ln + 1/2                      ≤ 0         MLP pre-act (E≤0)  z=ln−1/2
  11   −(z − ln + 1/2)                   ≤ 0         MLP pre-act (−E≤0)
  12   o − mr                            ≤ 0         MLP out (E≤0)      o=mr
  13   −(o − mr)                         ≤ 0         MLP out (−E≤0)
-/
noncomputable def bPremise (i : Fin 14) (st : BState) : ℝ :=
  if i.val = 0 then (-1) - st.c
  else if i.val = 1 then st.c - 1
  else if i.val = 2 then (7/10) - st.t
  else if i.val = 3 then st.t - 1
  else if i.val = 4 then ((-1) * st.t + st.c * (7/10) - (-1) * (7/10)) - st.p
  else if i.val = 5 then st.p - ((1:ℝ) * st.t + st.c * (7/10) - (1:ℝ) * (7/10))
  else if i.val = 6 then (0:ℝ) * st.z - st.mr
  else if i.val = 7 then st.mr - (1/4) * (st.z - (-3/2))
  else if i.val = 8 then st.ln - st.p
  else if i.val = 9 then -(st.ln - st.p)
  else if i.val = 10 then st.z - st.ln + (1/2)
  else if i.val = 11 then -(st.z - st.ln + (1/2))
  else if i.val = 12 then st.o - st.mr
  else -(st.o - st.mr)

/-- Every premise is `≤ 0` on every genuine execution.  Box premises are the
    DERIVED centered/rsqrt-variance boxes; McCormick premises are
    `mccormick_lower_R`/`mccormick_upper1_R` at `(c,t)`; the two ReLU premises are
    `reluR_lower` (α=0) and `reluR_upper` (slope 1/4 on `z∈[−3/2,1/2]`, using
    `z_genuine_box`); the six affine premises hold because the structural
    equalities are exact. -/
theorem bPremise_sound :
    ∀ i : Fin 14, ∀ st : BState, st.valid → bPremise i st ≤ 0 := by
  intro i st hv
  have hcb := c_genuine_box st hv
  have htb := t_genuine_box st hv
  have hzb := z_genuine_box st hv
  obtain ⟨_, _, _, _, hpeq, hlneq, hzeq, hmreq, hoeq⟩ := hv
  fin_cases i
  · show (-1:ℝ) - st.c ≤ 0; linarith [hcb.1]
  · show st.c - 1 ≤ 0; linarith [hcb.2]
  · show (7/10:ℝ) - st.t ≤ 0; linarith [htb.1]
  · show st.t - 1 ≤ 0; linarith [htb.2]
  · -- McCormick lower-1
    show ((-1) * st.t + st.c * (7/10) - (-1) * (7/10)) - st.p ≤ 0
    rw [hpeq]
    have := mccormick_lower_R (a := st.c) (b := st.t)
        (al := (-1:ℝ)) (bl := (7/10:ℝ)) hcb.1 htb.1
    linarith
  · -- McCormick upper-1
    show st.p - ((1:ℝ) * st.t + st.c * (7/10) - (1:ℝ) * (7/10)) ≤ 0
    rw [hpeq]
    have := mccormick_upper1_R (a := st.c) (b := st.t)
        (ah := (1:ℝ)) (bl := (7/10:ℝ)) hcb.2 htb.1
    linarith
  · -- ReLU lower (α = 0)
    show (0:ℝ) * st.z - st.mr ≤ 0
    rw [hmreq]
    have := reluR_lower 0 st.z (le_refl 0) (by norm_num)
    linarith
  · -- ReLU upper chord (slope 1/4, lz = −3/2, uz = 1/2):  s(uz−lz)=uz ⇒ (1/4)(2)=1/2
    show st.mr - (1/4) * (st.z - (-3/2)) ≤ 0
    rw [hmreq]
    have := reluR_upper (-3/2:ℝ) (1/2:ℝ) (1/4:ℝ) st.z
        (by norm_num) (by norm_num) (by norm_num) hzb.1 hzb.2
    linarith
  · show st.ln - st.p ≤ 0; rw [hlneq]; linarith
  · show -(st.ln - st.p) ≤ 0; rw [hlneq]; linarith
  · show st.z - st.ln + (1/2) ≤ 0; rw [hzeq]; linarith
  · show -(st.z - st.ln + (1/2)) ≤ 0; rw [hzeq]; linarith
  · show st.o - st.mr ≤ 0; rw [hoeq]; linarith
  · show -(st.o - st.mr) ≤ 0; rw [hoeq]; linarith

/-! ## 5. The two kernel-checked block bounds, via `farkas_premise_combination_R`.

Lower bound `o ≥ 0`.  Certificate (nonzero multipliers):
  ReLU lower:    μ₆  = 1
  MLP-out (−E):  μ₁₃ = 1
Identity: μ₆·(0·z − mr) + μ₁₃·(−(o − mr)) = −o.  (c = 0.) -/
theorem block_lower :
    ∀ st : BState, st.valid → -(0 : ℝ) ≤ st.o := by
  refine farkas_premise_combination_R (S := BState) (ι := Fin 14)
        (premises := Finset.univ)
        (g := bPremise) (out := fun st => st.o)
        (μ := ![ 0, 0, 0, 0, 0, 0, 1, 0,  0, 0, 0, 0, 0, 1 ])
        (c := (0 : ℝ)) (valid := BState.valid)
        ?hμ ?hg ?hcert
  case hμ => intro i _; fin_cases i <;> norm_num
  case hg => intro i _ st hv; exact bPremise_sound i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, bPremise, Fin.val_succ,
               Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
               Matrix.cons_val_fin_one]
    norm_num
    ring

/-! Upper bound `o ≤ 1/2`.  Apply the core to `out := −o`.  Certificate (nonzero
multipliers; the chord/McCormick/box chain worked out by hand):
  centered box hi:   μ₁  = 7/40
  rsqrt-var box hi:  μ₃  = 1/4
  McCormick upper-1: μ₅  = 1/4
  ReLU upper chord:  μ₇  = 1
  LN affine (+E):    μ₈  = 1/4
  MLP pre-act (+E):  μ₁₀ = 1/4
  MLP-out (+E):      μ₁₂ = 1
Identity: combo = o − 1/2 = −(−o) − 1/2.  (c = 1/2.) -/
theorem block_upper :
    ∀ st : BState, st.valid → st.o ≤ (1/2 : ℝ) := by
  have key : ∀ st : BState, st.valid → (-(1/2) : ℝ) ≤ (fun st => -st.o) st := by
    refine farkas_premise_combination_R (S := BState) (ι := Fin 14)
          (premises := Finset.univ)
          (g := bPremise) (out := fun st => -st.o)
          (μ := ![ 0, (7/40), 0, (1/4), 0, (1/4), 0, 1,
                   (1/4), 0, (1/4), 0, 1, 0 ])
          (c := (1/2 : ℝ)) (valid := BState.valid)
          ?hμ ?hg ?hcert
    case hμ => intro i _; fin_cases i <;> norm_num
    case hg => intro i _ st hv; exact bPremise_sound i st hv
    case hcert =>
      intro st
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, bPremise, Fin.val_succ,
                 Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
                 Matrix.cons_val_fin_one]
      norm_num
      ring
  intro st hv
  have := key st hv
  simp only at this
  linarith

/-- **The end-to-end block bound with GENUINE rsqrt(variance) LayerNorm.**
    Every genuine execution of the concrete block — whose LayerNorm normalizer
    `t = rsqrt 1 (var hvec)` is DERIVED (not assumed) from the residual-stream box
    through Variance + Rsqrt — satisfies `o ∈ [0, 1/2]`. -/
theorem block_bound (st : BState) (hv : st.valid) :
    (0 : ℝ) ≤ st.o ∧ st.o ≤ (1/2 : ℝ) := by
  refine ⟨?_, block_upper st hv⟩
  have := block_lower st hv; linarith

/-! ## 6. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms reluR_lower
#print axioms reluR_upper
#print axioms var_box_derived
#print axioms t_box_derived
#print axioms tNorm_box_concrete
#print axioms centered0_box
#print axioms c_genuine_box
#print axioms t_genuine_box
#print axioms z_genuine_box
#print axioms bPremise_sound
#print axioms block_lower
#print axioms block_upper
#print axioms block_bound

end Crownproof.DerivedLN
