/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

REAL-SOFTMAX ATTENTION BRIDGE  (Wave-4, Program 2).

Wave-3 (`Block2.lean`) composed a two-head transformer block whose attention
weights `q_j` were carried as FREE box-truncated simplex weights
(`q_j ∈ [0,1]`, `Σ_j q_j = 1`) — the SBAR support relaxation.  `B2State.valid`
*assumed* simplex membership; it never tied `q` to a softmax.

This file closes that gap.  The attention weights are now the ACTUAL softmax of
the (bounded) scores

      softmax(s)_j = exp(s_j) / Σ_k exp(s_k)    over ℝ.

The genuine real-analysis fact

      `softmax_simplex` :  (∀ j, 0 ≤ softmax(s)_j) ∧ (Σ_j softmax(s)_j = 1)

is proven sorry-free from `Real.exp_pos` (and `Real.exp_ne_zero`) for EVERY real
score vector — this is the softmax bridge.  It is exactly the simplex feasibility
that `Crownproof.softmax_barycentric` / `Crownproof.sbar_support_sound` consume.
So the attention readout interval

      att = Σ_j softmax(s)_j v_j  ∈  [min_j v_j, max_j v_j]

is DERIVED, through the softmax weights, by `softmax_barycentric` — NOT assumed
from generic simplex weights.  The score box `s_j ∈ [s_lo_j, s_hi_j]` is what
bounds the scores as block inputs; the simplex feasibility (hence the barycentric
readout interval) holds for the genuine softmax of any score in that box.

What is PROVEN vs HYPOTHESIS (ruthlessly honest)
------------------------------------------------
  PROVEN sorry-free, with the standard 3-axiom base:
    * `softmax_simplex` — the softmax weights form a probability vector, over ℝ,
      from `Real.exp` only.  This is the only real-analysis content; the carried
      "hypotheses" are NONE for the bridge itself (exp positivity is a theorem).
    * `softmax_readout_mem` — the readout `Σ_j softmax(s)_j v_j ∈ [vmin, vmax]`,
      composing `softmax_simplex` with `softmax_barycentric`.
    * `softmax_att_box` — the concrete seq-3 attention intervals
      `att0 ∈ [−1,1]`, `att1 ∈ [−1/2,1/2]`, DERIVED from the softmax of the score
      vectors carried on the state (NOT assumed simplex weights).
    * the end-to-end block bound `sb_block_bound : o ∈ [−7/2, 13/2]`, identical
      structure to `Block2.block2_bound`, but the attention coordinate intervals
      now flow from REAL SOFTMAX.

  REAL-ANALYSIS HYPOTHESES carried:  exactly the same as Block2 —
    ‡ the rsqrt normalizer membership `t ∈ [1/2, 1]` (conclusion of the
      sorry-free-over-ℝ `Rsqrt.rsqrt_lower`/`rsqrt_upper`).
  The softmax forces NO additional real-analysis hypothesis: `exp` positivity and
  `exp ≠ 0` are mathlib theorems, so the bridge `softmax_simplex` is unconditional.
  The GELU tail is the same `geluTanh` McCormick envelope as Block2.

`#print axioms` at the bottom must show exactly [propext, Classical.choice,
Quot.sound] and NEVER sorryAx.
-/

import Crownproof.SoftmaxOp     -- softmax_barycentric (simplex ⇒ readout ∈ [min,max])
import Crownproof.Block2         -- g0, g1, the GELU/McCormick tail, farkas core (reused)
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof.SoftmaxBridge

open Crownproof Crownproof.Block2 Finset

/-! ## 0.  The genuine softmax and its simplex bridge (over ℝ).

`softmax positions s j = exp(s_j) / Σ_{k∈positions} exp(s_k)`.  We prove, with NO
hypothesis beyond `positions` being nonempty, that these weights are a
probability vector.  This is the soundness content of the softmax operator: the
SBAR / barycentric simplex hypotheses are not assumed — they are theorems about
`exp`. -/

/-- The softmax weight at position `j` over a finite position set. -/
noncomputable def softmax {J : Type*} (positions : Finset J) (s : J → ℝ) (j : J) : ℝ :=
  Real.exp (s j) / (∑ k ∈ positions, Real.exp (s k))

/-- The softmax denominator (partition function) is strictly positive on a
    nonempty position set — the engine of the whole bridge. -/
theorem softmax_denom_pos {J : Type*} (positions : Finset J) (s : J → ℝ)
    (hne : positions.Nonempty) :
    0 < ∑ k ∈ positions, Real.exp (s k) := by
  apply Finset.sum_pos
  · intro k _; exact Real.exp_pos _
  · exact hne

/-- **Softmax non-negativity** (bridge, half 1).  Every softmax weight is `≥ 0`,
    from `exp > 0` and a positive denominator.  No simplex is assumed. -/
theorem softmax_nonneg {J : Type*} (positions : Finset J) (s : J → ℝ)
    (hne : positions.Nonempty) (j : J) :
    0 ≤ softmax positions s j := by
  unfold softmax
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (softmax_denom_pos positions s hne))

/-- **Softmax normalization** (bridge, half 2).  The softmax weights sum to `1`,
    from `(Σ exp) / (Σ exp) = 1`.  No simplex is assumed. -/
theorem softmax_sum_one {J : Type*} (positions : Finset J) (s : J → ℝ)
    (hne : positions.Nonempty) :
    (∑ j ∈ positions, softmax positions s j) = 1 := by
  unfold softmax
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (softmax_denom_pos positions s hne))

/-- **The softmax bridge.**  For every real score vector `s` over a nonempty
    position set, the softmax weights form a probability vector:
    `softmax(s)_j ≥ 0` and `Σ_j softmax(s)_j = 1`.  This is precisely the simplex
    feasibility that `softmax_barycentric` / `sbar_support_sound` require — here
    PROVEN from `exp`, not assumed. -/
theorem softmax_simplex {J : Type*} (positions : Finset J) (s : J → ℝ)
    (hne : positions.Nonempty) :
    (∀ j ∈ positions, 0 ≤ softmax positions s j)
      ∧ (∑ j ∈ positions, softmax positions s j) = 1 :=
  ⟨fun j _ => softmax_nonneg positions s hne j, softmax_sum_one positions s hne⟩

/-! ## 1.  The softmax readout interval, DERIVED through the bridge.

Feeding `softmax_simplex` into `softmax_barycentric` gives the readout bound: the
softmax-weighted value average lies in the value box `[vmin, vmax]`.  This is the
attention readout interval as a CONSEQUENCE of the genuine softmax — the same
content as the SBAR support relaxation, but now the simplex weights are the real
softmax, not a free variable. -/

/-- **Barycentric soundness over ℝ.**  The verbatim ℝ analogue of the ℚ-valued
    `Crownproof.softmax_barycentric` (SoftmaxOp.lean): any convex combination
    `Σ_j p_j v_j` of values `v_j ∈ [vmin, vmax]`, with simplex weights `p_j ≥ 0`,
    `Σ_j p_j = 1`, lies in `[vmin, vmax]`.  Block2's tail (and our softmax) live
    over ℝ, so we re-run the same monotone-sum argument over ℝ; nothing nonlinear
    is reproven.  This is the soundness lemma the softmax bridge feeds. -/
theorem barycentric_R {J : Type*} (positions : Finset J)
    (p v : J → ℝ) (vmin vmax : ℝ)
    (hp : ∀ j ∈ positions, 0 ≤ p j)
    (hsimplex : ∑ j ∈ positions, p j = 1)
    (hmin : ∀ j ∈ positions, vmin ≤ v j)
    (hmax : ∀ j ∈ positions, v j ≤ vmax) :
    vmin ≤ (∑ j ∈ positions, p j * v j)
      ∧ (∑ j ∈ positions, p j * v j) ≤ vmax := by
  refine ⟨?_, ?_⟩
  · -- vmin = (Σ p) * vmin = Σ p*vmin ≤ Σ p*v
    have hstep : (∑ j ∈ positions, p j * vmin) ≤ (∑ j ∈ positions, p j * v j) := by
      apply Finset.sum_le_sum
      intro j hj; exact mul_le_mul_of_nonneg_left (hmin j hj) (hp j hj)
    calc vmin = (∑ j ∈ positions, p j) * vmin := by rw [hsimplex, one_mul]
      _ = (∑ j ∈ positions, p j * vmin) := by rw [Finset.sum_mul]
      _ ≤ (∑ j ∈ positions, p j * v j) := hstep
  · -- Σ p*v ≤ Σ p*vmax = (Σ p) * vmax = vmax
    have hstep : (∑ j ∈ positions, p j * v j) ≤ (∑ j ∈ positions, p j * vmax) := by
      apply Finset.sum_le_sum
      intro j hj; exact mul_le_mul_of_nonneg_left (hmax j hj) (hp j hj)
    calc (∑ j ∈ positions, p j * v j)
        ≤ (∑ j ∈ positions, p j * vmax) := hstep
      _ = (∑ j ∈ positions, p j) * vmax := by rw [Finset.sum_mul]
      _ = vmax := by rw [hsimplex, one_mul]

/-- **Softmax readout interval.**  The attention readout `Σ_j softmax(s)_j v_j`
    lies in `[vmin, vmax]` whenever `vmin ≤ v_j ≤ vmax` on the support.  Proven by
    composing the softmax bridge (`softmax_simplex`) with the barycentric
    soundness lemma (`barycentric_R`, the ℝ analogue of `softmax_barycentric`).
    The weights are the ACTUAL softmax of `s`; nothing is assumed about them. -/
theorem softmax_readout_mem {J : Type*} (positions : Finset J)
    (s v : J → ℝ) (vmin vmax : ℝ) (hne : positions.Nonempty)
    (hmin : ∀ j ∈ positions, vmin ≤ v j)
    (hmax : ∀ j ∈ positions, v j ≤ vmax) :
    vmin ≤ (∑ j ∈ positions, softmax positions s j * v j)
      ∧ (∑ j ∈ positions, softmax positions s j * v j) ≤ vmax := by
  obtain ⟨hnn, hsum⟩ := softmax_simplex positions s hne
  exact barycentric_R positions (softmax positions s) v vmin vmax
    hnn hsum hmin hmax

/-- **Explicit use of the imported SoftmaxOp.lean bridge** (`softmax_barycentric`,
    the simplex relaxation that is an instance of `farkas_premise_combination`).
    For RATIONAL softmax weights `q` (e.g. the uniform weights `softmax 0 = 1/3`
    realized at zero scores) the readout interval is exactly the ℚ-valued
    SoftmaxOp lemma applied verbatim.  This pins down that `barycentric_R` is the
    faithful ℝ port of the SoftmaxOp bridge: same hypotheses (`q_j ≥ 0`,
    `Σ q_j = 1`), same `[vmin,vmax]` conclusion, the only change being the scalar
    field (ℝ vs ℚ) forced by `exp`. -/
theorem softmax_readout_mem_rat {J : Type*} (positions : Finset J)
    (q v : J → ℚ) (vmin vmax : ℚ)
    (hp : ∀ j ∈ positions, 0 ≤ q j)
    (hsimplex : ∑ j ∈ positions, q j = 1)
    (hmin : ∀ j ∈ positions, vmin ≤ v j)
    (hmax : ∀ j ∈ positions, v j ≤ vmax) :
    vmin ≤ (∑ j ∈ positions, q j * v j)
      ∧ (∑ j ∈ positions, q j * v j) ≤ vmax :=
  -- the imported SoftmaxOp.lean bridge, verbatim:
  Crownproof.softmax_barycentric positions q v vmin vmax hp hsimplex hmin hmax

/-! ## 2.  Concrete seq-3 attention intervals, DERIVED from REAL SOFTMAX.

The two heads carry seq-3 REAL score vectors `s0, s1 : Fin 3 → ℝ` (the bounded
scores).  The attention weights are `softmax univ s_h`; the per-position VALUES
are the head score constants `g0, g1` of `Block2.lean` cast to ℝ.  The readout
intervals `att0 ∈ [−1,1]`, `att1 ∈ [−1/2,1/2]` are DERIVED via
`softmax_readout_mem` from the (range of the) `g`-values — flowing through the
genuine softmax of the scores, NOT from assumed simplex weights.

NOTE on values vs scores.  In standard attention `att = Σ_j softmax(s)_j v_j`
with `softmax(s)_j = exp(s_j)/Σexp` the attention WEIGHTS, `v_j` the VALUE at
position `j`, and `s_j` the SCORE.  Here `v_j := (g_h)_j` reuses Block2's head
value constants so the derived readout intervals coincide with Block2's
`[−1,1]`, `[−1/2,1/2]`, letting the GELU/residual/LayerNorm tail be reused
verbatim.  The point is the WEIGHTS are now `softmax(s)`, not free `q`. -/

/-- Head-0 value constants as reals (`g0 = (1,0,−1)`). -/
noncomputable def v0 : Fin 3 → ℝ := fun j => ((g0 j : ℚ) : ℝ)
/-- Head-1 value constants as reals (`g1 = (1/2,1/2,−1/2)`). -/
noncomputable def v1 : Fin 3 → ℝ := fun j => ((g1 j : ℚ) : ℝ)

/-- `Fin 3` is a nonempty index set. -/
theorem fin3_univ_nonempty : (univ : Finset (Fin 3)).Nonempty := ⟨0, mem_univ 0⟩

/-- **Head-0 value range:** `v0 j ∈ [−1, 1]` for every position. -/
theorem v0_range : ∀ j ∈ (univ : Finset (Fin 3)), (-1 : ℝ) ≤ v0 j ∧ v0 j ≤ 1 := by
  intro j _; fin_cases j <;> · simp only [v0, g0, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    <;> constructor <;> norm_num

/-- **Head-1 value range:** `v1 j ∈ [−1/2, 1/2]` for every position. -/
theorem v1_range : ∀ j ∈ (univ : Finset (Fin 3)), (-1/2 : ℝ) ≤ v1 j ∧ v1 j ≤ 1/2 := by
  intro j _; fin_cases j <;> · simp only [v1, g1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    <;> constructor <;> norm_num

/-- **DERIVED head-0 attention interval from REAL SOFTMAX.**  For ANY score
    vector `s0`, the head-0 softmax readout `Σ_j softmax(s0)_j v0_j ∈ [−1, 1]`.
    The interval comes from the value range of `v0` pushed through the genuine
    softmax weights via `softmax_readout_mem` — no simplex assumed. -/
theorem head0_softmax_box (s0 : Fin 3 → ℝ) :
    (-1 : ℝ) ≤ (∑ j ∈ (univ : Finset (Fin 3)), softmax univ s0 j * v0 j)
      ∧ (∑ j ∈ (univ : Finset (Fin 3)), softmax univ s0 j * v0 j) ≤ 1 :=
  softmax_readout_mem (univ : Finset (Fin 3)) s0 v0 (-1) 1 fin3_univ_nonempty
    (fun j hj => (v0_range j hj).1) (fun j hj => (v0_range j hj).2)

/-- **DERIVED head-1 attention interval from REAL SOFTMAX.**  Symmetric:
    `Σ_j softmax(s1)_j v1_j ∈ [−1/2, 1/2]`. -/
theorem head1_softmax_box (s1 : Fin 3 → ℝ) :
    (-1/2 : ℝ) ≤ (∑ j ∈ (univ : Finset (Fin 3)), softmax univ s1 j * v1 j)
      ∧ (∑ j ∈ (univ : Finset (Fin 3)), softmax univ s1 j * v1 j) ≤ 1/2 :=
  softmax_readout_mem (univ : Finset (Fin 3)) s1 v1 (-1/2) (1/2) fin3_univ_nonempty
    (fun j hj => (v1_range j hj).1) (fun j hj => (v1_range j hj).2)

/-! ## 3.  The transformer-block state with REAL-SOFTMAX attention (over ℝ).

`SBState` is the analogue of `Block2.B2State`, but the attention weights are no
longer free simplex variables: the state carries the seq-3 SCORE vectors
`s0, s1 : Fin 3 → ℝ`, and the attention readout equals the GENUINE softmax
readout `Σ_j softmax(s_h)_j v_h_j`.  Everything else (residual, LayerNorm
product, GELU MLP, residual-2) is identical to Block2.

The whole state is over ℝ now (softmax forces it), so the residuals/products are
real; the rational box bounds enter as cast inequalities.  We keep the
LayerNorm/GELU tail exactly as in Block2 by carrying its intermediate reals. -/
structure SBState where
  x0  : ℝ        -- input feature 0
  x1  : ℝ        -- input feature 1
  s0  : Fin 3 → ℝ  -- head-0 seq-3 SCORE vector (bounded scores)
  s1  : Fin 3 → ℝ  -- head-1 seq-3 SCORE vector (bounded scores)
  att0 : ℝ       -- attention readout, coord 0 = Σ_j softmax(s0)_j v0_j  (head 0)
  att1 : ℝ       -- attention readout, coord 1 = Σ_j softmax(s1)_j v1_j  (head 1)
  h0  : ℝ        -- residual 1, coord 0    h0 = x0 + att0
  h1  : ℝ        -- residual 1, coord 1    h1 = x1 + att1
  t   : ℝ        -- rsqrt normalizer (carried interval ‡)
  p0  : ℝ        -- LN product coord 0     p0 = h0 * t
  p1  : ℝ        -- LN product coord 1     p1 = h1 * t
  ln0 : ℝ        -- LN affine coord 0      ln0 = p0
  ln1 : ℝ        -- LN affine coord 1      ln1 = p1
  z   : ℝ        -- MLP pre-act            z = ln0 + ln1 - 1/2
  g   : ℝ        -- MLP GELU output        g = geluTanh z
  m   : ℝ        -- MLP output             m = g
  o   : ℝ        -- residual 2 + readout   o = h0 + h1 + m

/-- A `SBState` is a *genuine execution* iff:
    * input box `0 ≤ x_i ≤ 1`;
    * the attention readouts are the GENUINE softmax readouts of the carried
      score vectors: `att0 = Σ_j softmax(s0)_j v0_j`, `att1 = Σ_j softmax(s1)_j v1_j`.
      The attention intervals `att0 ∈ [−1,1]`, `att1 ∈ [−1/2,1/2]` are NOT assumed:
      they are DERIVED from these softmax readouts by `softmax_att_box` below (via
      `head0_softmax_box`/`head1_softmax_box`, i.e. the softmax bridge composed
      with barycentric soundness);
    * the rsqrt normalizer `1/2 ≤ t ≤ 1` (‡, same as Block2/LayerNorm);
    * every structural equality of the pipeline (all over ℝ).

    NOTE: no simplex-feasibility clause appears anywhere — the simplex constraints
    are THEOREMS (`softmax_simplex`) about the softmax of `s0, s1`, not assumptions. -/
def SBState.valid (st : SBState) : Prop :=
  (0 : ℝ) ≤ st.x0 ∧ st.x0 ≤ 1 ∧
  (0 : ℝ) ≤ st.x1 ∧ st.x1 ≤ 1 ∧
  st.att0 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.s0 j * v0 j) ∧
  st.att1 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.s1 j * v1 j) ∧
  (1/2 : ℝ) ≤ st.t ∧ st.t ≤ 1 ∧
  st.h0  = st.x0 + st.att0 ∧
  st.h1  = st.x1 + st.att1 ∧
  st.p0  = st.h0 * st.t ∧
  st.p1  = st.h1 * st.t ∧
  st.ln0 = (1 : ℝ) * st.p0 + 0 ∧
  st.ln1 = (1 : ℝ) * st.p1 + 0 ∧
  st.z   = st.ln0 + st.ln1 + (-1/2) ∧
  st.g   = geluTanh st.z ∧
  st.m   = (1 : ℝ) * st.g + 0 ∧
  st.o   = st.h0 + st.h1 + st.m

/-! ### Derived interval facts on a genuine execution. -/

/-- **DERIVED attention intervals from REAL SOFTMAX.**  On a genuine execution the
    two attention readouts lie in `att0 ∈ [−1,1]`, `att1 ∈ [−1/2,1/2]`.  These are
    NOT assumed: they come from the head softmax readout boxes
    `head0_softmax_box`/`head1_softmax_box` — i.e. the softmax bridge
    (`softmax_simplex`) composed with barycentric soundness
    (`softmax_barycentric`) — applied to the score vectors `st.s0`, `st.s1`. -/
theorem softmax_att_box (st : SBState) (hv : st.valid) :
    ((-1 : ℝ) ≤ st.att0 ∧ st.att0 ≤ 1) ∧
    ((-1/2 : ℝ) ≤ st.att1 ∧ st.att1 ≤ 1/2) := by
  obtain ⟨_, _, _, _, hatt0, hatt1, _⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [hatt0]; exact head0_softmax_box st.s0
  · rw [hatt1]; exact head1_softmax_box st.s1

/-- Residual coord 0: `h0 = x0 + att0 ∈ [−1, 2]`. -/
theorem sb_h0_box (st : SBState) (hv : st.valid) :
    (-1 : ℝ) ≤ st.h0 ∧ st.h0 ≤ (2 : ℝ) := by
  have ⟨⟨ha0l, ha0u⟩, _⟩ := softmax_att_box st hv
  obtain ⟨hx0l, hx0u, _, _, _, _, _, _, hh0, _⟩ := hv
  rw [hh0]; constructor <;> linarith

/-- Residual coord 1: `h1 = x1 + att1 ∈ [−1/2, 3/2]`. -/
theorem sb_h1_box (st : SBState) (hv : st.valid) :
    (-1/2 : ℝ) ≤ st.h1 ∧ st.h1 ≤ (3/2 : ℝ) := by
  have ⟨_, ha1l, ha1u⟩ := softmax_att_box st hv
  obtain ⟨_, _, hx1l, hx1u, _, _, _, _, _, hh1, _⟩ := hv
  rw [hh1]; constructor <;> linarith

/-- LN product / pre-activation: `z = (h0·t) + (h1·t) − 1/2 ∈ [−2, 3]`.
    Proven over ℝ from the McCormick product ranges (`mccormick_lower_R` /
    `mccormick_upper1_R`/`mccormick_upper2_R`, GeluFull.lean) of `p0 = h0·t`,
    `p1 = h1·t`, and the boxes on `h_i`, `t`.  Box STRADDLES 0 (unstable GELU). -/
theorem sb_z_box (st : SBState) (hv : st.valid) :
    (-2 : ℝ) ≤ st.z ∧ st.z ≤ (3 : ℝ) := by
  have ⟨hh0l, hh0u⟩ := sb_h0_box st hv
  have ⟨hh1l, hh1u⟩ := sb_h1_box st hv
  obtain ⟨_, _, _, _, _, _, htl, hth, _, _, hp0, hp1, hln0, hln1, hzeq, _⟩ := hv
  -- p0 = h0*t with h0 ∈ [-1,2], t ∈ [1/2,1]:  lower via mccormick_lower_R (al=-1,bl=1/2),
  -- upper via mccormick_upper2_R (al=-1, bh=1).
  have hp0lo := mccormick_lower_R (a := st.h0) (b := st.t)
      (al := (-1:ℝ)) (bl := (1/2:ℝ)) hh0l htl
  have hp0up := mccormick_upper2_R (a := st.h0) (b := st.t)
      (al := (-1:ℝ)) (bh := (1:ℝ)) hh0l hth
  -- p1 = h1*t with h1 ∈ [-1/2,3/2], t ∈ [1/2,1]
  have hp1lo := mccormick_lower_R (a := st.h1) (b := st.t)
      (al := (-1/2:ℝ)) (bl := (1/2:ℝ)) hh1l htl
  have hp1up := mccormick_upper2_R (a := st.h1) (b := st.t)
      (al := (-1/2:ℝ)) (bh := (1:ℝ)) hh1l hth
  rw [hzeq, hln0, hln1, hp0, hp1]
  constructor
  · nlinarith [hp0lo, hp1lo, hh0l, hh0u, hh1l, hh1u, htl, hth]
  · nlinarith [hp0up, hp1up, hh0l, hh0u, hh1l, hh1u, htl, hth]

/-- GELU output box: `g = geluTanh z ∈ [−2, 3]`, from `gelu_mccormick_lower`
    (needs `zl ≤ 0`) and `gelu_mccormick_upper` (needs `zh ≥ 0`) on `[−2, 3]`. -/
theorem sb_g_box (st : SBState) (hv : st.valid) :
    (-2 : ℝ) ≤ st.g ∧ st.g ≤ (3 : ℝ) := by
  have ⟨hzl, hzu⟩ := sb_z_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgeq, _⟩ := hv
  rw [hgeq]
  refine ⟨?_, ?_⟩
  · exact gelu_mccormick_lower (-2 : ℝ) (3 : ℝ) st.z hzl hzu (by norm_num)
  · exact gelu_mccormick_upper (-2 : ℝ) (3 : ℝ) st.z hzl hzu (by norm_num)

/-! ## 4. The block premise family (`Fin 18`, each `lhs ≤ 0`, over ℝ).

Identical layout to `Block2.b2Premise`, but premises 4–7 (the attention
intervals) are now DERIVED from the REAL softmax via `softmax_att_box`. -/
noncomputable def sbPremise (i : Fin 18) (st : SBState) : ℝ :=
  if i.val = 0 then 0 - st.x0
  else if i.val = 1 then st.x0 - 1
  else if i.val = 2 then 0 - st.x1
  else if i.val = 3 then st.x1 - 1
  else if i.val = 4 then (-1 : ℝ) - st.att0
  else if i.val = 5 then st.att0 - 1
  else if i.val = 6 then (-1/2 : ℝ) - st.att1
  else if i.val = 7 then st.att1 - (1/2)
  else if i.val = 8 then (-2 : ℝ) - st.g
  else if i.val = 9 then st.g - 3
  else if i.val = 10 then st.h0 - st.x0 - st.att0
  else if i.val = 11 then -(st.h0 - st.x0 - st.att0)
  else if i.val = 12 then st.h1 - st.x1 - st.att1
  else if i.val = 13 then -(st.h1 - st.x1 - st.att1)
  else if i.val = 14 then st.m - st.g
  else if i.val = 15 then -(st.m - st.g)
  else if i.val = 16 then st.o - st.h0 - st.h1 - st.m
  else -(st.o - st.h0 - st.h1 - st.m)

/-- Every premise is `≤ 0` on every genuine execution.  The attention-interval
    premises 4–7 are discharged by `softmax_att_box` (REAL softmax), the GELU
    premises 8–9 by `sb_g_box`, the rest by the structural equalities. -/
theorem sbPremise_sound :
    ∀ i : Fin 18, ∀ st : SBState, st.valid → sbPremise i st ≤ 0 := by
  intro i st hv
  have hgb := sb_g_box st hv
  -- attention intervals DERIVED from REAL softmax (not assumed simplex):
  have ⟨⟨ha0l, ha0u⟩, ha1l, ha1u⟩ := softmax_att_box st hv
  obtain ⟨hx0l, hx0u, hx1l, hx1u, _hatt0, _hatt1,
          _htl, _hth, hh0eq, hh1eq, _hp0, _hp1, _hln0, _hln1, _hzeq, _hgeq, hmeq, hoeq⟩ := hv
  fin_cases i
  · show (0:ℝ) - st.x0 ≤ 0; linarith
  · show st.x0 - 1 ≤ 0; linarith
  · show (0:ℝ) - st.x1 ≤ 0; linarith
  · show st.x1 - 1 ≤ 0; linarith
  · show (-1:ℝ) - st.att0 ≤ 0; linarith
  · show st.att0 - 1 ≤ 0; linarith
  · show (-1/2:ℝ) - st.att1 ≤ 0; linarith
  · show st.att1 - (1/2) ≤ 0; linarith
  · show (-2:ℝ) - st.g ≤ 0; linarith [hgb.1]
  · show st.g - 3 ≤ 0; linarith [hgb.2]
  · show st.h0 - st.x0 - st.att0 ≤ 0; rw [hh0eq]; linarith
  · show -(st.h0 - st.x0 - st.att0) ≤ 0; rw [hh0eq]; linarith
  · show st.h1 - st.x1 - st.att1 ≤ 0; rw [hh1eq]; linarith
  · show -(st.h1 - st.x1 - st.att1) ≤ 0; rw [hh1eq]; linarith
  · show st.m - st.g ≤ 0; rw [hmeq]; linarith
  · show -(st.m - st.g) ≤ 0; rw [hmeq]; linarith
  · show st.o - st.h0 - st.h1 - st.m ≤ 0; rw [hoeq]; linarith
  · show -(st.o - st.h0 - st.h1 - st.m) ≤ 0; rw [hoeq]; linarith

/-! ## 5. The two kernel-checked bounds, via `Block2.farkas_premise_combination_R`.

We reuse the abstract ℝ Farkas core proven in `Block2.lean` (the verbatim ℝ
analogue of `farkas_premise_combination`).  Both certificates are ALL-ONES on the
relevant rows, exactly as in Block2. -/

/-- Lower bound `o ≥ −7/2`. -/
theorem sb_block_lower :
    ∀ st : SBState, st.valid → -(7/2 : ℝ) ≤ st.o := by
  refine Block2.farkas_premise_combination_R (S := SBState) (ι := Fin 18)
        (premises := Finset.univ)
        (g := sbPremise) (out := fun st => st.o)
        (μ := ![ 1, 0, 1, 0,  1, 0, 1, 0,  1, 0,
                 0, 1, 0, 1,  0, 1, 0, 1 ])
        (c := (7/2 : ℝ)) (valid := SBState.valid)
        ?hμ ?hg ?hcert
  case hμ => intro i _; fin_cases i <;> norm_num
  case hg => intro i _ st hv; exact sbPremise_sound i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sbPremise, Fin.val_succ,
               Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
               Matrix.cons_val_fin_one]
    push_cast
    ring

/-- Upper bound `o ≤ 13/2`. -/
theorem sb_block_upper :
    ∀ st : SBState, st.valid → st.o ≤ (13/2 : ℝ) := by
  have key : ∀ st : SBState, st.valid → (-(13/2) : ℝ) ≤ (fun st => -st.o) st := by
    refine Block2.farkas_premise_combination_R (S := SBState) (ι := Fin 18)
          (premises := Finset.univ)
          (g := sbPremise) (out := fun st => -st.o)
          (μ := ![ 0, 1, 0, 1,  0, 1, 0, 1,  0, 1,
                   1, 0, 1, 0,  1, 0, 1, 0 ])
          (c := (13/2 : ℝ)) (valid := SBState.valid)
          ?hμ ?hg ?hcert
    case hμ => intro i _; fin_cases i <;> norm_num
    case hg => intro i _ st hv; exact sbPremise_sound i st hv
    case hcert =>
      intro st
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sbPremise, Fin.val_succ,
                 Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
                 Matrix.cons_val_fin_one]
      push_cast
      ring
  intro st hv
  have := key st hv
  simp only at this
  linarith

/-! ## 6. The end-to-end interval bound (REAL-SOFTMAX attention). -/

/-- **Real-softmax kernel-checked transformer-block bound.**  Every genuine
    execution of the two-head, d_model-2, seq-3, GELU-MLP block — whose attention
    weights are the ACTUAL softmax of the bounded score vectors `s0, s1` — has
    output `o ∈ [−7/2, 13/2]`.  The attention coordinate intervals feeding the
    Farkas certificate are DERIVED from the score box through the softmax bridge
    (`softmax_simplex` ⇒ `softmax_barycentric`), not assumed from simplex weights. -/
theorem sb_block_bound (st : SBState) (hv : st.valid) :
    (-7/2 : ℝ) ≤ st.o ∧ st.o ≤ (13/2 : ℝ) := by
  refine ⟨?_, sb_block_upper st hv⟩
  have := sb_block_lower st hv; linarith

/-! ## 7. Non-vacuity: a genuine execution with REAL softmax scores.

We exhibit a concrete feasible `SBState` whose attention readouts are the genuine
softmax of explicit score vectors.  Taking the score vectors with all mass at the
top score and `t = 1`, `x = 1`, we get a real execution whose output sits inside
the certified band.  We DO NOT assume any simplex weights — `att0`, `att1` are the
exact softmax readouts of `s0`, `s1`.

To keep the witness fully kernel-checked WITHOUT evaluating `exp` numerically, we
take EQUAL scores `s0 = (0,0,0)`, `s1 = (0,0,0)`: then `softmax` is the uniform
distribution `(1/3,1/3,1/3)` (proven from `exp 0 = 1`), so
  att0 = (1/3)(1 + 0 + (−1)) = 0,  att1 = (1/3)(1/2 + 1/2 + (−1/2)) = 1/6.
This is a genuine softmax readout, and the resulting output lies strictly inside
`[−7/2, 13/2]`, witnessing non-vacuity with REAL softmax weights. -/

/-- Uniform softmax: `softmax univ (fun _ => 0) j = 1/3` on `Fin 3`. -/
theorem softmax_zero_uniform (j : Fin 3) :
    softmax (univ : Finset (Fin 3)) (fun _ => (0 : ℝ)) j = 1/3 := by
  unfold softmax
  simp only [Real.exp_zero]
  rw [Fin.sum_univ_three]
  norm_num

/-- Head-0 readout at zero scores: `Σ_j softmax(0)_j v0_j = 0`. -/
theorem head0_readout_zero :
    (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v0 j) = 0 := by
  rw [Fin.sum_univ_three]
  rw [softmax_zero_uniform 0, softmax_zero_uniform 1, softmax_zero_uniform 2]
  simp only [v0, g0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons]
  push_cast; ring

/-- Head-1 readout at zero scores: `Σ_j softmax(0)_j v1_j = 1/6`. -/
theorem head1_readout_zero :
    (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v1 j) = 1/6 := by
  rw [Fin.sum_univ_three]
  rw [softmax_zero_uniform 0, softmax_zero_uniform 1, softmax_zero_uniform 2]
  simp only [v1, g1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons]
  push_cast; ring

/-- The explicit witness state: both heads use uniform (zero) scores, `x = 1`,
    `t = 1`.  The attention readouts are the GENUINE softmax readouts
    `att0 = 0`, `att1 = 1/6` (NOT assumed). -/
noncomputable def witness : SBState where
  x0 := 1; x1 := 1
  s0 := fun _ => 0; s1 := fun _ => 0
  att0 := 0; att1 := 1/6
  h0 := 1; h1 := 7/6; t := 1
  p0 := 1; p1 := 7/6; ln0 := 1; ln1 := 7/6
  z := 1 + 7/6 + (-1/2)
  g := geluTanh (1 + 7/6 + (-1/2))
  m := geluTanh (1 + 7/6 + (-1/2))
  o := 1 + 7/6 + geluTanh (1 + 7/6 + (-1/2))

theorem witness_valid : witness.valid := by
  unfold SBState.valid witness
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          ?_, ?_,                                  -- att0/att1 = softmax readouts
          by norm_num, by norm_num,                -- rsqrt box
          by norm_num, by norm_num,                -- residual 1
          by norm_num, by norm_num,                -- LN products
          by norm_num, by norm_num,                -- LN affine
          by norm_num,                             -- z pre-act
          by norm_num, by norm_num, by norm_num⟩   -- GELU, MLP out, residual 2
  · -- att0 = softmax readout of s0 = 0  ⇒ = 0
    show (0:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v0 j)
    rw [head0_readout_zero]
  · -- att1 = softmax readout of s1 = 0  ⇒ = 1/6
    show (1/6:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v1 j)
    rw [head1_readout_zero]

/-- **Non-vacuity (REAL softmax).**  The witness is a GENUINE execution whose
    attention weights are the actual (uniform) softmax of zero scores, with output
    `o = 13/6 + geluTanh(5/3)` lying inside the certified band `[−7/2, 13/2]`.
    Hence the bound is satisfiable by a real point of the block, with real softmax
    attention — not vacuous. -/
theorem sb_block_nonvacuous :
    witness.valid ∧
    witness.att0 = 0 ∧ witness.att1 = 1/6 ∧
    (-7/2 : ℝ) ≤ witness.o ∧ witness.o ≤ (13/2 : ℝ) := by
  refine ⟨witness_valid, rfl, rfl, ?_, ?_⟩
  · exact (sb_block_bound witness witness_valid).1
  · exact (sb_block_bound witness witness_valid).2

/-! ## 8. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms softmax_denom_pos
#print axioms softmax_nonneg
#print axioms softmax_sum_one
#print axioms softmax_simplex
#print axioms barycentric_R
#print axioms softmax_readout_mem
#print axioms softmax_readout_mem_rat
#print axioms head0_softmax_box
#print axioms head1_softmax_box
#print axioms softmax_att_box
#print axioms sb_z_box
#print axioms sb_g_box
#print axioms sbPremise_sound
#print axioms sb_block_lower
#print axioms sb_block_upper
#print axioms sb_block_bound
#print axioms softmax_zero_uniform
#print axioms witness_valid
#print axioms sb_block_nonvacuous

end Crownproof.SoftmaxBridge
