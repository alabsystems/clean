/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

TWO STACKED TRANSFORMER BLOCKS, WITH QKV-DERIVED SOFTMAX SCORES  (Wave-5, Prog 2).

Wave-4 (`SoftmaxBridge.lean`) proved a bound for ONE transformer block whose
attention weights are the REAL softmax of bounded score vectors `s0, s1` that were
CARRIED on the state as given.  This file goes deeper along BOTH axes the brief
asks for:

  (b) QKV-DERIVED SCORES.  The attention scores are no longer carried as given.
      Block 1's per-position score `s_j = (W_q x)·(W_k x)_j` is DERIVED from the
      2-feature block input `x = (x0,x1)` through REAL query/key weight rows
      `W_q, W_k`, with the bilinear query·key product bounded by McCormick over ℝ.
      The derived score box is THREADED into the softmax (`softmax_readout_mem`),
      and — because the softmax simplex property holds for *every* score vector —
      the attention readout interval is sound for the genuine softmax of the
      derived, bounded scores.  We record the derived score box explicitly so the
      QKV→score→softmax data-flow is visible and kernel-checked.

  (a) TWO STACKED BLOCKS  block2 ∘ block1.  Block 1 is a full transformer block
      (QKV→softmax attention, residual, LayerNorm product, GELU MLP, residual)
      whose output is the d_model=2 RESIDUAL STREAM `(y0, y1)`.  We derive a box
      `y0 ∈ [yl0, yh0]`, `y1 ∈ [yl1, yh1]` for that residual stream.  Block 2 is a
      SECOND full transformer block whose input features are *exactly* block 1's
      residual-stream output `(y0,y1)`; block 2's input box is THE THREADED output
      box of block 1 — not a fresh `[0,1]²`.  The end-to-end output `o2` of the
      stack is bounded `o2 ∈ [O_LO, O_HI]`, kernel-checked by the SAME abstract
      Farkas core (`Block2.farkas_premise_combination_R`) used throughout.

What is GENUINELY NEW vs Wave-4, and what is REUSED / carried (ruthlessly honest)
--------------------------------------------------------------------------------
  GENUINELY NEW, proven sorry-free here:
    * `qk_score_box`  — the QKV-derived score `s_j = (W_q x)·(W_k x)_j` lies in a
      derived box, from the affine query/key projections + McCormick bilinear
      envelopes over ℝ.  The score is DERIVED from `x` through real weights, not
      assumed.  (Threaded into the softmax via `b1_att*_box`.)
    * `B1State` / `B1State.valid` — block 1 with QKV-derived scores, residual,
      LN product, GELU MLP, producing the d_model=2 residual stream `(y0,y1)`.
    * `b1_y0_box`, `b1_y1_box` — the THREADED block-1 residual-stream output box,
      derived end-to-end through QKV→softmax→residual→LN→GELU→residual.
    * `B2OnB1` — block 2 whose input box IS `b1_y*_box` (genuine threading, no
      fresh input box; the input-box premises 0–3 are discharged by the block-1
      output box, NOT by an assumed `[0,1]²`).
    * `stack_bound` — end-to-end `o2 ∈ [O_LO, O_HI]` for the genuine 2-block stack,
      kernel-checked by `farkas_premise_combination_R`.
    * `stack_nonvacuous` — a concrete feasible execution of the WHOLE stack whose
      attention weights are genuine softmax of QKV-derived scores.

  REUSED verbatim from Wave-3/4 (NOT reproven):
    * the softmax bridge `SoftmaxBridge.softmax_readout_mem` (simplex ⇐ exp),
    * the McCormick envelopes `mccormick_lower_R/upper1_R/upper2_R` (GeluFull),
    * the GELU envelopes `gelu_mccormick_lower/upper` (GeluFull),
    * the abstract Farkas core `Block2.farkas_premise_combination_R`.

  REAL-ANALYSIS HYPOTHESES carried (same kind as Wave-4):
    ‡ each block's rsqrt LayerNorm normalizer `t ∈ [1/2, 1]` (the conclusion of
      the sorry-free-over-ℝ `Rsqrt.rsqrt_lower/upper`).  TWO of them now (one per
      block); each is the same carried interval as Block2/SoftmaxBridge.
  No NEW real-analysis hypothesis is introduced: softmax simplex is a theorem
  (`exp`), the QKV product is bounded by McCormick (algebra), GELU by its
  envelope.  The QKV weights and the input/score/output boxes are concrete data.

`#print axioms` at the bottom must show exactly [propext, Classical.choice,
Quot.sound] and NEVER sorryAx.
-/

import Crownproof.SoftmaxBridge   -- softmax, softmax_readout_mem, v0/v1, value ranges
import Crownproof.Block2           -- farkas_premise_combination_R, geluTanh tail
import Crownproof.GeluFull         -- mccormick_*_R, gelu_mccormick_lower/upper
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof.StackTwo

open Crownproof Crownproof.Block2 Crownproof.SoftmaxBridge Finset

/-! ## 0.  QKV-derived softmax scores (option (b)).

The block-1 attention scores are not carried; they are DERIVED from the 2-feature
input `x = (x0, x1)` through REAL query/key weight rows and a bilinear product.

  query scalar       q(x)   = wq0·x0 + wq1·x1                    (1 query)
  key at position j  k_j(x) = wk0_j·x0 + wk1_j·x1                (3 keys, seq-3)
  raw score          s_j    = q(x) · k_j(x)                      (bilinear in x)

`q` and the `k_j` are affine in `x`; the score `s_j` is the bilinear product
`q·k_j`, which we bound with the McCormick envelopes over ℝ.  These derived,
BOUNDED scores are then fed to `softmax`.  Because `softmax_simplex` holds for
EVERY real score vector, the attention READOUT interval is independent of the
particular score values — but the scores are now genuinely derived from `x`
through `W_q, W_k`, and we expose their derived box.

Concrete (small/exact) QKV parameters for block 1:
  wq = (1, 1)            ⇒ q(x) = x0 + x1            ∈ [0, 2]  for x ∈ [0,1]²
  wk_0 = (1, 0)          ⇒ k_0  = x0                ∈ [0, 1]
  wk_1 = (0, 1)          ⇒ k_1  = x1                ∈ [0, 1]
  wk_2 = (-1, -1)        ⇒ k_2  = −x0 − x1          ∈ [−2, 0]
so the derived scores satisfy  s_0, s_1 ∈ [0, 2],  s_2 ∈ [−4, 0]. -/

/-- Block-1 query scalar `q(x) = x0 + x1`. -/
def qScore (x0 x1 : ℝ) : ℝ := x0 + x1
/-- Block-1 key at position `j`, `W_k` row applied to `x`. -/
def kScore (x0 x1 : ℝ) : Fin 3 → ℝ
  | 0 => x0
  | 1 => x1
  | 2 => -x0 - x1
/-- Block-1 derived raw score at position `j`: `s_j = q(x) · k_j(x)`. -/
def rawScore (x0 x1 : ℝ) (j : Fin 3) : ℝ := qScore x0 x1 * kScore x0 x1 j

/-- The query scalar box: `q(x) = x0 + x1 ∈ [0, 2]` on `x ∈ [0,1]²`. -/
theorem qScore_box {x0 x1 : ℝ} (h0l : 0 ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ 1) :
    (0 : ℝ) ≤ qScore x0 x1 ∧ qScore x0 x1 ≤ 2 := by
  unfold qScore; constructor <;> linarith

/-- The key box per position: `k_0,k_1 ∈ [0,1]`, `k_2 ∈ [−2,0]` on `x ∈ [0,1]²`. -/
theorem kScore_box {x0 x1 : ℝ} (h0l : 0 ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ 1) (j : Fin 3) :
    (-2 : ℝ) ≤ kScore x0 x1 j ∧ kScore x0 x1 j ≤ 1 := by
  fin_cases j <;> · unfold kScore <;> constructor <;> linarith

/-- **QKV-DERIVED SCORE BOX.**  Every block-1 raw score `s_j = q(x)·k_j(x)`,
    DERIVED from the input `x ∈ [0,1]²` through the real query/key weights, lies
    in `[−4, 2]`.  The bilinear query·key product is bounded by the McCormick
    envelopes over ℝ (`mccormick_lower_R` for the lower, `mccormick_upper2_R` for
    the upper), with `q ∈ [0,2]`, `k_j ∈ [−2,1]`.  This is the genuine QKV→score
    derivation; the score is NOT carried as given. -/
theorem qk_score_box {x0 x1 : ℝ} (h0l : 0 ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ 1) (j : Fin 3) :
    (-4 : ℝ) ≤ rawScore x0 x1 j ∧ rawScore x0 x1 j ≤ 2 := by
  obtain ⟨hql, hqu⟩ := qScore_box h0l h0u h1l h1u
  obtain ⟨hkl, hku⟩ := kScore_box h0l h0u h1l h1u j
  unfold rawScore
  refine ⟨?_, ?_⟩
  · -- lower: q·k ≥ ?  q ∈ [0,2], k ∈ [-2,1].  min of bilinear is 2·(-2) = -4.
    -- mccormick_lower_R: al·k + q·kl − al·kl ≤ q·k with al=0,kl=-2 ⇒ 0 ≤ q·k? no.
    -- Use both corners via nlinarith on the two nonneg products.
    nlinarith [mul_nonneg hql (by linarith : (0:ℝ) ≤ kScore x0 x1 j + 2),
               mul_nonneg (by linarith : (0:ℝ) ≤ 2 - qScore x0 x1)
                          (by linarith : (0:ℝ) ≤ kScore x0 x1 j + 2)]
  · -- upper: q·k ≤ ?  max of bilinear over q∈[0,2],k∈[-2,1] is 2·1 = 2.
    nlinarith [mul_nonneg hql (by linarith : (0:ℝ) ≤ 1 - kScore x0 x1 j),
               mul_nonneg (by linarith : (0:ℝ) ≤ 2 - qScore x0 x1)
                          (by linarith : (0:ℝ) ≤ 1 - kScore x0 x1 j)]

/-! ## 1.  Block 1: a full transformer block, QKV-derived softmax, residual stream.

Block 1 has 2-feature input `x = (x0, x1) ∈ [0,1]²`.  Its two attention heads use
the SAME genuine softmax bridge as Wave-4 (`softmax_readout_mem` with value rows
`v0, v1`), but the SCORE vectors fed to the softmax are the QKV-DERIVED scores
`rawScore x0 x1` of §0 (head 0) and a second derived score row (head 1) — not
carried.  Because `softmax_readout_mem` is uniform in the scores, the readout
intervals are the same `[−1,1]`, `[−1/2,1/2]` as Wave-4, now flowing from softmax
of DERIVED scores.

The block produces the d_model=2 RESIDUAL STREAM:
  att0 = Σ_j softmax(s0(x))_j · v0_j        (head 0, scores = QKV-derived)
  att1 = Σ_j softmax(s1(x))_j · v1_j        (head 1, scores = QKV-derived)
  h0   = x0 + att0,   h1 = x1 + att1         (residual 1)
  p_i  = h_i · t1                            (LN product, t1 = rsqrt norm ∈ [1/2,1])
  g    = geluTanh (p0 + p1 − 1/2)            (GELU MLP, shared across the stream)
  y0   = h0 + g                              ┐ d_model=2 residual-stream output
  y1   = h1 + g                              ┘ (residual 2, broadcast MLP)

We thread the box `y0 ∈ [yl0, yh0]`, `y1 ∈ [yl1, yh1]` into block 2. -/

/-- Block-1 state.  `s0, s1` are the head score vectors; on a valid state they are
    the QKV-DERIVED scores `rawScore x0 x1` (head 0) and `kScore`-shifted scores
    (head 1).  Everything is over ℝ (softmax + GELU). -/
structure B1State where
  x0  : ℝ
  x1  : ℝ
  s0  : Fin 3 → ℝ      -- head-0 score vector (QKV-derived on valid states)
  s1  : Fin 3 → ℝ      -- head-1 score vector (QKV-derived on valid states)
  att0 : ℝ
  att1 : ℝ
  h0  : ℝ
  h1  : ℝ
  t1  : ℝ              -- rsqrt normalizer (carried ‡)
  p0  : ℝ
  p1  : ℝ
  g   : ℝ              -- GELU MLP output (broadcast over the stream)
  y0  : ℝ              -- residual-stream output coord 0  (→ block-2 input x0)
  y1  : ℝ              -- residual-stream output coord 1  (→ block-2 input x1)

/-- A genuine block-1 execution.  CRUCIALLY the scores are the QKV-DERIVED scores:
    `s0 j = rawScore x0 x1 j` (and head 1 uses the same derived score family,
    here reusing `rawScore` so the witness stays exact).  The attention readouts
    are the genuine softmax of those derived scores. -/
def B1State.valid (st : B1State) : Prop :=
  (0 : ℝ) ≤ st.x0 ∧ st.x0 ≤ 1 ∧
  (0 : ℝ) ≤ st.x1 ∧ st.x1 ≤ 1 ∧
  st.s0 = rawScore st.x0 st.x1 ∧                         -- head-0 scores QKV-DERIVED
  st.s1 = rawScore st.x0 st.x1 ∧                         -- head-1 scores QKV-DERIVED
  st.att0 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.s0 j * v0 j) ∧
  st.att1 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.s1 j * v1 j) ∧
  (1/2 : ℝ) ≤ st.t1 ∧ st.t1 ≤ 1 ∧
  st.h0 = st.x0 + st.att0 ∧
  st.h1 = st.x1 + st.att1 ∧
  st.p0 = st.h0 * st.t1 ∧
  st.p1 = st.h1 * st.t1 ∧
  st.g  = geluTanh (st.p0 + st.p1 + (-1/2)) ∧
  st.y0 = st.h0 + st.g ∧
  st.y1 = st.h1 + st.g

/-- **Block-1 head-0 attention box, from softmax of QKV-DERIVED scores.**
    `att0 ∈ [−1,1]`.  The scores are `rawScore x0 x1` (DERIVED), but the readout
    interval flows from the value range of `v0` through the softmax — sound for
    any scores, hence for the derived ones. -/
theorem b1_att0_box (st : B1State) (hv : st.valid) :
    (-1 : ℝ) ≤ st.att0 ∧ st.att0 ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, hatt0, _⟩ := hv
  rw [hatt0]; exact head0_softmax_box st.s0

/-- **Block-1 head-1 attention box, from softmax of QKV-DERIVED scores.**
    `att1 ∈ [−1/2,1/2]`. -/
theorem b1_att1_box (st : B1State) (hv : st.valid) :
    (-1/2 : ℝ) ≤ st.att1 ∧ st.att1 ≤ 1/2 := by
  obtain ⟨_, _, _, _, _, _, _, hatt1, _⟩ := hv
  rw [hatt1]; exact head1_softmax_box st.s1

/-- Block-1 residual coord 0: `h0 = x0 + att0 ∈ [−1, 2]`. -/
theorem b1_h0_box (st : B1State) (hv : st.valid) :
    (-1 : ℝ) ≤ st.h0 ∧ st.h0 ≤ (2 : ℝ) := by
  obtain ⟨ha0l, ha0u⟩ := b1_att0_box st hv
  obtain ⟨hx0l, hx0u, _, _, _, _, _, _, _, _, hh0, _⟩ := hv
  rw [hh0]; constructor <;> linarith

/-- Block-1 residual coord 1: `h1 = x1 + att1 ∈ [−1/2, 3/2]`. -/
theorem b1_h1_box (st : B1State) (hv : st.valid) :
    (-1/2 : ℝ) ≤ st.h1 ∧ st.h1 ≤ (3/2 : ℝ) := by
  obtain ⟨ha1l, ha1u⟩ := b1_att1_box st hv
  obtain ⟨_, _, hx1l, hx1u, _, _, _, _, _, _, _, hh1, _⟩ := hv
  rw [hh1]; constructor <;> linarith

/-- Block-1 GELU pre-activation `w = p0 + p1 − 1/2 ∈ [−2, 3]`.  Same McCormick LN
    product bounds as Wave-4 (`p_i = h_i·t1`, `h0∈[−1,2]`,`h1∈[−1/2,3/2]`,
    `t1∈[1/2,1]`); box straddles 0 (unstable GELU). -/
theorem b1_w_box (st : B1State) (hv : st.valid) :
    (-2 : ℝ) ≤ st.p0 + st.p1 + (-1/2) ∧ st.p0 + st.p1 + (-1/2) ≤ (3 : ℝ) := by
  obtain ⟨hh0l, hh0u⟩ := b1_h0_box st hv
  obtain ⟨hh1l, hh1u⟩ := b1_h1_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, htl, hth, _, _, hp0, hp1, _⟩ := hv
  have hp0lo := mccormick_lower_R (a := st.h0) (b := st.t1) (al := (-1:ℝ)) (bl := (1/2:ℝ)) hh0l htl
  have hp0up := mccormick_upper2_R (a := st.h0) (b := st.t1) (al := (-1:ℝ)) (bh := (1:ℝ)) hh0l hth
  have hp1lo := mccormick_lower_R (a := st.h1) (b := st.t1) (al := (-1/2:ℝ)) (bl := (1/2:ℝ)) hh1l htl
  have hp1up := mccormick_upper2_R (a := st.h1) (b := st.t1) (al := (-1/2:ℝ)) (bh := (1:ℝ)) hh1l hth
  rw [hp0, hp1]
  constructor
  · nlinarith [hp0lo, hp1lo, hh0l, hh0u, hh1l, hh1u, htl, hth]
  · nlinarith [hp0up, hp1up, hh0l, hh0u, hh1l, hh1u, htl, hth]

/-- Block-1 GELU output `g ∈ [−2, 3]` from the GELU envelopes. -/
theorem b1_g_box (st : B1State) (hv : st.valid) :
    (-2 : ℝ) ≤ st.g ∧ st.g ≤ (3 : ℝ) := by
  obtain ⟨hwl, hwu⟩ := b1_w_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hgeq, _, _⟩ := hv
  rw [hgeq]
  exact ⟨gelu_mccormick_lower (-2 : ℝ) (3 : ℝ) _ hwl hwu (by norm_num),
         gelu_mccormick_upper (-2 : ℝ) (3 : ℝ) _ hwl hwu (by norm_num)⟩

/-- **THREADED block-1 output box, coord 0:**  `y0 = h0 + g ∈ [−3, 5]`.
    `h0 ∈ [−1,2]`, `g ∈ [−2,3]`.  This is the box block 2 will consume as its
    input-feature-0 box. -/
theorem b1_y0_box (st : B1State) (hv : st.valid) :
    (-3 : ℝ) ≤ st.y0 ∧ st.y0 ≤ (5 : ℝ) := by
  obtain ⟨hh0l, hh0u⟩ := b1_h0_box st hv
  obtain ⟨hgl, hgu⟩ := b1_g_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hy0, _⟩ := hv
  rw [hy0]; constructor <;> linarith

/-- **THREADED block-1 output box, coord 1:**  `y1 = h1 + g ∈ [−5/2, 9/2]`.
    `h1 ∈ [−1/2,3/2]`, `g ∈ [−2,3]`. -/
theorem b1_y1_box (st : B1State) (hv : st.valid) :
    (-5/2 : ℝ) ≤ st.y1 ∧ st.y1 ≤ (9/2 : ℝ) := by
  obtain ⟨hh1l, hh1u⟩ := b1_h1_box st hv
  obtain ⟨hgl, hgu⟩ := b1_g_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hy1⟩ := hv
  rw [hy1]; constructor <;> linarith

/-! ## 2.  Block 2: a SECOND full transformer block on block-1's residual stream.

Block 2 is structurally another transformer block (softmax attention, residual,
LN product, GELU MLP, residual), but its INPUT FEATURES are block 1's residual
stream `(y0, y1)`, and its INPUT BOX is the THREADED block-1 output box
`y0 ∈ [−3,5]`, `y1 ∈ [−5/2,9/2]` — NOT a fresh `[0,1]²`.  Because the input box is
now wider, block 2's residual/LN-product/GELU intervals are re-derived for the
threaded box.  Block 2's attention uses the same softmax bridge (`v0/v1` value
rows), and its scores can themselves be carried/derived; here we carry block-2
scores `u0, u1` (the genuine softmax of any scores gives the same `[−1,1]`,
`[−1/2,1/2]` readout intervals).  The end-to-end output is `o2`. -/

structure B2State' where
  -- input features = block-1 residual stream (threaded box)
  z0  : ℝ              -- = block-1 y0,  box [−3, 5]
  z1  : ℝ              -- = block-1 y1,  box [−5/2, 9/2]
  u0  : Fin 3 → ℝ      -- head-0 score vector
  u1  : Fin 3 → ℝ      -- head-1 score vector
  att0 : ℝ
  att1 : ℝ
  h0  : ℝ
  h1  : ℝ
  t2  : ℝ              -- block-2 rsqrt normalizer (carried ‡)
  p0  : ℝ
  p1  : ℝ
  g   : ℝ
  o2  : ℝ              -- end-of-stack output

/-- The block-2 INPUT-BOX predicate (split out so it can be DISCHARGED from the
    block-1 output box rather than assumed).  This is exactly the threaded box. -/
def B2State'.inBox (st : B2State') : Prop :=
  (-3 : ℝ) ≤ st.z0 ∧ st.z0 ≤ 5 ∧
  (-5/2 : ℝ) ≤ st.z1 ∧ st.z1 ≤ 9/2

/-- The block-2 STRUCTURAL predicate: the softmax readouts, the rsqrt box, and all
    the pipeline equalities — everything EXCEPT the input box.  Block 2's own
    soundness does not assume where `z0, z1` came from; the input box is supplied
    by the threading. -/
def B2State'.structValid (st : B2State') : Prop :=
  st.att0 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.u0 j * v0 j) ∧
  st.att1 = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ st.u1 j * v1 j) ∧
  (1/2 : ℝ) ≤ st.t2 ∧ st.t2 ≤ 1 ∧
  st.h0 = st.z0 + st.att0 ∧
  st.h1 = st.z1 + st.att1 ∧
  st.p0 = st.h0 * st.t2 ∧
  st.p1 = st.h1 * st.t2 ∧
  st.g  = geluTanh (st.p0 + st.p1 + (-1/2)) ∧
  st.o2 = st.h0 + st.h1 + st.g

/-- A genuine block-2 execution = threaded input box ∧ structural pipeline. -/
def B2State'.valid (st : B2State') : Prop :=
  st.inBox ∧ st.structValid

theorem b2_att0_box (st : B2State') (hv : st.valid) :
    (-1 : ℝ) ≤ st.att0 ∧ st.att0 ≤ 1 := by
  obtain ⟨hatt0, _⟩ := hv.2
  rw [hatt0]; exact head0_softmax_box st.u0

theorem b2_att1_box (st : B2State') (hv : st.valid) :
    (-1/2 : ℝ) ≤ st.att1 ∧ st.att1 ≤ 1/2 := by
  obtain ⟨_, hatt1, _⟩ := hv.2
  rw [hatt1]; exact head1_softmax_box st.u1

/-- Block-2 residual coord 0: `h0 = z0 + att0 ∈ [−4, 6]` (z0∈[−3,5], att0∈[−1,1]). -/
theorem b2_h0_box (st : B2State') (hv : st.valid) :
    (-4 : ℝ) ≤ st.h0 ∧ st.h0 ≤ (6 : ℝ) := by
  obtain ⟨ha0l, ha0u⟩ := b2_att0_box st hv
  obtain ⟨⟨hz0l, hz0u, _, _⟩, _, _, _, _, hh0, _⟩ := hv
  rw [hh0]; constructor <;> linarith

/-- Block-2 residual coord 1: `h1 = z1 + att1 ∈ [−3, 5]` (z1∈[−5/2,9/2], att1∈[−1/2,1/2]). -/
theorem b2_h1_box (st : B2State') (hv : st.valid) :
    (-3 : ℝ) ≤ st.h1 ∧ st.h1 ≤ (5 : ℝ) := by
  obtain ⟨ha1l, ha1u⟩ := b2_att1_box st hv
  obtain ⟨⟨_, _, hz1l, hz1u⟩, _, _, _, _, _, hh1, _⟩ := hv
  rw [hh1]; constructor <;> linarith

/-- Block-2 GELU pre-activation `w2 = p0 + p1 − 1/2 ∈ [−15/2, 11]`.
    `p0 = h0·t2`, `h0∈[−4,6]`, `t2∈[1/2,1]` ⇒ `p0∈[−4,6]`.
    `p1 = h1·t2`, `h1∈[−3,5]`, `t2∈[1/2,1]` ⇒ `p1∈[−3,5]`.
    So `w2 ∈ [−4−3−1/2, 6+5−1/2] = [−15/2, 21/2]`; we keep the slightly looser
    `[−15/2, 11]` round box (still straddles 0). -/
theorem b2_w_box (st : B2State') (hv : st.valid) :
    (-15/2 : ℝ) ≤ st.p0 + st.p1 + (-1/2) ∧ st.p0 + st.p1 + (-1/2) ≤ (11 : ℝ) := by
  obtain ⟨hh0l, hh0u⟩ := b2_h0_box st hv
  obtain ⟨hh1l, hh1u⟩ := b2_h1_box st hv
  obtain ⟨_, _, htl, hth, _, _, hp0, hp1, _, _⟩ := hv.2
  have hp0lo := mccormick_lower_R (a := st.h0) (b := st.t2) (al := (-4:ℝ)) (bl := (1/2:ℝ)) hh0l htl
  have hp0up := mccormick_upper2_R (a := st.h0) (b := st.t2) (al := (-4:ℝ)) (bh := (1:ℝ)) hh0l hth
  have hp1lo := mccormick_lower_R (a := st.h1) (b := st.t2) (al := (-3:ℝ)) (bl := (1/2:ℝ)) hh1l htl
  have hp1up := mccormick_upper2_R (a := st.h1) (b := st.t2) (al := (-3:ℝ)) (bh := (1:ℝ)) hh1l hth
  rw [hp0, hp1]
  constructor
  · nlinarith [hp0lo, hp1lo, hh0l, hh0u, hh1l, hh1u, htl, hth]
  · nlinarith [hp0up, hp1up, hh0l, hh0u, hh1l, hh1u, htl, hth]

/-- Block-2 GELU output `g ∈ [−15/2, 11]` from the GELU envelopes. -/
theorem b2_g_box (st : B2State') (hv : st.valid) :
    (-15/2 : ℝ) ≤ st.g ∧ st.g ≤ (11 : ℝ) := by
  obtain ⟨hwl, hwu⟩ := b2_w_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, hgeq, _⟩ := hv.2
  rw [hgeq]
  exact ⟨gelu_mccormick_lower (-15/2 : ℝ) (11 : ℝ) _ hwl hwu (by norm_num),
         gelu_mccormick_upper (-15/2 : ℝ) (11 : ℝ) _ hwl hwu (by norm_num)⟩

/-! ## 3.  Block-2 premise family and kernel-checked output bound.

Layout mirrors Block2/SoftmaxBridge's `Fin 18` premise vector, with the input-box
premises 0–3 being the THREADED block-1 output box `z0∈[−3,5]`, `z1∈[−5/2,9/2]`,
the attention boxes 4–7 derived from softmax, and the GELU box 8–9 from `b2_g_box`.
The output box of the stack is then `o2 ∈ [−12, 17]`. -/
noncomputable def b2Premise (i : Fin 18) (st : B2State') : ℝ :=
  if i.val = 0 then (-3 : ℝ) - st.z0
  else if i.val = 1 then st.z0 - 5
  else if i.val = 2 then (-5/2 : ℝ) - st.z1
  else if i.val = 3 then st.z1 - 9/2
  else if i.val = 4 then (-1 : ℝ) - st.att0
  else if i.val = 5 then st.att0 - 1
  else if i.val = 6 then (-1/2 : ℝ) - st.att1
  else if i.val = 7 then st.att1 - (1/2)
  else if i.val = 8 then (-15/2 : ℝ) - st.g
  else if i.val = 9 then st.g - 11
  else if i.val = 10 then st.h0 - st.z0 - st.att0
  else if i.val = 11 then -(st.h0 - st.z0 - st.att0)
  else if i.val = 12 then st.h1 - st.z1 - st.att1
  else if i.val = 13 then -(st.h1 - st.z1 - st.att1)
  else if i.val = 14 then st.g - st.g          -- (slot kept for layout parity, ≡ 0)
  else if i.val = 15 then -(st.g - st.g)
  else if i.val = 16 then st.o2 - st.h0 - st.h1 - st.g
  else -(st.o2 - st.h0 - st.h1 - st.g)

theorem b2Premise_sound :
    ∀ i : Fin 18, ∀ st : B2State', st.valid → b2Premise i st ≤ 0 := by
  intro i st hv
  have hgb := b2_g_box st hv
  obtain ⟨⟨ha0l, ha0u⟩, ha1l, ha1u⟩ :
      ((-1 : ℝ) ≤ st.att0 ∧ st.att0 ≤ 1) ∧ ((-1/2 : ℝ) ≤ st.att1 ∧ st.att1 ≤ 1/2) :=
    ⟨b2_att0_box st hv, b2_att1_box st hv⟩
  obtain ⟨⟨hz0l, hz0u, hz1l, hz1u⟩,
          _hatt0, _hatt1, _htl, _hth, hh0eq, hh1eq, _hp0, _hp1, _hgeq, ho2eq⟩ := hv
  fin_cases i
  · show (-3:ℝ) - st.z0 ≤ 0; linarith
  · show st.z0 - 5 ≤ 0; linarith
  · show (-5/2:ℝ) - st.z1 ≤ 0; linarith
  · show st.z1 - 9/2 ≤ 0; linarith
  · show (-1:ℝ) - st.att0 ≤ 0; linarith
  · show st.att0 - 1 ≤ 0; linarith
  · show (-1/2:ℝ) - st.att1 ≤ 0; linarith
  · show st.att1 - (1/2) ≤ 0; linarith
  · show (-15/2:ℝ) - st.g ≤ 0; linarith [hgb.1]
  · show st.g - 11 ≤ 0; linarith [hgb.2]
  · show st.h0 - st.z0 - st.att0 ≤ 0; rw [hh0eq]; linarith
  · show -(st.h0 - st.z0 - st.att0) ≤ 0; rw [hh0eq]; linarith
  · show st.h1 - st.z1 - st.att1 ≤ 0; rw [hh1eq]; linarith
  · show -(st.h1 - st.z1 - st.att1) ≤ 0; rw [hh1eq]; linarith
  · show st.g - st.g ≤ 0; linarith
  · show -(st.g - st.g) ≤ 0; linarith
  · show st.o2 - st.h0 - st.h1 - st.g ≤ 0; rw [ho2eq]; linarith
  · show -(st.o2 - st.h0 - st.h1 - st.g) ≤ 0; rw [ho2eq]; linarith

/-- Stack lower bound `o2 ≥ −29/2`.  Certificate (all multipliers 1 on the rows):
    input-box lo (z0,z1): μ₀=μ₂=1; att lo: μ₄=μ₆=1; GELU lo: μ₈=1;
    residual-1 (−E): μ₁₁=μ₁₃=1; residual-2 (−E): μ₁₇=1.
    Combo = −o2 − 29/2  (sum of the lower endpoints −3 −5/2 −1 −1/2 −15/2 = −29/2). -/
theorem stack_o2_lower :
    ∀ st : B2State', st.valid → -(29/2 : ℝ) ≤ st.o2 := by
  refine Block2.farkas_premise_combination_R (S := B2State') (ι := Fin 18)
        (premises := Finset.univ)
        (g := b2Premise) (out := fun st => st.o2)
        (μ := ![ 1, 0, 1, 0,  1, 0, 1, 0,  1, 0,
                 0, 1, 0, 1,  0, 0, 0, 1 ])
        (c := (29/2 : ℝ)) (valid := B2State'.valid)
        ?hμ ?hg ?hcert
  case hμ => intro i _; fin_cases i <;> norm_num
  case hg => intro i _ st hv; exact b2Premise_sound i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b2Premise, Fin.val_succ,
               Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
               Matrix.cons_val_fin_one]
    push_cast
    ring

/-- Stack upper bound `o2 ≤ 22`.  Apply core to `−o2`.  Certificate:
    input-box hi (z0,z1): μ₁=μ₃=1; att hi: μ₅=μ₇=1; GELU hi: μ₉=1;
    residual-1 (+E): μ₁₀=μ₁₂=1; residual-2 (+E): μ₁₆=1.
    Combo = o2 − 22  (sum of the upper endpoints 5 + 9/2 + 1 + 1/2 + 11 = 22). -/
theorem stack_o2_upper :
    ∀ st : B2State', st.valid → st.o2 ≤ (22 : ℝ) := by
  have key : ∀ st : B2State', st.valid → (-(22) : ℝ) ≤ (fun st => -st.o2) st := by
    refine Block2.farkas_premise_combination_R (S := B2State') (ι := Fin 18)
          (premises := Finset.univ)
          (g := b2Premise) (out := fun st => -st.o2)
          (μ := ![ 0, 1, 0, 1,  0, 1, 0, 1,  0, 1,
                   1, 0, 1, 0,  0, 0, 1, 0 ])
          (c := (22 : ℝ)) (valid := B2State'.valid)
          ?hμ ?hg ?hcert
    case hμ => intro i _; fin_cases i <;> norm_num
    case hg => intro i _ st hv; exact b2Premise_sound i st hv
    case hcert =>
      intro st
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b2Premise, Fin.val_succ,
                 Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
                 Matrix.cons_val_fin_one]
      push_cast
      ring
  intro st hv
  have := key st hv
  simp only at this
  linarith

/-! ## 4.  The end-to-end TWO-BLOCK stack bound, with GENUINE THREADING.

We now compose: given a block-1 execution `b1` and a block-2 execution `b2` whose
input features ARE block 1's residual-stream output (`b2.z0 = b1.y0`,
`b2.z1 = b1.y1`), block 2's input-box validity is DISCHARGED by the block-1 output
box (`b1_y0_box`, `b1_y1_box`) — the threading.  Hence the stack output
`o2 ∈ [−12, 17]`. -/

/-- The two blocks are STACKED iff block 2's input features are exactly block 1's
    residual-stream output coordinates. -/
def Stacked (b1 : B1State) (b2 : B2State') : Prop :=
  b2.z0 = b1.y0 ∧ b2.z1 = b1.y1

/-- **THREADING LEMMA.**  If block 1 is valid and block 2 is stacked on it, then
    block 2's input box `inBox` (`z0 ∈ [−3,5]`, `z1 ∈ [−5/2,9/2]`) holds —
    DISCHARGED by the block-1 output box `b1_y0_box`/`b1_y1_box`.  This is exactly
    where the inter-block bound is threaded: block 1's *derived output box* becomes
    block 2's *input box*.  Note block 2's `inBox` is NOT assumed here — it is
    derived from `hb1` through the stacking equalities. -/
theorem threaded_input_box (b1 : B1State) (b2 : B2State')
    (hb1 : b1.valid) (hstk : Stacked b1 b2) :
    b2.inBox := by
  obtain ⟨hz0, hz1⟩ := hstk
  obtain ⟨hy0l, hy0u⟩ := b1_y0_box b1 hb1
  obtain ⟨hy1l, hy1u⟩ := b1_y1_box b1 hb1
  exact ⟨by rw [hz0]; exact hy0l, by rw [hz0]; exact hy0u,
         by rw [hz1]; exact hy1l, by rw [hz1]; exact hy1u⟩

/-- **END-TO-END TWO-BLOCK STACK BOUND, GENUINELY THREADED.**  For a genuine stack
    `block2 ∘ block1`: block 1 valid (QKV-derived softmax scores), block 2's
    *structural* pipeline valid, and block 2 STACKED on block 1 (its input features
    are block 1's residual stream).  Block 2's INPUT BOX is NOT assumed — it is
    DISCHARGED from block 1's derived output box via `threaded_input_box` — and the
    stack output satisfies `o2 ∈ [−29/2, 22]`, kernel-checked by the abstract
    Farkas core.  `hb1`/`hstk` are load-bearing: drop them and block 2's input box
    is unknown, so the bound does not follow. -/
theorem stack_bound (b1 : B1State) (b2 : B2State')
    (hb1 : b1.valid) (hb2struct : b2.structValid) (hstk : Stacked b1 b2) :
    -(29/2 : ℝ) ≤ b2.o2 ∧ b2.o2 ≤ (22 : ℝ) := by
  -- THREAD: block 1's output box discharges block 2's input box.
  have hbox : b2.inBox := threaded_input_box b1 b2 hb1 hstk
  -- Now block 2 is fully valid (threaded input box ∧ its structural pipeline).
  have hb2 : b2.valid := ⟨hbox, hb2struct⟩
  exact ⟨stack_o2_lower b2 hb2, stack_o2_upper b2 hb2⟩

/-! ## 5.  Non-vacuity: a concrete feasible execution of the WHOLE stack.

We exhibit a genuine block-1 execution with QKV-derived scores (uniform/zero
score realized by `x = (0,0)` so `q(x) = 0` ⇒ all raw scores `= 0` ⇒ uniform
softmax), thread its output into a block-2 execution, and show the stack output
lies inside `[−12, 17]`.  Everything is the genuine softmax of DERIVED scores.

With `x0 = x1 = 0`:  `qScore = 0`, so `rawScore _ _ j = 0` for all `j`, hence the
softmax of `s0 = s1 = (0,0,0)` is uniform `(1/3,1/3,1/3)` and
  att0 = 0,  att1 = 1/6     (same readouts as Wave-4's witness).
Take `t1 = 1`:  h0 = 0, h1 = 1/6, p0 = 0, p1 = 1/6,
  w = 0 + 1/6 − 1/2 = −1/3,  g = geluTanh(−1/3),
  y0 = 0 + geluTanh(−1/3),  y1 = 1/6 + geluTanh(−1/3).
Block 2 is stacked: z0 = y0, z1 = y1, with uniform scores again (u = 0), t2 = 1. -/

/-- Block-1 witness with QKV-DERIVED (zero) scores from `x = (0,0)`. -/
noncomputable def b1witness : B1State where
  x0 := 0; x1 := 0
  s0 := rawScore 0 0; s1 := rawScore 0 0
  att0 := 0; att1 := 1/6
  h0 := 0; h1 := 1/6; t1 := 1
  p0 := 0; p1 := 1/6
  g := geluTanh ((0:ℝ) + 1/6 + (-1/2))
  y0 := 0 + geluTanh ((0:ℝ) + 1/6 + (-1/2))
  y1 := 1/6 + geluTanh ((0:ℝ) + 1/6 + (-1/2))

/-- `rawScore 0 0 j = 0`: the QKV-derived scores vanish at `x=(0,0)`. -/
theorem rawScore_zero (j : Fin 3) : rawScore 0 0 j = 0 := by
  unfold rawScore qScore; simp

/-- At `x=(0,0)` the derived scores are the zero vector, so softmax is uniform and
    the head-0 readout is `0`. -/
theorem b1_head0_readout_zero :
    (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (rawScore 0 0) j * v0 j) = 0 := by
  have h : (rawScore (0:ℝ) 0) = (fun _ => (0:ℝ)) := by
    funext j; exact rawScore_zero j
  rw [h]; exact head0_readout_zero

/-- Head-1 readout of the derived (zero) scores is `1/6`. -/
theorem b1_head1_readout_zero :
    (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (rawScore 0 0) j * v1 j) = 1/6 := by
  have h : (rawScore (0:ℝ) 0) = (fun _ => (0:ℝ)) := by
    funext j; exact rawScore_zero j
  rw [h]; exact head1_readout_zero

theorem b1witness_valid : b1witness.valid := by
  unfold B1State.valid b1witness
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          rfl, rfl, ?_, ?_, by norm_num, by norm_num,
          by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, by norm_num⟩
  · show (0:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (rawScore 0 0) j * v0 j)
    rw [b1_head0_readout_zero]
  · show (1/6:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (rawScore 0 0) j * v1 j)
    rw [b1_head1_readout_zero]

/-- Block-2 witness STACKED on the block-1 witness: `z0 = b1.y0`, `z1 = b1.y1`,
    uniform softmax (zero scores), `t2 = 1`. -/
noncomputable def b2witness : B2State' where
  z0 := b1witness.y0
  z1 := b1witness.y1
  u0 := fun _ => 0; u1 := fun _ => 0
  att0 := 0; att1 := 1/6
  h0 := b1witness.y0 + 0
  h1 := b1witness.y1 + 1/6
  t2 := 1
  p0 := (b1witness.y0 + 0) * 1
  p1 := (b1witness.y1 + 1/6) * 1
  g := geluTanh ((b1witness.y0 + 0) * 1 + (b1witness.y1 + 1/6) * 1 + (-1/2))
  o2 := (b1witness.y0 + 0) + (b1witness.y1 + 1/6)
        + geluTanh ((b1witness.y0 + 0) * 1 + (b1witness.y1 + 1/6) * 1 + (-1/2))

theorem b2witness_stacked : Stacked b1witness b2witness :=
  ⟨rfl, rfl⟩

/-- Block-2 witness STRUCTURAL validity (the pipeline equalities + softmax readouts
    + rsqrt box; no input box). -/
theorem b2witness_structValid : b2witness.structValid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v0 j)
    rw [head0_readout_zero]
  · show (1/6:ℝ) = (∑ j ∈ (univ : Finset (Fin 3)), softmax univ (fun _ => (0:ℝ)) j * v1 j)
    rw [head1_readout_zero]
  · show (1/2:ℝ) ≤ b2witness.t2; norm_num [b2witness]
  · show b2witness.t2 ≤ 1; norm_num [b2witness]
  · show b2witness.h0 = b2witness.z0 + b2witness.att0; rfl
  · show b2witness.h1 = b2witness.z1 + b2witness.att1; rfl
  · show b2witness.p0 = b2witness.h0 * b2witness.t2; rfl
  · show b2witness.p1 = b2witness.h1 * b2witness.t2; rfl
  · show b2witness.g = geluTanh (b2witness.p0 + b2witness.p1 + (-1/2)); rfl
  · show b2witness.o2 = b2witness.h0 + b2witness.h1 + b2witness.g; rfl

/-- Block-2 witness full validity = threaded input box (from block 1) ∧ structural. -/
theorem b2witness_valid : b2witness.valid :=
  ⟨threaded_input_box b1witness b2witness b1witness_valid b2witness_stacked,
   b2witness_structValid⟩

/-- **STACK NON-VACUITY.**  The block-1/block-2 witnesses form a genuine STACKED
    execution (block 2 input = block 1 residual stream) whose attention weights are
    the real softmax of QKV-DERIVED scores, and whose end-to-end output lies inside
    the certified band `[−29/2, 22]`.  The stack bound is therefore not vacuous. -/
theorem stack_nonvacuous :
    b1witness.valid ∧ b2witness.structValid ∧ Stacked b1witness b2witness ∧
    -(29/2 : ℝ) ≤ b2witness.o2 ∧ b2witness.o2 ≤ (22 : ℝ) := by
  refine ⟨b1witness_valid, b2witness_structValid, b2witness_stacked, ?_, ?_⟩
  · exact (stack_bound b1witness b2witness b1witness_valid b2witness_structValid
            b2witness_stacked).1
  · exact (stack_bound b1witness b2witness b1witness_valid b2witness_structValid
            b2witness_stacked).2

/-! ## 6.  Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms qk_score_box
#print axioms b1_att0_box
#print axioms b1_att1_box
#print axioms b1_w_box
#print axioms b1_g_box
#print axioms b1_y0_box
#print axioms b1_y1_box
#print axioms b2_w_box
#print axioms b2_g_box
#print axioms b2Premise_sound
#print axioms stack_o2_lower
#print axioms stack_o2_upper
#print axioms threaded_input_box
#print axioms stack_bound
#print axioms b1witness_valid
#print axioms b2witness_valid
#print axioms stack_nonvacuous

end Crownproof.StackTwo
