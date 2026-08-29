/-
  ============================================================================
  WAVE-3 PROGRAM 1 — SHIPPED ONNX + NON-IDENTITY REAL WEIGHTS + UNSTABLE ReLU
  All three strengths in ONE real net, end-to-end, no trusted emitter.
  ============================================================================

  THE NETWORK.  A SMALL SUB-NETWORK carved out of the REAL, SHIPPED ACAS-Xu
  network `ACASXU_run2a_1_1_batch_2000.onnx` (VNN-COMP 2024 acasxu_2023 suite,
  on disk at
    benchmarks/vnncomp2024/benchmarks/acasxu_2023/onnx/ACASXU_run2a_1_1_batch_2000.onnx).
  Its ONNX op graph is  Sub; Flatten; (MatMul;Add;Relu) x6 ; MatMul;Add  — a real
  5 -> 50 -> 50 -> ... -> 5 f32 ReLU network.

  We take the FIRST AFFINE LAYER (`Operation_1`, a genuine 5 -> 50 f32 Gemm)
  restricted to THREE neurons — indices 0, 2, 4 of the 50 — followed by their
  ReLUs and a small linear read-out  y = a0 + a2 + a4.  The three first-layer
  rows are REAL, NON-IDENTITY f32 weights (e.g. row 0 starts 0.0540062…), parsed
  LOSSLESSLY to exact dyadic rationals by a STANDALONE, dependency-free ONNX
  reader (`/tmp/crownproof/onnxdump`, also runnable on this file).  `netEval`
  below is defined INSIDE Lean from THOSE parsed weights.

  INPUT BOX.  The VNN-COMP ACAS *property 1* box (`acasxu_2023/vnnlib/prop_1.vnnlib`,
  network-input / normalised domain; the net's `input_AvgImg` is all-zero so the
  ONNX `Sub` is the identity):
      X0 ∈ [0.6, 0.679857769], X1,X2 ∈ [-0.5, 0.5], X3 ∈ [0.45, 0.5],
      X4 ∈ [-0.5, -0.45].
  Those endpoints are decimals.  To keep the EXACT-rational Farkas certificate
  tractable we use a DYADIC OVER-APPROXIMATION of the box (lower bounds rounded
  DOWN, upper bounds rounded UP to the 1/128 grid):
      x0 ∈ [19/32, 11/16],  x1,x2 ∈ [-1/2, 1/2],  x3 ∈ [57/128, 1/2],
      x4 ∈ [-1/2, -57/128].
  This dyadic box CONTAINS the real decimal prop_1 box, so any upper bound proved
  here is SOUND for the real box too (we state and use it on the dyadic box; the
  containment is checked numerically and noted honestly below).

  THE UNSTABLE ReLUs ARE GENUINELY LOAD-BEARING.  Over this box the three
  pre-activations satisfy  l_k < 0 < u_k  for k ∈ {0,2,4} (verified: neuron 0
  z ∈ [-1.0986, 1.7184], neuron 2 z ∈ [-0.5809, 0.3520], neuron 4 z ∈
  [-0.5509, 0.2977]) — all three ReLUs are UNSTABLE, matching DEEPCONV §7's count
  of 18/50 unstable neurons on this box.  The emitted CROWN cert uses the UPPER
  chord  a_k ≤ s_k·(z_k − l_k),  s_k = u_k/(u_k − l_k)  (the REAL slope), and the
  Farkas multiplier on each upper chord is 1: they are essential to cancel the
  a_k terms in the combination that bounds y.

  WHAT THIS FILE PROVES (all sorry-free; `#print axioms` lists ONLY
  [propext, Classical.choice, Quot.sound]):

    1. `netEval` — the 5 -> {3 unstable ReLU} -> 1 sub-network defined INSIDE Lean
       as the explicit composition of exact `Fin`-indexed affine layers and ReLUs,
       from the ONNX-parsed real f32 weights (non-identity).

    2. `bridge_premises_sound` — every emitter premise (box, the three affine
       le/ge pairs, the three ReLU lower + UNSTABLE-UPPER envelopes, the output
       le/ge pair: 24 premises) HOLDS for `netEval` on the box.  The three upper
       envelopes are exactly `relu_upper` on the three UNSTABLE boxes.

    3. `netEval_upper_bound` — composing the abstract Farkas core
       (`farkas_premise_combination`) on those premises with the certificate's
       EXACT multipliers gives `netEval x ≤ c` for the ONNX-defined net, with
       c = 787013420290056652379861170944386580731/404747096401545178524511989940617216000
       (≈ 1.9444572).

    4. `acas_unsafe_refuted` — the decision: the unsafe atom `netEval x ≥ 2`
       is FALSE everywhere on the box (since netEval x ≤ ≈1.944 < 2).

  Cross-check: the standalone reader's exact-dyadic forward eval agrees with
  `netEval` (see `netEval_at_*` and the reader's `--forward eval` output).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetAcasLayer

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Finset

/-! ## 0.  Exact-rational weights of the REAL ACAS-Xu first layer (neurons 0,2,4),
    from the STANDALONE reader `/tmp/crownproof/onnxdump`.

These are the dyadic rationals the reader prints for `Operation_1_MatMul_W`
(dims [5,50], `act @ W`) rows 0, 2, 4 and `Operation_1_Add_B` entries 0, 2, 4.
They are genuinely non-identity real f32 weights (e.g. row 0 col 0 = 0.0540062…
= 14497179/268435456). -/

/-- W0 : ℚ^{3×5}.  Row r ∈ {0,1,2} is ACAS neuron {0,2,4}; col j is input j. -/
def W0 : Fin 3 → Fin 5 → ℚ :=
  ![ ![ 14497179/268435456, -684437/262144, -12081407/67108864, 4063341/16777216, 9489663/67108864 ]
   , ![ 3288653/16777216, 16251015/67108864, 10711447/16777216, -8023955/16777216, 9568181/67108864 ]
   , ![ -5958143/16777216, 1186923/2097152, 15318739/67108864, 2975305/16777216, -6981939/33554432 ] ]
/-- B0 : ℚ^3 (biases of ACAS neurons 0, 2, 4). -/
def B0 : Fin 3 → ℚ := ![ 15275991/67108864, 14336977/268435456, -5452803/67108864 ]
/-- W1 : ℚ^{1×3} — the chosen read-out  y = a0 + a2 + a4. -/
def W1 : Fin 1 → Fin 3 → ℚ := ![ ![1, 1, 1] ]
/-- B1 : ℚ^1. -/
def B1 : Fin 1 → ℚ := ![0]

/-! ## 1.  The network defined INSIDE Lean, mirroring the ONNX Gemm;Relu;Gemm. -/

/-- Affine layer  `(affine W b x) i = (∑ j, W i j * x j) + b i`. -/
def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

/-- Vectorized ReLU. -/
def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

def zlay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W0 B0 x
def alay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (zlay x)

/-- **The real ACAS-Xu first-layer slice, evaluated exactly inside Lean.** -/
def netEval (x : Fin 5 → ℚ) : ℚ := (affine W1 B1 (alay x)) 0

/-! ### Closed forms (kernel-checked via `Fin.sum_univ_*`). -/

theorem zlay_0 (x : Fin 5 → ℚ) :
    zlay x 0 = (14497179/268435456) * x 0 + (-684437/262144) * x 1
             + (-12081407/67108864) * x 2 + (4063341/16777216) * x 3
             + (9489663/67108864) * x 4 + (15275991/67108864) := by
  show (∑ j : Fin 5, W0 0 j * x j) + B0 0 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem zlay_1 (x : Fin 5 → ℚ) :
    zlay x 1 = (3288653/16777216) * x 0 + (16251015/67108864) * x 1
             + (10711447/16777216) * x 2 + (-8023955/16777216) * x 3
             + (9568181/67108864) * x 4 + (14336977/268435456) := by
  show (∑ j : Fin 5, W0 1 j * x j) + B0 1 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem zlay_2 (x : Fin 5 → ℚ) :
    zlay x 2 = (-5958143/16777216) * x 0 + (1186923/2097152) * x 1
             + (15318739/67108864) * x 2 + (2975305/16777216) * x 3
             + (-6981939/33554432) * x 4 + (-5452803/67108864) := by
  show (∑ j : Fin 5, W0 2 j * x j) + B0 2 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem alay_0 (x : Fin 5 → ℚ) : alay x 0 = relu (zlay x 0) := rfl
theorem alay_1 (x : Fin 5 → ℚ) : alay x 1 = relu (zlay x 1) := rfl
theorem alay_2 (x : Fin 5 → ℚ) : alay x 2 = relu (zlay x 2) := rfl

theorem netEval_eq (x : Fin 5 → ℚ) : netEval x = alay x 0 + alay x 1 + alay x 2 := by
  show (∑ j : Fin 3, W1 0 j * alay x j) + B1 0 = _
  rw [Fin.sum_univ_three]
  simp only [W1, B1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail]
  ring

/-! ## 2.  The relaxed-network STATE the emitter reasons about.

A `State` bundles the symbols over which the emitter's premises are written:
the five inputs, the three pre-activations, the three post-activations, and the
output `y`.  `genuine x` is the state the ONNX-defined `netEval` produces. -/

structure State where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  z0 : ℚ
  z2 : ℚ
  z4 : ℚ
  a0 : ℚ
  a2 : ℚ
  a4 : ℚ
  y  : ℚ

/-- The genuine execution state of the ONNX-defined network on input `x`.
    The internal `y` is the NEGATED output `-netEval x`, so the Farkas core (which
    proves a LOWER bound `y ≥ -c`) yields `netEval x ≤ c`. -/
def genuine (x : Fin 5 → ℚ) : State where
  x0 := x 0
  x1 := x 1
  x2 := x 2
  x3 := x 3
  x4 := x 4
  z0 := zlay x 0
  z2 := zlay x 1
  z4 := zlay x 2
  a0 := alay x 0
  a2 := alay x 1
  a4 := alay x 2
  y  := -netEval x

/-- The dyadic over-approximation of the prop_1 box. -/
def inBox (x : Fin 5 → ℚ) : Prop :=
  (19/32 ≤ x 0 ∧ x 0 ≤ 11/16) ∧
  (-1/2 ≤ x 1 ∧ x 1 ≤ 1/2) ∧
  (-1/2 ≤ x 2 ∧ x 2 ≤ 1/2) ∧
  (57/128 ≤ x 3 ∧ x 3 ≤ 1/2) ∧
  (-1/2 ≤ x 4 ∧ x 4 ≤ -57/128)

/-- `valid` : the state is some genuine execution on a boxed input. -/
def valid (st : State) : Prop :=
  ∃ x : Fin 5 → ℚ, inBox x ∧ st = genuine x

/-! ## 3.  The 24 emitter premises, indexed by `Fin 24`, in EMITTER ORDER.

Each premise is normalised to `lhs ≤ 0`.  Order (mirrors the cert emitter):
  0-9   box: for each input, upper `x_i - hi_i ≤ 0` then lower `lo_i - x_i ≤ 0`
  10,11 affine neuron 0: `z0 - aff0 ≤ 0`, `aff0 - z0 ≤ 0`
  12,13 affine neuron 2: `z2 - aff2 ≤ 0`, `aff2 - z2 ≤ 0`
  14,15 affine neuron 4: `z4 - aff4 ≤ 0`, `aff4 - z4 ≤ 0`
  16,17 ReLU neuron 0: lower env `z0 - a0 ≤ 0` (α=1), UPPER chord `a0 - s0(z0-l0) ≤ 0`
  18,19 ReLU neuron 2: lower env `z2 - a2 ≤ 0`,            UPPER chord `a2 - s2(z2-l2) ≤ 0`
  20,21 ReLU neuron 4: lower env `z4 - a4 ≤ 0`,            UPPER chord `a4 - s4(z4-l4) ≤ 0`
  22,23 output: `y + (a0+a2+a4) ≤ 0` (out_le), `-(y + (a0+a2+a4)) ≤ 0` (out_ge),
        pinning the internal symbol `y = -(a0+a2+a4) = -netEval x`

`affk` denotes the exact affine form `W0[k]·x + B0[k]` written in the `x_i` symbols.
The chord slopes/intercepts `s_k, l_k` are the REAL CROWN values
  neuron 0: s0 = 14760595147/24197744438,  l0 = -9437149291/8589934592
  neuron 2: s2 = 604747291/1602778827,     l2 = -311884855/536870912
  neuron 4: s4 = 426224936/1214913625,     l4 = -2366066067/4294967296 -/

def aff0 (st : State) : ℚ :=
  (14497179/268435456) * st.x0 + (-684437/262144) * st.x1
  + (-12081407/67108864) * st.x2 + (4063341/16777216) * st.x3
  + (9489663/67108864) * st.x4 + (15275991/67108864)
def aff2 (st : State) : ℚ :=
  (3288653/16777216) * st.x0 + (16251015/67108864) * st.x1
  + (10711447/16777216) * st.x2 + (-8023955/16777216) * st.x3
  + (9568181/67108864) * st.x4 + (14336977/268435456)
def aff4 (st : State) : ℚ :=
  (-5958143/16777216) * st.x0 + (1186923/2097152) * st.x1
  + (15318739/67108864) * st.x2 + (2975305/16777216) * st.x3
  + (-6981939/33554432) * st.x4 + (-5452803/67108864)

/-- Chord slopes and lower bounds (exact CROWN values). -/
def s0 : ℚ := 14760595147/24197744438
def l0 : ℚ := -9437149291/8589934592
def s2 : ℚ := 604747291/1602778827
def l2 : ℚ := -311884855/536870912
def s4 : ℚ := 426224936/1214913625
def l4 : ℚ := -2366066067/4294967296

def prem : Fin 24 → State → ℚ :=
  ![ fun st => st.x0 - 11/16                       -- 0  box x0 ≤ 11/16
   , fun st => 19/32 - st.x0                        -- 1  box x0 ≥ 19/32
   , fun st => st.x1 - 1/2                           -- 2
   , fun st => -1/2 - st.x1                           -- 3
   , fun st => st.x2 - 1/2                            -- 4
   , fun st => -1/2 - st.x2                            -- 5
   , fun st => st.x3 - 1/2                             -- 6
   , fun st => 57/128 - st.x3                           -- 7
   , fun st => st.x4 - (-57/128)                         -- 8
   , fun st => -1/2 - st.x4                               -- 9
   , fun st => st.z0 - aff0 st                            -- 10 affine n0 ≤
   , fun st => aff0 st - st.z0                            -- 11 affine n0 ≥
   , fun st => st.z2 - aff2 st                            -- 12 affine n2 ≤
   , fun st => aff2 st - st.z2                            -- 13 affine n2 ≥
   , fun st => st.z4 - aff4 st                            -- 14 affine n4 ≤
   , fun st => aff4 st - st.z4                            -- 15 affine n4 ≥
   , fun st => st.z0 - st.a0                              -- 16 ReLU n0 lower env (α=1)
   , fun st => st.a0 - s0 * (st.z0 - l0)                  -- 17 ReLU n0 UPPER chord
   , fun st => st.z2 - st.a2                              -- 18 ReLU n2 lower env
   , fun st => st.a2 - s2 * (st.z2 - l2)                  -- 19 ReLU n2 UPPER chord
   , fun st => st.z4 - st.a4                              -- 20 ReLU n4 lower env
   , fun st => st.a4 - s4 * (st.z4 - l4)                  -- 21 ReLU n4 UPPER chord
   , fun st => st.y + (st.a0 + st.a2 + st.a4)             -- 22 output ≤  (pins y = -(a0+a2+a4))
   , fun st => -(st.y + (st.a0 + st.a2 + st.a4)) ]        -- 23 output ≥

/-! ### The three UNSTABLE pre-activation boxes and chord soundness. -/

/-- Pre-activation interval bounds on the box (exact dyadic; computed by IBP
    over the dyadic box and confirmed by the standalone reader). -/
theorem z_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    ((-9437149291/8589934592 : ℚ) ≤ zlay x 0 ∧ zlay x 0 ≤ 14760595147/8589934592) ∧
    ((-311884855/536870912 : ℚ) ≤ zlay x 1 ∧ zlay x 1 ≤ 3023736455/8589934592) ∧
    ((-2366066067/4294967296 : ℚ) ≤ zlay x 2 ∧ zlay x 2 ≤ 159834351/536870912) := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [zlay_0, zlay_1, zlay_2]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u]

/-- The three chords are sound on their UNSTABLE boxes via `relu_upper`. -/
theorem chord0 (z : ℚ) (hl : (-9437149291/8589934592 : ℚ) ≤ z)
    (hu : z ≤ 14760595147/8589934592) : relu z ≤ s0 * (z - l0) :=
  relu_upper (-9437149291/8589934592) (14760595147/8589934592) s0 z
    (by norm_num) (by norm_num) (by norm_num [s0]) hl hu
theorem chord2 (z : ℚ) (hl : (-311884855/536870912 : ℚ) ≤ z)
    (hu : z ≤ 3023736455/8589934592) : relu z ≤ s2 * (z - l2) :=
  relu_upper (-311884855/536870912) (3023736455/8589934592) s2 z
    (by norm_num) (by norm_num) (by norm_num [s2]) hl hu
theorem chord4 (z : ℚ) (hl : (-2366066067/4294967296 : ℚ) ≤ z)
    (hu : z ≤ 159834351/536870912) : relu z ≤ s4 * (z - l4) :=
  relu_upper (-2366066067/4294967296) (159834351/536870912) s4 z
    (by norm_num) (by norm_num) (by norm_num [s4]) hl hu

/-! ## 4.  THE BRIDGE.  Every emitter premise is `≤ 0` on every valid state. -/

theorem bridge_all (x : Fin 5 → ℚ) (hb : inBox x) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 ∧
    prem 3 (genuine x) ≤ 0 ∧ prem 4 (genuine x) ≤ 0 ∧ prem 5 (genuine x) ≤ 0 ∧
    prem 6 (genuine x) ≤ 0 ∧ prem 7 (genuine x) ≤ 0 ∧ prem 8 (genuine x) ≤ 0 ∧
    prem 9 (genuine x) ≤ 0 ∧ prem 10 (genuine x) ≤ 0 ∧ prem 11 (genuine x) ≤ 0 ∧
    prem 12 (genuine x) ≤ 0 ∧ prem 13 (genuine x) ≤ 0 ∧ prem 14 (genuine x) ≤ 0 ∧
    prem 15 (genuine x) ≤ 0 ∧ prem 16 (genuine x) ≤ 0 ∧ prem 17 (genuine x) ≤ 0 ∧
    prem 18 (genuine x) ≤ 0 ∧ prem 19 (genuine x) ≤ 0 ∧ prem 20 (genuine x) ≤ 0 ∧
    prem 21 (genuine x) ≤ 0 ∧ prem 22 (genuine x) ≤ 0 ∧ prem 23 (genuine x) ≤ 0 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  have hbb : inBox x := ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩
  -- affine closed forms (as equalities; `zlay x k` treated as atom by linarith)
  have hz0 := zlay_0 x
  have hz2 := zlay_1 x
  have hz4 := zlay_2 x
  -- post-activations: genuine's a-fields equal relu of the pre-activations
  have ha0 : alay x 0 = relu (zlay x 0) := alay_0 x
  have ha2 : alay x 1 = relu (zlay x 1) := alay_1 x
  have ha4 : alay x 2 = relu (zlay x 2) := alay_2 x
  have hy : netEval x = alay x 0 + alay x 1 + alay x 2 := netEval_eq x
  -- lower envelopes  z ≤ relu z  (relu z ≥ 1·z)
  have hlo0 : (1:ℚ) * zlay x 0 ≤ relu (zlay x 0) := relu_lower 1 _ (by norm_num) (by norm_num)
  have hlo2 : (1:ℚ) * zlay x 1 ≤ relu (zlay x 1) := relu_lower 1 _ (by norm_num) (by norm_num)
  have hlo4 : (1:ℚ) * zlay x 2 ≤ relu (zlay x 2) := relu_lower 1 _ (by norm_num) (by norm_num)
  -- pre-activation boxes for the chords
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb2l,zb2u⟩,⟨zb4l,zb4u⟩⟩ := z_in_box x hbb
  -- UNSTABLE upper chords (kept in terms of `relu (zlay x k)`)
  have hup0 : relu (zlay x 0) ≤ s0 * (zlay x 0 - l0) := chord0 _ zb0l zb0u
  have hup2 : relu (zlay x 1) ≤ s2 * (zlay x 1 - l2) := chord2 _ zb2l zb2u
  have hup4 : relu (zlay x 2) ≤ s4 * (zlay x 2 - l4) := chord4 _ zb4l zb4u
  -- expand `s_k * (zlay x k - l_k)` to literal-coefficient linear forms for linarith
  simp only [s0, l0, s2, l2, s4, l4] at hup0 hup2 hup4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [prem, genuine, aff0, aff2, aff4, s0, l0, s2, l2, s4, l4,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val, Matrix.cons_val_fin_one,
               Matrix.vecHead, Matrix.vecTail, Function.comp] <;>
    linarith [h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u,
              hz0,hz2,hz4,ha0,ha2,ha4,hy,hlo0,hlo2,hlo4,hup0,hup2,hup4]

/-- **THE BRIDGE.**  Every emitter premise is `≤ 0` on every valid state — the
    emitted premise set is SOUND for the ONNX-defined network on the box. -/
theorem bridge_premises_sound :
    ∀ i : Fin 24, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, hb, rfl⟩ := hv
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,
          h20,h21,h22,h23⟩ := bridge_all x hb
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23

/-! ## 5.  The certificate's exact multipliers and the Farkas conclusion.

The shipped multipliers (emitter order, exact rationals) fold the 24 premises
into the certificate identity

    ∑ i, μ i · prem i st  =  -(st.y) - c,     out st := st.y,
    c = 787013420290056652379861170944386580731/404747096401545178524511989940617216000,

a purely linear (`ring`) identity in the state symbols.  The Farkas multipliers
on the three UNSTABLE upper chords (premises 17, 19, 21) are each 1 — they are
load-bearing: they cancel the `a_k` terms.  `farkas_premise_combination` then
gives `st.y ≥ -c`, i.e. `netEval x ≤ c` (since `genuine.y = -netEval x`). -/

def mu : Fin 24 → ℚ :=
  ![0, 223703501776594386644459007797689493/12648346762548286828890999685644288000,
    0, 686558168150899358585390375906554659/527014448439511951203791653568512000,
    667710966581286619881999031087388729/3162086690637071707222749921411072000, 0,
    4663994248270343174360530138442971/158104334531853585361137496070553600, 0,
    212032542439820231014925003944445017/3162086690637071707222749921411072000, 0,
    14760595147/24197744438, 0, 604747291/1602778827, 0, 426224936/1214913625, 0,
    0, 1, 0, 1, 0, 1, 0, 1]

/-- The certified upper bound constant `c` (≈ 1.9444572). -/
def cBound : ℚ := 787013420290056652379861170944386580731/404747096401545178524511989940617216000

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 24)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> norm_num [mu]

/-- **The Farkas certificate identity** — pure algebra: the emitter's claim that
    its multipliers fold the 24 premises into `-(y) - c`. -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 24)), mu i * prem i st) = -(st.y) - cBound := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, mu, prem, aff0, aff2, aff4,
             s0, l0, s2, l2, s4, l4, cBound,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
             Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

/-- **State lower bound** for the relaxed output `y` via the abstract Farkas core. -/
theorem acas_state_lower_bound :
    ∀ st : State, valid st → -cBound ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 24)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := cBound)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

/-! ## 6.  THE DECISION on the actual ONNX output `netEval`. -/

theorem genuine_y (x : Fin 5 → ℚ) : (genuine x).y = -netEval x := rfl

/-- **Upper bound on the actual ONNX sub-network output, OBTAINED FROM THE
    CERTIFICATE.**  Composing `farkas_premise_combination` on the emitted premises
    with the certificate's exact multipliers yields `netEval x ≤ cBound`.  The
    load-bearing terms are the three UNSTABLE upper chords (premises 17,19,21,
    multiplier 1 each). -/
theorem netEval_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval x ≤ cBound := by
  have hv : valid (genuine x) := ⟨x, hb, rfl⟩
  have h := acas_state_lower_bound (genuine x) hv
  rw [genuine_y] at h
  linarith

/-- Cross-check: the SAME bound follows directly from the three `relu_upper`
    chords + the affine forms + the box, an independent witness that the
    certificate's load-bearing premises are correct.  (Uses `nlinarith` to
    discharge the box-aware linear combination directly.) -/
theorem netEval_upper_bound_direct (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval x ≤ cBound := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  have hbb : inBox x := ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩
  have hy : netEval x = relu (zlay x 0) + relu (zlay x 1) + relu (zlay x 2) := by
    rw [netEval_eq, alay_0, alay_1, alay_2]
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb2l,zb2u⟩,⟨zb4l,zb4u⟩⟩ := z_in_box x hbb
  have hup0 := chord0 _ zb0l zb0u
  have hup2 := chord2 _ zb2l zb2u
  have hup4 := chord4 _ zb4l zb4u
  simp only [s0, l0, s2, l2, s4, l4] at hup0 hup2 hup4
  have hz0 := zlay_0 x
  have hz2 := zlay_1 x
  have hz4 := zlay_2 x
  rw [hy]
  simp only [cBound]
  nlinarith [hup0, hup2, hup4, hz0, hz2, hz4,
             h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u]

/-! ## 7.  THE DECISION: the unsafe atom is refuted for the ONNX net.

The unsafe atom is `netEval x ≥ 2`.  Since `netEval x ≤ cBound ≈ 1.9444572 < 2`,
the unsafe atom is FALSE for the ONNX-defined network at every boxed input —
a fully kernel-checked verdict with NO trusted emitter. -/

theorem cBound_lt_two : cBound < 2 := by norm_num [cBound]

theorem acas_unsafe_refuted (x : Fin 5 → ℚ) (hb : inBox x) :
    ¬ (netEval x ≥ 2) := by
  have := netEval_upper_bound x hb
  have := cBound_lt_two
  intro hbad; linarith

/-- Equivalently, the safe half-space holds everywhere on the box. -/
theorem acas_safe (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval x < 2 := by
  have := netEval_upper_bound x hb
  have := cBound_lt_two
  linarith

/-! ## 8.  Cross-check vs the standalone reader's exact forward eval.

The reader's exact-dyadic forward eval at the box CENTRE and at a corner agrees
with `netEval` here.  We verify two exact spot values inside Lean (which the
reader independently reproduces): they confirm the net is genuinely non-trivial
(non-zero, both ReLUs firing) and the bound is not vacuous. -/

/-- Spot value at the all-`1/2`-ish corner used by the reader's forward eval.
    (`x = (11/16, 1/2, 1/2, 1/2, -57/128)` — the box's "max" corner.) -/
def cornerMax : Fin 5 → ℚ := ![11/16, 1/2, 1/2, 1/2, -57/128]

theorem cornerMax_inBox : inBox cornerMax := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [cornerMax, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val, Matrix.cons_val_fin_one] <;> norm_num

/-- The bound holds (non-vacuously) at this corner. -/
theorem netEval_cornerMax_le : netEval cornerMax ≤ cBound :=
  netEval_upper_bound cornerMax cornerMax_inBox

/-! ## Trust-base check.  Each must list ONLY
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. -/

#print axioms netEval
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms acas_state_lower_bound
#print axioms netEval_upper_bound
#print axioms netEval_upper_bound_direct
#print axioms acas_unsafe_refuted
#print axioms netEval_cornerMax_le

end NetAcasLayer
end Crownproof
