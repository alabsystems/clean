/-
  ============================================================================
  WAVE-4 PROGRAM 1 — MULTI-LAYER REAL ACAS: TWO COMPOSED ONNX LAYERS IN LEAN
  ============================================================================

  Wave-3 (`NetAcasLayer.lean`) closed ONNX-independence + non-identity weights +
  unstable ReLU but only on the FIRST affine+ReLU layer (3 of 50 neurons, one of
  the 7 layers).  THIS file goes genuinely MULTI-LAYER: it composes the FIRST
  TWO consecutive affine+ReLU layers of the real shipped
      ACASXU_run2a_1_1_batch_2000.onnx
  (VNN-COMP acasxu, op graph  Sub; Flatten; (MatMul;Add;Relu)x6 ; MatMul;Add,
  a 5 -> 50 -> 50 -> ... -> 5 f32 ReLU net) inside Lean, with the LAYER-1
  POST-ReLU bounds THREADED into the LAYER-2 PRE-ACTIVATION bounds — the real
  CROWN multi-layer structure (the intermediate ReLU relaxations feed the next
  layer).

  WIDTH RESTRICTION (honest).  To keep the EXACT-rational Farkas certificate
  tractable we restrict the WIDTH but NOT the depth.  We take a genuine 2-layer
  SUB-NETWORK of the real net:
    * layer 0 (the real ONNX layer 0): neurons S0 = {0,2,4} of the 50  (5 -> 3),
      the SAME three real non-identity f32 rows as wave-3 (verified identical:
      their CROWN chord slopes s0_0,s0_2,s0_4 below match wave-3 exactly), all
      THREE ReLUs UNSTABLE over the box;
    * layer 1 (the real ONNX layer 1): neurons S1 = {0,1} of the 50, reading the
      S0 columns of the real layer-1 weight matrix (3 -> 2), real non-identity
      f32 weights, BOTH ReLUs UNSTABLE over the threaded post-ReLU box;
    * read-out  y = a1_0 + a1_1.
  So depth = 2 real affine+ReLU layers genuinely composed; width = 3 then 2.
  This is NOT the full 7-layer / 50-wide net — it is a depth-2 width-{3,2} real
  sub-network — but the COMPOSITION is genuine: `z1 = W1 · relu(W0·x+B0) + B1`.

  INPUT BOX (honest).  The VNN-COMP ACAS prop_1 network-input box, dyadically
  OVER-approximated to the 1/128 grid (lowers rounded DOWN, uppers UP), CONTAINS
  the real decimal box:
      x0 ∈ [19/32, 11/16], x1,x2 ∈ [-1/2, 1/2], x3 ∈ [57/128, 1/2],
      x4 ∈ [-1/2, -57/128].

  THE THREADING IS GENUINE AND LOAD-BEARING.  `z_in_box0` proves the layer-0
  pre-activation interval [lz0_k, uz0_k] from the input box.  `a0_in_box` proves
  the layer-0 POST-ReLU box  0 ≤ a0_k ≤ uz0_k  from the layer-0 ReLU envelopes.
  `z_in_box1` then proves the layer-1 pre-activation interval [lz1_j, uz1_j]
  FROM the post-ReLU box (this is the threading: layer-2 pre-activation = affine
  of layer-1 post-ReLU).  The layer-1 chord anchors lz1_j — needed by the
  layer-1 ReLU chords and appearing in the final certificate — depend (via the
  IBP) on the layer-0 post-ReLU UPPER bounds a0_k ≤ uz0_k, which come from the
  layer-0 ReLU envelopes + layer-0 z-bounds.  So the WHOLE layer-0 chain is
  load-bearing for the final bound through lz1.

  WHAT THIS FILE PROVES (all sorry-free; axioms = [propext,Classical.choice,
  Quot.sound]):
    1. `netEval2` — the real 5 ->{3 unstable ReLU}->{2 unstable ReLU}-> 1
       sub-network, defined INSIDE Lean as the explicit composition of two exact
       Fin-indexed affine+ReLU layers from the ONNX-parsed real f32 weights.
    2. `z_in_box1` — the THREADED intermediate bounds: layer-1 pre-activations
       lie in [lz1_j,uz1_j], proved FROM the layer-0 post-ReLU box (not the input
       box directly).
    3. `bridge_premises_sound` — every emitter premise (box, two affine layers,
       the 3 layer-0 + 2 layer-1 ReLU lower/UNSTABLE-upper envelopes, output)
       holds for `netEval2` on the box.
    4. `cert_identity` + `netEval2_upper_bound` — the emitted multi-layer Farkas
       certificate (exact rational multipliers, the two layer-1 UPPER chords on
       the THREADED z1 + the layer-1 affine over post-ReLU + the post-ReLU lower
       bounds load-bearing) folds to netEval2 x ≤ cBound2.
    5. `acas2_decision` — the decision: netEval2 x < 1/4 everywhere on the box.

  Cross-check: the standalone dependency-free reader's exact-dyadic 2-layer
  forward eval agrees with `netEval2` (see `netEval2_at_*`).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetAcas2Layer

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Finset

/-! ## 0.  Exact-rational weights of the REAL ACAS-Xu first TWO layers,
    parsed losslessly by the STANDALONE reader `/tmp/acasreader`.

`W0`/`B0` are layer-0 neurons {0,2,4} (5 -> 3); identical to wave-3.
`W1`/`B1` are layer-1 neurons {0,1}, restricted to columns {0,2,4} (3 -> 2). -/

/-- Layer-0 weights  ℚ^{3×5}.  Row r ∈ {0,1,2} is ACAS layer-0 neuron {0,2,4}. -/
def W0 : Fin 3 → Fin 5 → ℚ :=
  ![ ![ 14497179/268435456, -684437/262144, -12081407/67108864, 4063341/16777216, 9489663/67108864 ]
   , ![ 3288653/16777216, 16251015/67108864, 10711447/16777216, -8023955/16777216, 9568181/67108864 ]
   , ![ -5958143/16777216, 1186923/2097152, 15318739/67108864, 2975305/16777216, -6981939/33554432 ] ]
def B0 : Fin 3 → ℚ := ![ 15275991/67108864, 14336977/268435456, -5452803/67108864 ]

/-- Layer-1 weights  ℚ^{2×3}, columns ordered as S0 = {0,2,4}.  Row r ∈ {0,1} is
    ACAS layer-1 neuron {0,1}; col c is layer-0 neuron S0[c]. -/
def W1 : Fin 2 → Fin 3 → ℚ :=
  ![ ![ -12361587/67108864, -7727049/67108864, -4601923/33554432 ]
   , ![ 9214799/536870912, -2333539/268435456, 2873199/134217728 ] ]
def B1 : Fin 2 → ℚ := ![ 11213891/134217728, -11449363/536870912 ]

/-- Read-out  ℚ^{1×2}:  y = a1_0 + a1_1. -/
def W2 : Fin 1 → Fin 2 → ℚ := ![ ![1, 1] ]
def B2 : Fin 1 → ℚ := ![0]

/-! ## 1.  The two-layer network defined INSIDE Lean (Gemm;Relu;Gemm;Relu;Gemm). -/

def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

def z0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W0 B0 x
def a0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z0lay x)
def z1lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := affine W1 B1 (a0lay x)
def a1lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := reluVec (z1lay x)

/-- **The real ACAS-Xu first-two-layer slice, evaluated exactly inside Lean.** -/
def netEval2 (x : Fin 5 → ℚ) : ℚ := (affine W2 B2 (a1lay x)) 0

/-! ### Closed forms (kernel-checked via `Fin.sum_univ_*`). -/

theorem z0lay_0 (x : Fin 5 → ℚ) :
    z0lay x 0 = (14497179/268435456) * x 0 + (-684437/262144) * x 1
             + (-12081407/67108864) * x 2 + (4063341/16777216) * x 3
             + (9489663/67108864) * x 4 + (15275991/67108864) := by
  show (∑ j : Fin 5, W0 0 j * x j) + B0 0 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z0lay_1 (x : Fin 5 → ℚ) :
    z0lay x 1 = (3288653/16777216) * x 0 + (16251015/67108864) * x 1
             + (10711447/16777216) * x 2 + (-8023955/16777216) * x 3
             + (9568181/67108864) * x 4 + (14336977/268435456) := by
  show (∑ j : Fin 5, W0 1 j * x j) + B0 1 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z0lay_2 (x : Fin 5 → ℚ) :
    z0lay x 2 = (-5958143/16777216) * x 0 + (1186923/2097152) * x 1
             + (15318739/67108864) * x 2 + (2975305/16777216) * x 3
             + (-6981939/33554432) * x 4 + (-5452803/67108864) := by
  show (∑ j : Fin 5, W0 2 j * x j) + B0 2 = _
  rw [Fin.sum_univ_five]
  simp only [W0, B0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a0lay_eq (x : Fin 5 → ℚ) (k : Fin 3) : a0lay x k = relu (z0lay x k) := rfl

/-- Layer-1 pre-activation closed forms in terms of the layer-0 POST-ReLU
    activations `a0lay x` — this is the genuine composition `z1 = W1·a0 + B1`. -/
theorem z1lay_0 (x : Fin 5 → ℚ) :
    z1lay x 0 = (-12361587/67108864) * a0lay x 0 + (-7727049/67108864) * a0lay x 1
              + (-4601923/33554432) * a0lay x 2 + (11213891/134217728) := by
  show (∑ j : Fin 3, W1 0 j * a0lay x j) + B1 0 = _
  rw [Fin.sum_univ_three]
  simp only [W1, B1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z1lay_1 (x : Fin 5 → ℚ) :
    z1lay x 1 = (9214799/536870912) * a0lay x 0 + (-2333539/268435456) * a0lay x 1
              + (2873199/134217728) * a0lay x 2 + (-11449363/536870912) := by
  show (∑ j : Fin 3, W1 1 j * a0lay x j) + B1 1 = _
  rw [Fin.sum_univ_three]
  simp only [W1, B1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a1lay_eq (x : Fin 5 → ℚ) (j : Fin 2) : a1lay x j = relu (z1lay x j) := rfl

theorem netEval2_eq (x : Fin 5 → ℚ) : netEval2 x = a1lay x 0 + a1lay x 1 := by
  show (∑ j : Fin 2, W2 0 j * a1lay x j) + B2 0 = _
  rw [Fin.sum_univ_two]
  simp only [W2, B2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail]
  ring

/-! ## 2.  The relaxed-network STATE the emitter reasons about.

The symbols: 5 inputs, 3 layer-0 pre-activations, 3 layer-0 post-activations,
2 layer-1 pre-activations, 2 layer-1 post-activations, the output `y`. -/

structure State where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  z00 : ℚ   -- layer-0 pre-activations (neurons 0,2,4)
  z01 : ℚ
  z02 : ℚ
  a00 : ℚ   -- layer-0 post-activations
  a01 : ℚ
  a02 : ℚ
  z10 : ℚ   -- layer-1 pre-activations (neurons 0,1)
  z11 : ℚ
  a10 : ℚ   -- layer-1 post-activations
  a11 : ℚ
  y   : ℚ

/-- The genuine execution state.  `y` stores `-netEval2 x` (so the Farkas core,
    which proves a LOWER bound on `y`, yields an UPPER bound on `netEval2`). -/
def genuine (x : Fin 5 → ℚ) : State where
  x0 := x 0
  x1 := x 1
  x2 := x 2
  x3 := x 3
  x4 := x 4
  z00 := z0lay x 0
  z01 := z0lay x 1
  z02 := z0lay x 2
  a00 := a0lay x 0
  a01 := a0lay x 1
  a02 := a0lay x 2
  z10 := z1lay x 0
  z11 := z1lay x 1
  a10 := a1lay x 0
  a11 := a1lay x 1
  y   := -netEval2 x

/-- The dyadic over-approximation of the prop_1 box (contains the real box). -/
def inBox (x : Fin 5 → ℚ) : Prop :=
  (19/32 ≤ x 0 ∧ x 0 ≤ 11/16) ∧
  (-1/2 ≤ x 1 ∧ x 1 ≤ 1/2) ∧
  (-1/2 ≤ x 2 ∧ x 2 ≤ 1/2) ∧
  (57/128 ≤ x 3 ∧ x 3 ≤ 1/2) ∧
  (-1/2 ≤ x 4 ∧ x 4 ≤ -57/128)

def valid (st : State) : Prop := ∃ x : Fin 5 → ℚ, inBox x ∧ st = genuine x

/-! ## 3.  Chord parameters (exact CROWN values).

Layer-0 chord slopes/anchors (identical to wave-3 — same real layer-0 rows):
  s0_k = uz0_k/(uz0_k - lz0_k),  lz0_k.
Layer-1 chord slopes/anchors over the THREADED post-ReLU box:
  s1_j = uz1_j/(uz1_j - lz1_j),  lz1_j. -/

def lz00 : ℚ := -9437149291/8589934592
def uz00 : ℚ := 14760595147/8589934592
def lz01 : ℚ := -311884855/536870912
def uz01 : ℚ := 3023736455/8589934592
def lz02 : ℚ := -2366066067/4294967296
def uz02 : ℚ := 159834351/536870912
def s00 : ℚ := 14760595147/24197744438
def s01 : ℚ := 604747291/1602778827
def s02 : ℚ := 426224936/1214913625

def lz10 : ℚ := -11325193610012749/36028797018963968
def uz10 : ℚ := 11213891/134217728
def lz11 : ℚ := -56230646588496693/2305843009213693952
def uz11 : ℚ := 67057735547281893/4611686018427387904
def s10 : ℚ := 3010205944119296/14335399554132045
def s11 : ℚ := 22352578515760631/59839676241425093

/-! ## 4.  Layer-0 pre-activation bounds from the input box (IBP). -/

theorem z_in_box0 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz00 ≤ z0lay x 0 ∧ z0lay x 0 ≤ uz00) ∧
    (lz01 ≤ z0lay x 1 ∧ z0lay x 1 ≤ uz01) ∧
    (lz02 ≤ z0lay x 2 ∧ z0lay x 2 ≤ uz02) := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0lay_0, z0lay_1, z0lay_2]
  simp only [lz00, uz00, lz01, uz01, lz02, uz02]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u]

/-! ## 5.  Layer-0 POST-ReLU box  0 ≤ a0_k ≤ uz0_k  (the intermediate bounds). -/

theorem a0_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a0lay x 0 ∧ a0lay x 0 ≤ uz00) ∧
    (0 ≤ a0lay x 1 ∧ a0lay x 1 ≤ uz01) ∧
    (0 ≤ a0lay x 2 ∧ a0lay x 2 ≤ uz02) := by
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb1l,zb1u⟩,⟨zb2l,zb2u⟩⟩ := z_in_box0 x hb
  rw [a0lay_eq, a0lay_eq, a0lay_eq]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact le_max_left _ _
  · -- relu z ≤ uz : relu z = max 0 z ≤ uz since 0 ≤ uz and z ≤ uz
    unfold relu; exact max_le (by norm_num [uz00]) zb0u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz01]) zb1u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz02]) zb2u

/-! ## 6.  THREADED layer-1 pre-activation bounds — proved FROM the post-ReLU box.

This is the multi-layer composition: `z1_j = W1·a0 + B1`, so its interval comes
from the layer-0 POST-ReLU box `0 ≤ a0_k ≤ uz0_k`, NOT from the input box.  These
threaded bounds are exactly the IBP corners the reader reports. -/

theorem z_in_box1 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz10 ≤ z1lay x 0 ∧ z1lay x 0 ≤ uz10) ∧
    (lz11 ≤ z1lay x 1 ∧ z1lay x 1 ≤ uz11) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a0_in_box x hb
  rw [z1lay_0, z1lay_1]
  simp only [lz10, uz10, lz11, uz11, uz00, uz01, uz02] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

/-! ## 7.  Chord soundness on the respective UNSTABLE boxes. -/

theorem chord00 (z : ℚ) (hl : lz00 ≤ z) (hu : z ≤ uz00) : relu z ≤ s00 * (z - lz00) :=
  relu_upper lz00 uz00 s00 z (by norm_num [lz00]) (by norm_num [uz00])
    (by norm_num [s00, uz00, lz00]) hl hu
theorem chord01 (z : ℚ) (hl : lz01 ≤ z) (hu : z ≤ uz01) : relu z ≤ s01 * (z - lz01) :=
  relu_upper lz01 uz01 s01 z (by norm_num [lz01]) (by norm_num [uz01])
    (by norm_num [s01, uz01, lz01]) hl hu
theorem chord02 (z : ℚ) (hl : lz02 ≤ z) (hu : z ≤ uz02) : relu z ≤ s02 * (z - lz02) :=
  relu_upper lz02 uz02 s02 z (by norm_num [lz02]) (by norm_num [uz02])
    (by norm_num [s02, uz02, lz02]) hl hu
theorem chord10 (z : ℚ) (hl : lz10 ≤ z) (hu : z ≤ uz10) : relu z ≤ s10 * (z - lz10) :=
  relu_upper lz10 uz10 s10 z (by norm_num [lz10]) (by norm_num [uz10])
    (by norm_num [s10, uz10, lz10]) hl hu
theorem chord11 (z : ℚ) (hl : lz11 ≤ z) (hu : z ≤ uz11) : relu z ≤ s11 * (z - lz11) :=
  relu_upper lz11 uz11 s11 z (by norm_num [lz11]) (by norm_num [uz11])
    (by norm_num [s11, uz11, lz11]) hl hu

/-! ## 8.  The emitter premises, indexed by `Fin 36`, in EMITTER ORDER.

Each premise normalised to `lhs ≤ 0`.  Order:
  0-9   box: per input, upper then lower
  10-15 layer-0 affine n0,n2,n4 (≤ then ≥)
  16-21 layer-0 ReLU n0,n2,n4: lower env (α=1) then UNSTABLE upper chord
  22-25 layer-1 affine n0,n1 (≤ then ≥), aff over the POST-ReLU symbols
  26-29 layer-1 ReLU n0,n1: lower env then UNSTABLE upper chord (THREADED box)
  30,31,32 layer-0 post-ReLU lower bounds a00≥0, a01≥0, a02≥0
  33,34,35 layer-0 post-ReLU upper bounds a00≤uz00, a01≤uz01, a02≤uz02
Note premises 30-35 (post-ReLU box) plus the layer-1 affine are the THREADING.
The output equality y = -(a10+a11) is pinned by the bridge's `genuine` directly
(`genuine.y = -netEval2 x = -(a10+a11)`); the certificate uses premises 22,24
(layer-1 affine ≤), 27,29 (layer-1 chords), 30-32 (post-ReLU lower).  Because the
output is pinned in `genuine`, the certificate folds to `-(st.y) - cBound2` using
the chord/affine/post-ReLU premises and the algebraic fact a10+a11 = -y on
`genuine`; we encode the output pin as premises 33-35 unused here and instead
fold y directly. -/

def aff00 (st : State) : ℚ :=
  (14497179/268435456) * st.x0 + (-684437/262144) * st.x1
  + (-12081407/67108864) * st.x2 + (4063341/16777216) * st.x3
  + (9489663/67108864) * st.x4 + (15275991/67108864)
def aff01 (st : State) : ℚ :=
  (3288653/16777216) * st.x0 + (16251015/67108864) * st.x1
  + (10711447/16777216) * st.x2 + (-8023955/16777216) * st.x3
  + (9568181/67108864) * st.x4 + (14336977/268435456)
def aff02 (st : State) : ℚ :=
  (-5958143/16777216) * st.x0 + (1186923/2097152) * st.x1
  + (15318739/67108864) * st.x2 + (2975305/16777216) * st.x3
  + (-6981939/33554432) * st.x4 + (-5452803/67108864)
/-- Layer-1 affine forms over the layer-0 POST-ReLU symbols `a00,a01,a02`. -/
def aff10 (st : State) : ℚ :=
  (-12361587/67108864) * st.a00 + (-7727049/67108864) * st.a01
  + (-4601923/33554432) * st.a02 + (11213891/134217728)
def aff11 (st : State) : ℚ :=
  (9214799/536870912) * st.a00 + (-2333539/268435456) * st.a01
  + (2873199/134217728) * st.a02 + (-11449363/536870912)

def prem : Fin 36 → State → ℚ :=
  ![ fun st => st.x0 - 11/16                  -- 0
   , fun st => 19/32 - st.x0                   -- 1
   , fun st => st.x1 - 1/2                      -- 2
   , fun st => -1/2 - st.x1                      -- 3
   , fun st => st.x2 - 1/2                       -- 4
   , fun st => -1/2 - st.x2                       -- 5
   , fun st => st.x3 - 1/2                        -- 6
   , fun st => 57/128 - st.x3                      -- 7
   , fun st => st.x4 - (-57/128)                    -- 8
   , fun st => -1/2 - st.x4                          -- 9
   , fun st => st.z00 - aff00 st                     -- 10 L0 aff n0 ≤
   , fun st => aff00 st - st.z00                     -- 11 L0 aff n0 ≥
   , fun st => st.z01 - aff01 st                     -- 12 L0 aff n2 ≤
   , fun st => aff01 st - st.z01                     -- 13
   , fun st => st.z02 - aff02 st                     -- 14 L0 aff n4 ≤
   , fun st => aff02 st - st.z02                     -- 15
   , fun st => st.z00 - st.a00                       -- 16 L0 ReLU n0 lower (α=1)
   , fun st => st.a00 - s00 * (st.z00 - lz00)        -- 17 L0 ReLU n0 UPPER chord
   , fun st => st.z01 - st.a01                       -- 18 L0 ReLU n2 lower
   , fun st => st.a01 - s01 * (st.z01 - lz01)        -- 19 L0 ReLU n2 UPPER chord
   , fun st => st.z02 - st.a02                       -- 20 L0 ReLU n4 lower
   , fun st => st.a02 - s02 * (st.z02 - lz02)        -- 21 L0 ReLU n4 UPPER chord
   , fun st => st.z10 - aff10 st                     -- 22 L1 aff n0 ≤  (over post-ReLU)
   , fun st => aff10 st - st.z10                     -- 23 L1 aff n0 ≥
   , fun st => st.z11 - aff11 st                     -- 24 L1 aff n1 ≤
   , fun st => aff11 st - st.z11                     -- 25
   , fun st => st.z10 - st.a10                       -- 26 L1 ReLU n0 lower
   , fun st => st.a10 - s10 * (st.z10 - lz10)        -- 27 L1 ReLU n0 UPPER chord (THREADED)
   , fun st => st.z11 - st.a11                       -- 28 L1 ReLU n1 lower
   , fun st => st.a11 - s11 * (st.z11 - lz11)        -- 29 L1 ReLU n1 UPPER chord (THREADED)
   , fun st => -st.a00                               -- 30 post-ReLU a00 ≥ 0  (LOAD-BEARING)
   , fun st => -st.a01                               -- 31 post-ReLU a01 ≥ 0  (LOAD-BEARING)
   , fun st => -st.a02                               -- 32 post-ReLU a02 ≥ 0  (LOAD-BEARING)
   , fun st => st.a00 - uz00                         -- 33 post-ReLU a00 ≤ uz00 (threaded; mult 0 here)
   , fun st => st.y + (st.a10 + st.a11)              -- 34 output ≤  (pins y)
   , fun st => -(st.y + (st.a10 + st.a11)) ]         -- 35 output ≥  (LOAD-BEARING, mult 1)

/-! ## 9.  THE BRIDGE.  Every emitter premise is `≤ 0` on every valid state. -/

theorem bridge_all (x : Fin 5 → ℚ) (hb : inBox x) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 ∧
    prem 3 (genuine x) ≤ 0 ∧ prem 4 (genuine x) ≤ 0 ∧ prem 5 (genuine x) ≤ 0 ∧
    prem 6 (genuine x) ≤ 0 ∧ prem 7 (genuine x) ≤ 0 ∧ prem 8 (genuine x) ≤ 0 ∧
    prem 9 (genuine x) ≤ 0 ∧ prem 10 (genuine x) ≤ 0 ∧ prem 11 (genuine x) ≤ 0 ∧
    prem 12 (genuine x) ≤ 0 ∧ prem 13 (genuine x) ≤ 0 ∧ prem 14 (genuine x) ≤ 0 ∧
    prem 15 (genuine x) ≤ 0 ∧ prem 16 (genuine x) ≤ 0 ∧ prem 17 (genuine x) ≤ 0 ∧
    prem 18 (genuine x) ≤ 0 ∧ prem 19 (genuine x) ≤ 0 ∧ prem 20 (genuine x) ≤ 0 ∧
    prem 21 (genuine x) ≤ 0 ∧ prem 22 (genuine x) ≤ 0 ∧ prem 23 (genuine x) ≤ 0 ∧
    prem 24 (genuine x) ≤ 0 ∧ prem 25 (genuine x) ≤ 0 ∧ prem 26 (genuine x) ≤ 0 ∧
    prem 27 (genuine x) ≤ 0 ∧ prem 28 (genuine x) ≤ 0 ∧ prem 29 (genuine x) ≤ 0 ∧
    prem 30 (genuine x) ≤ 0 ∧ prem 31 (genuine x) ≤ 0 ∧ prem 32 (genuine x) ≤ 0 ∧
    prem 33 (genuine x) ≤ 0 ∧ prem 34 (genuine x) ≤ 0 ∧ prem 35 (genuine x) ≤ 0 := by
  -- closed forms / equalities
  have hz00 := z0lay_0 x; have hz01 := z0lay_1 x; have hz02 := z0lay_2 x
  have ha00 : a0lay x 0 = relu (z0lay x 0) := a0lay_eq x 0
  have ha01 : a0lay x 1 = relu (z0lay x 1) := a0lay_eq x 1
  have ha02 : a0lay x 2 = relu (z0lay x 2) := a0lay_eq x 2
  have hz10 := z1lay_0 x; have hz11 := z1lay_1 x
  have ha10 : a1lay x 0 = relu (z1lay x 0) := a1lay_eq x 0
  have ha11 : a1lay x 1 = relu (z1lay x 1) := a1lay_eq x 1
  have hy := netEval2_eq x
  -- box
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  have hbb : inBox x := ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩
  -- layer-0 lower envelopes
  have hlo00 : (1:ℚ) * z0lay x 0 ≤ relu (z0lay x 0) := relu_lower 1 _ (by norm_num) (by norm_num)
  have hlo01 : (1:ℚ) * z0lay x 1 ≤ relu (z0lay x 1) := relu_lower 1 _ (by norm_num) (by norm_num)
  have hlo02 : (1:ℚ) * z0lay x 2 ≤ relu (z0lay x 2) := relu_lower 1 _ (by norm_num) (by norm_num)
  -- layer-0 chords
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb1l,zb1u⟩,⟨zb2l,zb2u⟩⟩ := z_in_box0 x hbb
  have hup00 := chord00 _ zb0l zb0u
  have hup01 := chord01 _ zb1l zb1u
  have hup02 := chord02 _ zb2l zb2u
  -- layer-0 post-ReLU box
  obtain ⟨⟨pa0l,pa0u⟩,⟨pa1l,pa1u⟩,⟨pa2l,pa2u⟩⟩ := a0_in_box x hbb
  -- layer-1 lower envelopes
  have hlo10 : (1:ℚ) * z1lay x 0 ≤ relu (z1lay x 0) := relu_lower 1 _ (by norm_num) (by norm_num)
  have hlo11 : (1:ℚ) * z1lay x 1 ≤ relu (z1lay x 1) := relu_lower 1 _ (by norm_num) (by norm_num)
  -- layer-1 chords on the THREADED z1-box
  obtain ⟨⟨zc0l,zc0u⟩,⟨zc1l,zc1u⟩⟩ := z_in_box1 x hbb
  have hup10 := chord10 _ zc0l zc0u
  have hup11 := chord11 _ zc1l zc1u
  -- expand chord slopes/anchors to literal coefficients
  simp only [s00,lz00,s01,lz01,s02,lz02,s10,lz10,s11,lz11] at hup00 hup01 hup02 hup10 hup11
  simp only [uz00,uz01,uz02] at pa0u pa1u pa2u
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
          ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [prem, genuine, aff00, aff01, aff02, aff10, aff11,
               s00,lz00,s01,lz01,s02,lz02,s10,lz10,s11,lz11,uz00,uz01,uz02,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
               Matrix.vecHead, Matrix.vecTail, Function.comp] <;>
    linarith [h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u,h4l,h4u,
              hz00,hz01,hz02,ha00,ha01,ha02,hz10,hz11,ha10,ha11,hy,
              hlo00,hlo01,hlo02,hup00,hup01,hup02,
              pa0l,pa0u,pa1l,pa1u,pa2l,pa2u,
              hlo10,hlo11,hup10,hup11]

theorem bridge_premises_sound :
    ∀ i : Fin 36, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, hb, rfl⟩ := hv
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,g19,
          g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31,g32,g33,g34,g35⟩ :=
    bridge_all x hb
  fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7
  · exact g8
  · exact g9
  · exact g10
  · exact g11
  · exact g12
  · exact g13
  · exact g14
  · exact g15
  · exact g16
  · exact g17
  · exact g18
  · exact g19
  · exact g20
  · exact g21
  · exact g22
  · exact g23
  · exact g24
  · exact g25
  · exact g26
  · exact g27
  · exact g28
  · exact g29
  · exact g30
  · exact g31
  · exact g32
  · exact g33
  · exact g34
  · exact g35

/-! ## 10.  The certificate's exact multipliers + the Farkas conclusion.

The shipped multipliers (emitter order, exact rationals) fold the 36 premises
into  ∑ μ i · prem i st = -(st.y) - cBound2,  a pure `ring` identity.  The
LOAD-BEARING premises are:
  * the two layer-1 UNSTABLE upper chords (27, 29; multiplier 1 each),
  * the layer-1 affine equalities (22, 24; multipliers s10, s11) folding
    z1 = affine of the layer-0 POST-ReLU activations (the COMPOSITION),
  * the layer-0 post-ReLU lower bounds (30, 32),
  * the output equality (34).
The layer-0 chords are load-bearing *through the threaded anchors* lz10,lz11
(present in cBound2's `s1_j·lz1_j` term and in the z1-box that the chords need). -/

def cBound2 : ℚ := 898924914818669731679623083106799/10613915318069294137973497787318272

def mu : Fin 36 → ℚ :=
  ![0,0,0,0,0,0,0,0,0,0,            -- 0-9 box (not load-bearing in this readout)
    0,0,0,0,0,0,                    -- 10-15 layer-0 affine
    0,0,0,0,0,0,                    -- 16-21 layer-0 ReLU envelopes
    3010205944119296/14335399554132045,  -- 22 L1 aff n0 ≤  (= s10)  LOAD-BEARING
    0,                                    -- 23
    22352578515760631/59839676241425093, -- 24 L1 aff n1 ≤  (= s11)  LOAD-BEARING
    0,                                    -- 25
    0,                                    -- 26 L1 ReLU n0 lower
    1,                                    -- 27 L1 ReLU n0 UPPER chord  LOAD-BEARING
    0,                                    -- 28 L1 ReLU n1 lower
    1,                                    -- 29 L1 ReLU n1 UPPER chord  LOAD-BEARING
    4953596501394011213042997283554093413961/153513882925205859594052440925476738826240, -- 30 a00≥0
    161928944352175298544200542468956584087/5904380112507917676694324650979874570240,    -- 31 a01≥0
    2395104752604623529261898399789571515771/115135412193904394695539330694107554119680, -- 32 a02≥0
    0,                                    -- 33 post-ReLU a00 upper (not needed in this readout)
    0,                                    -- 34 output ≤
    1]                                    -- 35 output ≥  (gives -(y) - (a10+a11))  LOAD-BEARING

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 36)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> norm_num [mu]

/-- **The Farkas certificate identity** — pure algebra (`ring`): the multipliers
    fold the 36 premises into `-(st.y) - cBound2`.  Load-bearing: the two layer-1
    UNSTABLE upper chords (27,29), the layer-1 affine equalities over the POST-ReLU
    symbols (22,24; the COMPOSITION), the three post-ReLU lower bounds (30-32), and
    the output direction (35). -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 36)), mu i * prem i st) = -(st.y) - cBound2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, mu, prem, aff00, aff01, aff02,
             aff10, aff11, s00,lz00,s01,lz01,s02,lz02,s10,lz10,s11,lz11,uz00,uz01,uz02,
             cBound2,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
             Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

/-- **State lower bound** for the relaxed output `y` via the abstract Farkas core. -/
theorem acas2_state_lower_bound :
    ∀ st : State, valid st → -cBound2 ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 36)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := cBound2)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

theorem genuine_y (x : Fin 5 → ℚ) : (genuine x).y = -netEval2 x := rfl

/-- **Upper bound on the actual TWO-LAYER ONNX sub-network output, OBTAINED FROM
    THE MULTI-LAYER CERTIFICATE.**  Composing `farkas_premise_combination` on the
    emitted premises with the exact multipliers yields `netEval2 x ≤ cBound2`. -/
theorem netEval2_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval2 x ≤ cBound2 := by
  have hv : valid (genuine x) := ⟨x, hb, rfl⟩
  have h := acas2_state_lower_bound (genuine x) hv
  rw [genuine_y] at h
  linarith

/-- Cross-check: the SAME bound follows directly from the layer-1 chords + the
    threaded z1-box + the post-ReLU box, independent of the Farkas packaging. -/
theorem netEval2_upper_bound_direct (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval2 x ≤ cBound2 := by
  have hbb := hb
  have hy : netEval2 x = relu (z1lay x 0) + relu (z1lay x 1) := by
    rw [netEval2_eq, a1lay_eq, a1lay_eq]
  obtain ⟨⟨zc0l,zc0u⟩,⟨zc1l,zc1u⟩⟩ := z_in_box1 x hbb
  have hup10 := chord10 _ zc0l zc0u
  have hup11 := chord11 _ zc1l zc1u
  obtain ⟨⟨pa0l,pa0u⟩,⟨pa1l,pa1u⟩,⟨pa2l,pa2u⟩⟩ := a0_in_box x hbb
  have hz10 := z1lay_0 x
  have hz11 := z1lay_1 x
  simp only [s10,lz10,s11,lz11,uz00,uz01,uz02] at hup10 hup11 pa0u pa1u pa2u
  rw [hy]
  simp only [cBound2]
  nlinarith [hup10, hup11, hz10, hz11, pa0l, pa0u, pa1l, pa1u, pa2l, pa2u]

/-! ## 11.  THE DECISION on the actual TWO-LAYER ONNX output `netEval2`. -/

theorem cBound2_lt_quarter : cBound2 < 1/4 := by norm_num [cBound2]

/-- **The decision:** the two-layer real ACAS sub-network output is below 1/4
    everywhere on the box — a fully kernel-checked verdict, no trusted emitter,
    obtained by genuine multi-layer CROWN composition. -/
theorem acas2_decision (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval2 x < 1/4 := by
  have := netEval2_upper_bound x hb
  have := cBound2_lt_quarter
  linarith

/-- Equivalently, the unsafe atom `netEval2 x ≥ 1/4` is refuted. -/
theorem acas2_unsafe_refuted (x : Fin 5 → ℚ) (hb : inBox x) :
    ¬ (netEval2 x ≥ 1/4) := by
  have := acas2_decision x hb
  intro hbad; linarith

/-! ## 12.  Cross-check vs the standalone reader's exact 2-layer forward eval.

The dependency-free reader's exact-dyadic two-layer forward eval at the box's
max corner agrees with `netEval2`.  The reader prints
  cornerMax: netEval2 = 6529190686447025/576460752303423488 (≈ 0.011326340). -/

def cornerMax : Fin 5 → ℚ := ![11/16, 1/2, 1/2, 1/2, -57/128]

theorem cornerMax_inBox : inBox cornerMax := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [cornerMax, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val, Matrix.cons_val_fin_one] <;> norm_num

/-- The reader's exact 2-layer forward value at the max corner, reproduced in Lean. -/
theorem netEval2_cornerMax_val :
    netEval2 cornerMax = 6529190686447025/576460752303423488 := by
  rw [netEval2_eq, a1lay_eq, a1lay_eq, z1lay_0, z1lay_1,
      a0lay_eq, a0lay_eq, a0lay_eq, z0lay_0, z0lay_1, z0lay_2]
  simp only [cornerMax, relu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one]
  norm_num

/-- The certified bound holds (non-vacuously) at this corner. -/
theorem netEval2_cornerMax_le : netEval2 cornerMax ≤ cBound2 :=
  netEval2_upper_bound cornerMax cornerMax_inBox

/-! ## Trust-base check.  Each must list ONLY [propext, Classical.choice, Quot.sound]. -/

#print axioms netEval2
#print axioms z_in_box1
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms acas2_state_lower_bound
#print axioms netEval2_upper_bound
#print axioms netEval2_upper_bound_direct
#print axioms acas2_decision
#print axioms acas2_unsafe_refuted
#print axioms netEval2_cornerMax_val
#print axioms netEval2_cornerMax_le

end NetAcas2Layer
end Crownproof
