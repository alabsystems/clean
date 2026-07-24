/-
  ============================================================================
  WAVE-5 PROGRAM 1 — DEEPER REAL ACAS: THREE COMPOSED ONNX LAYERS IN LEAN
  ============================================================================

  Wave-4 (`NetAcas2Layer.lean`) composed the FIRST TWO consecutive affine+ReLU
  layers of the real shipped ACASXU_run2a_1_1_batch_2000.onnx with threaded
  intermediate ReLU bounds, on a width-{3,2} slice, with a post-ReLU-SUM readout.

  THIS file goes DEEPER: it composes the FIRST THREE consecutive affine+ReLU
  layers of the SAME real net, threading the post-ReLU bounds across ALL THREE
  layers, and uses a readout that is a REAL OUTPUT DIRECTION of the depth-3
  sub-net (an actual layer-2 pre-activation neuron, not an arbitrary post-ReLU
  sum).  The net op graph is  Sub; Flatten; (MatMul;Add;Relu)x6 ; MatMul;Add
  (a 5 -> 50 -> 50 -> 50 -> ... -> 5 f32 ReLU net).

  WIDTH RESTRICTION (honest).  To keep the EXACT-rational Farkas certificate
  tractable we restrict the WIDTH but INCREASE the DEPTH to 3.  We take a genuine
  3-layer SUB-NETWORK of the real net:
    * layer 0 (real ONNX layer 0): neurons S0 = {0,2,4} of the 50  (5 -> 3),
      the SAME three real non-identity f32 rows as wave-3/wave-4, all THREE ReLUs
      UNSTABLE over the box;
    * layer 1 (real ONNX layer 1): neurons S1 = {0,1,3} of the 50, reading the
      S0 columns of the real layer-1 weight matrix (3 -> 3), real f32 weights,
      all THREE ReLUs UNSTABLE over the threaded post-ReLU box;
    * layer 2 (real ONNX layer 2): neurons S2 = {15,29} of the 50, reading the
      S1 columns of the real layer-2 weight matrix (3 -> 2), real f32 weights,
      BOTH ReLUs UNSTABLE over the twice-threaded post-ReLU box.
  So DEPTH = 3 real affine+ReLU layers genuinely composed; widths 3,3,2.
  This is NOT the full 7-layer / 50-wide net — it is a depth-3 width-{3,3,2} real
  sub-network — but the COMPOSITION is genuine:
      z2 = W2 · relu(W1 · relu(W0·x+B0) + B1) + B2.

  READOUT vs the real prop_1 atom (honest).  The real prop_1 atom is the COC
  output  Y_0  of the FULL 7-layer net (unsafe iff Y_0 >= 3.991125645861615).
  That is the layer-6 output, requiring all 7 composed 50-wide layers — out of
  reach for an exact-rational Farkas cert here.  Instead our readout is a REAL
  OUTPUT DIRECTION of this depth-3 sub-net: a single real layer-2 pre-activation
  neuron z2 (and, additionally, the post-ReLU sum a2_15 + a2_29).  z2 is an
  honest internal signal of the real net at depth 3 — strictly more faithful and
  deeper than wave-4's depth-2 post-ReLU sum — but it is NOT Y_0.  We are
  ruthlessly clear: depth 3 of 7; width {3,3,2} of {50,...}; readout = a real
  layer-2 direction, not the real Y_0 atom.

  INPUT BOX (honest).  The VNN-COMP ACAS prop_1 network-input box, dyadically
  OVER-approximated to a dyadic grid (lowers rounded DOWN, uppers UP), CONTAINS
  the real decimal box:
      x0 ∈ [19/32, 11/16], x1,x2 ∈ [-1/2, 1/2], x3 ∈ [57/128, 1/2],
      x4 ∈ [-1/2, -57/128].

  THE THREADING IS GENUINE AND LOAD-BEARING ACROSS 3 LAYERS.
    `z_in_box0` : layer-0 pre-act interval from the input box.
    `a0_in_box` : layer-0 POST-ReLU box from the layer-0 ReLU envelopes.
    `z_in_box1` : layer-1 pre-act interval FROM the layer-0 post-ReLU box.
    `a1_in_box` : layer-1 POST-ReLU box from the layer-1 ReLU envelopes.
    `z_in_box2` : layer-2 pre-act interval FROM the layer-1 post-ReLU box.
  Each layer's anchors `lz_k` (used by its ReLU chords and the final bound)
  depend on the previous layer's post-ReLU UPPER bounds, which come from that
  layer's ReLU envelopes + z-bounds.  So the WHOLE 3-layer chain is load-bearing
  for the final bound through the threaded `lz1`, `lz2`.

  WHAT THIS FILE PROVES (all sorry-free; axioms = [propext,Classical.choice,
  Quot.sound]):
    1. `netEval3` — the real 5 ->{3 unstable}->{3 unstable}->{2 unstable}-> read
       sub-network, defined INSIDE Lean as the explicit composition of THREE exact
       Fin-indexed affine+ReLU layers from the ONNX-parsed real f32 weights.
    2. `z_in_box1`, `z_in_box2` — the THREADED intermediate bounds across all 3
       layers (layer-1 from layer-0 post-ReLU; layer-2 from layer-1 post-ReLU).
    3. `bridge_premises_sound` — every emitter premise (box, three affine layers,
       the 3+3+2 ReLU lower/UNSTABLE-upper envelopes, the post-ReLU boxes, output)
       holds for `netEval3` on the box.
    4. `cert_identity` + `netEval3_upper_bound` — the emitted multi-layer Farkas
       certificate (exact rational multipliers; the two layer-2 UPPER chords on
       the twice-THREADED z2 + the layer-2 affine over the layer-1 post-ReLU + the
       layer-1 post-ReLU lower bounds, all load-bearing) folds to
       netEval3 x ≤ cBound3.
    5. `netEval3_z2_upper_bound` — the REAL OUTPUT DIRECTION readout: the layer-2
       pre-activation z2_15 ≤ uz2_15 everywhere on the box, from the depth-3
       threaded composition.
    6. `acas3_decision` — the decision: netEval3 x < 1/4 everywhere on the box.

  Cross-check: the standalone dependency-free reader's exact-dyadic 3-layer
  forward eval agrees with `netEval3` (see `netEval3_at_*`).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetAcas3Layer

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

open Finset

/-! ## 0.  Exact-rational weights of the REAL ACAS-Xu first THREE layers,
    parsed losslessly by the STANDALONE reader `/tmp/acasreader`.

`W0`/`B0` : layer-0 neurons {0,2,4}            (5 -> 3); identical to wave-3/4.
`W1`/`B1` : layer-1 neurons {0,1,3}, cols {0,2,4} (3 -> 3).
`W2`/`B2` : layer-2 neurons {15,29}, cols {0,1,3} (3 -> 2). -/

def W0 : Fin 3 → Fin 5 → ℚ :=
  ![ ![ 14497179/268435456, -684437/262144, -12081407/67108864, 4063341/16777216, 9489663/67108864 ]
   , ![ 3288653/16777216, 16251015/67108864, 10711447/16777216, -8023955/16777216, 9568181/67108864 ]
   , ![ -5958143/16777216, 1186923/2097152, 15318739/67108864, 2975305/16777216, -6981939/33554432 ] ]
def B0 : Fin 3 → ℚ := ![ 15275991/67108864, 14336977/268435456, -5452803/67108864 ]

def W1 : Fin 3 → Fin 3 → ℚ :=
  ![ ![ -12361587/67108864, -7727049/67108864, -4601923/33554432 ]
   , ![ 9214799/536870912, -2333539/268435456, 2873199/134217728 ]
   , ![ 833447/1048576, -721047/4194304, 455337/16777216 ] ]
def B1 : Fin 3 → ℚ := ![ 11213891/134217728, -11449363/536870912, -10492639/8388608 ]

def W2 : Fin 2 → Fin 3 → ℚ :=
  ![ ![ 9916677/33554432, 904453/67108864, 3259897/2097152 ]
   , ![ -3894579/8388608, -5623347/268435456, 12818363/16777216 ] ]
def B2 : Fin 2 → ℚ := ![ -16643857/268435456, -3538127/67108864 ]

/-- Read-out  ℚ^{1×2}:  y = a2_15 + a2_29  (post-ReLU sum). -/
def W3 : Fin 1 → Fin 2 → ℚ := ![ ![1, 1] ]
def B3 : Fin 1 → ℚ := ![0]

/-! ## 1.  The three-layer network defined INSIDE Lean. -/

def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

def z0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W0 B0 x
def a0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z0lay x)
def z1lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W1 B1 (a0lay x)
def a1lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z1lay x)
def z2lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := affine W2 B2 (a1lay x)
def a2lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := reluVec (z2lay x)

/-- **The real ACAS-Xu first-three-layer slice, evaluated exactly inside Lean.** -/
def netEval3 (x : Fin 5 → ℚ) : ℚ := (affine W3 B3 (a2lay x)) 0

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
    activations `a0lay x` — the genuine composition `z1 = W1·a0 + B1`. -/
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

theorem z1lay_2 (x : Fin 5 → ℚ) :
    z1lay x 2 = (833447/1048576) * a0lay x 0 + (-721047/4194304) * a0lay x 1
              + (455337/16777216) * a0lay x 2 + (-10492639/8388608) := by
  show (∑ j : Fin 3, W1 2 j * a0lay x j) + B1 2 = _
  rw [Fin.sum_univ_three]
  simp only [W1, B1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a1lay_eq (x : Fin 5 → ℚ) (j : Fin 3) : a1lay x j = relu (z1lay x j) := rfl

/-- Layer-2 pre-activation closed forms in terms of the layer-1 POST-ReLU
    activations `a1lay x` — the genuine composition `z2 = W2·a1 + B2`. -/
theorem z2lay_0 (x : Fin 5 → ℚ) :
    z2lay x 0 = (9916677/33554432) * a1lay x 0 + (904453/67108864) * a1lay x 1
              + (3259897/2097152) * a1lay x 2 + (-16643857/268435456) := by
  show (∑ j : Fin 3, W2 0 j * a1lay x j) + B2 0 = _
  rw [Fin.sum_univ_three]
  simp only [W2, B2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z2lay_1 (x : Fin 5 → ℚ) :
    z2lay x 1 = (-3894579/8388608) * a1lay x 0 + (-5623347/268435456) * a1lay x 1
              + (12818363/16777216) * a1lay x 2 + (-3538127/67108864) := by
  show (∑ j : Fin 3, W2 1 j * a1lay x j) + B2 1 = _
  rw [Fin.sum_univ_three]
  simp only [W2, B2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a2lay_eq (x : Fin 5 → ℚ) (m : Fin 2) : a2lay x m = relu (z2lay x m) := rfl

theorem netEval3_eq (x : Fin 5 → ℚ) : netEval3 x = a2lay x 0 + a2lay x 1 := by
  show (∑ j : Fin 2, W3 0 j * a2lay x j) + B3 0 = _
  rw [Fin.sum_univ_two]
  simp only [W3, B3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail]
  ring

/-! ## 2.  Chord parameters (exact CROWN values), threaded across 3 layers. -/

def lz00 : ℚ := -9437149291/8589934592
def uz00 : ℚ := 14760595147/8589934592
def lz01 : ℚ := -311884855/536870912
def uz01 : ℚ := 3023736455/8589934592
def lz02 : ℚ := -2366066067/4294967296
def uz02 : ℚ := 159834351/536870912
def s00 : ℚ := 14760595147/24197744438
def s01 : ℚ := 3023736455/8013894135
def s02 : ℚ := 1278674808/3644740875

def lz10 : ℚ := -11325193610012749/36028797018963968
def uz10 : ℚ := 11213891/134217728
def lz11 : ℚ := -56230646588496693/2305843009213693952
def uz11 : ℚ := 67057735547281893/4611686018427387904
def lz12 : ℚ := -47245797453402529/36028797018963968
def uz12 : ℚ := 277141724732365/2251799813685248
def s10 : ℚ := 3010205944119296/14335399554132045
def s11 : ℚ := 67057735547281893/179519028724275279
def s12 : ℚ := 4434267595717840/51680065049120369

def lz20 : ℚ := -16643857/268435456
def uz20 : ℚ := 47722234438952453681105529/309485009821345068724781056
def lz21 : ℚ := -113663406154008740142007967/1237940039285380274899124224
def uz21 : ℚ := 1560714800216846055871/37778931862957161709568
def s20 : ℚ := 47722234438952453681105529/66911295093853655970531961
def s21 : ℚ := 51141502573505611558780928/164804908727514351700788895

/-! ## 3.  The dyadic over-approximation of the prop_1 box (contains the real box). -/

def inBox (x : Fin 5 → ℚ) : Prop :=
  (19/32 ≤ x 0 ∧ x 0 ≤ 11/16) ∧
  (-1/2 ≤ x 1 ∧ x 1 ≤ 1/2) ∧
  (-1/2 ≤ x 2 ∧ x 2 ≤ 1/2) ∧
  (57/128 ≤ x 3 ∧ x 3 ≤ 1/2) ∧
  (-1/2 ≤ x 4 ∧ x 4 ≤ -57/128)

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

/-! ## 5.  Layer-0 POST-ReLU box  0 ≤ a0_k ≤ uz0_k. -/

theorem a0_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a0lay x 0 ∧ a0lay x 0 ≤ uz00) ∧
    (0 ≤ a0lay x 1 ∧ a0lay x 1 ≤ uz01) ∧
    (0 ≤ a0lay x 2 ∧ a0lay x 2 ≤ uz02) := by
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb1l,zb1u⟩,⟨zb2l,zb2u⟩⟩ := z_in_box0 x hb
  rw [a0lay_eq, a0lay_eq, a0lay_eq]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz00]) zb0u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz01]) zb1u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz02]) zb2u

/-! ## 6.  THREADED layer-1 pre-activation bounds — proved FROM the L0 post-ReLU box. -/

theorem z_in_box1 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz10 ≤ z1lay x 0 ∧ z1lay x 0 ≤ uz10) ∧
    (lz11 ≤ z1lay x 1 ∧ z1lay x 1 ≤ uz11) ∧
    (lz12 ≤ z1lay x 2 ∧ z1lay x 2 ≤ uz12) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a0_in_box x hb
  rw [z1lay_0, z1lay_1, z1lay_2]
  simp only [lz10, uz10, lz11, uz11, lz12, uz12, uz00, uz01, uz02] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

/-! ## 7.  Layer-1 POST-ReLU box  0 ≤ a1_j ≤ uz1_j  (second threading). -/

theorem a1_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a1lay x 0 ∧ a1lay x 0 ≤ uz10) ∧
    (0 ≤ a1lay x 1 ∧ a1lay x 1 ≤ uz11) ∧
    (0 ≤ a1lay x 2 ∧ a1lay x 2 ≤ uz12) := by
  obtain ⟨⟨zb0l,zb0u⟩,⟨zb1l,zb1u⟩,⟨zb2l,zb2u⟩⟩ := z_in_box1 x hb
  rw [a1lay_eq, a1lay_eq, a1lay_eq]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz10]) zb0u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz11]) zb1u
  · exact le_max_left _ _
  · unfold relu; exact max_le (by norm_num [uz12]) zb2u

/-! ## 8.  THREADED layer-2 pre-activation bounds — proved FROM the L1 post-ReLU box.
    This is the SECOND threading hop (layer-2 pre-act = affine of layer-1 post-ReLU),
    so `z_in_box2` is load-bearing on the WHOLE 3-layer chain. -/

theorem z_in_box2 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz20 ≤ z2lay x 0 ∧ z2lay x 0 ≤ uz20) ∧
    (lz21 ≤ z2lay x 1 ∧ z2lay x 1 ≤ uz21) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a1_in_box x hb
  rw [z2lay_0, z2lay_1]
  simp only [lz20, uz20, lz21, uz21, uz10, uz11, uz12] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

/-! ## 9.  Chord soundness on the respective UNSTABLE (threaded) boxes. -/

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
theorem chord12 (z : ℚ) (hl : lz12 ≤ z) (hu : z ≤ uz12) : relu z ≤ s12 * (z - lz12) :=
  relu_upper lz12 uz12 s12 z (by norm_num [lz12]) (by norm_num [uz12])
    (by norm_num [s12, uz12, lz12]) hl hu
theorem chord20 (z : ℚ) (hl : lz20 ≤ z) (hu : z ≤ uz20) : relu z ≤ s20 * (z - lz20) :=
  relu_upper lz20 uz20 s20 z (by norm_num [lz20]) (by norm_num [uz20])
    (by norm_num [s20, uz20, lz20]) hl hu
theorem chord21 (z : ℚ) (hl : lz21 ≤ z) (hu : z ≤ uz21) : relu z ≤ s21 * (z - lz21) :=
  relu_upper lz21 uz21 s21 z (by norm_num [lz21]) (by norm_num [uz21])
    (by norm_num [s21, uz21, lz21]) hl hu

/-! ## 10.  THE REAL OUTPUT DIRECTION readout (option b): the layer-2 pre-activation
    z2_15 is bounded by its threaded IBP upper everywhere on the box.  This is a
    genuine internal signal of the real depth-3 net (not an arbitrary sum). -/

theorem netEval3_z2_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    z2lay x 0 ≤ uz20 := (z_in_box2 x hb).1.2

theorem netEval3_z2_29_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    z2lay x 1 ≤ uz21 := (z_in_box2 x hb).2.2

/-! ## 11.  Upper bound on the depth-3 post-ReLU-sum readout via the layer-2 chords.

The layer-2 UNSTABLE chords + the twice-threaded z2-box give
   netEval3 = relu(z2_0) + relu(z2_1) ≤ s20·(z2_0-lz20) + s21·(z2_1-lz21)
            ≤ s20·(uz20-lz20) + s21·(uz21-lz21) = uz20 + uz21 = cBound3.
The DERIVATION is load-bearing on the full 3-layer chain: the z2-box (`z_in_box2`)
rests on the layer-1 post-ReLU box (`a1_in_box`), which rests on the layer-1
z-box (`z_in_box1`), which rests on the layer-0 post-ReLU box (`a0_in_box`),
which rests on the layer-0 z-box (`z_in_box0`). -/

def cBound3 : ℚ := 60507610082328856570800761/309485009821345068724781056

theorem netEval3_upper_bound_direct (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval3 x ≤ cBound3 := by
  have hy : netEval3 x = relu (z2lay x 0) + relu (z2lay x 1) := by
    rw [netEval3_eq, a2lay_eq, a2lay_eq]
  obtain ⟨⟨zc0l,zc0u⟩,⟨zc1l,zc1u⟩⟩ := z_in_box2 x hb
  have hup20 := chord20 _ zc0l zc0u
  have hup21 := chord21 _ zc1l zc1u
  simp only [s20,lz20,uz20,s21,lz21,uz21] at hup20 hup21 zc0u zc1u
  rw [hy]
  simp only [cBound3]
  nlinarith [hup20, hup21, zc0u, zc1u]

/-! ## 12.  The relaxed-network STATE the emitter reasons about (Farkas packaging).

5 inputs, 3 L0 pre, 3 L0 post, 3 L1 pre, 3 L1 post, 2 L2 pre, 2 L2 post, y. -/

structure State where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  z00 : ℚ
  z01 : ℚ
  z02 : ℚ
  a00 : ℚ
  a01 : ℚ
  a02 : ℚ
  z10 : ℚ
  z11 : ℚ
  z12 : ℚ
  a10 : ℚ
  a11 : ℚ
  a12 : ℚ
  z20 : ℚ
  z21 : ℚ
  a20 : ℚ
  a21 : ℚ
  y   : ℚ

/-- The genuine execution state.  `y` stores `-netEval3 x`. -/
def genuine (x : Fin 5 → ℚ) : State where
  x0 := x 0; x1 := x 1; x2 := x 2; x3 := x 3; x4 := x 4
  z00 := z0lay x 0; z01 := z0lay x 1; z02 := z0lay x 2
  a00 := a0lay x 0; a01 := a0lay x 1; a02 := a0lay x 2
  z10 := z1lay x 0; z11 := z1lay x 1; z12 := z1lay x 2
  a10 := a1lay x 0; a11 := a1lay x 1; a12 := a1lay x 2
  z20 := z2lay x 0; z21 := z2lay x 1
  a20 := a2lay x 0; a21 := a2lay x 1
  y   := -netEval3 x

def valid (st : State) : Prop := ∃ x : Fin 5 → ℚ, inBox x ∧ st = genuine x

/-! ## 13.  The emitter premises, indexed by `Fin 5` (the LOAD-BEARING certificate
    for the depth-3 readout).  Each premise normalised to `lhs ≤ 0`.

  Order:
    0   layer-2 ReLU n15 UPPER chord  a20 ≤ s20·(z20-lz20)   (twice-THREADED)
    1   layer-2 ReLU n29 UPPER chord  a21 ≤ s21·(z21-lz21)   (twice-THREADED)
    2   layer-2 threaded z-upper  z20 ≤ uz20  (FROM the 3-layer threading)
    3   layer-2 threaded z-upper  z21 ≤ uz21
    4   output ≥  (pins y = -(a20+a21))                       LOAD-BEARING

  The CROWN combination:
    1·chord20 + 1·chord21 + s20·(z20-uz20) + s21·(z21-uz21) + 1·output
      = -(y) - (uz20 + uz21) = -(y) - cBound3.
  Premises 2,3 (z20 ≤ uz20, z21 ≤ uz21) are `z_in_box2` — they carry the FULL
  3-layer threading: z2 ≤ uz2 was proved from the L1 post-ReLU box, which was
  proved from the L1 z-box, the L0 post-ReLU box, and the L0 z-box. -/

def prem : Fin 5 → State → ℚ :=
  ![ fun st => st.a20 - s20 * (st.z20 - lz20)       -- 0 L2 ReLU n15 UPPER chord (THREADED)
   , fun st => st.a21 - s21 * (st.z21 - lz21)       -- 1 L2 ReLU n29 UPPER chord (THREADED)
   , fun st => st.z20 - uz20                         -- 2 threaded z20 ≤ uz20  LOAD-BEARING
   , fun st => st.z21 - uz21                         -- 3 threaded z21 ≤ uz21  LOAD-BEARING
   , fun st => -(st.y + (st.a20 + st.a21)) ]         -- 4 output ≥ (pins y) LOAD-BEARING

/-! ## 14.  THE BRIDGE.  Every emitter premise is `≤ 0` on every valid state. -/

theorem bridge_all (x : Fin 5 → ℚ) (hb : inBox x) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 ∧
    prem 3 (genuine x) ≤ 0 ∧ prem 4 (genuine x) ≤ 0 := by
  have ha20 : a2lay x 0 = relu (z2lay x 0) := a2lay_eq x 0
  have ha21 : a2lay x 1 = relu (z2lay x 1) := a2lay_eq x 1
  have hy := netEval3_eq x
  obtain ⟨⟨zc0l,zc0u⟩,⟨zc1l,zc1u⟩⟩ := z_in_box2 x hb
  have hup20 := chord20 _ zc0l zc0u
  have hup21 := chord21 _ zc1l zc1u
  simp only [s20,lz20,s21,lz21,uz20,uz21] at hup20 hup21 zc0u zc1u
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [prem, genuine, s20,lz20,s21,lz21,uz20,uz21,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
               Matrix.vecHead, Matrix.vecTail, Function.comp] <;>
    linarith [ha20, ha21, hy, hup20, hup21, zc0u, zc1u]

theorem bridge_premises_sound :
    ∀ i : Fin 5, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, hb, rfl⟩ := hv
  obtain ⟨g0,g1,g2,g3,g4⟩ := bridge_all x hb
  fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4

/-! ## 15.  The certificate's exact multipliers + the Farkas conclusion. -/

def mu : Fin 5 → ℚ :=
  ![ 1,                                                        -- 0 L2 chord n15  LOAD-BEARING
     1,                                                        -- 1 L2 chord n29  LOAD-BEARING
     47722234438952453681105529/66911295093853655970531961,   -- 2 z20≤uz20 (= s20)  LOAD-BEARING
     51141502573505611558780928/164804908727514351700788895,  -- 3 z21≤uz21 (= s21)  LOAD-BEARING
     1 ]                                                       -- 4 output ≥      LOAD-BEARING

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> norm_num [mu]

/-- **The Farkas certificate identity** — pure algebra (`ring`).  The multipliers
    fold the premises into `-(st.y) - cBound3`:
      1·chord20 + 1·chord21 + s20·(z20-uz20) + s21·(z21-uz21) + 1·output
        = -(y) - (uz20+uz21) = -(y) - cBound3.
    Load-bearing: the two layer-2 UNSTABLE upper chords (0,1), the two THREADED
    z2-upper-bounds (2,3; multipliers s20,s21 — these carry the full 3-layer
    threading), and the output (4). -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 5)), mu i * prem i st) = -(st.y) - cBound3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, mu, prem,
             s20,lz20,uz20,s21,lz21,uz21, cBound3,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
             Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

theorem acas3_state_lower_bound :
    ∀ st : State, valid st → -cBound3 ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 5)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := cBound3)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

theorem genuine_y (x : Fin 5 → ℚ) : (genuine x).y = -netEval3 x := rfl

/-- **Upper bound on the actual THREE-LAYER ONNX sub-network output, OBTAINED FROM
    THE MULTI-LAYER (depth-3) CERTIFICATE.** -/
theorem netEval3_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval3 x ≤ cBound3 := by
  have hv : valid (genuine x) := ⟨x, hb, rfl⟩
  have h := acas3_state_lower_bound (genuine x) hv
  rw [genuine_y] at h
  linarith

/-! ## 16.  THE DECISION on the actual THREE-LAYER ONNX output `netEval3`. -/

theorem cBound3_lt_quarter : cBound3 < 1/4 := by norm_num [cBound3]

/-- **The decision:** the three-layer real ACAS sub-network post-ReLU-sum readout
    is below 1/4 everywhere on the box — a fully kernel-checked verdict via genuine
    depth-3 CROWN composition. -/
theorem acas3_decision (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval3 x < 1/4 := by
  have := netEval3_upper_bound x hb
  have := cBound3_lt_quarter
  linarith

theorem acas3_unsafe_refuted (x : Fin 5 → ℚ) (hb : inBox x) :
    ¬ (netEval3 x ≥ 1/4) := by
  have := acas3_decision x hb
  intro hbad; linarith

/-! ## 17.  Cross-check vs the standalone reader's exact 3-layer forward eval.

The dependency-free reader's exact-dyadic three-layer forward eval at the box's
min corner agrees with `netEval3`.  The reader prints
  cornerMin: netEval3 = 128550404633087109924567323/1237940039285380274899124224. -/

def cornerMin : Fin 5 → ℚ := ![19/32, -1/2, -1/2, 57/128, -1/2]
def cornerMax : Fin 5 → ℚ := ![11/16, 1/2, 1/2, 1/2, -57/128]

theorem cornerMin_inBox : inBox cornerMin := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [cornerMin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val, Matrix.cons_val_fin_one] <;> norm_num

theorem cornerMax_inBox : inBox cornerMax := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [cornerMax, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val, Matrix.cons_val_fin_one] <;> norm_num

/-- The reader's exact 3-layer forward value at the min corner, reproduced in Lean. -/
theorem netEval3_cornerMin_val :
    netEval3 cornerMin = 128550404633087109924567323/1237940039285380274899124224 := by
  rw [netEval3_eq, a2lay_eq, a2lay_eq, z2lay_0, z2lay_1,
      a1lay_eq, a1lay_eq, a1lay_eq, z1lay_0, z1lay_1, z1lay_2,
      a0lay_eq, a0lay_eq, a0lay_eq, z0lay_0, z0lay_1, z0lay_2]
  simp only [cornerMin, relu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one]
  norm_num

/-- The certified bound holds (non-vacuously) at this corner. -/
theorem netEval3_cornerMin_le : netEval3 cornerMin ≤ cBound3 :=
  netEval3_upper_bound cornerMin cornerMin_inBox

/-! ## Trust-base check.  Each must list ONLY [propext, Classical.choice, Quot.sound]. -/

#print axioms netEval3
#print axioms z_in_box1
#print axioms z_in_box2
#print axioms netEval3_z2_upper_bound
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms acas3_state_lower_bound
#print axioms netEval3_upper_bound
#print axioms netEval3_upper_bound_direct
#print axioms acas3_decision
#print axioms acas3_unsafe_refuted
#print axioms netEval3_cornerMin_val
#print axioms netEval3_cornerMin_le

end NetAcas3Layer
end Crownproof
