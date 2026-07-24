/-
  ============================================================================
  WAVE-6 PROGRAM 1 — FULL DEPTH: ALL 7 ACAS LAYERS COMPOSED, REACHING REAL Y_0
  ============================================================================

  Trust-boundary depth story: wave-3 = 1 layer, wave-4 = 2, wave-5 = 3
  (`NetAcas3Layer.lean`).  THIS file COMPLETES the depth: it composes ALL SEVEN
  affine+ReLU layers of the real shipped `ACASXU_run2a_1_1_batch_2000.onnx`
  (the 6 hidden affine+ReLU layers L0..L5 + the final affine readout L6), as a
  narrow-width slice threaded through every layer, ENDING AT THE REAL Y_0 output
  direction (the COC output, output index 0 of the final affine layer).

  The ONNX op graph is  Sub; Flatten; (MatMul;Add;Relu)x6 ; MatMul;Add
  (a 5 -> 50 -> 50 -> 50 -> 50 -> 50 -> 50 -> 5 f32 ReLU net).  L0..L5 are the
  six 50-wide hidden affine+ReLU layers; L6 is the final affine readout 50 -> 5
  whose ROW 0 is Y_0 (the real prop_1 atom direction).

  WIDTH RESTRICTION (ruthlessly honest).  To keep the EXACT-rational arithmetic
  tractable we restrict the WIDTH but take DEPTH 7.  We take a genuine 7-layer
  SUB-NETWORK of the real net, choosing at each layer the genuinely-UNSTABLE
  neurons (l < 0 < u) over the threaded box, reading only the previous slice:
    * L0 : neurons S0 = {0,2,4}    of the 50  (5  -> 3), all 3 ReLU UNSTABLE;
    * L1 : neurons S1 = {0,1,3},   cols S0     (3  -> 3), all 3 ReLU UNSTABLE;
    * L2 : neurons S2 = {15,29,49},cols S1     (3  -> 3), all 3 ReLU UNSTABLE;
    * L3 : neurons S3 = {27,33,37},cols S2     (3  -> 3), all 3 ReLU UNSTABLE;
    * L4 : neurons S4 = {1,38},    cols S3     (3  -> 2), both ReLU  UNSTABLE;
    * L5 : neuron  S5 = {8},       cols S4     (2  -> 1), the ReLU   UNSTABLE;
    * L6 : ROW 0 = the REAL Y_0 (COC) affine readout, cols S5 (1 -> 1), NO ReLU.
  So DEPTH = 7 real layers genuinely composed (6 affine+ReLU + 1 affine readout);
  widths 3,3,3,3,2,1.  The slice NARROWS with depth because fewer deep neurons
  stay unstable over the (narrowing) threaded box — S4 has only 2 surviving
  unstable neurons, S5 only 1.  This is NOT the full 50-wide net; it is a genuine
  depth-7 width-{3,3,3,3,2,1} real sub-network whose COMPOSITION is exact:
      Y0 = W6row0 · relu(W5 · relu(W4 · relu(W3 · relu(W2 ·
                        relu(W1 · relu(W0·x+B0) + B1) + B2) + B3) + B4) + B5)+b6.

  READOUT = the REAL Y_0 (honest about width).  L0..L2 (S0,S1,S2) reproduce the
  wave-5 slice EXACTLY (the layer-2 z-bound uz20 = 47722.../309485... is identical
  to wave-5's `NetAcas3Layer.uz20`).  We go four layers DEEPER and end at the REAL
  Y_0 ROW of the real final affine readout, restricted to the S5 columns.  Because
  S5 = {8} is a single neuron, the narrow-slice Y_0 reads exactly ONE of the 50
  layer-5 activations:  Y0slice = w6_8 · relu(z5_8) + b6_0.  This IS the real Y_0
  output DIRECTION at depth 7 — the milestone — but it is a NARROW-WIDTH slice of
  it (the full Y_0 reads all 50 layer-5 neurons).

  Y_0 BOUND vs the real prop_1 threshold (ruthlessly honest).  prop_1 is unsafe
  iff Y_0 >= 3.991125645861615.  We prove  Y0slice <= cBoundY0 ≈ -0.009046505 < 0,
  hence FAR below 3.991126.  But this bound is on the NARROW-WIDTH Y_0 slice, NOT
  the full-width Y_0, so it DOES NOT decide the real prop_1 atom (that needs all
  50 layer-5 neurons / full width).  The milestone is reaching the REAL Y_0
  direction at DEPTH 7 with bounds threaded across EVERY layer — not deciding
  prop_1.

  INPUT BOX (honest).  The VNN-COMP ACAS prop_1 network-input box, dyadically
  OVER-approximated (lowers DOWN, uppers UP), CONTAINS the real decimal box:
    x0 ∈ [19/32,11/16], x1,x2 ∈ [-1/2,1/2], x3 ∈ [57/128,1/2], x4 ∈ [-1/2,-57/128].

  THE THREADING IS GENUINE AND LOAD-BEARING ACROSS ALL 7 LAYERS:
    z_in_box0 : L0 pre-act box from the input box.
    a0_in_box : L0 POST-ReLU box from the L0 ReLU envelopes.
    z_in_box1 : L1 pre-act box FROM the L0 post-ReLU box.    ... and so on ...
    z_in_box5 : L5 pre-act box FROM the L4 post-ReLU box (5th threading hop).
  The final Y_0 bound rests on z_in_box5, which rests on a4_in_box <- z_in_box4
  <- a3_in_box <- z_in_box3 <- a2_in_box <- z_in_box2 <- a1_in_box <- z_in_box1
  <- a0_in_box <- z_in_box0 <- inBox.  ALL SEVEN layers are load-bearing.

  WHAT THIS FILE PROVES (sorry-free; axioms = [propext,Classical.choice,Quot.sound]):
    1. `netEval7` — the real depth-7 slice, defined INSIDE Lean as the explicit
       composition of SIX Fin-indexed affine+ReLU layers + the final affine Y_0
       readout, from the ONNX-parsed real f32 weights.
    2. `z_in_box1..5` — the FIVE THREADED intermediate pre-act boxes (each from the
       previous layer's post-ReLU box).
    3. `bridge_premises_sound` — every emitter premise (the L5 ReLU UNSTABLE upper
       chord on the FIVE-times-threaded z5, the threaded z5-upper, and the Y_0
       output pin) holds for `netEval7` on the box.
    4. `cert_identity` + `acas7_state_lower_bound` — the emitted depth-7 Farkas
       certificate (exact rational multipliers) folds to  -netEval7 x ≥ -cBoundY0.
    5. `netEval7_upper_bound` — the REAL Y_0 (narrow slice) is ≤ cBoundY0 everywhere
       on the box, OBTAINED FROM the depth-7 certificate.
    6. `acas7_decision` — Y0slice < 0 < 3.991126 everywhere (does NOT decide the
       full-width prop_1; see honesty note above).

  Cross-check: the standalone dependency-free reader's exact-dyadic 7-layer
  forward eval agrees with `netEval7` at the box corners (see `netEval7_at_*`).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetAcas7Layer

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

open Finset

/-! ## 0.  Exact-rational weights of the REAL ACAS-Xu seven-layer slice,
    parsed losslessly by the STANDALONE reader `/tmp/acasreader`.

`W0`/`B0` : L0 neurons {0,2,4}                 (5 -> 3); identical to wave-3/4/5.
`W1`/`B1` : L1 neurons {0,1,3},   cols {0,2,4} (3 -> 3); identical to wave-5.
`W2`/`B2` : L2 neurons {15,29,49},cols S1      (3 -> 3); {15,29} match wave-5.
`W3`/`B3` : L3 neurons {27,33,37},cols S2      (3 -> 3).
`W4`/`B4` : L4 neurons {1,38},    cols S3      (3 -> 2).
`W5`/`B5` : L5 neuron  {8},       cols S4      (2 -> 1).
`W6`/`B6` : L6 ROW 0 = REAL Y_0,  cols S5      (1 -> 1); the COC direction. -/

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

/-- L2 neurons {15,29,49}, cols S1={0,1,3}.  Rows {15,29} match wave-5's W2. -/
def W2 : Fin 3 → Fin 3 → ℚ :=
  ![ ![ 9916677/33554432, 904453/67108864, 3259897/2097152 ]
   , ![ -3894579/8388608, -5623347/268435456, 12818363/16777216 ]
   , ![ -11486403/16777216, 14291879/536870912, -16561797/33554432 ] ]
def B2 : Fin 3 → ℚ := ![ -16643857/268435456, -3538127/67108864, 15326993/134217728 ]

def W3 : Fin 3 → Fin 3 → ℚ :=
  ![ ![ 8478383/16777216, 6836011/33554432, -9167423/16777216 ]
   , ![ 5758083/8388608, -6868995/67108864, 6186095/33554432 ]
   , ![ -13875513/8388608, -5961247/8388608, 12896109/16777216 ] ]
def B3 : Fin 3 → ℚ := ![ -10396599/134217728, -13552635/134217728, 7546895/33554432 ]

def W4 : Fin 2 → Fin 3 → ℚ :=
  ![ ![ -3256701/8388608, -15384959/16777216, 3256269/4194304 ]
   , ![ -9236663/67108864, -14695231/134217728, -9186901/33554432 ] ]
def B4 : Fin 2 → ℚ := ![ -9979357/67108864, 14061347/268435456 ]

def W5 : Fin 1 → Fin 2 → ℚ :=
  ![ ![ 2161283/8388608, -9747395/33554432 ] ]
def B5 : Fin 1 → ℚ := ![ 9094003/1073741824 ]

/-- L6 ROW 0 = the REAL Y_0 (COC) affine readout, restricted to the S5 column. -/
def W6 : Fin 1 → Fin 1 → ℚ := ![ ![ 5059431/134217728 ] ]
def B6 : Fin 1 → ℚ := ![ -11039677/1073741824 ]

/-! ## 1.  The seven-layer network defined INSIDE Lean. -/

def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

def z0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W0 B0 x
def a0lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z0lay x)
def z1lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W1 B1 (a0lay x)
def a1lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z1lay x)
def z2lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W2 B2 (a1lay x)
def a2lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z2lay x)
def z3lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := affine W3 B3 (a2lay x)
def a3lay (x : Fin 5 → ℚ) : Fin 3 → ℚ := reluVec (z3lay x)
def z4lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := affine W4 B4 (a3lay x)
def a4lay (x : Fin 5 → ℚ) : Fin 2 → ℚ := reluVec (z4lay x)
def z5lay (x : Fin 5 → ℚ) : Fin 1 → ℚ := affine W5 B5 (a4lay x)
def a5lay (x : Fin 5 → ℚ) : Fin 1 → ℚ := reluVec (z5lay x)

/-- **The real ACAS-Xu depth-7 slice, evaluated exactly inside Lean, ending at the
    REAL Y_0 (COC) output direction (layer-6 affine readout, no ReLU).** -/
def netEval7 (x : Fin 5 → ℚ) : ℚ := (affine W6 B6 (a5lay x)) 0

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

theorem z2lay_2 (x : Fin 5 → ℚ) :
    z2lay x 2 = (-11486403/16777216) * a1lay x 0 + (14291879/536870912) * a1lay x 1
              + (-16561797/33554432) * a1lay x 2 + (15326993/134217728) := by
  show (∑ j : Fin 3, W2 2 j * a1lay x j) + B2 2 = _
  rw [Fin.sum_univ_three]
  simp only [W2, B2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a2lay_eq (x : Fin 5 → ℚ) (m : Fin 3) : a2lay x m = relu (z2lay x m) := rfl

theorem z3lay_0 (x : Fin 5 → ℚ) :
    z3lay x 0 = (8478383/16777216) * a2lay x 0 + (6836011/33554432) * a2lay x 1
              + (-9167423/16777216) * a2lay x 2 + (-10396599/134217728) := by
  show (∑ j : Fin 3, W3 0 j * a2lay x j) + B3 0 = _
  rw [Fin.sum_univ_three]
  simp only [W3, B3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z3lay_1 (x : Fin 5 → ℚ) :
    z3lay x 1 = (5758083/8388608) * a2lay x 0 + (-6868995/67108864) * a2lay x 1
              + (6186095/33554432) * a2lay x 2 + (-13552635/134217728) := by
  show (∑ j : Fin 3, W3 1 j * a2lay x j) + B3 1 = _
  rw [Fin.sum_univ_three]
  simp only [W3, B3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z3lay_2 (x : Fin 5 → ℚ) :
    z3lay x 2 = (-13875513/8388608) * a2lay x 0 + (-5961247/8388608) * a2lay x 1
              + (12896109/16777216) * a2lay x 2 + (7546895/33554432) := by
  show (∑ j : Fin 3, W3 2 j * a2lay x j) + B3 2 = _
  rw [Fin.sum_univ_three]
  simp only [W3, B3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a3lay_eq (x : Fin 5 → ℚ) (j : Fin 3) : a3lay x j = relu (z3lay x j) := rfl

theorem z4lay_0 (x : Fin 5 → ℚ) :
    z4lay x 0 = (-3256701/8388608) * a3lay x 0 + (-15384959/16777216) * a3lay x 1
              + (3256269/4194304) * a3lay x 2 + (-9979357/67108864) := by
  show (∑ j : Fin 3, W4 0 j * a3lay x j) + B4 0 = _
  rw [Fin.sum_univ_three]
  simp only [W4, B4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem z4lay_1 (x : Fin 5 → ℚ) :
    z4lay x 1 = (-9236663/67108864) * a3lay x 0 + (-14695231/134217728) * a3lay x 1
              + (-9186901/33554432) * a3lay x 2 + (14061347/268435456) := by
  show (∑ j : Fin 3, W4 1 j * a3lay x j) + B4 1 = _
  rw [Fin.sum_univ_three]
  simp only [W4, B4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a4lay_eq (x : Fin 5 → ℚ) (j : Fin 2) : a4lay x j = relu (z4lay x j) := rfl

theorem z5lay_0 (x : Fin 5 → ℚ) :
    z5lay x 0 = (2161283/8388608) * a4lay x 0 + (-9747395/33554432) * a4lay x 1
              + (9094003/1073741824) := by
  show (∑ j : Fin 2, W5 0 j * a4lay x j) + B5 0 = _
  rw [Fin.sum_univ_two]
  simp only [W5, B5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
             Function.comp]

theorem a5lay_eq (x : Fin 5 → ℚ) (j : Fin 1) : a5lay x j = relu (z5lay x j) := rfl

/-- The REAL Y_0 readout in closed form:  Y0 = w6_8 · a5_8 + b6_0. -/
theorem netEval7_eq (x : Fin 5 → ℚ) :
    netEval7 x = (5059431/134217728) * a5lay x 0 + (-11039677/1073741824) := by
  show (∑ j : Fin 1, W6 0 j * a5lay x j) + B6 0 = _
  rw [Fin.sum_univ_one]
  simp only [W6, B6, Matrix.cons_val_zero, Matrix.cons_val_fin_one]

/-! ## 2.  Chord/box parameters (exact CROWN values), threaded across 7 layers.
    Layers 0,1,2 are computed exactly as in wave-5; layers 3,4,5 are the new
    deeper hops.  All `lz < 0 < uz` (UNSTABLE) and each slope `s = uz/(uz-lz)`. -/

-- Layer 0 (input box IBP).
def uz00 : ℚ := 14760595147/8589934592
def uz01 : ℚ := 3023736455/8589934592
def uz02 : ℚ := 159834351/536870912
def lz00 : ℚ := -9437149291/8589934592
def lz01 : ℚ := -311884855/536870912
def lz02 : ℚ := -2366066067/4294967296

-- Layer 1 (over L0 post-ReLU box).
def lz10 : ℚ := -11325193610012749/36028797018963968
def uz10 : ℚ := 11213891/134217728
def lz11 : ℚ := -56230646588496693/2305843009213693952
def uz11 : ℚ := 67057735547281893/4611686018427387904
def lz12 : ℚ := -47245797453402529/36028797018963968
def uz12 : ℚ := 277141724732365/2251799813685248

-- Layer 2 (over L1 post-ReLU box); rows {15,29} match wave-5.
def lz20 : ℚ := -16643857/268435456
def uz20 : ℚ := 47722234438952453681105529/309485009821345068724781056
def lz21 : ℚ := -113663406154008740142007967/1237940039285380274899124224
def uz21 : ℚ := 1560714800216846055871/37778931862957161709568
def lz22 : ℚ := -283689813202247626625/75557863725914323419136
def uz22 : ℚ := 283691498332993533245217635/2475880078570760549798248448

-- Layer 3 (over L2 post-ReLU box).
def lz30 : ℚ := -5818311510345932895682462789133149/41538374868278621028243970633760768
def uz30 : ℚ := 46108922504907314725492984325815/5192296858534827628530496329220096
def lz31 : ℚ := -266722579273379731116423175485/2535301200456458802993406410752
def uz31 : ℚ := 2159502586258322943269585739729229/83076749736557242056487941267521536
def lz32 : ℚ := -154474548245768130922638022780401/2596148429267413814265248164610048
def uz32 : ℚ := 13001119977658242870760276460166695/41538374868278621028243970633760768

-- Layer 4 (over L3 post-ReLU box).
def lz40 : ℚ := -245292209924149362262001222860126050661779/1393796574908163946345982392040522594123776
def uz40 : ℚ := 16427251947880457935243090540432108981819/174224571863520493293247799005065324265472
def lz41 : ℚ := -416797466013236641860692941120580518841003/11150372599265311570767859136324180752990208
def uz41 : ℚ := 14061347/268435456

-- Layer 5 (over L4 post-ReLU box).  Single neuron; the FIVE-times-threaded z5.
def lz50 : ℚ := -60775477123241/9007199254740992
def uz50 : ℚ := 47882055834175380365861268732930019437694707249/1461501637330902918203684832716283019655932542976
def s50  : ℚ := 47882055834175380365861268732930019437694707249/57743440801142865596467844208643371640669890097

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
  obtain ⟨⟨_,zb0u⟩,⟨_,zb1u⟩,⟨_,zb2u⟩⟩ := z_in_box0 x hb
  rw [a0lay_eq, a0lay_eq, a0lay_eq]
  refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · unfold relu; exact max_le (by norm_num [uz00]) zb0u
  · unfold relu; exact max_le (by norm_num [uz01]) zb1u
  · unfold relu; exact max_le (by norm_num [uz02]) zb2u

/-! ## 6.  THREADED layer-1 pre-activation bounds — FROM the L0 post-ReLU box. -/

theorem z_in_box1 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz10 ≤ z1lay x 0 ∧ z1lay x 0 ≤ uz10) ∧
    (lz11 ≤ z1lay x 1 ∧ z1lay x 1 ≤ uz11) ∧
    (lz12 ≤ z1lay x 2 ∧ z1lay x 2 ≤ uz12) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a0_in_box x hb
  rw [z1lay_0, z1lay_1, z1lay_2]
  simp only [lz10, uz10, lz11, uz11, lz12, uz12, uz00, uz01, uz02] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

theorem a1_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a1lay x 0 ∧ a1lay x 0 ≤ uz10) ∧
    (0 ≤ a1lay x 1 ∧ a1lay x 1 ≤ uz11) ∧
    (0 ≤ a1lay x 2 ∧ a1lay x 2 ≤ uz12) := by
  obtain ⟨⟨_,zb0u⟩,⟨_,zb1u⟩,⟨_,zb2u⟩⟩ := z_in_box1 x hb
  rw [a1lay_eq, a1lay_eq, a1lay_eq]
  refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · unfold relu; exact max_le (by norm_num [uz10]) zb0u
  · unfold relu; exact max_le (by norm_num [uz11]) zb1u
  · unfold relu; exact max_le (by norm_num [uz12]) zb2u

/-! ## 7.  THREADED layer-2 pre-activation bounds — FROM the L1 post-ReLU box. -/

theorem z_in_box2 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz20 ≤ z2lay x 0 ∧ z2lay x 0 ≤ uz20) ∧
    (lz21 ≤ z2lay x 1 ∧ z2lay x 1 ≤ uz21) ∧
    (lz22 ≤ z2lay x 2 ∧ z2lay x 2 ≤ uz22) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a1_in_box x hb
  rw [z2lay_0, z2lay_1, z2lay_2]
  simp only [lz20, uz20, lz21, uz21, lz22, uz22, uz10, uz11, uz12] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

theorem a2_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a2lay x 0 ∧ a2lay x 0 ≤ uz20) ∧
    (0 ≤ a2lay x 1 ∧ a2lay x 1 ≤ uz21) ∧
    (0 ≤ a2lay x 2 ∧ a2lay x 2 ≤ uz22) := by
  obtain ⟨⟨_,zb0u⟩,⟨_,zb1u⟩,⟨_,zb2u⟩⟩ := z_in_box2 x hb
  rw [a2lay_eq, a2lay_eq, a2lay_eq]
  refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · unfold relu; exact max_le (by norm_num [uz20]) zb0u
  · unfold relu; exact max_le (by norm_num [uz21]) zb1u
  · unfold relu; exact max_le (by norm_num [uz22]) zb2u

/-! ## 8.  THREADED layer-3 pre-activation bounds — FROM the L2 post-ReLU box. -/

theorem z_in_box3 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz30 ≤ z3lay x 0 ∧ z3lay x 0 ≤ uz30) ∧
    (lz31 ≤ z3lay x 1 ∧ z3lay x 1 ≤ uz31) ∧
    (lz32 ≤ z3lay x 2 ∧ z3lay x 2 ≤ uz32) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a2_in_box x hb
  rw [z3lay_0, z3lay_1, z3lay_2]
  simp only [lz30, uz30, lz31, uz31, lz32, uz32, uz20, uz21, uz22] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

theorem a3_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a3lay x 0 ∧ a3lay x 0 ≤ uz30) ∧
    (0 ≤ a3lay x 1 ∧ a3lay x 1 ≤ uz31) ∧
    (0 ≤ a3lay x 2 ∧ a3lay x 2 ≤ uz32) := by
  obtain ⟨⟨_,zb0u⟩,⟨_,zb1u⟩,⟨_,zb2u⟩⟩ := z_in_box3 x hb
  rw [a3lay_eq, a3lay_eq, a3lay_eq]
  refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · unfold relu; exact max_le (by norm_num [uz30]) zb0u
  · unfold relu; exact max_le (by norm_num [uz31]) zb1u
  · unfold relu; exact max_le (by norm_num [uz32]) zb2u

/-! ## 9.  THREADED layer-4 pre-activation bounds — FROM the L3 post-ReLU box. -/

theorem z_in_box4 (x : Fin 5 → ℚ) (hb : inBox x) :
    (lz40 ≤ z4lay x 0 ∧ z4lay x 0 ≤ uz40) ∧
    (lz41 ≤ z4lay x 1 ∧ z4lay x 1 ≤ uz41) := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩,⟨a2l,a2u⟩⟩ := a3_in_box x hb
  rw [z4lay_0, z4lay_1]
  simp only [lz40, uz40, lz41, uz41, uz30, uz31, uz32] at *
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [a0l,a0u,a1l,a1u,a2l,a2u]

theorem a4_in_box (x : Fin 5 → ℚ) (hb : inBox x) :
    (0 ≤ a4lay x 0 ∧ a4lay x 0 ≤ uz40) ∧
    (0 ≤ a4lay x 1 ∧ a4lay x 1 ≤ uz41) := by
  obtain ⟨⟨_,zb0u⟩,⟨_,zb1u⟩⟩ := z_in_box4 x hb
  rw [a4lay_eq, a4lay_eq]
  refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · unfold relu; exact max_le (by norm_num [uz40]) zb0u
  · unfold relu; exact max_le (by norm_num [uz41]) zb1u

/-! ## 10.  THREADED layer-5 pre-activation bounds — FROM the L4 post-ReLU box.
    This is the FIFTH and DEEPEST threading hop; `z_in_box5` is load-bearing on
    the WHOLE 7-layer chain (it rests on a4 <- z4 <- a3 <- z3 <- a2 <- z2 <- a1
    <- z1 <- a0 <- z0 <- inBox). -/

theorem z_in_box5 (x : Fin 5 → ℚ) (hb : inBox x) :
    lz50 ≤ z5lay x 0 ∧ z5lay x 0 ≤ uz50 := by
  obtain ⟨⟨a0l,a0u⟩,⟨a1l,a1u⟩⟩ := a4_in_box x hb
  rw [z5lay_0]
  simp only [lz50, uz50, uz40, uz41] at *
  refine ⟨?_,?_⟩ <;> nlinarith [a0l,a0u,a1l,a1u]

/-! ## 11.  Layer-5 ReLU UNSTABLE upper chord on the FIVE-times-threaded z5. -/

theorem chord50 (z : ℚ) (hl : lz50 ≤ z) (hu : z ≤ uz50) : relu z ≤ s50 * (z - lz50) :=
  relu_upper lz50 uz50 s50 z (by norm_num [lz50]) (by norm_num [uz50])
    (by norm_num [s50, uz50, lz50]) hl hu

/-! ## 12.  The relaxed-network STATE the emitter reasons about (Farkas packaging).
    We package the depth-7 readout: the threaded L5 pre-act `z5`, its post-ReLU
    `a5`, and the Y_0 output `y`.  The threading that produced `z5`'s bound is the
    full 7-layer chain (carried by premise 1 below). -/

structure State where
  z5 : ℚ
  a5 : ℚ
  y  : ℚ

/-- The genuine execution state.  `y` stores `-netEval7 x`. -/
def genuine (x : Fin 5 → ℚ) : State where
  z5 := z5lay x 0
  a5 := a5lay x 0
  y  := -netEval7 x

def valid (st : State) : Prop := ∃ x : Fin 5 → ℚ, inBox x ∧ st = genuine x

/-! ## 13.  The emitter premises (the LOAD-BEARING depth-7 certificate for Y_0).
    Each premise normalised to `lhs ≤ 0`.

  Order:
    0  L5 ReLU UPPER chord    a5 ≤ s50·(z5 - lz50)     (FIVE-times-THREADED)
    1  L5 threaded z-upper    z5 ≤ uz50                 (FROM the 7-layer threading)
    2  Y_0 output pin         y = -(w6_8·a5 + b6_0)     (LOAD-BEARING)

  CROWN combination ( w6_8 = 5059431/134217728 > 0 ):
    w6_8·chord50 + (w6_8·s50)·(z5 - uz50) + 1·output
      = -(y) - (w6_8·uz50 + b6_0) = -(y) - cBoundY0. -/

def w6_8 : ℚ := 5059431/134217728
def b6_0 : ℚ := -11039677/1073741824

def prem : Fin 3 → State → ℚ :=
  ![ fun st => st.a5 - s50 * (st.z5 - lz50)          -- 0 L5 ReLU UPPER chord (THREADED)
   , fun st => st.z5 - uz50                           -- 1 threaded z5 ≤ uz50  LOAD-BEARING
   , fun st => -(st.y + (w6_8 * st.a5 + b6_0)) ]      -- 2 Y_0 output pin      LOAD-BEARING

/-! ## 14.  THE BRIDGE.  Every emitter premise is `≤ 0` on every valid state. -/

theorem bridge_all (x : Fin 5 → ℚ) (hb : inBox x) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 := by
  have ha5 : a5lay x 0 = relu (z5lay x 0) := a5lay_eq x 0
  have hy : netEval7 x = (5059431/134217728) * a5lay x 0 + (-11039677/1073741824) :=
    netEval7_eq x
  obtain ⟨zc0l, zc0u⟩ := z_in_box5 x hb
  have hup50 := chord50 _ zc0l zc0u
  simp only [s50, lz50, uz50] at hup50 zc0u
  refine ⟨?_,?_,?_⟩ <;>
    simp only [prem, genuine, s50, lz50, uz50, w6_8, b6_0,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
               Matrix.vecHead, Matrix.vecTail, Function.comp] <;>
    linarith [ha5, hy, hup50, zc0u]

theorem bridge_premises_sound :
    ∀ i : Fin 3, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, hb, rfl⟩ := hv
  obtain ⟨g0,g1,g2⟩ := bridge_all x hb
  fin_cases i
  · exact g0
  · exact g1
  · exact g2

/-! ## 15.  The certificate's exact multipliers + the Farkas conclusion. -/

/-- `cBoundY0 = w6_8·uz50 + b6_0 ≈ -0.009046505` — the CROWN upper bound on the
    REAL Y_0 (narrow S5 slice).  Strictly negative, hence far below the prop_1
    threshold 3.991125645861615 (but on the NARROW slice, not full-width Y_0). -/
def cBoundY0 : ℚ :=
  -1774557293756881013055932750646632786024593130638942025/196159429230833773869868419475239575503198607639501078528

/-- Multipliers:  μ0 = w6_8 (>0);  μ1 = w6_8·s50 (>0);  μ2 = 1. -/
def mu : Fin 3 → ℚ :=
  ![ 5059431/134217728,                                         -- 0 L5 chord  (= w6_8)
     242255957631157778859829844726716861173675170391515319/7750193431231895223767278874742071303870345046829039616, -- 1 z5≤uz50 (= w6_8·s50)
     1 ]                                                        -- 2 output pin

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> norm_num [mu]

/-- **The Farkas certificate identity** — pure algebra (`ring`).  The multipliers
    fold the three premises into `-(st.y) - cBoundY0`:
      w6_8·chord50 + (w6_8·s50)·(z5-uz50) + 1·output
        = -(y) - (w6_8·uz50 + b6_0) = -(y) - cBoundY0.
    Load-bearing: the L5 UNSTABLE upper chord (0), the FIVE-times-THREADED z5
    upper bound (1; multiplier w6_8·s50 — this carries the full 7-layer
    threading), and the Y_0 output pin (2). -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 3)), mu i * prem i st) = -(st.y) - cBoundY0 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, mu, prem,
             s50, lz50, uz50, w6_8, b6_0, cBoundY0,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_succ, Matrix.cons_val, Matrix.cons_val_fin_one,
             Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

theorem acas7_state_lower_bound :
    ∀ st : State, valid st → -cBoundY0 ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 3)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := cBoundY0)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

theorem genuine_y (x : Fin 5 → ℚ) : (genuine x).y = -netEval7 x := rfl

/-- **Upper bound on the REAL ONNX 7-layer Y_0 output (narrow S5 slice), OBTAINED
    FROM THE DEPTH-7 CERTIFICATE.** -/
theorem netEval7_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval7 x ≤ cBoundY0 := by
  have hv : valid (genuine x) := ⟨x, hb, rfl⟩
  have h := acas7_state_lower_bound (genuine x) hv
  rw [genuine_y] at h
  linarith

/-! ## 16.  THE DECISION on the REAL 7-layer Y_0 output direction.

  HONEST: this is the bound on the NARROW-WIDTH Y_0 slice (reads only the single
  layer-5 neuron S5={8}), NOT the full-width Y_0 (which reads all 50).  It does
  NOT decide the real prop_1 atom.  It DOES certify the milestone: at DEPTH 7,
  reaching the REAL Y_0 direction, the slice value is strictly negative — far
  below the prop_1 threshold 3.991125645861615. -/

theorem cBoundY0_neg : cBoundY0 < 0 := by norm_num [cBoundY0]
theorem cBoundY0_lt_thr : cBoundY0 < 3991125645861615/1000000000000000 := by
  norm_num [cBoundY0]

/-- **The decision:** the REAL 7-layer ACAS Y_0 (narrow S5 slice) is strictly
    negative everywhere on the box — fully kernel-checked via genuine depth-7
    CROWN composition reaching the real Y_0 output direction. -/
theorem acas7_decision (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval7 x < 0 := by
  have := netEval7_upper_bound x hb
  have := cBoundY0_neg
  linarith

/-- The narrow-slice Y_0 stays below the prop_1 threshold (NOT a decision of the
    real full-width prop_1 — see honesty note). -/
theorem acas7_below_prop1_threshold (x : Fin 5 → ℚ) (hb : inBox x) :
    netEval7 x < 3991125645861615/1000000000000000 := by
  have := netEval7_upper_bound x hb
  have := cBoundY0_lt_thr
  linarith

/-! ## 17.  Cross-check vs the standalone reader's exact 7-layer forward eval.

The dependency-free reader's exact-dyadic seven-layer forward eval (Python bignum
ref, overflow-free) at the box corners agrees with `netEval7`:
  cornerMin: netEval7 = -63812474377622243450151773052890747255582099576958200899
                        /6277101735386680763835789423207666416102355444464034512896
  cornerMax: netEval7 = -6968021309524451923022051685940032742328439539968871
                        /766247770432944429179173513575154591809369561091801088. -/

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

/-- The reader's exact 7-layer forward value at the min corner, reproduced in Lean. -/
theorem netEval7_cornerMin_val :
    netEval7 cornerMin =
      -63812474377622243450151773052890747255582099576958200899/6277101735386680763835789423207666416102355444464034512896 := by
  rw [netEval7_eq, a5lay_eq, z5lay_0,
      a4lay_eq, a4lay_eq, z4lay_0, z4lay_1,
      a3lay_eq, a3lay_eq, a3lay_eq, z3lay_0, z3lay_1, z3lay_2,
      a2lay_eq, a2lay_eq, a2lay_eq, z2lay_0, z2lay_1, z2lay_2,
      a1lay_eq, a1lay_eq, a1lay_eq, z1lay_0, z1lay_1, z1lay_2,
      a0lay_eq, a0lay_eq, a0lay_eq, z0lay_0, z0lay_1, z0lay_2]
  simp only [cornerMin, relu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one]
  norm_num

theorem netEval7_cornerMax_val :
    netEval7 cornerMax =
      -6968021309524451923022051685940032742328439539968871/766247770432944429179173513575154591809369561091801088 := by
  rw [netEval7_eq, a5lay_eq, z5lay_0,
      a4lay_eq, a4lay_eq, z4lay_0, z4lay_1,
      a3lay_eq, a3lay_eq, a3lay_eq, z3lay_0, z3lay_1, z3lay_2,
      a2lay_eq, a2lay_eq, a2lay_eq, z2lay_0, z2lay_1, z2lay_2,
      a1lay_eq, a1lay_eq, a1lay_eq, z1lay_0, z1lay_1, z1lay_2,
      a0lay_eq, a0lay_eq, a0lay_eq, z0lay_0, z0lay_1, z0lay_2]
  simp only [cornerMax, relu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.cons_val_fin_one]
  norm_num

/-- The certified bound holds (non-vacuously) at this corner. -/
theorem netEval7_cornerMin_le : netEval7 cornerMin ≤ cBoundY0 :=
  netEval7_upper_bound cornerMin cornerMin_inBox

/-! ## Trust-base check.  Each must list ONLY [propext, Classical.choice, Quot.sound]. -/

#print axioms netEval7
#print axioms z_in_box1
#print axioms z_in_box2
#print axioms z_in_box3
#print axioms z_in_box4
#print axioms z_in_box5
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms acas7_state_lower_bound
#print axioms netEval7_upper_bound
#print axioms acas7_decision
#print axioms acas7_below_prop1_threshold
#print axioms netEval7_cornerMin_val
#print axioms netEval7_cornerMax_val
#print axioms netEval7_cornerMin_le

end NetAcas7Layer
end Crownproof
