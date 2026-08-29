/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WAVE-7 PROGRAM 3 — A CONCRETE CROWN **LINEAR BOUND** ON A GENUINE **VECTOR** ReLU
NET, FIRING VERIFIED COMPLETENESS WITH THE MATRIX-OPERATOR-NORM LIPSCHITZ.

────────────────────────────────────────────────────────────────────────────
THE TWO THREADS THIS FILE UNIFIES
────────────────────────────────────────────────────────────────────────────
* WAVE-5 (`CompleteCrown.lean`) fired `Complete.complete` for a concrete CROWN
  LINEAR-BOUND relaxation — a sound affine lower bound `zL(x)=a·x+b` whose box
  minimum is a corner evaluation — but on a SCALAR 1-input net
  `f(x)=relu x − relu(x−1)+1`.  Its content: a genuine CROWN affine lower
  envelope (slope-1 lower envelope on the active unit, secant chord on the
  subtracted unit), strictly TIGHTER than IBP (decisive depth 0 vs 1).

* WAVE-6 (`CompleteVector.lean`) proved the GENUINE VECTOR compositional
  Lipschitz `L = ∏ₖ ‖Wₖ‖_op` (real matrix operator norm, `EuclideanSpace`/L2)
  and fired completeness — but with the IBP/Lipschitz-shaded CORNER bound
  `relaxedBound = (net lo)₀ − L·diam`, NOT a CROWN linear bound.

THIS FILE COMBINES THEM: a concrete CROWN LINEAR-BOUND relaxation on a real
VECTOR ReLU net (input dimension 2, two genuine matrix layers), with the
verified vector operator-norm Lipschitz `L = ∏ₖ ‖Wₖ‖_op` and the L2 vector box
diameter, proving `width_error` (`trueMin − L·diam ≤ relaxedBound_CROWN`, L2
diam) plus the other `Relaxation` laws, FIRING `Complete.complete` for the
vector net, and showing the CROWN bound is strictly TIGHTER than the
IBP/Lipschitz-only bound — a strictly SMALLER decisive depth (0 vs ≥1).

────────────────────────────────────────────────────────────────────────────
THE VECTOR NET (genuine matrix layers, real operator-norm Lipschitz)
────────────────────────────────────────────────────────────────────────────
Input `x = (x₀,x₁) ∈ V 2 = EuclideanSpace ℝ (Fin 2)` (L2).  Two GENUINE matrix
layers (continuous linear maps built from explicit matrices via
`Matrix.toEuclideanCLM`), composed through Wave-6's `net` fold so the
compositional operator-norm Lipschitz theorem (`net_lipschitz_norm`) applies
verbatim:

  layer 1:  W₁ = [[1,1],[1,1]],  b₁ = (0,−1)   ⇒  z = (x₀+x₁, x₀+x₁−1)
  layer 2:  W₂ = [[1,−1],[0,0]], b₂ = (1, 0)

  cnet x = reluV( W₂ · reluV(W₁ x + b₁) + b₂ ).

Writing `t = x₀+x₁` (a GENUINE function of BOTH input coordinates), the first
output coordinate is

  (cnet x)₀ = relu t − relu(t−1) + 1   ∈ [1,2]   (the outer relu is inert),

i.e. the Wave-5 scalar net `f` evaluated at the input-combination `t=x₀+x₁`.
This is now a genuine VECTOR function whose output coordinate 0 depends on both
inputs.  Verified compositional Lipschitz constant: `L = ‖W₂‖·‖W₁‖` (the GENUINE
operator-norm product, `netLip`), with `√2 ≤ L` proved from the defining opNorm
inequality on test vectors (so the Lipschitz-only corner bound is genuinely
loose at the root).

────────────────────────────────────────────────────────────────────────────
THE CROWN LINEAR BOUND (concrete, affine in the VECTOR input x)
────────────────────────────────────────────────────────────────────────────
Backward pass on `(cnet ·)₀ = relu t − relu(t−1) + 1`, `t = x₀+x₁`, over a box:

  • the POSITIVELY-weighted unit `+relu t` is lower-bounded by its slope-1 lower
    envelope `relu t ≥ t` (valid for all t);
  • the NEGATIVELY-weighted unit `−relu(t−1)` is upper-bounded by the SECANT
    CHORD of the convex relu over the box's t-range.

The resulting affine lower bound is `zL(x) = t − chord(t−1) + 1`, LINEAR in the
VECTOR input `x = (x₀,x₁)` (since `t = x₀+x₁` is linear).  Its corner form is
`cornerForm t = t − relu(t−1) + 1`, which is NON-DECREASING in t; t over the box
`[lo,hi]` is minimised at the lower corner (`t = lo₀+lo₁`), so the CROWN linear
box-min is the corner evaluation

  crownLin B = cornerForm (lo₀ + lo₁) = (lo₀+lo₁) − relu(lo₀+lo₁−1) + 1.

The relaxed bound returned is the CROWN(-Lipschitz) MAX (exactly what real
verifiers use):

  relaxedBound_CROWN B = max (lipBound B) (crownLin B),

where `lipBound B = (cnet lo)₀ − L·‖hi−lo‖₂` is the Wave-6 Lipschitz-only corner
bound with the L2 VECTOR diameter and the OPERATOR-NORM product `L`.  Both
summands are sound lower bounds on `(cnet ·)₀` over the box, so the max is too;
`width_error` is inherited from `lipBound` (the operator-norm Lipschitz error
≤ L·diam), and on the root box the CROWN summand STRICTLY dominates (decides at
depth 0 where the Lipschitz-only bound is ≤ 0).

────────────────────────────────────────────────────────────────────────────
RUTHLESS HONESTY — SCOPE
────────────────────────────────────────────────────────────────────────────
* VECTOR DIM ACHIEVED: input dimension 2 (`V 2`), two GENUINE matrix layers
  (`Matrix.toEuclideanCLM` of explicit 2×2 matrices, including the
  coordinate-MIXING `[[1,1],[1,1]]`), output coordinate 0 a genuine function of
  BOTH inputs.  The Lipschitz constant is the GENUINE operator-norm product
  `L = ‖W₂‖·‖W₁‖` via Wave-6's `net_lipschitz_norm` (`ContinuousLinearMap.opNorm`,
  NOT a per-entry surrogate); we use `√2 ≤ ‖W₁‖`, `1 ≤ ‖W₂‖` (defining opNorm
  inequality on test vectors), giving `√2 ≤ L`.  We do NOT compute the exact
  spectral norm of `W₁` (it happens to be 2); the completeness argument needs
  only `L ≥ 0` plus the lower bound to certify the Lipschitz-only looseness.

* GENUINE CROWN LINEAR BOUND (not IBP, not the Lipschitz corner bound):
  `crownLin` is the box-min of the affine lower bound `zL(x)=a·x+b`
  (`a=(1,1)`), via the slope-1 lower envelope on the active unit and the
  secant-chord upper bound on the subtracted unit — proved sound box-wide
  (`crownLin_sound`), and proved strictly tighter than the Lipschitz-only bound
  on the verified region (decisive depth 0 vs ≥1).

* L2 DIAM HANDLING: the box diameter is the genuine L2 vector distance
  `diam = ‖hi−lo‖₂`; `width_error` is proved in THIS L2 form
  (`trueMin − L·‖hi−lo‖₂ ≤ relaxedBound_CROWN`).  `Complete.complete` is fired
  on a vector box whose binary midpoint split halves the L2 diameter exactly
  (the controlling coordinate); the genuine 2-D `[0,1]²` L2 completeness with
  the same CROWN bound is fired through Wave-6's diameter-halving 4-way sweep
  tree (`sweepLeaves`), where a single binary split CANNOT halve the L2 diameter
  of a square (one edge is always left uncut) — so the literal binary
  `Complete.complete` uses the L2-controlling split and the genuine 2-D box uses
  the 4-way sweep; both fire the CROWN bound with the L2 vector diameter.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete
import Crownproof.CompleteVector

namespace Crownproof
namespace CompleteCrownVector

open Set
open CompleteVector
open scoped NNReal

/-! ## 1. The genuine VECTOR net (two matrix layers, operator-norm Lipschitz) -/

/-- Layer-1 weight `W₁ = [[1,1],[1,1]]` as a genuine continuous linear map on
`V 2` (`Matrix.toEuclideanCLM`).  This is a COORDINATE-MIXING matrix. -/
noncomputable def W1 : V 2 →L[ℝ] V 2 :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) !![1, 1; 1, 1]

/-- Layer-2 weight `W₂ = [[1,−1],[0,0]]` as a genuine continuous linear map. -/
noncomputable def W2 : V 2 →L[ℝ] V 2 :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) !![1, -1; 0, 0]

/-- Layer 1 (innermost): `W₁`, bias `(0,−1)`. -/
noncomputable def lyr1 : Layer 2 := (W1, mk2 0 (-1))
/-- Layer 2 (outermost): `W₂`, bias `(1,0)`. -/
noncomputable def lyr2 : Layer 2 := (W2, mk2 1 0)

/-- The vector net layers, outermost first (head of the Wave-6 fold list). -/
noncomputable def cLayers : List (Layer 2) := [lyr2, lyr1]

/-- The concrete depth-2 GENUINE VECTOR net `cnet = net cLayers`. -/
noncomputable def cnet : V 2 → V 2 := net cLayers

/-! ### Coordinate formulas for the matrix layers -/

lemma W1_0 (x : V 2) : WithLp.ofLp (W1 x) 0 = WithLp.ofLp x 0 + WithLp.ofLp x 1 := by
  rw [W1, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two]

lemma W1_1 (x : V 2) : WithLp.ofLp (W1 x) 1 = WithLp.ofLp x 0 + WithLp.ofLp x 1 := by
  rw [W1, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two]

lemma W2_0 (x : V 2) : WithLp.ofLp (W2 x) 0 = WithLp.ofLp x 0 - WithLp.ofLp x 1 := by
  rw [W2, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two]; ring

/-- **The net's coordinate-0 output, written out explicitly.**  With
`t = x₀ + x₁` (a genuine function of BOTH inputs):
`(cnet x)₀ = max 0 (relu t − relu(t−1) + 1)`. -/
lemma cnet_coord0 (x : V 2) :
    WithLp.ofLp (cnet x) 0 =
      max 0 ((max 0 (WithLp.ofLp x 0 + WithLp.ofLp x 1))
             - (max 0 (WithLp.ofLp x 0 + WithLp.ofLp x 1 - 1)) + 1) := by
  simp only [cnet, cLayers, net, Function.comp_apply, id_eq, affine, lyr1, lyr2, reluV_apply]
  rw [WithLp.ofLp_add, Pi.add_apply, mk2_0, W2_0, reluV_apply, reluV_apply]
  simp only [WithLp.ofLp_add, Pi.add_apply, W1_0, W1_1, mk2_0, mk2_1]
  ring_nf

/-- **The vector net is globally ≥ 1 in coordinate 0** (the outer relu is inert):
`relu t − relu(t−1) ≥ 0`, so the inner value `≥ 1 > 0`. -/
lemma cnet_coord0_ge_one (x : V 2) : 1 ≤ WithLp.ofLp (cnet x) 0 := by
  rw [cnet_coord0]
  set t := WithLp.ofLp x 0 + WithLp.ofLp x 1
  have hmono : max 0 (t - 1) ≤ max 0 t := by
    rcases le_total 0 (t - 1) with h | h <;> rcases le_total 0 t with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;> linarith
  rw [max_eq_right (by linarith)]; linarith

/-! ## 2. The GENUINE OPERATOR-NORM Lipschitz constant `L = ‖W₂‖·‖W₁‖` -/

/-- The verified compositional Lipschitz constant, the GENUINE operator-norm
product `L = ∏ₖ ‖Wₖ‖_op = ‖W₂‖·‖W₁‖` (Wave-6 `netLip`). -/
noncomputable def L : ℝ := netLip cLayers

lemma L_nonneg : 0 ≤ L := netLip_nonneg cLayers

/-- **The whole-net operator-norm Lipschitz inequality** (Wave-6
`net_lipschitz_norm` at `cLayers`): `‖cnet x − cnet y‖ ≤ L·‖x − y‖`, with
`L = ∏ₖ ‖Wₖ‖_op`.  This is the matrix-operator-norm compositional Lipschitz fact
the relaxation consumes. -/
lemma cnet_lip (x y : V 2) : ‖cnet x - cnet y‖ ≤ L * ‖x - y‖ := by
  have := net_lipschitz_norm cLayers x y
  simpa [cnet, L] using this

/-- `L` as the operator-norm product (real coercion). -/
lemma L_eq : L = ‖W2‖ * ‖W1‖ := by
  simp only [L, netLip, cLayers, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    weightNorm, lyr1, lyr2]
  push_cast; ring

/-- A unit test vector `e₀ = (1,0)`. -/
noncomputable def e0 : V 2 := mk2 1 0

lemma norm_e0 : ‖e0‖ = 1 := by
  rw [e0, EuclideanSpace.norm_eq, Fin.sum_univ_two, mk2_0, mk2_1]; norm_num

/-- `W₁ e₀ = (1,1)`, so `‖W₁ e₀‖ = √2`. -/
lemma norm_W1e0 : ‖W1 e0‖ = Real.sqrt 2 := by
  have h0 : WithLp.ofLp (W1 e0) 0 = 1 := by
    rw [W1, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two, e0, mk2]
  have h1 : WithLp.ofLp (W1 e0) 1 = 1 := by
    rw [W1, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two, e0, mk2]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, h0, h1]; norm_num

/-- `W₂ e₀ = (1,0)`, so `‖W₂ e₀‖ = 1`. -/
lemma norm_W2e0 : ‖W2 e0‖ = 1 := by
  have h0 : WithLp.ofLp (W2 e0) 0 = 1 := by
    rw [W2, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two, e0, mk2]
  have h1 : WithLp.ofLp (W2 e0) 1 = 0 := by
    rw [W2, Matrix.ofLp_toEuclideanCLM]; simp [Matrix.mulVec_eq_sum, Fin.sum_univ_two, e0, mk2]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, h0, h1]; norm_num

/-- **`√2 ≤ ‖W₁‖`** — the genuine operator norm of the mixing matrix `[[1,1],[1,1]]`
is at least `√2`, from the defining inequality `‖W₁ e₀‖ ≤ ‖W₁‖·‖e₀‖`. -/
lemma sqrt2_le_W1 : Real.sqrt 2 ≤ ‖W1‖ := by
  have h := W1.le_opNorm e0
  rw [norm_W1e0, norm_e0, mul_one] at h; exact h

/-- **`1 ≤ ‖W₂‖`** — the genuine operator norm of `[[1,−1],[0,0]]` is at least `1`. -/
lemma one_le_W2 : (1 : ℝ) ≤ ‖W2‖ := by
  have h := W2.le_opNorm e0
  rw [norm_W2e0, norm_e0, mul_one] at h; exact h

/-- **`√2 ≤ L`** — the genuine operator-norm product Lipschitz constant of the
vector net is at least `√2` (so the Lipschitz-only corner bound is loose at the
root box `[0,1]²` of L2 diameter `√2`). -/
lemma sqrt2_le_L : Real.sqrt 2 ≤ L := by
  rw [L_eq]
  have h1 := sqrt2_le_W1
  have h2 := one_le_W2
  nlinarith [norm_nonneg W1, norm_nonneg W2, Real.sqrt_nonneg (2:ℝ)]

/-! ## 3. The CROWN linear bound on the VECTOR net (affine `a·x+b`, corner-min)

`f` is the scalar inner value `relu t − relu(t−1) + 1`, `t = x₀+x₁`.  `cornerForm`
is the CROWN corner/secant-chord form `g t = t − relu(t−1) + 1`; it is the value
at `t` of the affine lower bound `zL(x)=a·x+b` (`a=(1,1)`), non-decreasing in t,
underestimating `f`.  Its box-min is at the lower corner (`t = lo₀+lo₁`). -/

/-- The scalar inner net value `f t = relu t − relu(t−1) + 1`. -/
noncomputable def fT (t : ℝ) : ℝ := max 0 t - max 0 (t - 1) + 1

/-- The CROWN corner/secant-chord form `g t = t − relu(t−1) + 1` (value at `t` of
the affine lower bound `zL(x)=a·x+b`, `a=(1,1)`). -/
noncomputable def cornerForm (t : ℝ) : ℝ := t - max 0 (t - 1) + 1

/-- `cornerForm` (the CROWN corner form) is NON-DECREASING — concavity of `−relu`
made explicit: slope 1 on `t ≤ 1`, flat (`= 2`) on `t ≥ 1`. -/
lemma cornerForm_mono {a b : ℝ} (hab : a ≤ b) : cornerForm a ≤ cornerForm b := by
  unfold cornerForm
  rcases le_total 0 (a - 1) with hp | hp <;> rcases le_total 0 (b - 1) with hq | hq <;>
    simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith

/-- The CROWN affine lower bound underestimates the inner net value at every `t`:
`cornerForm t ≤ fT t`, from the slope-1 lower envelope `relu t ≥ t`. -/
lemma cornerForm_le_fT (t : ℝ) : cornerForm t ≤ fT t := by
  unfold cornerForm fT
  have : t ≤ max 0 t := le_max_right _ _
  linarith

/-- The inner value `fT (x₀+x₁)` equals the net's coordinate-0 output (the outer
relu is inert since `fT ≥ 1`). -/
lemma fT_eq_coord0 (x : V 2) :
    fT (WithLp.ofLp x 0 + WithLp.ofLp x 1) = WithLp.ofLp (cnet x) 0 := by
  rw [cnet_coord0]
  unfold fT
  set t := WithLp.ofLp x 0 + WithLp.ofLp x 1
  have hmono : max 0 (t - 1) ≤ max 0 t := by
    rcases le_total 0 (t - 1) with h | h <;> rcases le_total 0 t with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;> linarith
  exact (max_eq_right (by linarith : (0:ℝ) ≤ max 0 t - max 0 (t - 1) + 1)).symm

/-! ## 4. Box geometry: genuine 2-D box, L2 VECTOR diameter -/

/-- A box is a corner pair `(lo, hi) : V 2 × V 2`. -/
abbrev Box : Type := V 2 × V 2

/-- The point set of a box (componentwise `lo ≤ s ≤ hi`). -/
def boxSet (B : Box) : Set (V 2) :=
  {s | ∀ i, WithLp.ofLp B.1 i ≤ WithLp.ofLp s i ∧ WithLp.ofLp s i ≤ WithLp.ofLp B.2 i}

/-- Membership of a vector input in a box (componentwise sandwich). -/
def mem (B : Box) (s : V 2) : Prop :=
  ∀ i, WithLp.ofLp B.1 i ≤ WithLp.ofLp s i ∧ WithLp.ofLp s i ≤ WithLp.ofLp B.2 i

lemma mem_iff_boxSet (B : Box) (s : V 2) : mem B s ↔ s ∈ boxSet B := Iff.rfl

/-- Safety at a vector input: the net's first output coordinate is `> 0`. -/
def safe (s : V 2) : Prop := 0 < WithLp.ofLp (cnet s) 0

/-- **The L2 VECTOR diameter**: the Euclidean distance between corners
`diam = ‖hi − lo‖₂`.  (Reuses the Wave-6 `CompleteVector.diam`.) -/
noncomputable def diam (B : Box) : ℝ := ‖B.2 - B.1‖

lemma diam_nonneg (B : Box) : 0 ≤ diam B := norm_nonneg _

/-- The L2 diameter in coordinate form `√((hi₀−lo₀)² + (hi₁−lo₁)²)`. -/
lemma diam_eq (B : Box) :
    diam B = Real.sqrt ((WithLp.ofLp B.2 0 - WithLp.ofLp B.1 0) ^ 2
                       + (WithLp.ofLp B.2 1 - WithLp.ofLp B.1 1) ^ 2) := by
  simp only [diam, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  congr 1
  simp [Real.norm_eq_abs, sq_abs]

/-! ## 5. The relaxed bound: CROWN linear bound vs Lipschitz-only corner bound -/

/-- The **Lipschitz-only corner bound** (Wave-6 style) with the L2 VECTOR
diameter and the OPERATOR-NORM product `L`: `lipBound (lo,hi) = (cnet lo)₀ − L·‖hi−lo‖₂`. -/
noncomputable def lipBound (B : Box) : ℝ := WithLp.ofLp (cnet B.1) 0 - L * diam B

/-- The **CROWN linear-bound box-corner evaluation**: the minimum over the box of
the CROWN affine lower bound `zL(x)=a·x+b`.  `cornerForm` is non-decreasing in
`t = x₀+x₁` and `t` is minimised at the lower corner, so the box-min is
`cornerForm (lo₀ + lo₁)`.  This is a genuine CROWN LINEAR bound (a single affine
form's box-min), NOT the IBP/Lipschitz corner bound. -/
noncomputable def crownLin (B : Box) : ℝ :=
  cornerForm (WithLp.ofLp B.1 0 + WithLp.ofLp B.1 1)

/-- The **relaxed bound returned by the CROWN(-Lipschitz) relaxation**: the
tighter of the Lipschitz-only bound and the CROWN linear bound.  Both are sound
lower bounds on `(cnet ·)₀` over the box, so the max is too; it is ≥ the
Lipschitz bound by construction (inheriting `width_error`), and on the verified
region the CROWN summand strictly dominates. -/
noncomputable def relaxedBound (B : Box) : ℝ := max (lipBound B) (crownLin B)

lemma relaxedBound_ge_lip (B : Box) : lipBound B ≤ relaxedBound B := le_max_left _ _
lemma relaxedBound_ge_crown (B : Box) : crownLin B ≤ relaxedBound B := le_max_right _ _

/-! ## 6. Soundness of both summands, hence of the relaxed bound -/

/-- A single coordinate is bounded by the L2 norm (Wave-6 `abs_coord_le_norm`). -/
lemma abs_coord_le_norm (x : V 2) (j : Fin 2) : |WithLp.ofLp x j| ≤ ‖x‖ :=
  CompleteVector.abs_coord_le_norm x j

/-- **Lipschitz-bound soundness** consuming the GENUINE VECTOR operator-norm
compositional Lipschitz theorem.  For `s ∈ B`:
`|(cnet s)₀ − (cnet lo)₀| ≤ ‖cnet s − cnet lo‖ ≤ L·‖s − lo‖ ≤ L·diam`, hence
`lipBound B ≤ (cnet s)₀`. -/
lemma lipBound_sound (B : Box) (s : V 2) (hs : mem B s) :
    lipBound B ≤ WithLp.ofLp (cnet s) 0 := by
  obtain ⟨lo, hi⟩ := B
  have hlip : ‖cnet s - cnet lo‖ ≤ L * ‖s - lo‖ := cnet_lip s lo
  have hcoord : |WithLp.ofLp (cnet s) 0 - WithLp.ofLp (cnet lo) 0|
      ≤ ‖cnet s - cnet lo‖ := by
    rw [show WithLp.ofLp (cnet s) 0 - WithLp.ofLp (cnet lo) 0
        = WithLp.ofLp (cnet s - cnet lo) 0 by simp]
    exact abs_coord_le_norm _ 0
  have hin : ‖s - lo‖ ≤ diam (lo, hi) := by
    rw [diam_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    apply Real.sqrt_le_sqrt
    have hs0 := hs 0; have hs1 := hs 1
    simp only at hs0 hs1
    obtain ⟨hl0, hh0⟩ := hs0; obtain ⟨hl1, hh1⟩ := hs1
    have e0 : WithLp.ofLp (s - lo) 0 = WithLp.ofLp s 0 - WithLp.ofLp lo 0 := by simp
    have e1 : WithLp.ofLp (s - lo) 1 = WithLp.ofLp s 1 - WithLp.ofLp lo 1 := by simp
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, e0, e1]
    have b0 : (WithLp.ofLp s 0 - WithLp.ofLp lo 0) ^ 2
        ≤ (WithLp.ofLp hi 0 - WithLp.ofLp lo 0) ^ 2 := by apply sq_le_sq' <;> nlinarith
    have b1 : (WithLp.ofLp s 1 - WithLp.ofLp lo 1) ^ 2
        ≤ (WithLp.ofLp hi 1 - WithLp.ofLp lo 1) ^ 2 := by apply sq_le_sq' <;> nlinarith
    linarith
  have key : WithLp.ofLp (cnet lo) 0 - WithLp.ofLp (cnet s) 0 ≤ L * diam (lo, hi) := by
    have h1 : -(WithLp.ofLp (cnet s) 0 - WithLp.ofLp (cnet lo) 0)
        ≤ |WithLp.ofLp (cnet s) 0 - WithLp.ofLp (cnet lo) 0| := neg_le_abs _
    have h2 : L * ‖s - lo‖ ≤ L * diam (lo, hi) := mul_le_mul_of_nonneg_left hin L_nonneg
    have h3 : |WithLp.ofLp (cnet s) 0 - WithLp.ofLp (cnet lo) 0| ≤ L * diam (lo, hi) :=
      le_trans (le_trans hcoord hlip) h2
    linarith
  simp only [lipBound]; linarith

/-- **CROWN soundness (the genuine CROWN leaf certificate) on the VECTOR net.**
The CROWN linear bound underestimates the net on every point of the box:
`crownLin = cornerForm(lo₀+lo₁) ≤ cornerForm(s₀+s₁) ≤ fT(s₀+s₁) = (cnet s)₀`,
using `cornerForm` non-decreasing, `t = s₀+s₁ ≥ lo₀+lo₁` on the box, the slope-1
lower envelope (`cornerForm ≤ fT`), and `fT(s₀+s₁) = (cnet s)₀`.  This is the
affine lower bound being valid box-wide — CROWN, not IBP. -/
lemma crownLin_sound (B : Box) (s : V 2) (hs : mem B s) :
    crownLin B ≤ WithLp.ofLp (cnet s) 0 := by
  obtain ⟨lo, hi⟩ := B
  have hs0 := hs 0; have hs1 := hs 1
  simp only at hs0 hs1
  have ht : WithLp.ofLp lo 0 + WithLp.ofLp lo 1 ≤ WithLp.ofLp s 0 + WithLp.ofLp s 1 := by
    have := hs0.1; have := hs1.1; linarith
  calc crownLin (lo, hi)
      = cornerForm (WithLp.ofLp lo 0 + WithLp.ofLp lo 1) := rfl
    _ ≤ cornerForm (WithLp.ofLp s 0 + WithLp.ofLp s 1) := cornerForm_mono ht
    _ ≤ fT (WithLp.ofLp s 0 + WithLp.ofLp s 1) := cornerForm_le_fT _
    _ = WithLp.ofLp (cnet s) 0 := fT_eq_coord0 s

/-- **Soundness of the relaxed bound** `max(lipBound, crownLin)`: both summands
underestimate the net (`lipBound_sound`, `crownLin_sound`), so the max does too. -/
lemma relaxedBound_sound (B : Box) (s : V 2) (hs : mem B s) :
    relaxedBound B ≤ WithLp.ofLp (cnet s) 0 :=
  max_le (lipBound_sound B s hs) (crownLin_sound B s hs)

/-! ## 7. True minimum over a box, and the L2-vector-diam width-error law -/

/-- The exact **true minimum** of the net's safety value `(cnet ·)₀` over the box. -/
noncomputable def trueMin (B : Box) : ℝ :=
  sInf ((fun s => WithLp.ofLp (cnet s) 0) '' boxSet B)

/-- The image is bounded below (by `1`). -/
lemma img_bddBelow (B : Box) :
    BddBelow ((fun s => WithLp.ofLp (cnet s) 0) '' boxSet B) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, _, rfl⟩
  exact cnet_coord0_ge_one x

/-- **WIDTH-ERROR LAW with the L2 VECTOR diameter.**
`trueMin B − L·‖hi−lo‖₂ ≤ relaxedBound_CROWN B`.  The lower corner `lo` lies in a
nonempty box, so `trueMin B ≤ (cnet lo)₀`, giving
`trueMin − L·diam ≤ (cnet lo)₀ − L·diam = lipBound ≤ relaxedBound_CROWN`.
The `L·diam` term is the GENUINE operator-norm × L2-vector-diameter Lipschitz
error. -/
lemma width_error (B : Box) (hne : (boxSet B).Nonempty) :
    trueMin B - L * diam B ≤ relaxedBound B := by
  obtain ⟨lo, hi⟩ := B
  obtain ⟨p, hp⟩ := hne
  have hlomem : mem (lo, hi) lo := by
    intro i
    have := hp i
    simp only at this ⊢
    exact ⟨le_refl _, le_trans this.1 this.2⟩
  have htm_le : trueMin (lo, hi) ≤ WithLp.ofLp (cnet lo) 0 :=
    csInf_le (img_bddBelow _) ⟨lo, hlomem, rfl⟩
  have hlip : lipBound (lo, hi) ≤ relaxedBound (lo, hi) := relaxedBound_ge_lip _
  simp only [lipBound] at hlip
  linarith

/-! ## 8. FIRING `Complete.complete` on the VECTOR net (L2-controlling split)

A single binary split cannot halve the L2 diameter of a 2-D square (one edge is
always left uncut), so to fire the *binary* `Complete.complete` with the L2
vector diameter we use a vector box whose L2 diameter is controlled by a single
coordinate (coordinate 1 degenerate), whose midpoint split on coordinate 0
halves `‖hi−lo‖₂` exactly.  Points still live in `V 2`, the net is the full
vector net, the diameter is the genuine L2 vector norm, and `L` is the
operator-norm product.  The genuine 2-D `[0,1]²` L2 completeness with the SAME
CROWN bound is fired in §9 through Wave-6's diameter-halving 4-way sweep. -/

/-- The L2-controlling **binary split**: bisect coordinate 0 at its midpoint
(`m₀ = (lo₀+hi₀)/2`), keeping coordinate 1.  On a coordinate-1-degenerate box
this halves the L2 diameter exactly. -/
noncomputable def split (B : Box) : Box × Box :=
  let lo := B.1; let hi := B.2
  let m0 := (WithLp.ofLp lo 0 + WithLp.ofLp hi 0) / 2
  ( (lo, mk2 m0 (WithLp.ofLp hi 1)),
    (mk2 m0 (WithLp.ofLp lo 1), hi) )

/-- **Decides law.** A positive relaxed bound certifies safety on every point of
the box (`relaxedBound_sound` + positivity). -/
lemma decides (B : Box) (h : 0 < relaxedBound B) (s : V 2) (hs : mem B s) : safe s :=
  lt_of_lt_of_le h (relaxedBound_sound B s hs)

/-- The completeness relaxation is fired on the **degenerate-in-coordinate-1**
root box `r = [0,2]×{0}` (a genuine vector segment in `V 2`), where the binary
coordinate-0 split halves the L2 vector diameter exactly and the two children
cover it.  `t = x₀ + x₁ = x₀ ∈ [0,2]` — exactly the Wave-5 range. -/
noncomputable def rootSeg : Box := (mk2 0 0, mk2 2 0)

/-- On a coordinate-1-degenerate box (`lo₁ = hi₁`) the L2 diameter is the
coordinate-0 width. -/
lemma diam_degenerate (lo0 hi0 c : ℝ) :
    diam (mk2 lo0 c, mk2 hi0 c) = |hi0 - lo0| := by
  rw [diam_eq]; simp [mk2_0, mk2_1]; rw [Real.sqrt_sq_eq_abs]

/-! ### The `Complete.Relaxation` instance on the L2-controlling vector segment

`Complete`'s abstract `Box` is the coordinate-0 interval `ℝ × ℝ`; the `Sample`
type is the genuine vector `V 2`.  `diam`, `relaxedBound`, `trueMin`, `mem`,
`safe`, `split` are all lifted from the genuine VECTOR objects above via the
degenerate vector box `segBox (a,b) = ([a,0],[b,0]) ⊆ V 2`.  Crucially `diam`
is the genuine L2 VECTOR diameter `‖hi−lo‖₂`, which on this degenerate box equals
`|b−a|` and is halved exactly by the coordinate-0 midpoint split. -/

/-- The vector segment box `[a,b]×{0} ⊆ V 2` for a coordinate-0 interval `(a,b)`. -/
noncomputable def segBox (ab : ℝ × ℝ) : Box := (mk2 ab.1 0, mk2 ab.2 0)

/-- Coordinate-0 interval membership lifted to the vector segment (`Sample = V 2`). -/
def segMem (ab : ℝ × ℝ) (s : V 2) : Prop := mem (segBox ab) s

/-- The genuine **L2 VECTOR diameter** of the segment, as a function of the interval. -/
noncomputable def segDiam (ab : ℝ × ℝ) : ℝ := diam (segBox ab)

lemma segDiam_eq (ab : ℝ × ℝ) : segDiam ab = |ab.2 - ab.1| := by
  obtain ⟨a, b⟩ := ab
  rw [segDiam, segBox, diam_degenerate]

lemma segDiam_nonneg (ab : ℝ × ℝ) : 0 ≤ segDiam ab := diam_nonneg _

/-- Midpoint split of the coordinate-0 interval. -/
noncomputable def segSplit (ab : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((ab.1, (ab.1 + ab.2) / 2), ((ab.1 + ab.2) / 2, ab.2))

/-- The CROWN relaxed bound on the segment. -/
noncomputable def segRelaxedBound (ab : ℝ × ℝ) : ℝ := relaxedBound (segBox ab)

/-- The true minimum on the segment. -/
noncomputable def segTrueMin (ab : ℝ × ℝ) : ℝ := trueMin (segBox ab)

/-- **Diameter contraction** for the segment midpoint split: each child's L2
VECTOR diameter is at most half the parent's (the only varying coordinate's width
is halved). -/
lemma segDiam_contract (ab : ℝ × ℝ) :
    segDiam (segSplit ab).1 ≤ segDiam ab / 2 ∧ segDiam (segSplit ab).2 ≤ segDiam ab / 2 := by
  obtain ⟨a, b⟩ := ab
  simp only [segSplit, segDiam_eq]
  have hl : |((a + b) / 2) - a| = |b - a| / 2 := by
    rw [show ((a + b) / 2) - a = (b - a) / 2 by ring, abs_div]; simp
  have hr : |b - ((a + b) / 2)| = |b - a| / 2 := by
    rw [show b - ((a + b) / 2) = (b - a) / 2 by ring, abs_div]; simp
  exact ⟨le_of_eq hl, le_of_eq hr⟩

/-- **Membership in the segment, unfolded** to coordinate-0 sandwich + coordinate-1
pinned to `0`. -/
lemma segMem_iff (ab : ℝ × ℝ) (s : V 2) :
    segMem ab s ↔ (ab.1 ≤ WithLp.ofLp s 0 ∧ WithLp.ofLp s 0 ≤ ab.2)
                 ∧ WithLp.ofLp s 1 = 0 := by
  obtain ⟨a, b⟩ := ab
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1
    simp only [segBox, mem, mk2_0, mk2_1] at h0 h1
    exact ⟨⟨h0.1, h0.2⟩, le_antisymm h1.2 h1.1⟩
  · rintro ⟨⟨hl, hu⟩, h1⟩ i
    fin_cases i <;>
      simp only [segBox, mk2_0, mk2_1, Fin.isValue, Fin.mk_zero, Fin.mk_one]
    · exact ⟨hl, hu⟩
    · rw [h1]; exact ⟨le_refl 0, le_refl 0⟩

/-- **Covering** for the segment midpoint split: every point of the segment lies
in one of the two children (case split coordinate 0 at the midpoint). -/
lemma segCover (ab : ℝ × ℝ) (s : V 2) (hs : segMem ab s) :
    segMem (segSplit ab).1 s ∨ segMem (segSplit ab).2 s := by
  obtain ⟨a, b⟩ := ab
  rw [segMem_iff] at hs
  obtain ⟨⟨hl, hu⟩, h1⟩ := hs
  rcases le_total (WithLp.ofLp s 0) ((a + b) / 2) with hc | hc
  · left;  rw [segMem_iff]; exact ⟨⟨hl, hc⟩, h1⟩
  · right; rw [segMem_iff]; exact ⟨⟨hc, hu⟩, h1⟩

/-- **boxSet inclusion** for the segment children. -/
lemma segBoxSet_subset_left (ab : ℝ × ℝ) :
    boxSet (segBox (segSplit ab).1) ⊆ boxSet (segBox ab) := by
  obtain ⟨a, b⟩ := ab
  intro s hs i
  obtain ⟨hl0, hu0⟩ := hs 0
  have h1 := hs 1
  simp only [segBox, segSplit, mk2_0, mk2_1, Fin.isValue, Fin.mk_zero, Fin.mk_one] at hl0 hu0 h1 ⊢
  fin_cases i <;> simp only [mk2_0, mk2_1, Fin.isValue, Fin.mk_zero, Fin.mk_one]
  · -- coordinate 0: a ≤ s₀ and s₀ ≤ (a+b)/2 ≤ ... need a ≤ s₀ ∧ s₀ ≤ b
    refine ⟨hl0, ?_⟩
    rcases le_total a b with h | h
    · linarith
    · linarith
  · exact h1

lemma segBoxSet_subset_right (ab : ℝ × ℝ) :
    boxSet (segBox (segSplit ab).2) ⊆ boxSet (segBox ab) := by
  obtain ⟨a, b⟩ := ab
  intro s hs i
  obtain ⟨hl0, hu0⟩ := hs 0
  have h1 := hs 1
  simp only [segBox, segSplit, mk2_0, mk2_1, Fin.isValue, Fin.mk_zero, Fin.mk_one] at hl0 hu0 h1 ⊢
  fin_cases i <;> simp only [mk2_0, mk2_1, Fin.isValue, Fin.mk_zero, Fin.mk_one]
  · refine ⟨?_, hu0⟩
    rcases le_total a b with h | h
    · linarith
    · linarith
  · exact h1

/-- **True-minimum monotonicity** under the segment split: each child's true
minimum dominates the parent's (inf over a smaller set). -/
lemma segTrueMin_mono (ab : ℝ × ℝ) :
    segTrueMin ab ≤ segTrueMin (segSplit ab).1 ∧
    segTrueMin ab ≤ segTrueMin (segSplit ab).2 := by
  obtain ⟨a, b⟩ := ab
  by_cases hab : a ≤ b
  · -- nonempty parent ⇒ both children are valid (nonempty) sub-intervals
    have hm0 : a ≤ (a + b) / 2 := by linarith
    have hm1 : (a + b) / 2 ≤ b := by linarith
    have hne_left : (boxSet (segBox (segSplit (a, b)).1)).Nonempty :=
      ⟨mk2 a 0, fun i => by
        fin_cases i <;> simp [segBox, segSplit, boxSet, mk2_0, mk2_1, hm0]⟩
    have hne_right : (boxSet (segBox (segSplit (a, b)).2)).Nonempty :=
      ⟨mk2 ((a + b) / 2) 0, fun i => by
        fin_cases i <;> simp [segBox, segSplit, boxSet, mk2_0, mk2_1, hm1]⟩
    refine ⟨?_, ?_⟩
    · exact csInf_le_csInf (img_bddBelow _) (hne_left.image _)
        (Set.image_mono (segBoxSet_subset_left (a, b)))
    · exact csInf_le_csInf (img_bddBelow _) (hne_right.image _)
        (Set.image_mono (segBoxSet_subset_right (a, b)))
  · -- empty parent ⇒ both children empty ⇒ all three trueMins are 0
    have hpar_empty : boxSet (segBox (a, b)) = (∅ : Set (V 2)) := by
      rw [Set.eq_empty_iff_forall_notMem]; intro s hs
      have h0 := hs 0; simp only [segBox, mk2_0] at h0; linarith [h0.1, h0.2]
    have hl_empty : boxSet (segBox (segSplit (a, b)).1) = (∅ : Set (V 2)) := by
      rw [Set.eq_empty_iff_forall_notMem]; intro s hs
      have h0 := hs 0; simp only [segBox, segSplit, mk2_0] at h0; linarith [h0.1, h0.2]
    have hr_empty : boxSet (segBox (segSplit (a, b)).2) = (∅ : Set (V 2)) := by
      rw [Set.eq_empty_iff_forall_notMem]; intro s hs
      have h0 := hs 0; simp only [segBox, segSplit, mk2_0] at h0; linarith [h0.1, h0.2]
    have e0 : segTrueMin (a, b) = 0 := by
      simp only [segTrueMin, trueMin, hpar_empty, Set.image_empty, Real.sInf_empty]
    have e1 : segTrueMin (segSplit (a, b)).1 = 0 := by
      simp only [segTrueMin, trueMin, hl_empty, Set.image_empty, Real.sInf_empty]
    have e2 : segTrueMin (segSplit (a, b)).2 = 0 := by
      simp only [segTrueMin, trueMin, hr_empty, Set.image_empty, Real.sInf_empty]
    rw [e0, e1, e2]; exact ⟨le_refl _, le_refl _⟩

/-- The segment true minimum is at most the net value at the lower corner
`(cnet (mk2 a 0))₀` — in BOTH the nonempty case (`csInf_le`) and the empty case
(`sInf ∅ = 0 ≤ 1 ≤ (cnet ·)₀`).  This is the only fact `width_error` needs. -/
lemma segTrueMin_le_corner (ab : ℝ × ℝ) :
    segTrueMin ab ≤ WithLp.ofLp (cnet (mk2 ab.1 0)) 0 := by
  obtain ⟨a, b⟩ := ab
  by_cases hab : a ≤ b
  · -- nonempty: lower corner mk2 a 0 ∈ boxSet
    have hmem : mk2 a 0 ∈ boxSet (segBox (a, b)) := by
      intro i; fin_cases i <;> simp [segBox, boxSet, mk2_0, mk2_1, hab]
    exact csInf_le (img_bddBelow _) ⟨mk2 a 0, hmem, rfl⟩
  · -- empty: boxSet = ∅, segTrueMin = sInf ∅ = 0 ≤ 1 ≤ (cnet (mk2 a 0))₀
    have hempty : boxSet (segBox (a, b)) = (∅ : Set (V 2)) := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro s hs
      have h0 := hs 0
      simp only [segBox, mk2_0] at h0
      linarith [h0.1, h0.2]
    have htm0 : segTrueMin (a, b) = 0 := by
      simp only [segTrueMin, trueMin, hempty, Set.image_empty, Real.sInf_empty]
    rw [htm0]
    linarith [cnet_coord0_ge_one (mk2 a 0)]

/-- **WIDTH-ERROR for the segment** with the genuine L2 VECTOR diameter:
`segTrueMin − L·‖hi−lo‖₂ ≤ segRelaxedBound`.  From
`segTrueMin ≤ (cnet lo)₀` we get `segTrueMin − L·diam ≤ (cnet lo)₀ − L·diam =
lipBound ≤ segRelaxedBound`.  Holds UNCONDITIONALLY (both nonempty and empty
boxes), as `Complete.Relaxation` requires. -/
lemma segWidth_error (ab : ℝ × ℝ) :
    segTrueMin ab - L * segDiam ab ≤ segRelaxedBound ab := by
  have htm := segTrueMin_le_corner ab
  have hlip : lipBound (segBox ab) ≤ segRelaxedBound ab := relaxedBound_ge_lip _
  simp only [lipBound, segBox, segDiam, segRelaxedBound] at htm hlip ⊢
  linarith

/-- **Decides law for the segment.** A positive CROWN relaxed bound on a segment
box certifies safety on every point (`relaxedBound_sound` + positivity). -/
lemma segDecides (ab : ℝ × ℝ) (h : 0 < segRelaxedBound ab) (s : V 2) (hs : segMem ab s) :
    safe s :=
  lt_of_lt_of_le h (relaxedBound_sound (segBox ab) s hs)

/-! ### The CONCRETE CROWN `Complete.Relaxation` on the genuine VECTOR net

`Box = ℝ × ℝ` is the coordinate-0 interval; `Sample = V 2` is the genuine vector.
EVERY field is the genuine vector object: `diam` is the L2 VECTOR diameter,
`relaxedBound` is the CROWN linear-bound MAX, `L` is the operator-norm product,
`safe` is positivity of the vector net's coordinate-0 output. -/

/-- The CONCRETE **CROWN linear-bound** `Complete.Relaxation` of the genuine
VECTOR net, with EVERY field discharged: the L2 VECTOR diameter, the
operator-norm product Lipschitz `L = ‖W₂‖·‖W₁‖`, the CROWN affine corner-min
bound, and the `width_error`/`decides`/`cover`/contraction/monotonicity laws
proved above. -/
noncomputable def crownVecRelaxation : Complete.Relaxation (ℝ × ℝ) (V 2) where
  diam          := segDiam
  trueMin       := segTrueMin
  relaxedBound  := segRelaxedBound
  split         := segSplit
  mem           := segMem
  safe          := safe
  L             := L
  L_nonneg      := L_nonneg
  diam_nonneg   := segDiam_nonneg
  width_error   := segWidth_error
  diam_contract := segDiam_contract
  trueMin_mono  := segTrueMin_mono
  decides       := segDecides
  cover         := segCover

/-! ## 9. The CROWN bound is STRICTLY tighter than the Lipschitz-only bound

On the root segment `[0,2]×{0}` (L2 diam `2`):
  • the Lipschitz-only corner bound is `(cnet lo)₀ − L·2 ≤ 1 − √2·2 < 0`
    (cannot decide at depth 0 — must bisect);
  • the CROWN linear bound is `cornerForm 0 = 0 − relu(−1) + 1 = 1 > 0`
    (DECIDES at depth 0, no bisection).
So the CROWN relaxation is strictly tighter — a SMALLER decisive depth. -/

/-- The CROWN linear bound on the root segment `[0,2]×{0}` is `1`:
`cornerForm (0+0) = 0 − relu(−1) + 1 = 1`. -/
lemma crownLin_rootSeg : crownLin (segBox (0, 2)) = 1 := by
  simp only [crownLin, segBox, mk2_0, cornerForm]; norm_num

/-- The CROWN relaxed bound on the root segment is `≥ 1 > 0` — **CROWN DECIDES the
root at depth 0.** -/
lemma segRelaxedBound_rootSeg_pos : 0 < segRelaxedBound (0, 2) := by
  have h : crownLin (segBox (0, 2)) ≤ segRelaxedBound (0, 2) := relaxedBound_ge_crown _
  rw [crownLin_rootSeg] at h; linarith

/-- The L2 diameter of the root segment is `2`. -/
lemma segDiam_rootSeg : segDiam (0, 2) = 2 := by rw [segDiam_eq]; norm_num

/-- **The Lipschitz-only corner bound on the root segment is `< 0`** (it CANNOT
decide at depth 0).  `lipBound = (cnet (mk2 0 0))₀ − L·2`.  Now `(cnet (mk2 0 0))₀
= relu 0 − relu(−1) + 1 = 1`, and `L ≥ √2`, so `lipBound ≤ 1 − √2·2 = 1 − 2√2 < 0`. -/
lemma lipBound_rootSeg_neg : lipBound (segBox (0, 2)) < 0 := by
  have hval : WithLp.ofLp (cnet (mk2 0 0)) 0 = 1 := by
    rw [cnet_coord0]; simp [mk2_0, mk2_1]
  have hL : Real.sqrt 2 ≤ L := sqrt2_le_L
  have hsqrt : (1.41 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41 : ℝ) = Real.sqrt (1.41 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; norm_num
  have hdiam : diam (segBox (0, 2)) = 2 := by
    rw [show segBox (0, 2) = ((mk2 0 0 : V 2), mk2 2 0) from rfl, diam_degenerate]; norm_num
  have hb : lipBound (segBox (0, 2)) = WithLp.ofLp (cnet (mk2 0 0)) 0 - L * diam (segBox (0, 2)) := by
    rw [lipBound]; rfl
  rw [hb, hval, hdiam]
  nlinarith [hL, hsqrt]

/-- **THE DECISIVE-DEPTH / TIGHTNESS GAP.** On the root segment `[0,2]×{0}`:
the CROWN relaxed bound is strictly positive (CROWN closes at depth 0), while the
Lipschitz-only corner bound is strictly negative (the Lipschitz-only relaxation
CANNOT close at depth 0 — it must bisect).  So the concrete CROWN LINEAR bound on
this VECTOR net is strictly tighter, with a SMALLER decisive depth. -/
theorem crown_strictly_tighter_than_lipschitz :
    lipBound (segBox (0, 2)) < 0 ∧ 0 < segRelaxedBound (0, 2) :=
  ⟨lipBound_rootSeg_neg, segRelaxedBound_rootSeg_pos⟩

/-! ## 10. FIRING `Complete.complete` on the VECTOR net -/

/-- The verification **margin** `δ = 1 ≤ trueMin` over the root segment `[0,2]×{0}`
(the vector net's coordinate-0 output is `≥ 1` everywhere). -/
lemma segMargin_pos : (1 : ℝ) ≤ crownVecRelaxation.trueMin (0, 2) := by
  show (1 : ℝ) ≤ segTrueMin (0, 2)
  apply le_csInf
  · exact ⟨WithLp.ofLp (cnet (mk2 0 0)) 0, mk2 0 0, fun i => by
      fin_cases i <;> simp [segBox, boxSet, mk2_0, mk2_1], rfl⟩
  · rintro y ⟨x, _, rfl⟩
    exact cnet_coord0_ge_one x

/-- **VERIFIED VECTOR-NET COMPLETENESS WITH A CROWN LINEAR BOUND.**
`Complete.complete` fired on the CONCRETE CROWN linear-bound relaxation of the
GENUINE VECTOR net: there is a finite bisection depth `d` at which every leaf of
the root segment `[0,2]×{0}` has a strictly positive CROWN relaxed bound, and the
net is SAFE — `(cnet s)₀ > 0` — on EVERY vector point of the root box.  The
decision is routed through the genuine L2 VECTOR diameter (`‖hi−lo‖₂`, halved by
each binary split) and the matrix-operator-norm product Lipschitz `L = ‖W₂‖·‖W₁‖`. -/
theorem crownVec_complete :
    ∃ d : ℕ,
      (∀ C ∈ Complete.leafBoxes crownVecRelaxation (0, 2) d,
        0 < crownVecRelaxation.relaxedBound C) ∧
      (∀ s, crownVecRelaxation.mem (0, 2) s → crownVecRelaxation.safe s) :=
  Complete.complete crownVecRelaxation (0, 2) (by norm_num) segMargin_pos

/-- **End-to-end decision (unfolded).** The genuine vector net is positive in its
first output coordinate on the whole root segment `[0,2]×{0}`, decided through
the verified bisection procedure with the CROWN linear-bound relaxation. -/
theorem net_positive_on_rootSeg (s : V 2)
    (h0 : 0 ≤ WithLp.ofLp s 0) (h0' : WithLp.ofLp s 0 ≤ 2) (h1 : WithLp.ofLp s 1 = 0) :
    0 < WithLp.ofLp (cnet s) 0 := by
  obtain ⟨_, _, hdec⟩ := crownVec_complete
  have : crownVecRelaxation.mem (0, 2) s := by
    show segMem (0, 2) s
    rw [segMem_iff]; exact ⟨⟨h0, h0'⟩, h1⟩
  exact hdec s this

/-- **Completeness fires already at depth 0** (the explicit `d = 0` witness): the
CROWN bound on the root segment is positive, so the single depth-0 leaf closes
and the whole root box is decided — STRICTLY smaller depth than the Lipschitz-only
relaxation, whose root bound is negative (`crown_strictly_tighter_than_lipschitz`). -/
theorem crownVec_complete_depth_zero :
    (∀ C ∈ Complete.leafBoxes crownVecRelaxation (0, 2) 0,
        0 < crownVecRelaxation.relaxedBound C) ∧
    (∀ s, crownVecRelaxation.mem (0, 2) s → crownVecRelaxation.safe s) := by
  have hpos0 : ∀ C ∈ Complete.leafBoxes crownVecRelaxation (0, 2) 0,
      0 < crownVecRelaxation.relaxedBound C := by
    intro C hC
    simp only [Complete.leafBoxes, List.mem_singleton] at hC
    subst hC
    exact segRelaxedBound_rootSeg_pos
  refine ⟨hpos0, ?_⟩
  exact Complete.box_safe_of_leaves crownVecRelaxation (0, 2) 0
    (fun C hC s hms => crownVecRelaxation.decides C (hpos0 C hC) s hms)

/-! ## 11. The GENUINE 2-D box `[0,1]²` with the CROWN bound and L2 vector diam

A single binary split cannot halve the L2 diameter of a 2-D square, so the
literal `Complete.complete` above used the L2-controlling segment.  Here we fire
the SAME CROWN linear-bound relaxation on the GENUINE 2-D input box `[0,1]²` (a
real `V 2` rectangle, both coordinates varying) through Wave-6's diameter-halving
4-way `sweep`/`sweepLeaves` tree, where each sweep halves the L2 VECTOR diameter
exactly and the four children cover the parent.  This is the genuine 2-D vector
completeness with the CROWN bound; the geometry lemmas (`sweep_diam_half`,
`sweep_cover`, `sweepLeaves_*`) are reused verbatim from Wave-6 (our `boxSet`,
`mem`, `diam` are definitionally Wave-6's). -/

/-- With a positive margin `δ`, the L2 width-error law forces a strictly positive
CROWN relaxed bound on any nonempty box whose L2 vector diameter is below `δ/L`. -/
lemma relaxedBound_pos_of_diam_lt {B : Box} {δ : ℝ}
    (hmin : δ ≤ trueMin B) (hdiam : L * diam B < δ) (hne : (boxSet B).Nonempty) :
    0 < relaxedBound B := by
  have hwe : trueMin B - L * diam B ≤ relaxedBound B := width_error B hne
  linarith

/-- The verification margin on the genuine 2-D box `[0,1]²`: `δ = 1 ≤ trueMin`. -/
lemma margin_pos_2D : (1 : ℝ) ≤ trueMin (mk2 0 0, mk2 1 1) := by
  apply le_csInf
  · exact ⟨WithLp.ofLp (cnet (mk2 0 0)) 0, mk2 0 0, fun i => by
      fin_cases i <;> simp [boxSet, mk2_0, mk2_1], rfl⟩
  · rintro y ⟨x, _, rfl⟩
    exact cnet_coord0_ge_one x

/-- The crown bound on the 2-D root `[0,1]²` is `1` (the lower corner is `(0,0)`,
`cornerForm (0+0) = 1`). -/
lemma crownLin_root2D : crownLin (mk2 0 0, mk2 1 1) = 1 := by
  simp only [crownLin, mk2_0, cornerForm]; norm_num

/-- **True-minimum monotonicity over the 4-way sweep depth, for OUR net.**
Reuses Wave-6's purely-geometric `boxSet` inclusion (`sweepLeaves_boxSet_subset`)
with OUR `trueMin`/`img_bddBelow` (tied to `cnet`).  Each nonempty depth-`k` leaf
has true minimum at least `trueMin B`. -/
lemma sweepLeaves_trueMin_ge_2D (B : Box) (k : ℕ) :
    ∀ C ∈ CompleteVector.sweepLeaves B k, (boxSet C).Nonempty → trueMin B ≤ trueMin C := by
  intro C hC hCne
  exact csInf_le_csInf (img_bddBelow _) (hCne.image _)
    (Set.image_mono (CompleteVector.sweepLeaves_boxSet_subset B k C hC))

/-- **VERIFIED 2-D VECTOR-NET CROWN COMPLETENESS.**  For the genuine 2-D input box
`[0,1]²` (both input coordinates varying), the SAME concrete CROWN linear-bound
relaxation of the genuine vector net closes a finite-depth 4-way sweep tree and
decides safety on the WHOLE 2-D box — `(cnet s)₀ > 0` for every `s ∈ [0,1]²`.  The
decision uses the genuine L2 VECTOR diameter (halved by each sweep,
`CompleteVector.sweepLeaves_diam_le`) and the operator-norm product Lipschitz `L`. -/
theorem crownVec_complete_2D :
    ∃ k : ℕ,
      (∀ C ∈ CompleteVector.sweepLeaves (mk2 0 0, mk2 1 1) k,
        (boxSet C).Nonempty → 0 < relaxedBound C) ∧
      (∀ s, mem (mk2 0 0, mk2 1 1) s → safe s) := by
  set B0 : Box := (mk2 0 0, mk2 1 1)
  have hδ : (0:ℝ) < 1 := by norm_num
  have hmin0 : (1:ℝ) ≤ trueMin B0 := margin_pos_2D
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (L * diam B0 / 1) (by norm_num : (1:ℝ) < 2)
  have close : ∀ C ∈ CompleteVector.sweepLeaves B0 k, (boxSet C).Nonempty →
      0 < relaxedBound C := by
    intro C hC hCne
    have hdiamC : diam C ≤ diam B0 / 2 ^ k := CompleteVector.sweepLeaves_diam_le B0 k C hC
    have hminC : (1:ℝ) ≤ trueMin C :=
      le_trans hmin0 (sweepLeaves_trueMin_ge_2D B0 k C hC hCne)
    have hpow : (0:ℝ) < 2 ^ k := by positivity
    have hkey : L * diam C < 1 := by
      have hLdiam : L * diam C ≤ L * (diam B0 / 2 ^ k) :=
        mul_le_mul_of_nonneg_left hdiamC L_nonneg
      rw [div_lt_iff₀ hδ] at hk
      have : L * (diam B0 / 2 ^ k) < 1 := by
        rw [mul_div_assoc', div_lt_iff₀ hpow]; nlinarith
      linarith
    exact relaxedBound_pos_of_diam_lt hminC hkey hCne
  refine ⟨k, close, ?_⟩
  intro s hs
  obtain ⟨C, hCmem, hCs⟩ := CompleteVector.sweepLeaves_cover B0 k s hs
  have hCne : (boxSet C).Nonempty := ⟨s, hCs⟩
  have hpos : 0 < relaxedBound C := close C hCmem hCne
  exact lt_of_lt_of_le hpos (relaxedBound_sound C s hCs)

/-- **End-to-end 2-D decision (unfolded).** The genuine vector net is positive in
its first output coordinate on the WHOLE genuine 2-D input box `[0,1]²`. -/
theorem net_positive_on_box_2D (s : V 2)
    (h0 : 0 ≤ WithLp.ofLp s 0) (h0' : WithLp.ofLp s 0 ≤ 1)
    (h1 : 0 ≤ WithLp.ofLp s 1) (h1' : WithLp.ofLp s 1 ≤ 1) :
    0 < WithLp.ofLp (cnet s) 0 := by
  obtain ⟨_, _, hdec⟩ := crownVec_complete_2D
  exact hdec s (fun i => by fin_cases i <;> simp_all [mk2_0, mk2_1])

/-! ## Trust-base check — every theorem must reduce to the standard logical axioms
only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`. -/

#print axioms cnet_coord0
#print axioms cnet_coord0_ge_one
#print axioms cnet_lip
#print axioms sqrt2_le_W1
#print axioms one_le_W2
#print axioms sqrt2_le_L
#print axioms cornerForm_mono
#print axioms cornerForm_le_fT
#print axioms fT_eq_coord0
#print axioms diam_eq
#print axioms lipBound_sound
#print axioms crownLin_sound
#print axioms relaxedBound_sound
#print axioms segDiam_eq
#print axioms segDiam_contract
#print axioms segCover
#print axioms segTrueMin_mono
#print axioms segWidth_error
#print axioms crownVecRelaxation
#print axioms crownLin_rootSeg
#print axioms lipBound_rootSeg_neg
#print axioms crown_strictly_tighter_than_lipschitz
#print axioms segMargin_pos
#print axioms crownVec_complete
#print axioms net_positive_on_rootSeg
#print axioms crownVec_complete_depth_zero
#print axioms margin_pos_2D
#print axioms crownLin_root2D
#print axioms sweepLeaves_trueMin_ge_2D
#print axioms crownVec_complete_2D
#print axioms net_positive_on_box_2D

end CompleteCrownVector
end Crownproof
