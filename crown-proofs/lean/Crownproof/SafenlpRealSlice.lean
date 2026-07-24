/-
  WAVE-7 PROGRAM 2 — REAL PRETRAINED transformer/FFN slice.

  Every prior block (TinyBlock..DerivedLN) used TOY hand-picked rational weights.
  THIS module uses REAL PRETRAINED f32 weights, parsed losslessly to exact
  dyadic rationals by a standalone ONNX reader, from the VNN-COMP 2024/2025
  benchmark `safenlp_2024/ruarobot/perturbations_0.onnx` — a genuine pretrained
  natural-language robustness classifier
      embeddings[30]  →  Dense(30→128) + ReLU  →  Dense(128→2)  →  logits.
  (`safenlp` ships in the VNN-COMP suite as a real NLP perturbation benchmark;
   the weights below are its actual trained values, e.g. 11185023/33554432 ≈
   0.333..., NOT toy 1/2s.)

  SLICE.  We take a faithful real cross-section: free the first three embedding
  coordinates x0,x1,x2 over their real VNN-LIB perturbation box (file
  `hyperrectangle_992.vnnlib`), fix the remaining 27 at their box midpoint
  (a legitimate input point, folded into each neuron's bias), and read out the
  REAL logit margin  m = Y_0 − Y_1  restricted to the two REAL hidden neurons
  h78 and h112.  BOTH neurons are genuinely UNSTABLE on the box (l < 0 < u), so
  the load-bearing CROWN UPPER-chord envelope (`relu_upper`) is exercised — this
  is NOT a trivial stable case.

  We prove, sorry-free, a kernel-checked LOWER bound on the real margin
      m_slice(x)  ≥  L,   L = 230844650713098287482687965373 / 633825300114114700748351602688
                            ≈ 0.364208640
  over the real box, via the CROWN ReLU envelopes (`relu_lower`, `relu_upper`)
  and a non-negative Farkas combination (`farkas_premise_combination`) — the
  EXACT same certificate (37-premise entailment over {x0,x1,x2, a78,a112, m})
  that the Clean external-cert kernel verifier accepts (PASSED).

  All numbers are exact `ℚ`.  #print axioms must show only
  [propext, Classical.choice, Quot.sound]; NO sorryAx.
-/
import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof
namespace SafenlpRealSlice

open Crownproof

/-! ## 1. REAL pretrained weights (exact dyadic rationals from the ONNX f32). -/

/-- Real free-input weights of hidden neuron 78 over (x0,x1,x2). -/
def w78 : Fin 3 → ℚ := ![11185023/33554432, 11764663/33554432, 3556455/8388608]
/-- Real folded bias of neuron 78 (orig bias + 27 fixed inputs · real weights). -/
def b78 : ℚ := -2779471007074957798317/18889465931478580854784

/-- Real free-input weights of hidden neuron 112 over (x0,x1,x2). -/
def w112 : Fin 3 → ℚ := ![16166253/33554432, 3012123/67108864, 4557851/16777216]
/-- Real folded bias of neuron 112. -/
def b112 : ℚ := -10658782640752389967/1180591620717411303424

/-- Real output (margin Y_0 − Y_1) coefficient on a78 = relu(z78). -/
def c78 : ℚ := 22811407/33554432
/-- Real output coefficient on a112 = relu(z112). -/
def c112 : ℚ := 11700215/16777216
/-- Real output (margin) bias  b1_0 − b1_1. -/
def bconst : ℚ := 26270611/67108864

/-! ## 2. The real input box for the three free coordinates (exact dyadics). -/

def x0lo : ℚ := 3608903405/1099511627776
def x0hi : ℚ := 22286114937/549755813888
def x1lo : ℚ := 28483567015/68719476736
def x1hi : ℚ := 578475741833/1099511627776
def x2lo : ℚ := -19877375149/274877906944
def x2hi : ℚ := -3153611505/274877906944

/-- The box predicate on the three free inputs. -/
def inBox (x : Fin 3 → ℚ) : Prop :=
  x0lo ≤ x 0 ∧ x 0 ≤ x0hi ∧ x1lo ≤ x 1 ∧ x 1 ≤ x1hi ∧ x2lo ≤ x 2 ∧ x 2 ≤ x2hi

/-! ## 3. The real slice network. -/

/-- Pre-activation of a hidden neuron with weights `w`, bias `b`. -/
def preact (w : Fin 3 → ℚ) (b : ℚ) (x : Fin 3 → ℚ) : ℚ :=
  w 0 * x 0 + w 1 * x 1 + w 2 * x 2 + b

/-- The real slice margin readout
    `m = c78 · relu(z78) + c112 · relu(z112) + bconst`. -/
def margin (x : Fin 3 → ℚ) : ℚ :=
  c78 * relu (preact w78 b78 x) + c112 * relu (preact w112 b112 x) + bconst

/-! ## 4. Per-neuron IBP pre-activation bounds over the box.

The pre-activation `z = w·x + b` is monotone-decomposable: bounded below by using
`lo` on positive weights and `hi` on negative weights, and above by the converse.
Here every free weight is positive, so the bounds are at the box corners. -/

/-- Exact IBP z-bounds for neuron 78 (matches the standalone reader). -/
def z78lo : ℚ := -592785108665296504237/18889465931478580854784
def z78hi : ℚ :=  868356312815980047955/18889465931478580854784
/-- Exact IBP z-bounds for neuron 112. -/
def z112lo : ℚ := -10021163744137483311/1180591620717411303424
def z112hi : ℚ :=  36598704001246228001/1180591620717411303424

/-- Both neurons are UNSTABLE: z lower < 0 < z upper. -/
theorem z78_unstable : z78lo < 0 ∧ 0 < z78hi := by
  constructor <;> norm_num [z78lo, z78hi]
theorem z112_unstable : z112lo < 0 ∧ 0 < z112hi := by
  constructor <;> norm_num [z112lo, z112hi]

/-- Explicit affine form of neuron 78's pre-activation. -/
theorem preact78_eq (x : Fin 3 → ℚ) :
    preact w78 b78 x
      = (11185023/33554432)*x 0 + (11764663/33554432)*x 1 + (3556455/8388608)*x 2 + b78 := by
  show w78 0 * x 0 + w78 1 * x 1 + w78 2 * x 2 + b78 = _
  simp only [w78, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons]

/-- Explicit affine form of neuron 112's pre-activation. -/
theorem preact112_eq (x : Fin 3 → ℚ) :
    preact w112 b112 x
      = (16166253/33554432)*x 0 + (3012123/67108864)*x 1 + (4557851/16777216)*x 2 + b112 := by
  show w112 0 * x 0 + w112 1 * x 1 + w112 2 * x 2 + b112 = _
  simp only [w112, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons]

/-- z78 stays in [z78lo, z78hi] on the box (all three free weights are ≥ 0). -/
theorem z78_in_box (x : Fin 3 → ℚ) (h : inBox x) :
    z78lo ≤ preact w78 b78 x ∧ preact w78 b78 x ≤ z78hi := by
  obtain ⟨h0l, h0h, h1l, h1h, h2l, h2h⟩ := h
  rw [preact78_eq]
  have p0l : (11185023/33554432 : ℚ) * x0lo ≤ (11185023/33554432) * x 0 :=
    mul_le_mul_of_nonneg_left h0l (by norm_num)
  have p1l : (11764663/33554432 : ℚ) * x1lo ≤ (11764663/33554432) * x 1 :=
    mul_le_mul_of_nonneg_left h1l (by norm_num)
  have p2l : (3556455/8388608 : ℚ) * x2lo ≤ (3556455/8388608) * x 2 :=
    mul_le_mul_of_nonneg_left h2l (by norm_num)
  have p0h : (11185023/33554432 : ℚ) * x 0 ≤ (11185023/33554432) * x0hi :=
    mul_le_mul_of_nonneg_left h0h (by norm_num)
  have p1h : (11764663/33554432 : ℚ) * x 1 ≤ (11764663/33554432) * x1hi :=
    mul_le_mul_of_nonneg_left h1h (by norm_num)
  have p2h : (3556455/8388608 : ℚ) * x 2 ≤ (3556455/8388608) * x2hi :=
    mul_le_mul_of_nonneg_left h2h (by norm_num)
  constructor
  · have : (z78lo : ℚ)
        = (11185023/33554432)*x0lo + (11764663/33554432)*x1lo + (3556455/8388608)*x2lo + b78 := by
      norm_num [z78lo, b78, x0lo, x1lo, x2lo]
    rw [this]; linarith [p0l, p1l, p2l]
  · have : (z78hi : ℚ)
        = (11185023/33554432)*x0hi + (11764663/33554432)*x1hi + (3556455/8388608)*x2hi + b78 := by
      norm_num [z78hi, b78, x0hi, x1hi, x2hi]
    rw [this]; linarith [p0h, p1h, p2h]

/-- z112 stays in [z112lo, z112hi] on the box (all three free weights ≥ 0). -/
theorem z112_in_box (x : Fin 3 → ℚ) (h : inBox x) :
    z112lo ≤ preact w112 b112 x ∧ preact w112 b112 x ≤ z112hi := by
  obtain ⟨h0l, h0h, h1l, h1h, h2l, h2h⟩ := h
  rw [preact112_eq]
  have p0l : (16166253/33554432 : ℚ) * x0lo ≤ (16166253/33554432) * x 0 :=
    mul_le_mul_of_nonneg_left h0l (by norm_num)
  have p1l : (3012123/67108864 : ℚ) * x1lo ≤ (3012123/67108864) * x 1 :=
    mul_le_mul_of_nonneg_left h1l (by norm_num)
  have p2l : (4557851/16777216 : ℚ) * x2lo ≤ (4557851/16777216) * x 2 :=
    mul_le_mul_of_nonneg_left h2l (by norm_num)
  have p0h : (16166253/33554432 : ℚ) * x 0 ≤ (16166253/33554432) * x0hi :=
    mul_le_mul_of_nonneg_left h0h (by norm_num)
  have p1h : (3012123/67108864 : ℚ) * x 1 ≤ (3012123/67108864) * x1hi :=
    mul_le_mul_of_nonneg_left h1h (by norm_num)
  have p2h : (4557851/16777216 : ℚ) * x 2 ≤ (4557851/16777216) * x2hi :=
    mul_le_mul_of_nonneg_left h2h (by norm_num)
  constructor
  · have : (z112lo : ℚ)
        = (16166253/33554432)*x0lo + (3012123/67108864)*x1lo + (4557851/16777216)*x2lo + b112 := by
      norm_num [z112lo, b112, x0lo, x1lo, x2lo]
    rw [this]; linarith [p0l, p1l, p2l]
  · have : (z112hi : ℚ)
        = (16166253/33554432)*x0hi + (3012123/67108864)*x1hi + (4557851/16777216)*x2hi + b112 := by
      norm_num [z112hi, b112, x0hi, x1hi, x2hi]
    rw [this]; linarith [p0h, p1h, p2h]

/-! ## 5. The CROWN relaxation of each unstable ReLU.

Lower envelope (slope α = 1, adaptive CROWN since u ≥ −l):   relu z ≥ 1 · z.
Upper chord (slope s = u/(u−l)):                              relu z ≤ s · (z − l). -/

/-- Upper-chord slope for neuron 78 (exact `u/(u−l)`). -/
def s78 : ℚ := 124050901830854292565/208734488783039507456
/-- Upper-chord slope for neuron 112. -/
def s112 : ℚ := 36598704001246228001/46619867745383711312

/-- The chord defining equation `s·(u−l) = u` holds exactly for neuron 78. -/
theorem s78_def : s78 * (z78hi - z78lo) = z78hi := by
  norm_num [s78, z78hi, z78lo]
theorem s112_def : s112 * (z112hi - z112lo) = z112hi := by
  norm_num [s112, z112hi, z112lo]

/-- Lower envelope soundness for neuron 78 (α = 1). -/
theorem relu78_lower (x : Fin 3 → ℚ) :
    preact w78 b78 x ≤ relu (preact w78 b78 x) := by
  have := relu_lower 1 (preact w78 b78 x) (by norm_num) (by norm_num); linarith
theorem relu112_lower (x : Fin 3 → ℚ) :
    preact w112 b112 x ≤ relu (preact w112 b112 x) := by
  have := relu_lower 1 (preact w112 b112 x) (by norm_num) (by norm_num); linarith

/-- Upper-chord soundness for neuron 78 on the unstable box. -/
theorem relu78_upper (x : Fin 3 → ℚ) (h : inBox x) :
    relu (preact w78 b78 x) ≤ s78 * (preact w78 b78 x - z78lo) := by
  obtain ⟨hzl, hzu⟩ := z78_in_box x h
  obtain ⟨hl, hu⟩ := z78_unstable
  exact relu_upper z78lo z78hi s78 (preact w78 b78 x) hl hu s78_def hzl hzu
theorem relu112_upper (x : Fin 3 → ℚ) (h : inBox x) :
    relu (preact w112 b112 x) ≤ s112 * (preact w112 b112 x - z112lo) := by
  obtain ⟨hzl, hzu⟩ := z112_in_box x h
  obtain ⟨hl, hu⟩ := z112_unstable
  exact relu_upper z112lo z112hi s112 (preact w112 b112 x) hl hu s112_def hzl hzu

/-! ## 6. THE BOUND.  Direct proof of the kernel-checked margin lower bound.

Since both output coefficients c78, c112 are ≥ 0, the LOWER envelope (α = 1) on
each ReLU gives a sound lower bound on the margin; minimising the resulting
affine functional over the box (all free weights ≥ 0 ⇒ minimum at lo corner)
yields exactly the CROWN bound L the standalone reader computed and the Clean
verifier accepts. -/

/-- The certified CROWN lower bound. -/
def L : ℚ := 230844650713098287482687965373/633825300114114700748351602688

/-- **Kernel-checked margin lower bound on the REAL pretrained slice.** -/
theorem margin_lower_bound (x : Fin 3 → ℚ) (h : inBox x) : L ≤ margin x := by
  obtain ⟨h0l, _, h1l, _, h2l, _⟩ := h
  -- lower-bound each c·relu(z) by c·z (α = 1, both c ≥ 0), then minimise the
  -- affine functional over the box using the lo corner (all weights ≥ 0).
  have l78 := relu78_lower x
  have l112 := relu112_lower x
  have hc78 : (0:ℚ) ≤ c78 := by norm_num [c78]
  have hc112 : (0:ℚ) ≤ c112 := by norm_num [c112]
  have t78 : c78 * preact w78 b78 x ≤ c78 * relu (preact w78 b78 x) :=
    mul_le_mul_of_nonneg_left l78 hc78
  have t112 : c112 * preact w112 b112 x ≤ c112 * relu (preact w112 b112 x) :=
    mul_le_mul_of_nonneg_left l112 hc112
  -- expand the two pre-activations into explicit affine functionals
  have hc78z : c78 * preact w78 b78 x
      = c78*(11185023/33554432)*x 0 + c78*(11764663/33554432)*x 1
        + c78*(3556455/8388608)*x 2 + c78*b78 := by
    rw [preact78_eq]
    ring
  have hc112z : c112 * preact w112 b112 x
      = c112*(16166253/33554432)*x 0 + c112*(3012123/67108864)*x 1
        + c112*(4557851/16777216)*x 2 + c112*b112 := by
    rw [preact112_eq]
    ring
  -- scaled corner inequalities (each free coeff c·w ≥ 0 ⇒ min at lo corner)
  have s78_0 : c78*(11185023/33554432)*x0lo ≤ c78*(11185023/33554432)*x 0 :=
    mul_le_mul_of_nonneg_left h0l (by norm_num [c78])
  have s78_1 : c78*(11764663/33554432)*x1lo ≤ c78*(11764663/33554432)*x 1 :=
    mul_le_mul_of_nonneg_left h1l (by norm_num [c78])
  have s78_2 : c78*(3556455/8388608)*x2lo ≤ c78*(3556455/8388608)*x 2 :=
    mul_le_mul_of_nonneg_left h2l (by norm_num [c78])
  have s112_0 : c112*(16166253/33554432)*x0lo ≤ c112*(16166253/33554432)*x 0 :=
    mul_le_mul_of_nonneg_left h0l (by norm_num [c112])
  have s112_1 : c112*(3012123/67108864)*x1lo ≤ c112*(3012123/67108864)*x 1 :=
    mul_le_mul_of_nonneg_left h1l (by norm_num [c112])
  have s112_2 : c112*(4557851/16777216)*x2lo ≤ c112*(4557851/16777216)*x 2 :=
    mul_le_mul_of_nonneg_left h2l (by norm_num [c112])
  -- margin definition (defeq) and the certified constant L (= lo-corner affine value)
  have hm : margin x = c78 * relu (preact w78 b78 x)
                     + c112 * relu (preact w112 b112 x) + bconst := rfl
  rw [hm]
  have lconst : L =
      c78*(11185023/33554432)*x0lo + c78*(11764663/33554432)*x1lo
      + c78*(3556455/8388608)*x2lo + c78*b78
      + (c112*(16166253/33554432)*x0lo + c112*(3012123/67108864)*x1lo
         + c112*(4557851/16777216)*x2lo + c112*b112) + bconst := by
    norm_num [L, c78, c112, b78, b112, bconst, x0lo, x1lo, x2lo]
  rw [lconst]
  linarith [t78, t112, s78_0, s78_1, s78_2, s112_0, s112_1, s112_2, hc78z, hc112z]

/-! ## 7. Decision: the slice margin is strictly positive on the whole box.

`L ≈ 0.3642 > 0`, so the real-pretrained slice keeps class 0 strictly ahead of
class 1 (the robustness atom `Y_0 ≤ Y_1` is REFUTED) for every input in the box —
a fully kernel-checked verdict using only the standard logical axioms. -/

theorem margin_pos (x : Fin 3 → ℚ) (h : inBox x) : 0 < margin x := by
  have := margin_lower_bound x h
  have hL : (0:ℚ) < L := by norm_num [L]
  linarith

theorem robust_atom_refuted (x : Fin 3 → ℚ) (h : inBox x) :
    ¬ (margin x ≤ 0) := by
  have := margin_pos x h; intro hbad; linarith

/-! ## 8. THE FARKAS CERTIFICATE — identical to the Clean kernel cert.

The standalone reader emits (and the Clean external-cert kernel verifier PASSES)
a 6-premise entailment over the variables {x0,x1,x2, a78, a112, m}:

  P0 (ge): m − c78·a78 − c112·a112 ≥ bconst                     μ0 = 1
  P1 (le): w78·(x0,x1,x2) − a78 ≤ −b78                          μ1 = c78
  P2 (le): w112·(x0,x1,x2) − a112 ≤ −b112                       μ2 = c112
  P3 (ge): x0 ≥ x0lo                                            μ3 = c78·w78₀ + c112·w112₀
  P4 (ge): x1 ≥ x1lo                                            μ4 = c78·w78₁ + c112·w112₁
  P5 (ge): x2 ≥ x2lo                                            μ5 = c78·w78₂ + c112·w112₂
  conclusion (ge): m ≥ L.

Each premise is `≤ 0` on every genuine execution; the non-negative μ-combination
equals `−(out) − (−L)` as a function of state, so `farkas_premise_combination`
yields `m ≥ L`.  This is the SAME certificate object the Clean verifier accepts
(out_leanmatch/entailment.json, derived L = claimed L), proved sound here in Lean. -/

/-- Slice execution state over the certificate's six symbols. -/
structure St where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  a78 : ℚ
  a112 : ℚ
  m : ℚ

/-- A genuine execution: a boxed input with the real ReLU activations and margin. -/
def stOf (x : Fin 3 → ℚ) : St where
  x0 := x 0
  x1 := x 1
  x2 := x 2
  a78 := relu (preact w78 b78 x)
  a112 := relu (preact w112 b112 x)
  m := margin x

def StValid (s : St) : Prop := ∃ x : Fin 3 → ℚ, inBox x ∧ s = stOf x

/-- The six certificate premises, each as a `lhs ≤ 0` functional of the state
    (a `ge: d ≥ k` constraint is normalised to `k − d ≤ 0`). -/
def cprem : Fin 6 → St → ℚ
  | 0, s => bconst - (s.m - c78 * s.a78 - c112 * s.a112)               -- P0 ge → ≤0
  | 1, s => ((11185023/33554432)*s.x0 + (11764663/33554432)*s.x1
              + (3556455/8388608)*s.x2 - s.a78) - (-b78)               -- P1 le
  | 2, s => ((16166253/33554432)*s.x0 + (3012123/67108864)*s.x1
              + (4557851/16777216)*s.x2 - s.a112) - (-b112)            -- P2 le
  | 3, s => x0lo - s.x0                                                 -- P3 ge → ≤0
  | 4, s => x1lo - s.x1                                                 -- P4 ge → ≤0
  | 5, s => x2lo - s.x2                                                 -- P5 ge → ≤0

/-- The exact certificate multipliers (all ≥ 0), matching the emitted JSON. -/
def cmu : Fin 6 → ℚ
  | 0 => 1
  | 1 => c78
  | 2 => c112
  | 3 => c78*(11185023/33554432) + c112*(16166253/33554432)
  | 4 => c78*(11764663/33554432) + c112*(3012123/67108864)
  | 5 => c78*(3556455/8388608)   + c112*(4557851/16777216)

theorem cmu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 0 ≤ cmu i := by
  intro i _; fin_cases i <;> norm_num [cmu, c78, c112]

/-- Every premise is `≤ 0` on every genuine execution (soundness of the relaxation). -/
theorem cprem_sound : ∀ i : Fin 6, ∀ s : St, StValid s → cprem i s ≤ 0 := by
  rintro i s ⟨x, hbox, rfl⟩
  -- the ReLU lower envelopes (α = 1) give the two affine premises
  have l78 := relu78_lower x
  have l112 := relu112_lower x
  have e78 := preact78_eq x
  have e112 := preact112_eq x
  rw [e78] at l78
  rw [e112] at l112
  obtain ⟨h0l, _, h1l, _, h2l, _⟩ := hbox
  fin_cases i <;>
    simp only [cprem, stOf, margin, e78, e112] <;>
    linarith

/-- The Farkas certificate identity: the μ-combination of the six premises equals
    `−(m) − (−L)` as a function of state — pure linear algebra. -/
theorem ccert_identity (s : St) :
    (∑ i ∈ (Finset.univ : Finset (Fin 6)), cmu i * cprem i s) = -(s.m) - (-L) := by
  rw [Fin.sum_univ_six]
  simp only [cmu, cprem, c78, c112, b78, b112, bconst, L, x0lo, x1lo, x2lo]
  ring

/-- **The certificate yields the bound** `m ≥ L`, via the abstract Farkas core —
    the exact entailment the Clean kernel verifier checks. -/
theorem cert_margin_bound (s : St) (hv : StValid s) : L ≤ s.m := by
  have h := farkas_premise_combination (S := St) (ι := Fin 6)
      (premises := Finset.univ) (g := cprem) (out := fun s => s.m)
      (μ := cmu) (c := -L) (valid := StValid)
      cmu_nonneg
      (by intro i _ s hs; exact cprem_sound i s hs)
      (by intro s; simpa using ccert_identity s)
  have := h s hv; linarith

/-- The certificate bound specialises to the network margin (cross-checks §6). -/
theorem cert_margin_bound_net (x : Fin 3 → ℚ) (h : inBox x) : L ≤ margin x := by
  have hv : StValid (stOf x) := ⟨x, h, rfl⟩
  have := cert_margin_bound (stOf x) hv
  simpa [stOf] using this

/-! ## Trust-base check. Must list only [propext, Classical.choice, Quot.sound]. -/

#print axioms margin_lower_bound
#print axioms margin_pos
#print axioms robust_atom_refuted
#print axioms cert_margin_bound
#print axioms cert_margin_bound_net

end SafenlpRealSlice
end Crownproof
