/-
  ============================================================================
  GRAND-CHALLENGE PROGRAM 1 — CLOSE THE ONNX-SEMANTICS TRUST BOUNDARY
  First deliverable: a REAL ReLU network, its semantics formalized INSIDE Lean,
  with the emitter's premises PROVEN sound for the Lean-defined network, and the
  property bound discharged end-to-end with NO trusted emitter.
  ============================================================================

  THE NETWORK (`test_small` from the VNN-COMP empirical suite,
  `crown-proofs/empirical/real_networks/test_small/`):

    architecture : 1 input  ->  affine  ->  ReLU  ->  affine  ->  ReLU  ->  affine  ->  1 output
                   ( 2 hidden layers, width 2 — the EMPIRICAL.md `test_small` net )

    exact rational weights (recovered losslessly from the real certificate's
    affine-equality premises — each affine layer is emitted as paired le/ge
    constraints, which pin the weights exactly):

      layer 1 (affine):  z1 = W1 * x + b1
            W1 = [[1],[1]]          b1 = [3/2, 3/2]
      layer 1 (ReLU):    a1_i = relu (z1_i)

      layer 2 (affine):  z2 = W2 * a1 + b2
            W2 = [[2,2],[2,2]]      b2 = [5/2, 5/2]
      layer 2 (ReLU):    a2_i = relu (z2_i)

      layer 3 (affine):  y = W3 * a2 + b3
            W3 = [[-3,-3]]          b3 = [-7/2]

    input box : x0 ∈ [-1, 1].
    property  : the unsafe atom { y ≤ -100 } is refuted; the certified exact
                lower bound is  y ≥ -157/2  (tight: attained at x0 = 1).

  WHAT THIS FILE PROVES (all sorry-free; `#print axioms` lists only the three
  standard logical axioms):

    1. `netEval`  — the network is defined INSIDE Lean as the explicit
       composition of exact `Fin`-indexed affine layers (`z = W x + b`) and
       vectorized ReLU layers (`a_i = relu z_i`).  The definition is itself
       kernel-checked; there is no external/trusted description of the net.

    2. `bridge_premises_sound` (the BRIDGE) — for every input x0 in the box,
       EACH premise the emitter produced for this net (box bounds, every affine
       equality as a le/ge pair, every ReLU envelope as a le/ge pair) HOLDS for
       the values produced by `netEval`.  i.e. the emitted premise set is SOUND
       for the Lean-defined network.

    3. `netSmall_output_lower_bound` — composing the EXISTING abstract Farkas
       core (`farkas_premise_combination`, re-proved in `Bridge.lean`) on those
       premises with the bridge yields  `netEval x ≥ -157/2`  for the ACTUAL
       (Lean-defined) network, with the certificate's exact multipliers.

    4. `netSmall_unsafe_refuted` — the end-to-end decision: for every x in the
       box, the real unsafe atom `netEval x ≤ -100` is FALSE for `netEval x`.
       This is a fully kernel-checked (no trusted emitter) verdict for a real
       net: the network semantics are Lean-defined and the premises are proven
       valid against them.

  The multipliers used are EXACTLY the ones in the shipped certificate
  (`test_small/entailment.json`):  the 20 premises (in emitter order) carry
  multipliers
      [24,0, 12,0, 12,0, 3,0, 3,0, 0,12, 0,12, 0,3, 0,3, 0,1].
  We feed the certificate's own numbers; nothing is re-derived by hand beyond
  checking the linear identity, which `ring`/`linarith` discharge.
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetSmall

-- The `simp only` calls below intentionally include vector-cons lemmas to make
-- the term-reduction explicit and robust; silence the unused-arg linter.
set_option linter.unusedSimpArgs false

open Finset

/-! ## 0.  Exact-rational weights of the real `test_small` network. -/

/-- W1 : ℚ^{2×1}.  Row i, col j. -/
def W1 : Fin 2 → Fin 1 → ℚ := ![![1], ![1]]
/-- b1 : ℚ^2. -/
def b1 : Fin 2 → ℚ := ![3/2, 3/2]

/-- W2 : ℚ^{2×2}. -/
def W2 : Fin 2 → Fin 2 → ℚ := ![![2, 2], ![2, 2]]
/-- b2 : ℚ^2. -/
def b2 : Fin 2 → ℚ := ![5/2, 5/2]

/-- W3 : ℚ^{1×2}. -/
def W3 : Fin 1 → Fin 2 → ℚ := ![![-3, -3]]
/-- b3 : ℚ^1. -/
def b3 : Fin 1 → ℚ := ![-7/2]

/-! ## 1.  The network defined INSIDE Lean.

`affine` is an honest matrix-vector product over `Fin`; `reluVec` applies the
exact-rational `relu` componentwise.  `netEval` is their explicit composition,
exactly mirroring the ONNX `Gemm; Relu; Gemm; Relu; Gemm` graph. -/

/-- Affine layer  `(affine W b x) i = (∑ j, W i j * x j) + b i`. -/
def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

/-- Vectorized ReLU. -/
def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

/-- The pre-activations / post-activations of the real network, as explicit
    functions of the input `x : Fin 1 → ℚ`. -/
def z1 (x : Fin 1 → ℚ) : Fin 2 → ℚ := affine W1 b1 x
def a1 (x : Fin 1 → ℚ) : Fin 2 → ℚ := reluVec (z1 x)
def z2 (x : Fin 1 → ℚ) : Fin 2 → ℚ := affine W2 b2 (a1 x)
def a2 (x : Fin 1 → ℚ) : Fin 2 → ℚ := reluVec (z2 x)

/-- **The real network, evaluated exactly inside Lean.**  Scalar output. -/
def netEval (x : Fin 1 → ℚ) : ℚ := (affine W3 b3 (a2 x)) 0

/-! ### Closed forms of the affine layers (kernel-checked via `Fin.sum_univ`). -/

theorem z1_0 (x : Fin 1 → ℚ) : z1 x 0 = x 0 + 3/2 := by
  simp only [z1, affine, W1, b1, Fin.sum_univ_one, Matrix.cons_val_zero,
             Matrix.cons_val_one, Matrix.head_cons]
  ring
theorem z1_1 (x : Fin 1 → ℚ) : z1 x 1 = x 0 + 3/2 := by
  simp only [z1, affine, W1, b1, Fin.sum_univ_one, Matrix.cons_val_zero,
             Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem a1_0 (x : Fin 1 → ℚ) : a1 x 0 = relu (z1 x 0) := rfl
theorem a1_1 (x : Fin 1 → ℚ) : a1 x 1 = relu (z1 x 1) := rfl

theorem z2_0 (x : Fin 1 → ℚ) : z2 x 0 = 2 * a1 x 0 + 2 * a1 x 1 + 5/2 := by
  show (∑ j : Fin 2, W2 0 j * a1 x j) + b2 0 = _
  rw [Fin.sum_univ_two]
  simp only [W2, b2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  <;> ring
theorem z2_1 (x : Fin 1 → ℚ) : z2 x 1 = 2 * a1 x 0 + 2 * a1 x 1 + 5/2 := by
  show (∑ j : Fin 2, W2 1 j * a1 x j) + b2 1 = _
  rw [Fin.sum_univ_two]
  simp only [W2, b2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  <;> ring

theorem a2_0 (x : Fin 1 → ℚ) : a2 x 0 = relu (z2 x 0) := rfl
theorem a2_1 (x : Fin 1 → ℚ) : a2 x 1 = relu (z2 x 1) := rfl

theorem netEval_eq (x : Fin 1 → ℚ) : netEval x = -3 * a2 x 0 + -3 * a2 x 1 + -7/2 := by
  show (∑ j : Fin 2, W3 0 j * a2 x j) + b3 0 = _
  rw [Fin.sum_univ_two]
  simp only [W3, b3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  <;> ring

/-! ## 2.  The relaxed-network STATE the emitter reasons about.

The emitter's premises are written over the symbols
  x0, z1_0, z1_1, a1_0, a1_1, z2_0, z2_1, a2_0, a2_1, y.
A `State` bundles those ten rationals.  `genuine x` is the state that the REAL
network produces on input `x` — this is the only place `netEval` enters the
Farkas machinery, and it is built purely from the Lean network definition. -/

structure State where
  x0   : ℚ
  z1_0 : ℚ
  z1_1 : ℚ
  a1_0 : ℚ
  a1_1 : ℚ
  z2_0 : ℚ
  z2_1 : ℚ
  a2_0 : ℚ
  a2_1 : ℚ
  y    : ℚ

/-- The genuine execution state of the Lean-defined network on input `x`. -/
def genuine (x : Fin 1 → ℚ) : State where
  x0   := x 0
  z1_0 := z1 x 0
  z1_1 := z1 x 1
  a1_0 := a1 x 0
  a1_1 := a1 x 1
  z2_0 := z2 x 0
  z2_1 := z2 x 1
  a2_0 := a2 x 0
  a2_1 := a2 x 1
  y    := netEval x

/-- `valid` : the state lies on the network's graph and inside the box.
    A state is valid iff it is *some* genuine execution on a boxed input. -/
def valid (st : State) : Prop :=
  ∃ x : Fin 1 → ℚ, (-1 ≤ x 0 ∧ x 0 ≤ 1) ∧ st = genuine x

/-! ## 3.  The 20 emitter premises, indexed by `Fin 20`, in EMITTER ORDER.

Each premise is normalised to `lhs ≤ 0` (the `le` form; a `ge a ≤ b` constraint
`coeffs·v ≥ b` becomes `b - coeffs·v ≤ 0`).  These are read directly off
`test_small/entailment.json`:

  0  x0 ≤ 1                  : x0 - 1                 ≤ 0
  1  x0 ≥ -1                 : -1 - x0                ≤ 0
  2  z1_0 - x0 ≤ 3/2         : z1_0 - x0 - 3/2        ≤ 0
  3  z1_0 - x0 ≥ 3/2         : 3/2 - (z1_0 - x0)      ≤ 0
  4  z1_1 - x0 ≤ 3/2         : z1_1 - x0 - 3/2        ≤ 0
  5  z1_1 - x0 ≥ 3/2         : 3/2 - (z1_1 - x0)      ≤ 0
  6  z2_0 - 2a1_0 - 2a1_1 ≤ 5/2 : (z2_0 - 2a1_0 - 2a1_1) - 5/2 ≤ 0
  7  z2_0 - 2a1_0 - 2a1_1 ≥ 5/2 : 5/2 - (z2_0 - 2a1_0 - 2a1_1) ≤ 0
  8  z2_1 - 2a1_0 - 2a1_1 ≤ 5/2 : (z2_1 - 2a1_0 - 2a1_1) - 5/2 ≤ 0
  9  z2_1 - 2a1_0 - 2a1_1 ≥ 5/2 : 5/2 - (z2_1 - 2a1_0 - 2a1_1) ≤ 0
  10 a1_0 - z1_0 ≥ 0         : -(a1_0 - z1_0)         ≤ 0     ReLU1 lower (active)
  11 a1_0 - z1_0 ≤ 0         : (a1_0 - z1_0)          ≤ 0     ReLU1 upper (active)
  12 a1_1 - z1_1 ≥ 0         : -(a1_1 - z1_1)         ≤ 0
  13 a1_1 - z1_1 ≤ 0         : (a1_1 - z1_1)          ≤ 0
  14 a2_0 - z2_0 ≥ 0         : -(a2_0 - z2_0)         ≤ 0     ReLU2 lower (active)
  15 a2_0 - z2_0 ≤ 0         : (a2_0 - z2_0)          ≤ 0     ReLU2 upper (active)
  16 a2_1 - z2_1 ≥ 0         : -(a2_1 - z2_1)         ≤ 0
  17 a2_1 - z2_1 ≤ 0         : (a2_1 - z2_1)          ≤ 0
  18 3a2_0 + 3a2_1 + y ≤ -7/2: (3a2_0 + 3a2_1 + y) + 7/2 ≤ 0
  19 3a2_0 + 3a2_1 + y ≥ -7/2: -7/2 - (3a2_0 + 3a2_1 + y) ≤ 0

NOTE on the ReLU envelopes (premises 10–17): on this box BOTH ReLUs are stable
ACTIVE — every pre-activation is ≥ 0 — so the emitter's lower envelope
(slope α = 1, giving `a ≥ z`) and upper envelope (the active chord, giving
`a ≤ z`) collapse to the exact relation `a = z`.  We prove each holds for
`netEval` directly from `relu`'s definition on a nonneg argument (the lower
envelope soundness is `relu_lower` with α = 1; the upper is `relu z = z` when
`z ≥ 0`).  The box premises pin `z ≥ 0` because the affine maps are exact. -/

def prem : Fin 20 → State → ℚ :=
  ![ fun st => st.x0 - 1                                  -- 0  box  x0 ≤ 1
   , fun st => -1 - st.x0                                 -- 1  box  x0 ≥ -1
   , fun st => (st.z1_0 - st.x0) - 3/2                    -- 2  affine L1 ≤
   , fun st => 3/2 - (st.z1_0 - st.x0)                    -- 3  affine L1 ≥
   , fun st => (st.z1_1 - st.x0) - 3/2                    -- 4
   , fun st => 3/2 - (st.z1_1 - st.x0)                    -- 5
   , fun st => (st.z2_0 - 2*st.a1_0 - 2*st.a1_1) - 5/2    -- 6  affine L2 ≤
   , fun st => 5/2 - (st.z2_0 - 2*st.a1_0 - 2*st.a1_1)    -- 7  affine L2 ≥
   , fun st => (st.z2_1 - 2*st.a1_0 - 2*st.a1_1) - 5/2    -- 8
   , fun st => 5/2 - (st.z2_1 - 2*st.a1_0 - 2*st.a1_1)    -- 9
   , fun st => -(st.a1_0 - st.z1_0)                       -- 10 ReLU1_0 lower env
   , fun st => (st.a1_0 - st.z1_0)                        -- 11 ReLU1_0 upper env
   , fun st => -(st.a1_1 - st.z1_1)                       -- 12 ReLU1_1 lower env
   , fun st => (st.a1_1 - st.z1_1)                        -- 13 ReLU1_1 upper env
   , fun st => -(st.a2_0 - st.z2_0)                       -- 14 ReLU2_0 lower env
   , fun st => (st.a2_0 - st.z2_0)                        -- 15 ReLU2_0 upper env
   , fun st => -(st.a2_1 - st.z2_1)                       -- 16 ReLU2_1 lower env
   , fun st => (st.a2_1 - st.z2_1)                        -- 17 ReLU2_1 upper env
   , fun st => (3*st.a2_0 + 3*st.a2_1 + st.y) + 7/2       -- 18 output affine ≤
   , fun st => -7/2 - (3*st.a2_0 + 3*st.a2_1 + st.y) ]    -- 19 output affine ≥

/-! ### Pre-activations are nonnegative on the box (so both ReLUs are active). -/

/-- z1 is ≥ 1/2 > 0 on the box: z1 = x0 + 3/2 ≥ -1 + 3/2 = 1/2. -/
theorem z1_nonneg (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) :
    0 ≤ z1 x 0 ∧ 0 ≤ z1 x 1 := by
  rw [z1_0, z1_1]; constructor <;> linarith

/-- a1 = z1 on the box (active ReLU), hence a1 ≥ 1/2. -/
theorem a1_active (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) :
    a1 x 0 = z1 x 0 ∧ a1 x 1 = z1 x 1 := by
  obtain ⟨h0, h1⟩ := z1_nonneg x hxl
  rw [a1_0, a1_1, relu, relu, max_eq_right h0, max_eq_right h1]
  exact ⟨rfl, rfl⟩

/-- z2 ≥ 0 on the box: z2 = 2 a1_0 + 2 a1_1 + 5/2, with a1 ≥ 0. -/
theorem z2_nonneg (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) :
    0 ≤ z2 x 0 ∧ 0 ≤ z2 x 1 := by
  obtain ⟨e0, e1⟩ := a1_active x hxl
  obtain ⟨h0, h1⟩ := z1_nonneg x hxl
  rw [z2_0, z2_1]
  rw [e0, e1]
  constructor <;> nlinarith

/-- a2 = z2 on the box (active ReLU). -/
theorem a2_active (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) :
    a2 x 0 = z2 x 0 ∧ a2 x 1 = z2 x 1 := by
  obtain ⟨h0, h1⟩ := z2_nonneg x hxl
  rw [a2_0, a2_1, relu, relu, max_eq_right h0, max_eq_right h1]
  exact ⟨rfl, rfl⟩

/-! ## 4.  THE BRIDGE.

Every emitter premise is `≤ 0` on every valid state — i.e. the emitted premise
set faithfully encodes (is sound for) the Lean-defined network on the box. -/

/-- Soundness of all 20 premises stated as an explicit numeral-indexed
    conjunction.  Each `prem k (genuine x)` reduces (via `simp [prem, genuine]`)
    to a linear (in)equality in the network's values, closed by `linarith` from
    the box bounds, the affine closed forms, and the active-ReLU equalities. -/
theorem bridge_all (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 ∧
    prem 3 (genuine x) ≤ 0 ∧ prem 4 (genuine x) ≤ 0 ∧ prem 5 (genuine x) ≤ 0 ∧
    prem 6 (genuine x) ≤ 0 ∧ prem 7 (genuine x) ≤ 0 ∧ prem 8 (genuine x) ≤ 0 ∧
    prem 9 (genuine x) ≤ 0 ∧ prem 10 (genuine x) ≤ 0 ∧ prem 11 (genuine x) ≤ 0 ∧
    prem 12 (genuine x) ≤ 0 ∧ prem 13 (genuine x) ≤ 0 ∧ prem 14 (genuine x) ≤ 0 ∧
    prem 15 (genuine x) ≤ 0 ∧ prem 16 (genuine x) ≤ 0 ∧ prem 17 (genuine x) ≤ 0 ∧
    prem 18 (genuine x) ≤ 0 ∧ prem 19 (genuine x) ≤ 0 := by
  -- Active-ReLU equalities (both ReLUs are stable-active on the box).
  obtain ⟨ea0, ea1⟩ := a1_active x hxl
  obtain ⟨eb0, eb1⟩ := a2_active x hxl
  -- Closed forms of the affine layers.
  have hz10 : z1 x 0 = x 0 + 3/2 := z1_0 x
  have hz11 : z1 x 1 = x 0 + 3/2 := z1_1 x
  have hz20 : z2 x 0 = 2 * a1 x 0 + 2 * a1 x 1 + 5/2 := z2_0 x
  have hz21 : z2 x 1 = 2 * a1 x 0 + 2 * a1 x 1 + 5/2 := z2_1 x
  have hy  : netEval x = -3 * a2 x 0 + -3 * a2 x 1 + -7/2 := netEval_eq x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [prem, genuine, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail,
               Function.comp] <;>
    linarith [hxl, hxu, hz10, hz11, hz20, hz21, hy, ea0, ea1, eb0, eb1]

/-- **THE BRIDGE.**  Every emitter premise is `≤ 0` on every valid state — i.e.
    the emitted premise set faithfully encodes (is sound for) the Lean-defined
    network on the box.  This is the no-trusted-emitter guarantee. -/
theorem bridge_premises_sound :
    ∀ i : Fin 20, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, ⟨hxl, hxu⟩, rfl⟩ := hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := bridge_all x hxl hxu
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

/-! ## 5.  The certificate's exact multipliers, and the Farkas conclusion.

The shipped multipliers (entailment.json, emitter order) are
  [24,0, 12,0, 12,0, 3,0, 3,0, 0,12, 0,12, 0,3, 0,3, 0,1].
We must check the Farkas certificate IDENTITY:

    ∑ i, μ i · prem i st  =  -(out st) - c,     out st := st.y,   c = 157/2,

i.e. the nonneg μ-combination of the premise LHSs equals `-y - 157/2` *as a
function of the state* (a purely linear/`ring` identity — no network facts).
Then `farkas_premise_combination` gives  `out st ≥ -157/2`  on every valid st. -/

/-- The 20 certificate multipliers, as a `Fin 20 → ℚ` family. -/
def mu : Fin 20 → ℚ :=
  ![24, 0, 12, 0, 12, 0, 3, 0, 3, 0, 0, 12, 0, 12, 0, 3, 0, 3, 0, 1]

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 20)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> simp [mu]

/-- **The Farkas certificate identity** — pure algebra, exactly the emitter's
    claim that its multipliers fold the premises into `-(y) - 157/2`. -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 20)), mu i * prem i st)
      = -(st.y) - 157/2 := by
  -- Expand the Fin 20 sum and the vector multipliers `mu`.
  simp only [mu, Fin.sum_univ_succ, Fin.sum_univ_zero,
             Matrix.cons_val_zero, Matrix.cons_val_succ]
  -- Convert the `Fin.succ`-chained indices to numerals (defeq), then evaluate
  -- the pattern-matched premises and check the linear identity by `ring`.
  show 24 * prem 0 st + (0 * prem 1 st + (12 * prem 2 st + (0 * prem 3 st
     + (12 * prem 4 st + (0 * prem 5 st + (3 * prem 6 st + (0 * prem 7 st
     + (3 * prem 8 st + (0 * prem 9 st + (0 * prem 10 st + (12 * prem 11 st
     + (0 * prem 12 st + (12 * prem 13 st + (0 * prem 14 st + (3 * prem 15 st
     + (0 * prem 16 st + (3 * prem 17 st + (0 * prem 18 st
     + (1 * prem 19 st + 0))))))))))))))))))) = -(st.y) - 157/2
  simp only [prem, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

/-- **Output lower bound for the REAL (Lean-defined) network.**
    Composing the abstract Farkas core with the bridge and the certificate. -/
theorem netSmall_state_lower_bound :
    ∀ st : State, valid st → -(157/2) ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 20)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := 157/2)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

/-- **End-to-end bound on the actual Lean network output `netEval`.**
    For every input in the box, the real network's output is ≥ -157/2. -/
theorem netEval_lower_bound (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    -(157/2) ≤ netEval x := by
  have hv : valid (genuine x) := ⟨x, ⟨hxl, hxu⟩, rfl⟩
  have := netSmall_state_lower_bound (genuine x) hv
  -- (genuine x).y = netEval x by `rfl`
  simpa [genuine] using this

/-! ## 6.  THE DECISION: the real unsafe atom is refuted for the real net.

The property under test refutes the unsafe region `{ y ≤ -100 }`.  Since
`-157/2 = -78.5 > -100`, the lower bound proves the unsafe atom is FALSE for the
Lean-defined network at every boxed input — a fully kernel-checked verdict with
NO trusted emitter. -/

theorem netSmall_unsafe_refuted (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    ¬ (netEval x ≤ -100) := by
  have := netEval_lower_bound x hxl hxu
  intro hbad; linarith

/-- Equivalently, the safe half-space holds everywhere on the box. -/
theorem netSmall_safe (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    -100 < netEval x := by
  have := netEval_lower_bound x hxl hxu; linarith

/-! ## 7.  Sanity: the bound is TIGHT — attained at x0 = 1 (`y = -157/2`).
    This shows the certified bound is the best possible, so the formalized
    network and premises are not vacuously loose. -/

theorem netEval_at_one : netEval ![1] = -157/2 := by
  have h1 : (-1 : ℚ) ≤ (![1] : Fin 1 → ℚ) 0 := by norm_num
  obtain ⟨ea0, ea1⟩ := a1_active ![1] h1
  obtain ⟨eb0, eb1⟩ := a2_active ![1] h1
  rw [netEval_eq, eb0, eb1, z2_0, z2_1, ea0, ea1, z1_0, z1_1]
  norm_num

/-! ## Trust-base check.  Each must list ONLY `[propext, Classical.choice,
    Quot.sound]` — no `sorryAx`. -/

#print axioms netEval
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms netSmall_state_lower_bound
#print axioms netEval_lower_bound
#print axioms netSmall_unsafe_refuted
#print axioms netEval_at_one

end NetSmall
end Crownproof
