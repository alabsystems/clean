/-
  ============================================================================
  WAVE-2 PROGRAM 1 — CLOSE THE ITER-1 CAVEAT
  A REAL on-disk ONNX network, weights parsed INDEPENDENTLY of any certificate,
  with an UNSTABLE ReLU on its box, the emitter's premises PROVEN sound for the
  ONNX-derived `netEval`, and the property discharged end-to-end with NO trusted
  emitter.
  ============================================================================

  THE NETWORK (`test_tiny.onnx`, shipped on disk in the VNN-COMP test suite at
  `vnncomp2024/benchmarks/test/test_tiny.onnx`).  Its ONNX op graph is

      MatMul(W0,X_0) -> Add(.,B0) -> Relu -> MatMul(W1,.) -> Add(.,B1) -> Y_0

  i.e. a 1 -> affine -> ReLU -> affine -> 1 network (one hidden ReLU unit,
  scalar read-out).  The weights below were recovered by a STANDALONE,
  dependency-free protobuf/ONNX reader (`/tmp/crownproof/onnxdump`) that decodes
  each f32 LOSSLESSLY to an exact dyadic rational n/2^k.  The reader is wholly
  independent of the certificate emitter; the parsed values are

      layer 0 (hidden):  z = W0 * x + B0,   W0 = [[1]],  B0 = [0]
      layer 0 (ReLU):    a = relu z
      layer 1 (read-out):y = W1 * a + B1,   W1 = [[1]],  B1 = [0]

  so the net computes exactly  y = relu x.

  INPUT BOX (`test_tiny.vnnlib`):  x0 in [-1, 1].
  PROPERTY (the unsafe region in the vnnlib `or` clause):  { Y_0 >= 100 }.

  THE UNSTABLE RELU IS GENUINELY LOAD-BEARING.  On the box the pre-activation
  z = x ranges over [-1, 1], so  lz = -1 < 0 < 1 = uz  : the hidden ReLU is
  UNSTABLE.  The emitter's CROWN cert (`/tmp/crownproof/out_tiny/entailment.json`,
  PASSED by Clean's kernel verifier) uses the UPPER chord
        a <= s*(z - lz),   s = uz/(uz - lz) = 1/2,
  with Farkas multiplier 1 on that premise; the linear combination
        (1/2)(x0-1) + (1/2)(z-x0) + 1*(a - (1/2)z - 1/2) + 1*(-a - y) = -y - 1
  cancels `a` ONLY because of the upper-chord premise.  Dropping it leaves an
  uncancelled `a` term (verified in /tmp/crownproof/check_identity.py): the
  unstable envelope is essential to the y<=1 bound.  This is the unstable case
  the iter-1 `test_small` run did NOT exercise (there both ReLUs were active).

  WHAT THIS FILE PROVES (all sorry-free; `#print axioms` lists only
  [propext, Classical.choice, Quot.sound]):

    1. `netEval`  — the network defined INSIDE Lean as the explicit composition
       of exact `Fin`-indexed affine layers and a ReLU, from the ONNX-parsed
       weights.

    2. `bridge_premises_sound` — every one of the emitter's 8 premises (box,
       affine le/ge pairs, ReLU lower+UPPER envelope, output le/ge pair) HOLDS
       for `netEval` on the box.  The UPPER envelope soundness is exactly
       `relu_upper` on the UNSTABLE box [-1,1].

    3. `netEval_upper_bound` — composing the abstract Farkas core
       (`farkas_premise_combination`) on those premises with the certificate's
       EXACT multipliers gives  netEval x <= 1  for the ONNX-defined net.

    4. `tiny_unsafe_refuted` — the decision: the unsafe atom `netEval x >= 100`
       is FALSE everywhere on the box.

  Cross-check: the standalone reader's forward eval and the emitter agree with
  these Lean values (relu 1 = 1, relu (-1) = 0, max output 1 at x0=1).
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Crownproof
namespace NetOnnx

set_option linter.unusedSimpArgs false

open Finset

/-! ## 0.  Exact-rational weights of `test_tiny.onnx`, from the STANDALONE reader.

These are the dyadic rationals printed by `/tmp/crownproof/onnxdump`:
  layer 0:  W0 = [[1]]  B0 = [0]
  layer 1:  W1 = [[1]]  B1 = [0]
All are integers (f32 1.0 -> 1, f32 0.0 -> 0); the reader confirms losslessness. -/

/-- W0 : ℚ^{1×1}. -/
def W0 : Fin 1 → Fin 1 → ℚ := ![![1]]
/-- B0 : ℚ^1. -/
def B0 : Fin 1 → ℚ := ![0]
/-- W1 : ℚ^{1×1}. -/
def W1 : Fin 1 → Fin 1 → ℚ := ![![1]]
/-- B1 : ℚ^1. -/
def B1 : Fin 1 → ℚ := ![0]

/-! ## 1.  The network defined INSIDE Lean, mirroring the ONNX Gemm;Relu;Gemm. -/

/-- Affine layer  `(affine W b x) i = (∑ j, W i j * x j) + b i`. -/
def affine {n m : ℕ} (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j : Fin n, W i j * x j) + b i

/-- Vectorized ReLU. -/
def reluVec {m : ℕ} (z : Fin m → ℚ) : Fin m → ℚ := fun i => relu (z i)

def zlay (x : Fin 1 → ℚ) : Fin 1 → ℚ := affine W0 B0 x
def alay (x : Fin 1 → ℚ) : Fin 1 → ℚ := reluVec (zlay x)

/-- **The real ONNX network, evaluated exactly inside Lean.** Scalar output. -/
def netEval (x : Fin 1 → ℚ) : ℚ := (affine W1 B1 (alay x)) 0

/-! ### Closed forms (kernel-checked via `Fin.sum_univ_one`). -/

theorem zlay_0 (x : Fin 1 → ℚ) : zlay x 0 = x 0 := by
  simp only [zlay, affine, W0, B0, Fin.sum_univ_one, Matrix.cons_val_zero,
             Matrix.head_cons]
  ring

theorem alay_0 (x : Fin 1 → ℚ) : alay x 0 = relu (zlay x 0) := rfl

theorem netEval_eq (x : Fin 1 → ℚ) : netEval x = alay x 0 := by
  show (∑ j : Fin 1, W1 0 j * alay x j) + B1 0 = _
  simp only [Fin.sum_univ_one, W1, B1, Matrix.cons_val_zero, Matrix.head_cons]
  ring

/-- Direct closed form: the ONNX net computes `relu (x 0)`. -/
theorem netEval_is_relu (x : Fin 1 → ℚ) : netEval x = relu (x 0) := by
  rw [netEval_eq, alay_0, zlay_0]

/-! ## 2.  The relaxed-network STATE the emitter reasons about.

The emitter's premises (out_tiny/entailment.json) are written over the symbols
  x0, z1_0, a1_0, y.  A `State` bundles those four rationals; `genuine x` is the
state the ONNX-defined `netEval` produces on input `x`. -/

structure State where
  x0   : ℚ
  z1_0 : ℚ
  a1_0 : ℚ
  y    : ℚ

/-- The genuine execution state of the ONNX-defined network on input `x`.

    NOTE the sign of `y`.  The emitter bounds the NEGATED output (it proves a
    LOWER bound `y ≥ -1` on its internal symbol `y` in order to refute the unsafe
    region `Y_0 ≥ 100`).  Premises 6/7 of the shipped cert pin `a1_0 + y = 0`,
    i.e. the emitter's `y` symbol is `-Y_0 = -netEval x`.  We set `genuine.y`
    accordingly so the emitted premises are literally satisfied; the Farkas core
    then proves `y ≥ -1`, which is exactly `netEval x ≤ 1`. -/
def genuine (x : Fin 1 → ℚ) : State where
  x0   := x 0
  z1_0 := zlay x 0
  a1_0 := alay x 0
  y    := -netEval x

/-- `valid` : the state is some genuine execution on a boxed input. -/
def valid (st : State) : Prop :=
  ∃ x : Fin 1 → ℚ, (-1 ≤ x 0 ∧ x 0 ≤ 1) ∧ st = genuine x

/-! ## 3.  The 8 emitter premises, indexed by `Fin 8`, in EMITTER ORDER.

Read directly off `out_tiny/entailment.json` and normalised to `lhs ≤ 0`
(a `ge: coeffs·v ≥ k` constraint becomes `k - coeffs·v ≤ 0`):

  0  x0 ≤ 1                         : x0 - 1            ≤ 0    box upper
  1  x0 ≥ -1                        : -1 - x0           ≤ 0    box lower
  2  z1_0 - x0 ≤ 0                  : z1_0 - x0         ≤ 0    affine L1 ≤
  3  z1_0 - x0 ≥ 0                  : -(z1_0 - x0)      ≤ 0    affine L1 ≥
  4  a1_0 - z1_0 ≥ 0                : -(a1_0 - z1_0)    ≤ 0    ReLU lower env (α=1)
  5  a1_0 - (1/2)z1_0 ≤ 1/2         : a1_0 - (1/2)z1_0 - 1/2 ≤ 0   ReLU UPPER env
  6  a1_0 + y ≤ 0                   : a1_0 + y          ≤ 0    output affine ≤
  7  a1_0 + y ≥ 0                   : -(a1_0 + y)       ≤ 0    output affine ≥

The internal output symbol `y` is `-Y_0` (the emitter bounds the negated output
to refute `Y_0 ≥ 100`); premises 6/7 pin `a1_0 + y = 0`, i.e. `y = -a1_0`, while
`netEval x = a1_0`.  We therefore use `out st := st.y` and recover the Y_0 bound
by `Y_0 = netEval x = -y`. -/

def prem : Fin 8 → State → ℚ :=
  ![ fun st => st.x0 - 1                              -- 0  box  x0 ≤ 1
   , fun st => -1 - st.x0                             -- 1  box  x0 ≥ -1
   , fun st => st.z1_0 - st.x0                        -- 2  affine L1 ≤
   , fun st => -(st.z1_0 - st.x0)                     -- 3  affine L1 ≥
   , fun st => -(st.a1_0 - st.z1_0)                   -- 4  ReLU lower env (α=1)
   , fun st => st.a1_0 - (1/2)*st.z1_0 - 1/2          -- 5  ReLU UPPER env (chord)
   , fun st => st.a1_0 + st.y                         -- 6  output affine ≤
   , fun st => -(st.a1_0 + st.y) ]                    -- 7  output affine ≥

/-! ### The unstable ReLU facts on the box.

z = x ∈ [-1,1] is the pre-activation, so lz = -1 < 0 < 1 = uz : UNSTABLE.
The two ReLU premises are:
  * lower envelope (premise 4): relu z ≥ 1·z, which is `relu_lower` with α = 1.
  * UPPER envelope (premise 5): relu z ≤ s·(z - lz) with s = 1/2, lz = -1, which
    is `relu_upper` on the unstable box [-1,1].  This is the load-bearing,
    genuinely-unstable envelope the iter-1 stable-active run never exercised. -/

/-- The pre-activation stays in the chord box [-1,1] on the input box. -/
theorem zlay_in_box (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    -1 ≤ zlay x 0 ∧ zlay x 0 ≤ 1 := by
  rw [zlay_0]; exact ⟨hxl, hxu⟩

/-- The UNSTABLE upper-envelope soundness, instantiating `relu_upper` with
    l = -1, u = 1, s = 1/2 (so s*(u-l) = (1/2)*2 = 1 = u). -/
theorem relu_upper_tiny (z : ℚ) (hzl : -1 ≤ z) (hzu : z ≤ 1) :
    relu z ≤ (1/2) * (z - (-1)) := by
  have hs : (1/2 : ℚ) * (1 - (-1)) = 1 := by norm_num
  exact relu_upper (-1) 1 (1/2) z (by norm_num) (by norm_num) hs hzl hzu

/-! ## 4.  THE BRIDGE.  Every emitter premise is `≤ 0` on every valid state. -/

theorem bridge_all (x : Fin 1 → ℚ) (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    prem 0 (genuine x) ≤ 0 ∧ prem 1 (genuine x) ≤ 0 ∧ prem 2 (genuine x) ≤ 0 ∧
    prem 3 (genuine x) ≤ 0 ∧ prem 4 (genuine x) ≤ 0 ∧ prem 5 (genuine x) ≤ 0 ∧
    prem 6 (genuine x) ≤ 0 ∧ prem 7 (genuine x) ≤ 0 := by
  have hz0  : zlay x 0 = x 0 := zlay_0 x
  have ha0  : alay x 0 = relu (zlay x 0) := alay_0 x
  have hy   : netEval x = alay x 0 := netEval_eq x
  -- lower envelope: relu z ≥ 1·z  (α = 1)
  have hlow : (1 : ℚ) * zlay x 0 ≤ relu (zlay x 0) :=
    relu_lower 1 (zlay x 0) (by norm_num) (by norm_num)
  -- UPPER envelope: relu z ≤ (1/2)(z + 1)  on the unstable box [-1,1]
  obtain ⟨hzl, hzu⟩ := zlay_in_box x hxl hxu
  have hup  : relu (zlay x 0) ≤ (1/2) * (zlay x 0 - (-1)) := relu_upper_tiny _ hzl hzu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [prem, genuine, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail,
               Function.comp] <;>
    linarith [hxl, hxu, hz0, ha0, hy, hlow, hup]

/-- **THE BRIDGE.**  Every emitter premise is `≤ 0` on every valid state — the
    emitted premise set is SOUND for the ONNX-defined network on the box. -/
theorem bridge_premises_sound :
    ∀ i : Fin 8, ∀ st : State, valid st → prem i st ≤ 0 := by
  intro i st hv
  obtain ⟨x, ⟨hxl, hxu⟩, rfl⟩ := hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bridge_all x hxl hxu
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-! ## 5.  The certificate's exact multipliers and the Farkas conclusion.

The shipped multipliers (out_tiny/entailment.json, emitter order) are
  [1/2, 0, 1/2, 0, 0, 1, 0, 1].
The Farkas certificate IDENTITY is

    ∑ i, μ i · prem i st  =  -(out st) - c,   out st := st.y,   c = 1,

a purely linear (`ring`) identity in the state symbols.  Then
`farkas_premise_combination` gives  `out st ≥ -1`, i.e. `st.y ≥ -1`. -/

def mu : Fin 8 → ℚ := ![1/2, 0, 1/2, 0, 0, 1, 0, 1]

theorem mu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 8)), 0 ≤ mu i := by
  intro i _; fin_cases i <;> simp [mu]

/-- **The Farkas certificate identity** — pure algebra (the emitter's claim that
    its multipliers fold the premises into `-(y) - 1`). -/
theorem cert_identity (st : State) :
    (∑ i ∈ (Finset.univ : Finset (Fin 8)), mu i * prem i st) = -(st.y) - 1 := by
  simp only [mu, Fin.sum_univ_succ, Fin.sum_univ_zero,
             Matrix.cons_val_zero, Matrix.cons_val_succ]
  show (1/2) * prem 0 st + (0 * prem 1 st + ((1/2) * prem 2 st + (0 * prem 3 st
     + (0 * prem 4 st + (1 * prem 5 st + (0 * prem 6 st
     + (1 * prem 7 st + 0))))))) = -(st.y) - 1
  simp only [prem, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp]
  ring

/-- **State lower bound** for the relaxed output `y` via the abstract Farkas core. -/
theorem tiny_state_lower_bound :
    ∀ st : State, valid st → -(1 : ℚ) ≤ st.y := by
  have h :=
    farkas_premise_combination (S := State) (ι := Fin 8)
      (premises := Finset.univ)
      (g := prem) (out := fun st => st.y) (μ := mu) (c := 1)
      (valid := valid)
      mu_nonneg
      (by intro i _ st hst; exact bridge_premises_sound i st hst)
      (by intro st; simpa using cert_identity st)
  intro st hst
  have := h st hst
  linarith

/-! ## 6.  THE DECISION on the ACTUAL ONNX output `Y_0 = netEval x`.

The emitter's internal symbol `y` is `-Y_0 = -netEval x` (the genuine state sets
`(genuine x).y = -netEval x`).  The Farkas core proved `(genuine x).y ≥ -1`, i.e.
`-netEval x ≥ -1`, i.e. `netEval x ≤ 1`.  This is the certified bound `Y_0 ≤ 1`
obtained THROUGH the certificate (the unstable upper-envelope premise, multiplier 1,
is the load-bearing term in the Farkas combination — see check_identity.py). -/

/-- The genuine-state internal output equals `-netEval`. -/
theorem genuine_y (x : Fin 1 → ℚ) : (genuine x).y = -netEval x := rfl

/-- **Upper bound on the actual ONNX output, OBTAINED FROM THE CERTIFICATE.**
    Composing `farkas_premise_combination` (via `tiny_state_lower_bound`) on the
    emitted premises with the certificate's exact multipliers `[1/2,0,1/2,0,0,1,0,1]`
    yields the emitter's certified bound `netEval x ≤ 1`.  The load-bearing term is
    the UNSTABLE upper envelope (premise 5, multiplier 1). -/
theorem netEval_upper_bound (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    netEval x ≤ 1 := by
  have hv : valid (genuine x) := ⟨x, ⟨hxl, hxu⟩, rfl⟩
  have h := tiny_state_lower_bound (genuine x) hv   -- -1 ≤ (genuine x).y = -netEval x
  rw [genuine_y] at h
  linarith

/-- Cross-check: the SAME bound `netEval x ≤ 1` follows directly from `relu_upper`
    on the unstable box [-1,1] (the very envelope the certificate folds), giving an
    independent witness that the certificate's load-bearing premise is correct. -/
theorem netEval_upper_bound_direct (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    netEval x ≤ 1 := by
  rw [netEval_is_relu]
  have hup : relu (x 0) ≤ (1/2) * (x 0 - (-1)) := relu_upper_tiny (x 0) hxl hxu
  linarith

/-! ## 7.  THE DECISION: the unsafe atom is refuted for the ONNX net.

The vnnlib unsafe region is `{ Y_0 ≥ 100 }`.  Since `Y_0 = netEval x ≤ 1 < 100`,
the unsafe atom is FALSE for the ONNX-defined network at every boxed input —
a fully kernel-checked verdict with NO trusted emitter. -/

theorem tiny_unsafe_refuted (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    ¬ (netEval x ≥ 100) := by
  have := netEval_upper_bound x hxl hxu
  intro hbad; linarith

/-- Equivalently, the safe half-space holds everywhere on the box. -/
theorem tiny_safe (x : Fin 1 → ℚ)
    (hxl : -1 ≤ x 0) (hxu : x 0 ≤ 1) :
    netEval x < 100 := by
  have := netEval_upper_bound x hxl hxu; linarith

/-! ## 8.  Cross-check / tightness.  The bound is TIGHT: attained at x0 = 1
    (`netEval ![1] = 1`), matching the standalone reader's forward eval
    (relu 1 = 1) and the emitter's exact bound Y_0 ≤ 1. -/

theorem netEval_at_one : netEval ![1] = 1 := by
  rw [netEval_is_relu]; show relu ((![1] : Fin 1 → ℚ) 0) = 1
  simp only [Matrix.cons_val_zero]; unfold relu; norm_num

theorem netEval_at_neg_one : netEval ![-1] = 0 := by
  rw [netEval_is_relu]; show relu ((![-1] : Fin 1 → ℚ) 0) = 0
  simp only [Matrix.cons_val_zero]; unfold relu; norm_num

/-! ## Trust-base check.  Each must list ONLY
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. -/

#print axioms netEval
#print axioms bridge_premises_sound
#print axioms cert_identity
#print axioms tiny_state_lower_bound
#print axioms netEval_upper_bound
#print axioms netEval_upper_bound_direct
#print axioms tiny_unsafe_refuted
#print axioms netEval_at_one
#print axioms netEval_at_neg_one

end NetOnnx
end Crownproof
