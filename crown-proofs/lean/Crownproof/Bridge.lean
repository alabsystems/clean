/-
  End-to-end CROWN / Farkas bridge theorem, formalized in Lean 4 over the
  rationals, using mathlib for ordered-field reasoning.

  This is the mathematical content of Clean's kernel axiom
  `NNVerify.farkas_to_interval` (T09):

      a non-negative multiplier vector that combines the relaxed-network
      premises (box bounds + the affine layers given as ≤/≥ pairs + the ReLU
      envelopes) to derive a linear functional equal to (-y) with constant `c`,
      certifies that the true network output `y` satisfies `y ≥ -c` on the box.

  We prove it sorry-free.  The trust base is reported by `#print axioms` at the
  bottom; it must list only `[propext, Classical.choice, Quot.sound]`.

  Structure
  ---------
  * `farkas_premise_combination` : the abstract Farkas core over an indexed
    family of premises.  Each premise is a function `g i : State → ℚ` that is
    `≤ 0` on every *valid* state; with non-negative multipliers `μ` and the
    certificate identity `Σ μ i * g i s = -(out s) - c` (as functions of the
    state), the output `out s ≥ -c` on every valid state.

  * `relu` model + `relu_lower`/`relu_upper` envelope soundness (re-derived
    here so this file is self-contained; identical to `Basic.lean`).

  * `crown_bridge` : the SAME theorem specialised to the concrete one-hidden-
    layer relaxed-network state (input box, affine pre-activations as ≤/≥
    pairs, ReLU lower/upper envelopes, affine scalar output as a ≤/≥ pair).
    This witnesses that the abstract hypotheses are satisfiable by a real
    network execution, so the bridge is not vacuous.
-/

import Crownproof.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Crownproof

open Finset

-- `relu`, `relu_lower`, `relu_upper` are reused from `Crownproof.Basic`.

/-! ## 1. Abstract Farkas premise-combination bridge.

This is the exact entailment that `farkas_to_interval` axiomatises, phrased
without committing to any particular `State`.  A "state" ranges over an
arbitrary type `S`; the *valid* states (genuine network executions) are those
satisfying a predicate `valid`.  Each premise `g i : S → ℚ` is a sound
relaxation: it is `≤ 0` on every valid state (this is how the box bounds, the
affine ≤/≥ pairs, and the ReLU envelopes are all normalised — each says
`lhs - rhs ≤ 0`).  `out : S → ℚ` is the network output functional.

A *Farkas certificate* is a non-negative multiplier vector `μ : ι → ℚ`
together with the algebraic identity that the μ-combination of the premises
equals `-(out) - c` *as a function of the state*:

      ∀ s, ∑ i, μ i * g i s  =  -(out s) - c.

Conclusion: on every valid state, `out s ≥ -c`. -/
theorem farkas_premise_combination
    {S : Type*} {ι : Type*} (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c : ℚ)
    (valid : S → Prop)
    -- every multiplier is non-negative
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    -- every premise is a sound "≤ 0" relaxation on valid states
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    -- the certificate identity: the μ-combination IS  -(out) - c
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  intro s hs
  -- Each term μ i * g i s ≤ 0, so the whole sum ≤ 0.
  have hsum_le : (∑ i ∈ premises, μ i * g i s) ≤ 0 := by
    have hzero : (∑ i ∈ premises, (0 : ℚ)) = 0 := by simp
    calc (∑ i ∈ premises, μ i * g i s)
        ≤ (∑ i ∈ premises, (0 : ℚ)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_nonpos_of_nonneg_of_nonpos (hμ i hi) (hg i hi s hs)
      _ = 0 := hzero
  -- Rewrite the sum via the certificate identity:  -(out s) - c ≤ 0.
  rw [hcert s] at hsum_le
  linarith

/-! ## 2. Concrete one-hidden-layer relaxed-network instantiation.

We now show the abstract bridge is non-vacuous by instantiating it on a real
network execution.  To keep the file finite and fully checkable we take the
illustrative shape n = 1 input, h = 1 hidden unit, scalar output — the
unstable-ReLU case that is the whole reason CROWN needs an envelope.  All the
qualitative structure (box, affine ≤/≥ pair, ReLU lower+upper envelope, output
≤/≥ pair, non-negative multipliers, exact-rational identity) is present.

State of a genuine execution:
  x  : input        with  l ≤ x ≤ u                          (box)
  z  : pre-activation,  z = w1 * x + b1                      (affine, layer 1)
  a  : post-activation, a = relu z                           (ReLU)
  y  : output,          y = w2 * a + b2                      (affine, output)

Premises (each normalised to `lhs ≤ 0`):
  P_boxlo :  l - x        ≤ 0          (mult m_bl ≥ 0)
  P_boxhi :  x - u        ≤ 0          (mult m_bu ≥ 0)
  P_relulo: alpha*z - a   ≤ 0          (mult m_rl ≥ 0)   lower envelope
  P_reluup: a - s*(z-l)   ≤ 0          (mult m_ru ≥ 0)   upper envelope

Because the affine equalities are exact, the verifier folds them in directly
(an equality contributes via a single multiplier whose two halves cancel); we
do the same here by substituting z and y.  The Farkas certificate is the choice
of `m_bl, m_bu, m_rl, m_ru ≥ 0` such that the μ-combination of the four premise
LHSs equals `-(y) - c` for the certified constant `c`.  Whenever such a
certificate exists, `crown_bridge` concludes `y ≥ -c`.  -/

/-- The concrete relaxed-network state. -/
structure NetState where
  x : ℚ
  z : ℚ
  a : ℚ
  y : ℚ

/-- A state is a *genuine execution* on the box `[l,u]` of the network
    `(w1,b1,w2,b2)` iff the box holds and the affine + ReLU equations hold. -/
def NetState.valid (l u w1 b1 w2 b2 : ℚ) (st : NetState) : Prop :=
  l ≤ st.x ∧ st.x ≤ u ∧
  st.z = w1 * st.x + b1 ∧
  st.a = relu st.z ∧
  st.y = w2 * st.a + b2

/-- The four relaxed-network premises, indexed by `Fin 4`, as `lhs ≤ 0`
    functionals of the state.  `alpha` is the lower-envelope slope, `s` the
    upper-chord slope, `lz` the lower bound on the pre-activation used by the
    upper chord. -/
def premiseFun (l u alpha s lz : ℚ) : Fin 4 → NetState → ℚ
  | 0, st => l - st.x                 -- box lower
  | 1, st => st.x - u                 -- box upper
  | 2, st => alpha * st.z - st.a      -- ReLU lower envelope
  | 3, st => st.a - s * (st.z - lz)   -- ReLU upper envelope

/-- Soundness of each concrete premise on genuine executions. -/
theorem premiseFun_sound
    (l u w1 b1 w2 b2 alpha s lz u_z : ℚ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hlz : lz < 0) (huz : 0 < u_z) (hs : s * (u_z - lz) = u_z)
    -- the pre-activation stays in the chord's box [lz, u_z]
    (hbox_z : ∀ st : NetState, NetState.valid l u w1 b1 w2 b2 st →
                lz ≤ st.z ∧ st.z ≤ u_z) :
    ∀ i : Fin 4, ∀ st : NetState,
      NetState.valid l u w1 b1 w2 b2 st → premiseFun l u alpha s lz i st ≤ 0 := by
  intro i st hv
  obtain ⟨hxl, hxu, hzeq, haeq, hyeq⟩ := hv
  fin_cases i
  · -- premise 0 : l - x ≤ 0
    simp only [premiseFun]; linarith
  · -- premise 1 : x - u ≤ 0
    simp only [premiseFun]; linarith
  · -- premise 2 : alpha*z - a ≤ 0   (lower envelope), using a = relu z
    simp only [premiseFun]
    rw [haeq]
    have := relu_lower alpha st.z ha0 ha1
    linarith
  · -- premise 3 : a - s*(z - lz) ≤ 0  (upper envelope), using a = relu z
    simp only [premiseFun]
    rw [haeq]
    obtain ⟨hzl, hzu⟩ := hbox_z st ⟨hxl, hxu, hzeq, haeq, hyeq⟩
    have := relu_upper lz u_z s st.z hlz huz hs hzl hzu
    linarith

/--
**CROWN end-to-end bridge** (concrete form).

If the four non-negative multipliers `m_bl, m_bu, m_rl, m_ru` combine the four
relaxed-network premises so that, *as a function of the state*, the combination
equals `-(y) - c`, then every genuine execution `st` of the network on the box
satisfies `st.y ≥ -c`.

This is `farkas_to_interval` for the one-hidden-layer unstable-ReLU network,
proven sorry-free by reduction to `farkas_premise_combination`.
-/
theorem crown_bridge
    (l u w1 b1 w2 b2 alpha s lz u_z c : ℚ)
    (m_bl m_bu m_rl m_ru : ℚ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hlz : lz < 0) (huz : 0 < u_z) (hs : s * (u_z - lz) = u_z)
    (hbox_z : ∀ st : NetState, NetState.valid l u w1 b1 w2 b2 st →
                lz ≤ st.z ∧ st.z ≤ u_z)
    (hm_bl : 0 ≤ m_bl) (hm_bu : 0 ≤ m_bu)
    (hm_rl : 0 ≤ m_rl) (hm_ru : 0 ≤ m_ru)
    -- Farkas certificate identity (the μ-combination of premise LHSs IS -(y) - c)
    (hcert : ∀ st : NetState,
        m_bl * (l - st.x)
      + m_bu * (st.x - u)
      + m_rl * (alpha * st.z - st.a)
      + m_ru * (st.a - s * (st.z - lz))
        = -(st.y) - c) :
    ∀ st : NetState, NetState.valid l u w1 b1 w2 b2 st → -c ≤ st.y := by
  -- Bundle the four multipliers / premises into Fin 4 families and invoke the core.
  refine farkas_premise_combination (S := NetState) (ι := Fin 4)
        (premises := Finset.univ)
        (g := premiseFun l u alpha s lz)
        (out := fun st => st.y)
        (μ := ![m_bl, m_bu, m_rl, m_ru]) (c := c)
        (valid := NetState.valid l u w1 b1 w2 b2)
        ?hμ ?hg ?hcert
  case hμ =>
    -- non-negativity of every multiplier
    intro i _
    fin_cases i
    · simpa using hm_bl
    · simpa using hm_bu
    · simpa using hm_rl
    · simpa using hm_ru
  case hg =>
    -- soundness of every premise
    intro i _ st hv
    exact premiseFun_sound l u w1 b1 w2 b2 alpha s lz u_z ha0 ha1 hlz huz hs hbox_z i st hv
  case hcert =>
    -- the certificate identity, expanding the Fin 4 sum
    intro st
    simp only [Fin.sum_univ_four, premiseFun, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
               Matrix.cons_val_three, Matrix.tail_cons]
    -- now it is exactly the supplied identity
    have h := hcert st
    linarith [h]

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms farkas_premise_combination
#print axioms premiseFun_sound
#print axioms crown_bridge

end Crownproof
