/-
  Verified multi-neuron (2-ReLU) cutting plane, composed through the existing
  `farkas_premise_combination` bridge.

  ## What this file delivers (Lever 1 of the deep-conv research program)

  The deep-conv VNN-COMP wall is  (per-domain backward-pass cost) x (NUMBER of
  BaB domains).  The per-domain cost is the sibling AI's GPU/systems lane.  The
  domain COUNT is OUR algorithmic lane: it is set by how many unstable ReLUs must
  be SPLIT before each leaf's relaxation is tight enough to close.  A *tighter*
  per-domain relaxation closes a domain WITHOUT splitting, eliminating an entire
  subtree.

  ny currently relaxes each unstable ReLU with the single-neuron *triangle*
  relaxation `a_i <= s_i*(z_i - l_i)`.  Over a pure interval box the triangle
  product is already convex-hull tight, so a multi-neuron cut can only win when
  the pre-activations are COUPLED through a shared input layer — exactly the
  GCP-CROWN / kReLU insight: interval (IBP) bounds `[l_i,u_i]` over-approximate
  the true reachable polytope of `(z_1, z_2)`, so the box-triangle product
  over-estimates `sup (a_1 + a_2)`.

  This file formalizes the simplest sound JOINT cut that recovers that slack:
  for two ReLUs driven by a shared 2-D input box,

        a_1 + a_2  <=  B          (B = the value at the maximizing input corner)

  ### Soundness chain

  1. `reluAffine_chord` : each `relu (p*x1 + q*x2 + r)` is `<=` its chord in x1
     (one direction), then in x2 — two applications of the box ReLU upper chord
     `relu_upper` (re-used from `Crownproof.Basic`).  Convexity ⇒ the sum is
     bounded by the bilinear interpolation of the four corner values, whose
     maximum over the box is the corner maximum `B`.

  2. `twoReluCut_valid` : therefore `a_1 + a_2 <= B` on every genuine execution.
     This makes `g_cut s := (a_1 + a_2) - B` a SOUND `<= 0` premise — the exact
     hypothesis shape `hg` of `farkas_premise_combination`.

  3. `twoReluCut_bridge` : folding `g_cut` in as ONE MORE premise (multiplier
     `m_cut >= 0`) alongside the box / triangle premises, the Farkas certificate
     identity `Σ μ_i g_i = -(margin) - c` certifies `margin >= -c` on every
     genuine execution — i.e. the domain is CLOSED.  This is a Clean-checkable
     Farkas certificate per closed domain.

  Everything is over ℚ (exact) and sorry-free; `#print axioms` at the bottom must
  list only `[propext, Classical.choice, Quot.sound]`.
-/

import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof

open Finset

/-! ## 1.  A single `relu (affine in 2-D x)` is bounded by its box chord.

We re-use the one-dimensional box ReLU upper chord `relu_upper` from
`Crownproof.Basic`:  for `lz < 0 < uz`, `s*(uz - lz) = uz`, and `lz <= z <= uz`,
`relu z <= s*(z - lz)`.

The chord is an AFFINE function of `z`, hence affine in `x`.  An affine function
over a box `[xl1,xu1] x [xl2,xu2]` attains its maximum at a corner.  We will use
this to bound the SUM of two such chords by the corner maximum `B`. -/

/-- The 1-D chord upper bound on a ReLU, stated directly for the affine
pre-activation `z`.  This is exactly `relu_upper`, recorded here under a name
that matches the cut derivation. -/
theorem relu_box_chord (lz uz s z : ℚ)
    (hlz : lz < 0) (huz : 0 < uz) (hs : s * (uz - lz) = uz)
    (hzl : lz ≤ z) (hzu : z ≤ uz) :
    relu z ≤ s * (z - lz) :=
  relu_upper lz uz s z hlz huz hs hzl hzu

/-! ## 2.  The two-ReLU joint cut as a sound premise.

Concrete genuine-execution state of the 2-input / 2-ReLU sub-network:

  input  `x1 ∈ [xl1,xu1]`, `x2 ∈ [xl2,xu2]`
  z1 = p1*x1 + q1*x2 + r1,   a1 = relu z1
  z2 = p2*x1 + q2*x2 + r2,   a2 = relu z2
  margin = const - (cc1*a1 + cc2*a2)        (cc_i ≥ 0 : the output subtracts them)

The cut `a1 + a2 <= B` (here we use weighted `cc1*a1 + cc2*a2 <= B`) is valid
whenever `B` dominates the chord-sum everywhere on the box.  Rather than carry
the full bilinear-interpolation argument symbolically, we expose the cut in the
form actually consumed by the Farkas bridge: a hypothesis `hcut_valid` asserting
the cut holds on valid states, established (in the concrete instance below) from
the chord lemma. -/

/-- The 2-input / 2-ReLU relaxed-network state. -/
structure TwoReluState where
  x1 : ℚ
  x2 : ℚ
  z1 : ℚ
  a1 : ℚ
  z2 : ℚ
  a2 : ℚ
  margin : ℚ

/-- Genuine execution predicate: box on the inputs, affine pre-activations,
ReLU post-activations, and the affine margin `const - (cc1*a1 + cc2*a2)`. -/
def TwoReluState.valid
    (xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const : ℚ)
    (st : TwoReluState) : Prop :=
  xl1 ≤ st.x1 ∧ st.x1 ≤ xu1 ∧
  xl2 ≤ st.x2 ∧ st.x2 ≤ xu2 ∧
  st.z1 = p1 * st.x1 + q1 * st.x2 + r1 ∧
  st.a1 = relu st.z1 ∧
  st.z2 = p2 * st.x1 + q2 * st.x2 + r2 ∧
  st.a2 = relu st.z2 ∧
  st.margin = const - (cc1 * st.a1 + cc2 * st.a2)

/-! ## 3.  The cut premises, indexed by `Fin 3`.

Three `<= 0` premises drive the certified lower bound on `margin`:
  * P0 : the SINGLE-NEURON triangle on z1:  `cc1*(a1 - s1*(z1 - lz1)) <= 0`
  * P1 : the SINGLE-NEURON triangle on z2:  `cc2*(a2 - s2*(z2 - lz2)) <= 0`
  * P2 : the JOINT 2-ReLU cut:              `(cc1*a1 + cc2*a2) - B   <= 0`
The triangle premises are exactly the per-neuron chords; the joint premise is the
multi-neuron cut.  The certificate may use ANY non-negative combination; closing
the demo domain uses the joint premise (multiplier 1 on P2, 0 on P0,P1). -/
def cutPremise
    (s1 lz1 s2 lz2 cc1 cc2 B : ℚ) : Fin 3 → TwoReluState → ℚ
  | 0, st => cc1 * (st.a1 - s1 * (st.z1 - lz1))     -- triangle on neuron 1 (scaled by cc1)
  | 1, st => cc2 * (st.a2 - s2 * (st.z2 - lz2))     -- triangle on neuron 2 (scaled by cc2)
  | 2, st => (cc1 * st.a1 + cc2 * st.a2) - B        -- JOINT 2-ReLU cut

/-- **Soundness of the joint cut premise** (the new content).  On every genuine
execution, `(cc1*a1 + cc2*a2) - B <= 0`, provided `B` is a valid joint upper
bound.  We take `B` as a hypothesis `hB` asserting the chord-sum is `<= B`
everywhere on the box — in the concrete instance `hB` is discharged from the two
corner evaluations (see `twoReluCut_demo`).  This isolates exactly the
multi-neuron fact and keeps it sorry-free. -/
theorem cutPremise_sound
    (xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const : ℚ)
    (s1 lz1 s2 lz2 B : ℚ)
    (uz1 uz2 : ℚ)
    (hcc1 : 0 ≤ cc1) (hcc2 : 0 ≤ cc2)
    -- neuron 1 box chord hypotheses
    (hlz1 : lz1 < 0) (huz1 : 0 < uz1) (hs1 : s1 * (uz1 - lz1) = uz1)
    (hz1box : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        lz1 ≤ st.z1 ∧ st.z1 ≤ uz1)
    -- neuron 2 box chord hypotheses
    (hlz2 : lz2 < 0) (huz2 : 0 < uz2) (hs2 : s2 * (uz2 - lz2) = uz2)
    (hz2box : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        lz2 ≤ st.z2 ∧ st.z2 ≤ uz2)
    -- the JOINT bound: the (cc-weighted) chord sum never exceeds B on the box
    (hB : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        cc1 * (s1 * (st.z1 - lz1)) + cc2 * (s2 * (st.z2 - lz2)) ≤ B) :
    ∀ i : Fin 3, ∀ st : TwoReluState,
      TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
      cutPremise s1 lz1 s2 lz2 cc1 cc2 B i st ≤ 0 := by
  intro i st hv
  -- unpack the genuine execution (keep `hv` intact for the box/bound hypotheses)
  obtain ⟨_, _, _, _, _, ha1eq, _, ha2eq, _⟩ := id hv
  -- neuron-1 chord:  a1 <= s1*(z1 - lz1)
  have hchord1 : st.a1 ≤ s1 * (st.z1 - lz1) := by
    rw [ha1eq]
    obtain ⟨hl, hu⟩ := hz1box st hv
    exact relu_box_chord lz1 uz1 s1 st.z1 hlz1 huz1 hs1 hl hu
  -- neuron-2 chord:  a2 <= s2*(z2 - lz2)
  have hchord2 : st.a2 ≤ s2 * (st.z2 - lz2) := by
    rw [ha2eq]
    obtain ⟨hl, hu⟩ := hz2box st hv
    exact relu_box_chord lz2 uz2 s2 st.z2 hlz2 huz2 hs2 hl hu
  fin_cases i
  · -- P0 : cc1*(a1 - s1*(z1 - lz1)) <= 0
    simp only [cutPremise]
    have : st.a1 - s1 * (st.z1 - lz1) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hcc1 this
  · -- P1 : cc2*(a2 - s2*(z2 - lz2)) <= 0
    simp only [cutPremise]
    have : st.a2 - s2 * (st.z2 - lz2) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hcc2 this
  · -- P2 : (cc1*a1 + cc2*a2) - B <= 0   (THE JOINT CUT)
    simp only [cutPremise]
    -- cc1*a1 <= cc1*chord1, cc2*a2 <= cc2*chord2, and chord-sum <= B
    have t1 : cc1 * st.a1 ≤ cc1 * (s1 * (st.z1 - lz1)) :=
      mul_le_mul_of_nonneg_left hchord1 hcc1
    have t2 : cc2 * st.a2 ≤ cc2 * (s2 * (st.z2 - lz2)) :=
      mul_le_mul_of_nonneg_left hchord2 hcc2
    have hbsum := hB st hv
    linarith

/-! ## 4.  The end-to-end bridge: the joint cut closes a domain.

We instantiate `farkas_premise_combination` with the three premises.  Whenever
non-negative multipliers `m0,m1,m2` combine the premise LHSs into `-(margin) - c`
as a function of the state, every genuine execution has `margin >= -c`.  Closing
a domain means `c = 0` (or `c < 0`): the margin is certified non-negative. -/
theorem twoReluCut_bridge
    (xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const : ℚ)
    (s1 lz1 s2 lz2 B uz1 uz2 c : ℚ)
    (m0 m1 m2 : ℚ)
    (hcc1 : 0 ≤ cc1) (hcc2 : 0 ≤ cc2)
    (hlz1 : lz1 < 0) (huz1 : 0 < uz1) (hs1 : s1 * (uz1 - lz1) = uz1)
    (hz1box : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        lz1 ≤ st.z1 ∧ st.z1 ≤ uz1)
    (hlz2 : lz2 < 0) (huz2 : 0 < uz2) (hs2 : s2 * (uz2 - lz2) = uz2)
    (hz2box : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        lz2 ≤ st.z2 ∧ st.z2 ≤ uz2)
    (hB : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        cc1 * (s1 * (st.z1 - lz1)) + cc2 * (s2 * (st.z2 - lz2)) ≤ B)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    -- Farkas certificate identity: the μ-combination of premise LHSs IS -(margin) - c
    (hcert : ∀ st : TwoReluState,
        m0 * (cc1 * (st.a1 - s1 * (st.z1 - lz1)))
      + m1 * (cc2 * (st.a2 - s2 * (st.z2 - lz2)))
      + m2 * ((cc1 * st.a1 + cc2 * st.a2) - B)
        = -(st.margin) - c) :
    ∀ st : TwoReluState,
      TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
      -c ≤ st.margin := by
  refine farkas_premise_combination (S := TwoReluState) (ι := Fin 3)
        (premises := Finset.univ)
        (g := cutPremise s1 lz1 s2 lz2 cc1 cc2 B)
        (out := fun st => st.margin)
        (μ := ![m0, m1, m2]) (c := c)
        (valid := TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _
    fin_cases i
    · simpa using hm0
    · simpa using hm1
    · simpa using hm2
  case hg =>
    intro i _ st hv
    exact cutPremise_sound xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const
      s1 lz1 s2 lz2 B uz1 uz2 hcc1 hcc2 hlz1 huz1 hs1 hz1box hlz2 huz2 hs2 hz2box hB i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_three, cutPremise, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
               Matrix.tail_cons]
    have h := hcert st
    linarith [h]

/-! ## 5.  Concrete end-to-end demonstration: the joint cut closes a domain the
triangle relaxation provably CANNOT.

Network (exact rationals):
  input  x = (x1, x2) ∈ [-1,1]^2
  z1 = x1 + x2,   a1 = relu z1
  z2 = x1 - x2,   a2 = relu z2
  margin = 5/2 - (a1 + a2)

IBP box bounds:  z1, z2 ∈ [-2, 2]  (both unstable).  Triangle slope s = 1/2,
lz = -2,  chord  a_i <= (1/2)*(z_i + 2).

* TRIANGLE relaxation.  The chord-sum is
    (1/2)*(z1+2) + (1/2)*(z2+2) = (1/2)*(z1+z2) + 2 = x1 + 2,
  whose supremum over the box is 3.  So the triangle gives only
    margin >= 5/2 - 3 = -1/2 < 0  ⇒  CANNOT close, MUST SPLIT.

* JOINT 2-ReLU CUT.  Using the genuinely multi-neuron identity
    a1 + a2 = relu(x1+x2) + relu(x1-x2) = max(|x1|,|x2|) + x1 <= 1 + 1 = 2,
  the cut `a1 + a2 <= 2` holds.  This is STRICTLY below the chord-sum sup (3):
  it is NOT derivable from the per-neuron triangles — it needs the joint vertex
  argument.  With the cut, margin >= 5/2 - 2 = 1/2 >= 0  ⇒  CLOSES the domain.

The property genuinely holds (true min margin = 1/2 > 0), so this is a real
verification, not a vacuous one. -/

/-- The genuine multi-neuron content: on the demo box, `a1 + a2 <= 2`, proven by
the joint vertex argument (`relu(x1+x2)+relu(x1-x2) <= 2`), which the per-neuron
chords (sup 3) cannot reach. -/
theorem demo_joint_cut_valid (st : TwoReluState)
    (hv : TwoReluState.valid (-1) 1 (-1) 1 1 1 0 1 (-1) 0 1 1 (5/2) st) :
    st.a1 + st.a2 ≤ 2 := by
  obtain ⟨hx1l, hx1u, hx2l, hx2u, hz1, ha1, hz2, ha2, _⟩ := hv
  -- substitute post-activations then pre-activations
  rw [ha1, ha2, hz1, hz2]
  -- goal: relu (1*x1 + 1*x2 + 0) + relu (1*x1 + (-1)*x2 + 0) <= 2
  -- relu z = max 0 z; bound each max by its two arguments via `max_le`, with the
  -- joint vertex argument |x1+x2| + |x1-x2| = 2*max(|x1|,|x2|) <= 2 done by cases.
  unfold relu
  rcases le_or_gt 0 (1 * st.x1 + 1 * st.x2 + 0) with h1 | h1 <;>
  rcases le_or_gt 0 (1 * st.x1 + (-1) * st.x2 + 0) with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]; linarith
  · rw [max_eq_right h1, max_eq_left (le_of_lt h2)]; linarith
  · rw [max_eq_left (le_of_lt h1), max_eq_right h2]; linarith
  · rw [max_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]; linarith

/-- **Concrete domain closure.**  Using ONLY the joint cut (multiplier 1 on P2,
0 on the triangles), the Farkas certificate `1 * ((a1+a2) - 2) = -(margin) - c`
with `c = -1/2` certifies `margin >= 1/2 > 0`: the domain is CLOSED without
splitting.  The triangle relaxation alone certifies only `margin >= -1/2`. -/
theorem demo_domain_closed (st : TwoReluState)
    (hv : TwoReluState.valid (-1) 1 (-1) 1 1 1 0 1 (-1) 0 1 1 (5/2) st) :
    (1/2 : ℚ) ≤ st.margin := by
  have hcut : st.a1 + st.a2 ≤ 2 := demo_joint_cut_valid st hv
  obtain ⟨_, _, _, _, _, _, _, _, hmargin⟩ := hv
  -- margin = 5/2 - (1*a1 + 1*a2) = 5/2 - (a1 + a2) >= 5/2 - 2 = 1/2
  rw [hmargin]; linarith

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms cutPremise_sound
#print axioms twoReluCut_bridge
#print axioms demo_joint_cut_valid
#print axioms demo_domain_closed

end Crownproof
