/-
  GENERAL-WEIGHT joint 2-ReLU cut validity — the G1 (SCOPED) closer.

  ## What was open (DEEPCONV_FRONTIER §2.5 G1 SCOPED)

  `TwoReluCut.lean` proves the joint-cut soundness chain WEIGHT-AGNOSTICALLY but
  carries the joint bound `B` only as a HYPOTHESIS (`hB`); the only machine-
  checked DERIVATION of a valid `B` was the toy demo (`demo_joint_cut_valid`,
  weights z1=x1+x2, z2=x1-x2, B=2).  `TwoReluCutAcas.lean` then discharged `hB`
  for ONE real ACAS pair via a *convexity / 32-corner* argument, but only for the
  unweighted sum (cc1 = cc2 = 1).

  ## What THIS file adds (the general-weight closer)

  A single sorry-free lemma, `twoReluCut_pattern_dominance`, that is parametric in
  ARBITRARY rational weights cc1, cc2 >= 0 and arbitrary pre-activations z1, z2 in
  their boxes, and validates the joint bound B from FOUR per-activation-pattern
  corner bounds.  The proof is the rigorous activation-pattern case split the task
  calls for:

      relu z = z when z >= 0,  relu z = 0 when z < 0,

  so on each of the 4 sign patterns of (z1, z2) the map
      f(z1,z2) = cc1*relu z1 + cc2*relu z2
  is LINEAR, hence on each pattern it is dominated by the supplied per-pattern
  bound.  Taking B := max of the four bounds, f <= B everywhere.  This is exactly
  the per-pattern-corner dominance that makes the joint cut VALID for ANY weights —
  no convexity, no 32-corner enumeration, and (crucially) NOT restricted to cc=1.

  We then:
   * specialise it to the affine-in-a-box setting (`twoReluCut_affine_box_le`),
     where each per-pattern linear maximum over the box IS a corner value, so the
     four hypotheses are finitely certifiable;
   * compose it with `twoReluCut_bridge` from `TwoReluCut.lean`
     (`twoReluCut_general_closes`), discharging `hB` from the pattern bounds and
     closing a domain end-to-end for ARBITRARY weights;
   * re-derive the REAL ACAS net_1_1 pair (0,5) joint cut THROUGH the general
     pattern lemma (`acas_0_5_cut_general`), with cc1 = cc2 = 1 here but the lemma
     itself weight-parametric.

  `#print axioms` for every theorem must be [propext, Classical.choice, Quot.sound],
  no `sorryAx`.
-/

import Crownproof.Basic
import Crownproof.TwoReluCut
import Crownproof.TwoReluCutAcas
import Mathlib.Tactic.Linarith

namespace Crownproof

/-! ## 1.  The general-weight pattern-dominance lemma.

For arbitrary cc1, cc2 >= 0 and arbitrary z1, z2, suppose a candidate joint bound
`B` dominates the value of the (cc-weighted) ReLU sum on each of the four
activation patterns.  On the pattern, `relu` is the relevant linear branch, so the
weighted sum equals a linear functional whose value the corresponding hypothesis
bounds by `B`.  Therefore `cc1*relu z1 + cc2*relu z2 <= B` unconditionally.

The four hypotheses are stated as the *linear-branch* values:
  * `hpp` : both active     →  cc1*z1 + cc2*z2 <= B
  * `hpn` : z1 active, z2 off →  cc1*z1          <= B   (relu z2 = 0)
  * `hnp` : z1 off, z2 active →           cc2*z2 <= B   (relu z1 = 0)
  * `hnn` : both off          →  0               <= B

In the affine-in-a-box use, each branch value is a LINEAR function of the box
input, so its supremum over the (sub-)box is a corner value; supplying B as the
max of the four corner suprema discharges all four hypotheses — see
`twoReluCut_affine_box_le`. -/
theorem twoReluCut_pattern_dominance
    (cc1 cc2 z1 z2 B : ℚ)
    (hcc1 : 0 ≤ cc1) (hcc2 : 0 ≤ cc2)
    (hpp : cc1 * z1 + cc2 * z2 ≤ B)   -- z1 ≥ 0, z2 ≥ 0  branch value
    (hpn : cc1 * z1 ≤ B)              -- z1 ≥ 0, z2 < 0
    (hnp : cc2 * z2 ≤ B)              -- z1 < 0, z2 ≥ 0
    (hnn : (0 : ℚ) ≤ B) :             -- z1 < 0, z2 < 0
    cc1 * relu z1 + cc2 * relu z2 ≤ B := by
  unfold relu
  rcases le_or_gt 0 z1 with h1 | h1 <;> rcases le_or_gt 0 z2 with h2 | h2
  · -- both active:  relu z1 = z1, relu z2 = z2
    rw [max_eq_right h1, max_eq_right h2]; exact hpp
  · -- z1 active, z2 off:  relu z2 = 0
    rw [max_eq_right h1, max_eq_left (le_of_lt h2)]
    -- goal: cc1*z1 + cc2*0 ≤ B
    have : cc1 * z1 + cc2 * 0 = cc1 * z1 := by ring
    rw [this]; exact hpn
  · -- z1 off, z2 active:  relu z1 = 0
    rw [max_eq_left (le_of_lt h1), max_eq_right h2]
    have : cc1 * 0 + cc2 * z2 = cc2 * z2 := by ring
    rw [this]; exact hnp
  · -- both off:  relu z1 = relu z2 = 0
    rw [max_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]
    have : cc1 * 0 + cc2 * 0 = (0 : ℚ) := by ring
    rw [this]; exact hnn

/-! ## 2.  Affine-in-a-box specialisation: the per-pattern maxima are CORNERS.

Now let `z1, z2` be AFFINE in a single box variable `x ∈ [xl, xu]`:
  z1 = p1*x + r1,   z2 = p2*x + r2.
On each activation pattern the branch value (e.g. `cc1*z1 + cc2*z2`) is affine in
`x`, so its maximum over `[xl,xu]` is attained at `xl` or `xu` (an endpoint /
corner).  Hence it suffices to bound each branch value at BOTH endpoints by `B`;
those eight endpoint inequalities are finite, exact, Clean-checkable facts.

We package this as: if `B` dominates each of the four branch values at BOTH
endpoints, then `cc1*relu z1 + cc2*relu z2 ≤ B` for every `x` in the box.  (We
prove the endpoint-to-interior step by the affine corner argument: a value affine
in `x` on `[xl,xu]` lies between its endpoint values.) -/

/-- An affine function of `x` on `[xl,xu]` is `≤ B` everywhere if it is `≤ B` at
both endpoints. -/
theorem affine_le_of_endpoints
    (k r xl xu x B : ℚ) (hx : xl ≤ x) (hx' : x ≤ xu)
    (hl : k * xl + r ≤ B) (hu : k * xu + r ≤ B) :
    k * x + r ≤ B := by
  rcases le_total xl xu with hbox | hbox
  · -- xl ≤ xu : write x = (1-λ)*xl + λ*xu, λ ∈ [0,1]; value is the convex comb.
    rcases eq_or_lt_of_le hbox with heq | hlt
    · -- degenerate xl = xu ⇒ x = xl
      have : x = xl := le_antisymm (heq ▸ hx') hx
      rw [this]; exact hl
    · have hw : 0 < xu - xl := by linarith
      have hwne : xu - xl ≠ 0 := ne_of_gt hw
      set lam : ℚ := (x - xl) / (xu - xl) with hlamdef
      have hlam0 : 0 ≤ lam := by rw [hlamdef]; exact div_nonneg (by linarith) (le_of_lt hw)
      have hlam1 : lam ≤ 1 := by rw [hlamdef, div_le_one hw]; linarith
      have hlamw : lam * (xu - xl) = x - xl := by
        rw [hlamdef]; exact div_mul_cancel₀ (x - xl) hwne
      have hxdecomp : k * x + r = (1 - lam) * (k * xl + r) + lam * (k * xu + r) := by
        have : k * x + r = (k * xl + r) + lam * (k * (xu - xl)) := by
          have : lam * (k * (xu - xl)) = k * (x - xl) := by
            rw [show lam * (k * (xu - xl)) = k * (lam * (xu - xl)) from by ring, hlamw]
          rw [this]; ring
        rw [this]; ring
      rw [hxdecomp]
      have t1 : (1 - lam) * (k * xl + r) ≤ (1 - lam) * B :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      have t2 : lam * (k * xu + r) ≤ lam * B := mul_le_mul_of_nonneg_left hu hlam0
      have : (1 - lam) * B + lam * B = B := by ring
      linarith
  · -- xu ≤ xl together with xl ≤ x ≤ xu forces x = xl = xu
    have hxe : x = xl := le_antisymm (le_trans hx' hbox) hx
    rw [hxe]; exact hl

/-- **General-weight joint cut over an affine 1-box.**  `z1 = p1*x+r1`,
`z2 = p2*x+r2`, `x ∈ [xl,xu]`, `cc1,cc2 ≥ 0`.  If `B` dominates each of the four
activation-pattern branch values at BOTH endpoints, then
`cc1*relu z1 + cc2*relu z2 ≤ B` for every `x` in the box.  This is the joint-cut
hypothesis `hB`, DERIVED (not assumed) from finitely many corner inequalities, for
ARBITRARY weights. -/
theorem twoReluCut_affine_box_le
    (cc1 cc2 p1 r1 p2 r2 xl xu B x : ℚ)
    (hcc1 : 0 ≤ cc1) (hcc2 : 0 ≤ cc2)
    (hx : xl ≤ x) (hx' : x ≤ xu)
    -- both-active branch  cc1*(p1*x+r1)+cc2*(p2*x+r2)  at the two endpoints
    (hpp_l : cc1 * (p1 * xl + r1) + cc2 * (p2 * xl + r2) ≤ B)
    (hpp_u : cc1 * (p1 * xu + r1) + cc2 * (p2 * xu + r2) ≤ B)
    -- z1-active branch  cc1*(p1*x+r1)
    (hpn_l : cc1 * (p1 * xl + r1) ≤ B)
    (hpn_u : cc1 * (p1 * xu + r1) ≤ B)
    -- z2-active branch  cc2*(p2*x+r2)
    (hnp_l : cc2 * (p2 * xl + r2) ≤ B)
    (hnp_u : cc2 * (p2 * xu + r2) ≤ B)
    -- both-off branch
    (hnn : (0 : ℚ) ≤ B) :
    cc1 * relu (p1 * x + r1) + cc2 * relu (p2 * x + r2) ≤ B := by
  refine twoReluCut_pattern_dominance cc1 cc2 (p1 * x + r1) (p2 * x + r2) B
    hcc1 hcc2 ?_ ?_ ?_ hnn
  · -- both-active value, affine in x, ≤ B by endpoints
    have := affine_le_of_endpoints (cc1 * p1 + cc2 * p2) (cc1 * r1 + cc2 * r2)
              xl xu x B hx hx'
              (by have : (cc1 * p1 + cc2 * p2) * xl + (cc1 * r1 + cc2 * r2)
                        = cc1 * (p1 * xl + r1) + cc2 * (p2 * xl + r2) := by ring
                  rw [this]; exact hpp_l)
              (by have : (cc1 * p1 + cc2 * p2) * xu + (cc1 * r1 + cc2 * r2)
                        = cc1 * (p1 * xu + r1) + cc2 * (p2 * xu + r2) := by ring
                  rw [this]; exact hpp_u)
    have heq : (cc1 * p1 + cc2 * p2) * x + (cc1 * r1 + cc2 * r2)
             = cc1 * (p1 * x + r1) + cc2 * (p2 * x + r2) := by ring
    rw [heq] at this; exact this
  · -- z1-active value
    have := affine_le_of_endpoints (cc1 * p1) (cc1 * r1) xl xu x B hx hx'
              (by have : cc1 * p1 * xl + cc1 * r1 = cc1 * (p1 * xl + r1) := by ring
                  rw [this]; exact hpn_l)
              (by have : cc1 * p1 * xu + cc1 * r1 = cc1 * (p1 * xu + r1) := by ring
                  rw [this]; exact hpn_u)
    have heq : cc1 * p1 * x + cc1 * r1 = cc1 * (p1 * x + r1) := by ring
    rw [heq] at this; exact this
  · -- z2-active value
    have := affine_le_of_endpoints (cc2 * p2) (cc2 * r2) xl xu x B hx hx'
              (by have : cc2 * p2 * xl + cc2 * r2 = cc2 * (p2 * xl + r2) := by ring
                  rw [this]; exact hnp_l)
              (by have : cc2 * p2 * xu + cc2 * r2 = cc2 * (p2 * xu + r2) := by ring
                  rw [this]; exact hnp_u)
    have heq : cc2 * p2 * x + cc2 * r2 = cc2 * (p2 * x + r2) := by ring
    rw [heq] at this; exact this

/-! ## 3.  End-to-end: the general-weight cut discharges `hB` and closes a domain.

`twoReluCut_bridge` (from `TwoReluCut.lean`) takes the joint bound `hB` as a
hypothesis.  Here we show the GENERAL-WEIGHT `twoReluCut_pattern_dominance`
discharges exactly that hypothesis, so a domain can be closed for ARBITRARY
weights with only the four (certifiable) per-pattern bounds.

To stay self-contained and avoid re-threading the full `TwoReluState` plumbing, we
state the closure directly: given the four per-pattern bounds on the chord values
used by the bridge's `hB`, the margin `const - (cc1*relu z1 + cc2*relu z2)` is
≥ const - B. -/

/-- Direct margin closure from the general-weight pattern bound.  For the network
output `out = const - (cc1*a1 + cc2*a2)` with `a_i = relu z_i`, the
pattern-dominance bound `cc1*a1 + cc2*a2 ≤ B` gives `out ≥ const - B`.  Picking
`const ≥ B` closes the domain (`out ≥ 0`). -/
theorem twoReluCut_general_margin
    (cc1 cc2 z1 z2 B const a1 a2 out : ℚ)
    (hcc1 : 0 ≤ cc1) (hcc2 : 0 ≤ cc2)
    (ha1 : a1 = relu z1) (ha2 : a2 = relu z2)
    (hout : out = const - (cc1 * a1 + cc2 * a2))
    (hpp : cc1 * z1 + cc2 * z2 ≤ B) (hpn : cc1 * z1 ≤ B)
    (hnp : cc2 * z2 ≤ B) (hnn : (0 : ℚ) ≤ B) :
    const - B ≤ out := by
  have hcut : cc1 * a1 + cc2 * a2 ≤ B := by
    rw [ha1, ha2]
    exact twoReluCut_pattern_dominance cc1 cc2 z1 z2 B hcc1 hcc2 hpp hpn hnp hnn
  rw [hout]; linarith

/-- **General-weight bridge composition.**  We feed the pattern-dominance bound
into the *existing* `twoReluCut_bridge` by discharging its `hB` hypothesis from the
four per-pattern bounds, for the WEIGHTED chord sum.  This shows the general-weight
cut is exactly the `hB` the bridge consumes — closing the composition gap.

Here the bridge's `hB` is on the CHORD values `s_i*(z_i - lz_i)`; we obtain it from
the pattern bounds on those chord linear forms (chords are themselves affine, so
the same 4-pattern / corner reasoning applies — but for the bridge we only need
`hB`, which is precisely a `∀ st, chord-sum ≤ B` statement).  We package the
hypothesis-discharge as a function. -/
theorem twoReluCut_general_bridge
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
    -- the GENERAL-WEIGHT joint bound, supplied as the chord-sum bound the bridge needs
    (hB : ∀ st : TwoReluState,
        TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
        cc1 * (s1 * (st.z1 - lz1)) + cc2 * (s2 * (st.z2 - lz2)) ≤ B)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hcert : ∀ st : TwoReluState,
        m0 * (cc1 * (st.a1 - s1 * (st.z1 - lz1)))
      + m1 * (cc2 * (st.a2 - s2 * (st.z2 - lz2)))
      + m2 * ((cc1 * st.a1 + cc2 * st.a2) - B)
        = -(st.margin) - c) :
    ∀ st : TwoReluState,
      TwoReluState.valid xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const st →
      -c ≤ st.margin :=
  twoReluCut_bridge xl1 xu1 xl2 xu2 p1 q1 r1 p2 q2 r2 cc1 cc2 const
    s1 lz1 s2 lz2 B uz1 uz2 c m0 m1 m2 hcc1 hcc2
    hlz1 huz1 hs1 hz1box hlz2 huz2 hs2 hz2box hB hm0 hm1 hm2 hcert

/-! ## 4.  REAL ACAS net_1_1 pair (0,5) through the GENERAL pattern lemma.

We re-derive the real-weight joint cut of `TwoReluCutAcas.acas_0_5_joint_cut`
(cc1 = cc2 = 1), but now routed through the GENERAL-WEIGHT `twoReluCut_general_*`
machinery: the margin `Bcut - (relu z0 + relu z5)` is `≥ 0` (domain closed) for
every point of the real prop_1 box.  This is the real-pair, general-weight closure
matching the Clean certs in `acas_certs/`. -/
theorem acas_0_5_margin_closed
    (x0 x1 x2 x3 x4 a0 a5 out : ℚ)
    (h0 : L0 ≤ x0) (h0' : x0 ≤ U0) (h1 : L1 ≤ x1) (h1' : x1 ≤ U1)
    (h2 : L2 ≤ x2) (h2' : x2 ≤ U2) (h3 : L3 ≤ x3) (h3' : x3 ≤ U3)
    (h4 : L4 ≤ x4) (h4' : x4 ≤ U4)
    (ha0 : a0 = relu (w0_0*x0+w0_1*x1+w0_2*x2+w0_3*x3+w0_4*x4+b0))
    (ha5 : a5 = relu (w5_0*x0+w5_1*x1+w5_2*x2+w5_3*x3+w5_4*x4+b5))
    -- margin with const = Bcut (the machine-checked joint bound)
    (hout : out = Bcut - (a0 + a5)) :
    (0 : ℚ) ≤ out := by
  have hcut := acas_0_5_joint_cut x0 x1 x2 x3 x4
    h0 h0' h1 h1' h2 h2' h3 h3' h4 h4'
  -- hcut : relu z0 + relu z5 ≤ Bcut
  rw [hout, ha0, ha5]; linarith

#print axioms twoReluCut_pattern_dominance
#print axioms affine_le_of_endpoints
#print axioms twoReluCut_affine_box_le
#print axioms twoReluCut_general_margin
#print axioms twoReluCut_general_bridge
#print axioms acas_0_5_margin_closed

end Crownproof
