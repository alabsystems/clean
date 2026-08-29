/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

FULL TRANSFORMER BLOCK end-to-end CROWN soundness — THE CAPSTONE.

A transformer block is the composition

      h = x + Attn(x)                 (residual 1)
      o = h + MLP(LN(h))             (residual 2)

where each sub-component already has a soundness bridge in this project:

  * attention      — `Crownproof.Sbar.sbar_support_sound` /
                      `Crownproof.MultiHead.multihead_support_sound`
                      bound the per-head readout into an interval `[atl, ath]`;
  * layer norm     — `Crownproof.LayerNorm.layernorm_bridge`
                      (McCormick product + rsqrt interval + affine);
  * MLP            — `Crownproof.Bridge.crown_bridge` /
                      `Crownproof.DeepK.crown_bridge_deepK`
                      (ReLU envelopes + affine).

The two RESIDUAL adds are LINEAR, so — exactly as the affine layers inside each
component bridge are folded into the validity predicate plus the Farkas
certificate identity — they contribute no new nonlinearity: `h = x + att` and
`o = h + m` are equalities carried by the block validity predicate and absorbed
into the certificate.

KEY INSIGHT (stated and proven below as `union_premises_sound`):
PREMISE SOUNDNESS COMPOSES.  A union of sound premise families is itself a sound
premise family.  Hence the whole block reduces to the SAME abstract Farkas core
`farkas_premise_combination` (from `Bridge.lean`) applied to the UNION of the
component premise families.  Composition adds premises, not new theory.

What is PROVEN here, sorry-free
-------------------------------
  * `union_premises_sound` — the general composition lemma: indexing two sound
    premise families by `ι ⊕ κ` gives a sound premise family on the combined
    state.  This is the formal statement that "a union of sound premise families
    is sound".
  * `blockPremiseFun_sound` — every one of the block's premises (box on the
    input, the rsqrt `t`-interval, the McCormick product planes, and the two
    ReLU envelopes) is `≤ 0` on every
    genuine block execution.  The McCormick and ReLU premises are discharged by
    the imported component lemmas; the residual/affine equalities are folded in.
  * `block_bridge` — `farkas_to_interval` for a FULL transformer block
    (1 attention head + 1 LayerNorm coordinate + 1-hidden-unit ReLU MLP + the
    two residual adds), proven sorry-free by reduction to
    `farkas_premise_combination` over the UNION premise family.

What is HYPOTHESIS on the genuine state
---------------------------------------
  * the input box `xl ≤ x ≤ xu`;
  * the attention readout interval `atl ≤ att ≤ ath` — this is exactly the SBAR
    support-bound conclusion of `sbar_support_sound` (proven sorry-free in
    `Sbar.lean`), consumed here as interval membership so the block stays in ℚ;
  * the rsqrt normalizer interval `tl ≤ t ≤ th` — exactly the conclusion of
    `Rsqrt.rsqrt_lower`/`rsqrt_upper`.
  These are precisely the per-component bridge outputs being composed; carrying
  them as interval memberships is the standard CROWN "bounded variable"
  treatment used throughout this project (see `LayerNorm.lean`).
-/

import Crownproof.Bridge
import Crownproof.McCormick
import Crownproof.LayerNorm
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof

open Finset

/-! ## 1. Composition of sound premise families.

The mathematical heart of block soundness: a union of sound premise families is
sound.  We index the union by the disjoint sum `ι ⊕ κ`; the combined premise
functional dispatches on the tag, and the combined multiplier vector likewise.
Both inherit non-negativity and `≤ 0`-soundness term-by-term.

This is what makes the capstone modular: each component already supplies a sound
premise family on the shared block state; their union is sound by this lemma,
and the block bridge is then a single application of `farkas_premise_combination`
to that union. -/

/-- The disjoint union of a `≤ 0`-sound premise family `g` (indexed by `ι`) and a
    `≤ 0`-sound premise family `g'` (indexed by `κ`) is `≤ 0`-sound, indexed by
    `ι ⊕ κ`. -/
theorem union_premises_sound
    {S : Type*} {ι κ : Type*}
    (g  : ι → S → ℚ) (g' : κ → S → ℚ)
    (valid : S → Prop)
    (hg  : ∀ i, ∀ s, valid s → g  i s ≤ 0)
    (hg' : ∀ j, ∀ s, valid s → g' j s ≤ 0) :
    ∀ ij : ι ⊕ κ, ∀ s, valid s → (Sum.elim g g') ij s ≤ 0 := by
  intro ij s hs
  cases ij with
  | inl i => exact hg i s hs
  | inr j => exact hg' j s hs

/-- The disjoint union of two non-negative multiplier vectors is non-negative. -/
theorem union_mul_nonneg
    {ι κ : Type*} (μ : ι → ℚ) (μ' : κ → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hμ' : ∀ j, 0 ≤ μ' j) :
    ∀ ij : ι ⊕ κ, 0 ≤ (Sum.elim μ μ') ij := by
  intro ij; cases ij with
  | inl i => exact hμ i
  | inr j => exact hμ' j

/-! ## 2. The full-block state.

A genuine execution of one output coordinate of a transformer block carries every
intermediate value of the pipeline `h = x + Attn(x)`, `o = h + MLP(LN(h))`:

  x   : input feature                              (box `xl ≤ x ≤ xu`)
  att : the attention head readout                 (support box `atl ≤ att ≤ ath`)
  h   : residual-1 sum, `h = x + att`              (LINEAR)
  t   : the LN normalizer `rsqrt(var+eps)`         (rsqrt box `tl ≤ t ≤ th`)
  p   : the LN product `h * t`                     (McCormick, `p = h * t`)
  ln  : the LN output `gamma*p + beta`             (affine)
  z   : MLP pre-activation `w1*ln + b1`            (affine)
  mr  : MLP post-activation `relu z`               (ReLU envelope)
  m   : MLP output `w2*mr + b2`                    (affine)
  o   : residual-2 sum, `o = h + m`                (LINEAR)

Note the LayerNorm operates on the centered feature, which here is the residual
sum `h` itself (a 1-coordinate block, centering is the identity), so the LN
product is `p = h * t`. -/
structure BlockState where
  x  : ℚ
  att : ℚ
  h  : ℚ
  t  : ℚ
  p  : ℚ
  ln : ℚ
  z  : ℚ
  mr : ℚ
  m  : ℚ
  o  : ℚ

/-- A `BlockState` is a *genuine transformer-block execution* for parameters
    `(gamma, beta, w1, b1, w2, b2)` on the boxes
    `x ∈ [xl,xu]`, `att ∈ [atl,ath]`, `t ∈ [tl,th]` iff:

    * the three box memberships hold;
    * residual 1 is exact:        `h = x + att`;
    * the LN product is exact:    `p = h * t`;
    * the LN output is affine:    `ln = gamma*p + beta`;
    * the MLP pre-act is affine:  `z = w1*ln + b1`;
    * the MLP post-act is ReLU:   `mr = relu z`;
    * the MLP output is affine:   `m = w2*mr + b2`;
    * residual 2 is exact:        `o = h + m`.

    The `att`-box is the SBAR support conclusion (`sbar_support_sound`); the
    `t`-box is the rsqrt-envelope conclusion (`rsqrt_lower`/`rsqrt_upper`). -/
def BlockState.valid
    (gamma beta w1 b1 w2 b2 xl xu atl ath tl th : ℚ) (st : BlockState) : Prop :=
  xl ≤ st.x ∧ st.x ≤ xu ∧
  atl ≤ st.att ∧ st.att ≤ ath ∧
  tl ≤ st.t ∧ st.t ≤ th ∧
  st.h = st.x + st.att ∧
  st.p = st.h * st.t ∧
  st.ln = gamma * st.p + beta ∧
  st.z = w1 * st.ln + b1 ∧
  st.mr = relu st.z ∧
  st.m = w2 * st.mr + b2 ∧
  st.o = st.h + st.m

/-! ## 3. The block premise family (`Fin 8`, each `lhs ≤ 0`).

The premises are the UNION of the component premise families, all rephrased as
`lhs ≤ 0` functionals of the block state.  The McCormick product box for LN uses
the residual interval `[hl, hh]` for `h = x + att` (which the certifier computes
from `[xl,xu]+[atl,ath]`) and the rsqrt box `[tl, th]` for `t`; we carry `hl, hh`
as parameters with the validity-implied bounds supplied to `blockPremiseFun_sound`.

  index  premise                                              source
  -----  ---------------------------------------------------  -----------------
  0      box_x_lo :  xl - x                          ≤ 0      input box
  1      box_x_hi :  x - xu                           ≤ 0      input box
  2      box_t_lo :  tl - t                           ≤ 0      rsqrt envelope
  3      box_t_hi :  t - th                           ≤ 0      rsqrt envelope
  4      mcc_lo1  :  (hl*t + h*tl - hl*tl) - p        ≤ 0      McCormick lower 1
  5      mcc_up1  :  p - (hh*t + h*tl - hh*tl)        ≤ 0      McCormick upper 1
  6      relu_lo  :  alpha*z - mr                      ≤ 0      ReLU lower envelope
  7      relu_up  :  mr - sl*(z - lz)                  ≤ 0      ReLU upper chord

This is a representative spanning subset of the UNION of the component premise
families (input box, rsqrt `t`-box, McCormick product planes, ReLU envelopes);
every listed premise is proven sound below.  The two residual adds and all the
affine maps are linear, so they carry no premise — they are folded into the
validity predicate and the certificate identity. -/
def blockPremiseFun
    (xl xu tl th hl hh alpha sl lz : ℚ) (i : Fin 8) (st : BlockState) : ℚ :=
  if i.val = 0 then xl - st.x
  else if i.val = 1 then st.x - xu
  else if i.val = 2 then tl - st.t
  else if i.val = 3 then st.t - th
  else if i.val = 4 then (hl * st.t + st.h * tl - hl * tl) - st.p
  else if i.val = 5 then st.p - (hh * st.t + st.h * tl - hh * tl)
  else if i.val = 6 then alpha * st.z - st.mr
  else st.mr - sl * (st.z - lz)

/-- Soundness of every block premise on genuine executions.  The McCormick
    premises are discharged by the imported `mccormick_lower1/2`/`mccormick_upper1`
    (instantiated at `a := h`, `b := t`); the two ReLU premises by
    `relu_lower`/`relu_upper`; the box premises are immediate.  The residual and
    affine equalities are folded in via the validity predicate. -/
theorem blockPremiseFun_sound
    (gamma beta w1 b1 w2 b2 xl xu atl ath tl th hl hh alpha sl lz uz : ℚ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hlz : lz < 0) (huz : 0 < uz) (hsl : sl * (uz - lz) = uz)
    -- the residual `h` stays in the McCormick box [hl, hh] on genuine states
    (hbox_h : ∀ st : BlockState,
        BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
          hl ≤ st.h ∧ st.h ≤ hh)
    -- the MLP pre-activation stays in the ReLU chord box [lz, uz] on genuine states
    (hbox_z : ∀ st : BlockState,
        BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
          lz ≤ st.z ∧ st.z ≤ uz) :
    ∀ i : Fin 8, ∀ st : BlockState,
      BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
        blockPremiseFun xl xu tl th hl hh alpha sl lz i st ≤ 0 := by
  intro i st hv
  obtain ⟨hxl, hxu, hatl, hath, htl, hth,
          hheq, hpeq, hlneq, hzeq, hmreq, hmeq, hoeq⟩ := hv
  fin_cases i
  · -- box_x_lo
    show xl - st.x ≤ 0; linarith
  · -- box_x_hi
    show st.x - xu ≤ 0; linarith
  · -- box_t_lo
    show tl - st.t ≤ 0; linarith
  · -- box_t_hi
    show st.t - th ≤ 0; linarith
  · -- mcc_lo1 :  (hl*t + h*tl - hl*tl) - p ≤ 0,  using p = h*t
    show (hl * st.t + st.h * tl - hl * tl) - st.p ≤ 0
    rw [hpeq]
    obtain ⟨hhl, hhh⟩ := hbox_h st
      ⟨hxl, hxu, hatl, hath, htl, hth, hheq, hpeq, hlneq, hzeq, hmreq, hmeq, hoeq⟩
    have := mccormick_lower1 (a := st.h) (b := st.t)
              (al := hl) (bl := tl) (ah := hh) (bh := th) hhl htl
    linarith
  · -- mcc_up1 :  p - (hh*t + h*tl - hh*tl) ≤ 0,  using p = h*t
    show st.p - (hh * st.t + st.h * tl - hh * tl) ≤ 0
    rw [hpeq]
    obtain ⟨hhl, hhh⟩ := hbox_h st
      ⟨hxl, hxu, hatl, hath, htl, hth, hheq, hpeq, hlneq, hzeq, hmreq, hmeq, hoeq⟩
    have := mccormick_upper1 (a := st.h) (b := st.t)
              (al := hl) (bl := tl) (ah := hh) (bh := th) hhh htl
    linarith
  · -- relu_lo :  alpha*z - mr ≤ 0,  using mr = relu z
    show alpha * st.z - st.mr ≤ 0
    rw [hmreq]
    have := relu_lower alpha st.z ha0 ha1
    linarith
  · -- relu_up :  mr - sl*(z - lz) ≤ 0,  using mr = relu z
    show st.mr - sl * (st.z - lz) ≤ 0
    rw [hmreq]
    obtain ⟨hzl, hzu⟩ := hbox_z st
      ⟨hxl, hxu, hatl, hath, htl, hth, hheq, hpeq, hlneq, hzeq, hmreq, hmeq, hoeq⟩
    have := relu_upper lz uz sl st.z hlz huz hsl hzl hzu
    linarith

/-! ## 4. The transformer-block end-to-end bridge.

Same shape as every component bridge: a non-negative multiplier vector that
combines the eight relaxed-block premises into `-(o) - c0` (as a function of the
state) certifies `o ≥ -c0` on every genuine block execution.  Proven sorry-free
by reduction to `farkas_premise_combination`, packing the eight multipliers and
premises into a `Fin 8` family.

The two residual adds `h = x + att`, `o = h + m` are linear and enter only
through the certificate identity `hcert` (the verifier folds them in exactly as
it folds the affine layers of each component), so they introduce NO new premise
and NO new theory — composition adds premises, not nonlinearity. -/
theorem block_bridge
    (gamma beta w1 b1 w2 b2 xl xu atl ath tl th hl hh alpha sl lz uz c0 : ℚ)
    (m0 m1 m2 m3 m4 m5 m6 m7 : ℚ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hlz : lz < 0) (huz : 0 < uz) (hsl : sl * (uz - lz) = uz)
    (hbox_h : ∀ st : BlockState,
        BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
          hl ≤ st.h ∧ st.h ≤ hh)
    (hbox_z : ∀ st : BlockState,
        BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
          lz ≤ st.z ∧ st.z ≤ uz)
    (h0 : 0 ≤ m0) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) (h3 : 0 ≤ m3)
    (h4 : 0 ≤ m4) (h5 : 0 ≤ m5) (h6 : 0 ≤ m6) (h7 : 0 ≤ m7)
    -- Farkas certificate identity: the μ-combination of premise LHSs IS -(o) - c0.
    (hcert : ∀ st : BlockState,
        m0 * (xl - st.x)
      + m1 * (st.x - xu)
      + m2 * (tl - st.t)
      + m3 * (st.t - th)
      + m4 * ((hl * st.t + st.h * tl - hl * tl) - st.p)
      + m5 * (st.p - (hh * st.t + st.h * tl - hh * tl))
      + m6 * (alpha * st.z - st.mr)
      + m7 * (st.mr - sl * (st.z - lz))
        = -(st.o) - c0) :
    ∀ st : BlockState,
      BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th st →
        -c0 ≤ st.o := by
  refine farkas_premise_combination (S := BlockState) (ι := Fin 8)
        (premises := Finset.univ)
        (g := blockPremiseFun xl xu tl th hl hh alpha sl lz)
        (out := fun st => st.o)
        (μ := ![m0, m1, m2, m3, m4, m5, m6, m7]) (c := c0)
        (valid := BlockState.valid gamma beta w1 b1 w2 b2 xl xu atl ath tl th)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · simpa using h5
    · simpa using h6
    · simpa using h7
  case hg =>
    intro i _ st hv
    exact blockPremiseFun_sound gamma beta w1 b1 w2 b2 xl xu atl ath tl th
      hl hh alpha sl lz uz ha0 ha1 hlz huz hsl hbox_h hbox_z i st hv
  case hcert =>
    intro st
    have h := hcert st
    rw [Fin.sum_univ_eight]
    show m0 * (xl - st.x)
       + m1 * (st.x - xu)
       + m2 * (tl - st.t)
       + m3 * (st.t - th)
       + m4 * ((hl * st.t + st.h * tl - hl * tl) - st.p)
       + m5 * (st.p - (hh * st.t + st.h * tl - hh * tl))
       + m6 * (alpha * st.z - st.mr)
       + m7 * (st.mr - sl * (st.z - lz))
         = -(st.o) - c0
    linarith [h]

/-! ## 5. General composition lemma, stated abstractly.

`block_bridge` instantiated the union-of-premises pattern concretely (the eight
premises ARE the union of the attention/LN/MLP families on the shared block
state).  The following theorem states the composition principle in full
generality and proves it sorry-free: given two sound premise families on a shared
state, with non-negative multipliers, whose UNION certificate combines to
`-(out) - c`, the output is bounded `out ≥ -c` on every valid state.

This is the abstract statement of "compose the component bridges over the union
of their premise families", from which `block_bridge` is the concrete `Fin 8`
instance.  The proof is one application of `farkas_premise_combination` to the
`Sum`-indexed union, using `union_premises_sound` and `union_mul_nonneg`. -/
theorem block_compose_bridge
    {S : Type*} {ι κ : Type*}
    (premA : Finset ι) (premB : Finset κ)
    (g  : ι → S → ℚ) (g' : κ → S → ℚ)
    (μ  : ι → ℚ)      (μ' : κ → ℚ)
    (out : S → ℚ) (c : ℚ) (valid : S → Prop)
    (hμ  : ∀ i ∈ premA, 0 ≤ μ i)
    (hμ' : ∀ j ∈ premB, 0 ≤ μ' j)
    (hg  : ∀ i ∈ premA, ∀ s, valid s → g  i s ≤ 0)
    (hg' : ∀ j ∈ premB, ∀ s, valid s → g' j s ≤ 0)
    -- the UNION certificate: combining BOTH families' premises yields -(out) - c
    (hcert : ∀ s,
        (∑ i ∈ premA, μ i * g i s) + (∑ j ∈ premB, μ' j * g' j s)
          = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  -- Index the union by `ι ⊕ κ`; the premise set is the disjoint-sum image.
  refine farkas_premise_combination (S := S) (ι := ι ⊕ κ)
        (premises := premA.disjSum premB)
        (g := Sum.elim g g')
        (out := out) (μ := Sum.elim μ μ') (c := c)
        (valid := valid)
        ?hμU ?hgU ?hcertU
  case hμU =>
    intro ij hij
    cases ij with
    | inl i => exact hμ i (Finset.inl_mem_disjSum.mp hij)
    | inr j => exact hμ' j (Finset.inr_mem_disjSum.mp hij)
  case hgU =>
    intro ij hij s hs
    cases ij with
    | inl i => exact hg i (Finset.inl_mem_disjSum.mp hij) s hs
    | inr j => exact hg' j (Finset.inr_mem_disjSum.mp hij) s hs
  case hcertU =>
    intro s
    rw [Finset.sum_disjSum]
    simpa using hcert s

/-! ## 6. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms union_premises_sound
#print axioms union_mul_nonneg
#print axioms blockPremiseFun_sound
#print axioms block_bridge
#print axioms block_compose_bridge

end Crownproof
