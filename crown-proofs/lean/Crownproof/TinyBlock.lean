/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

FIRST END-TO-END KERNEL-CHECKED TRANSFORMER-BLOCK BOUND.

This file CERTIFIES, kernel-checked and sorry-free, a numeric output bound on a
CONCRETE tiny-but-real transformer block over an input box, by COMPOSING the
already-proven component soundness lemmas of this project:

  * attention      `Crownproof.sbar_support_sound`   (LP weak duality, Sbar.lean)
  * LayerNorm prod `Crownproof.mccormick_lower1 / _upper1`  (McCormick.lean)
  * MLP ReLU       `Crownproof.relu_lower / relu_upper`     (Basic.lean)

into a single Farkas certificate, discharged by the abstract Farkas core
`Crownproof.farkas_premise_combination` (Bridge.lean) — exactly the entailment
that Clean's kernel axiom `farkas_to_interval` (T09) axiomatises.

The block (single output coordinate; rationals throughout)
----------------------------------------------------------
      att = Σ_j g_j p_j              single-head self-attention readout
      h   = x + att                  residual 1
      p   = h * t                    LayerNorm product (1-coord centering = id)
      ln  = γ·p + β                  LayerNorm affine
      z   = w1·ln + b1               MLP pre-activation
      mr  = relu z                   MLP ReLU
      m   = w2·mr + b2               MLP output
      o   = h + m                    residual 2

Concrete parameters
-------------------
  input box        x  ∈ [0, 1]
  attention head   g = (1/2, −1/2) over a 2-position box-truncated simplex
                   ⇒ att = p₀ − 1/2 ∈ [−1/2, 1/2]   (certified by SBAR below)
  rsqrt normalizer t  ∈ [1/2, 1]    (rsqrt envelope interval, see note ‡)
  γ = 1, β = 0, w1 = 1, b1 = −1/2, w2 = 1, b2 = 0

Derived ranges (computed by the certifier, re-derived in Lean below):
  residual         h  ∈ [−1/2, 3/2]
  ReLU pre-act     z  ∈ [−1, 1]      (UNSTABLE: l<0<u — needs the upper chord)

MAIN RESULTS (both sorry-free, both TIGHT — see the achieving corners noted)
----------------------------------------------------------------------------
  `tinyblock_lower` :  o ≥ −1/2     (tight at x=0, att=−1/2, t=1/2)
  `tinyblock_upper` :  o ≤ 5/2      (tight at x=1, att=+1/2, t=1)

The upper bound is the non-trivial composition: its Farkas certificate uses the
ReLU UPPER chord (`relu_upper`, slope 1/2 on z∈[−1,1]) chained through the
McCormick UPPER plane (`mccormick_upper1` for p=h·t), i.e. it genuinely composes
the LayerNorm-product and MLP-ReLU relaxations.  The attention interval feeding
both bounds is the SBAR support conclusion `sbar_support_sound`, proven here on
the concrete head (`att_lower_cert` / `att_upper_cert`).

What is PROVEN vs. HYPOTHESIS
----------------------------
  PROVEN, sorry-free, by composing the imported lemmas:
    – the attention interval att ∈ [−1/2,1/2]  (two `sbar_support_sound` calls);
    – every premise of the block (boxes, McCormick planes, ReLU envelopes,
      and the affine/residual equalities) is `≤ 0` on every genuine execution;
    – the two Farkas certificates combine those premises to `−o − c` resp.
      `o − c`, giving the kernel-checked bounds via `farkas_premise_combination`.
  HYPOTHESIS carried on the genuine state (standard CROWN bounded-variable
  treatment, identical to LayerNorm.lean / Block.lean):
    – ‡ the rsqrt normalizer membership t ∈ [1/2,1].  This is precisely the
      conclusion of `Crownproof.rsqrt_lower`/`rsqrt_upper` (proven sorry-free over
      ℝ in Rsqrt.lean) transported to its rational endpoints; we consume it as
      interval membership so the whole composition stays in ℚ.  Everything else
      — including the att interval — is DERIVED, not assumed.

`#print axioms` at the bottom must show exactly [propext, Classical.choice,
Quot.sound] and NEVER sorryAx.
-/

import Crownproof.Bridge          -- farkas_premise_combination, relu, NetState
import Crownproof.McCormick        -- mccormick_lower1 / _upper1
import Crownproof.Sbar             -- sbar_support_sound (attention)
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof.TinyBlock

open Crownproof Finset

/-! ## 0. Concrete attention head: the SBAR support interval `att ∈ [−1/2, 1/2]`.

The head has two positions, scores `g = (1/2, −1/2)`, and a box-truncated simplex
`p₀ + p₁ = 1`, `0 ≤ pⱼ ≤ 1`.  The readout is `att = Σⱼ gⱼ pⱼ = p₀ − 1/2`.
We certify `att ≤ 1/2` and `−att ≤ 1/2` by two instances of `sbar_support_sound`,
exactly as `MultiHead.lean` does, but on closed rational data. -/

/-- The two scores `g₀ = 1/2`, `g₁ = −1/2`. -/
def gScore : Fin 2 → ℚ := ![ (1/2 : ℚ), (-1/2 : ℚ) ]

/-- Per-position lower box `p_lo = (0,0)`. -/
def pLo : Fin 2 → ℚ := ![ (0 : ℚ), (0 : ℚ) ]

/-- Per-position upper box `p_hi = (1,1)`. -/
def pHi : Fin 2 → ℚ := ![ (1 : ℚ), (1 : ℚ) ]

/-- **SBAR upper certificate**: for any feasible simplex weighting `p` of this
    head, the readout `Σ gⱼ pⱼ ≤ 1/2`.  Dual `λ = 1/2`, `μ⁺ = 0`, `μ⁻ = (0,1)`. -/
theorem att_upper_cert
    (p : Fin 2 → ℚ)
    (hlo : ∀ j ∈ (Finset.univ : Finset (Fin 2)), pLo j ≤ p j)
    (hhi : ∀ j ∈ (Finset.univ : Finset (Fin 2)), p j ≤ pHi j)
    (hsx : ∑ j ∈ (Finset.univ : Finset (Fin 2)), p j = 1) :
    (∑ j ∈ (Finset.univ : Finset (Fin 2)), gScore j * p j) ≤ (1/2 : ℚ) := by
  have h := sbar_support_sound (Finset.univ : Finset (Fin 2))
      gScore p pLo pHi
      (μp := ![ (0:ℚ), 0 ]) (μm := ![ (0:ℚ), 1 ]) (lam := (1/2 : ℚ))
      (by intro j _; fin_cases j <;> norm_num)
      (by intro j _; fin_cases j <;> norm_num)
      hlo hhi hsx
      (by intro j _; fin_cases j <;> simp [gScore] <;> norm_num)
  -- the dual value simplifies to  1/2 + 0 − 0 = 1/2
  simpa [pHi, pLo, Fin.sum_univ_two] using h

/-- **SBAR lower certificate**: `Σ gⱼ pⱼ ≥ −1/2`, via SBAR on the negated scores.
    Dual `λ = 1/2`, `ν⁺ = 0`, `ν⁻ = (1,0)`. -/
theorem att_lower_cert
    (p : Fin 2 → ℚ)
    (hlo : ∀ j ∈ (Finset.univ : Finset (Fin 2)), pLo j ≤ p j)
    (hhi : ∀ j ∈ (Finset.univ : Finset (Fin 2)), p j ≤ pHi j)
    (hsx : ∑ j ∈ (Finset.univ : Finset (Fin 2)), p j = 1) :
    (-1/2 : ℚ) ≤ (∑ j ∈ (Finset.univ : Finset (Fin 2)), gScore j * p j) := by
  have h := sbar_support_sound (Finset.univ : Finset (Fin 2))
      (fun j => - gScore j) p pLo pHi
      (μp := ![ (0:ℚ), 0 ]) (μm := ![ (1:ℚ), 0 ]) (lam := (1/2 : ℚ))
      (by intro j _; fin_cases j <;> norm_num)
      (by intro j _; fin_cases j <;> norm_num)
      hlo hhi hsx
      (by intro j _; fin_cases j <;> simp [gScore] <;> norm_num)
  -- h :  Σ (−g) p ≤ 1/2,  i.e.  −(Σ g p) ≤ 1/2,  i.e.  Σ g p ≥ −1/2.
  have hneg : (∑ j ∈ (Finset.univ : Finset (Fin 2)), (fun j => - gScore j) j * p j)
      = - (∑ j ∈ (Finset.univ : Finset (Fin 2)), gScore j * p j) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hneg] at h
  have hval : (1/2 : ℚ) + (∑ j ∈ (Finset.univ : Finset (Fin 2)), (![ (0:ℚ),0 ] : Fin 2 → ℚ) j * pHi j)
                  - (∑ j ∈ (Finset.univ : Finset (Fin 2)), (![ (1:ℚ),0 ] : Fin 2 → ℚ) j * pLo j)
              = (1/2 : ℚ) := by
    simp [pHi, pLo, Fin.sum_univ_two]
  rw [hval] at h
  linarith

/-! ## 1. The concrete tiny-block state and its genuine-execution predicate.

A `TBState` carries every intermediate of the pipeline; `att` is the attention
readout (already an SBAR-bounded variable), `t` the rsqrt normalizer (rsqrt
envelope interval, ‡).  All other fields are tied by exact equalities. -/
structure TBState where
  p0  : ℚ        -- attention weight on position 0 (simplex variable)
  p1  : ℚ        -- attention weight on position 1
  x   : ℚ        -- input feature
  att : ℚ        -- attention readout  Σ g p
  h   : ℚ        -- residual 1   h = x + att
  t   : ℚ        -- rsqrt normalizer
  p   : ℚ        -- LN product   p = h * t
  ln  : ℚ        -- LN affine    ln = γ p + β
  z   : ℚ        -- MLP pre-act  z = w1 ln + b1
  mr  : ℚ        -- MLP ReLU     mr = relu z
  m   : ℚ        -- MLP output   m = w2 mr + b2
  o   : ℚ        -- residual 2   o = h + m

/-- A `TBState` is a *genuine execution* of the concrete tiny block iff:
    * the input box `0 ≤ x ≤ 1` holds;
    * the attention weighting is a feasible box-truncated simplex
      (`p0,p1 ∈ [0,1]`, `p0 + p1 = 1`) and `att` is its readout `Σ g p`;
    * the rsqrt normalizer membership `1/2 ≤ t ≤ 1` holds (‡);
    * every structural equality of the pipeline holds. -/
def TBState.valid (st : TBState) : Prop :=
  (0 : ℚ) ≤ st.x ∧ st.x ≤ 1 ∧
  (0 : ℚ) ≤ st.p0 ∧ st.p0 ≤ 1 ∧
  (0 : ℚ) ≤ st.p1 ∧ st.p1 ≤ 1 ∧
  st.p0 + st.p1 = 1 ∧
  st.att = (1/2) * st.p0 + (-1/2) * st.p1 ∧
  (1/2 : ℚ) ≤ st.t ∧ st.t ≤ 1 ∧
  st.h  = st.x + st.att ∧
  st.p  = st.h * st.t ∧
  st.ln = (1 : ℚ) * st.p + 0 ∧
  st.z  = (1 : ℚ) * st.ln + (-1/2) ∧
  st.mr = relu st.z ∧
  st.m  = (1 : ℚ) * st.mr + 0 ∧
  st.o  = st.h + st.m

/-! ### Derived interval facts on a genuine execution.

These are the `hbox_h` / `hbox_z` style facts that the component bridges require
as hypotheses; here they are PROVEN from the input box + the SBAR att interval +
the rsqrt t interval + McCormick, *not* assumed. -/

/-- On a genuine execution, the SBAR readout lies in `[−1/2, 1/2]`. -/
theorem att_box (st : TBState) (hv : st.valid) :
    (-1/2 : ℚ) ≤ st.att ∧ st.att ≤ (1/2 : ℚ) := by
  obtain ⟨_, _, hp0l, hp0u, hp1l, hp1u, hsx, hatt,
          _, _, _, _, _, _, _, _, _⟩ := hv
  -- realise att as the SBAR objective Σ g p of the 2-point head
  set p : Fin 2 → ℚ := ![ st.p0, st.p1 ] with hp
  have hsum : (∑ j ∈ (Finset.univ : Finset (Fin 2)), gScore j * p j)
            = st.att := by
    have : (∑ j ∈ (Finset.univ : Finset (Fin 2)), gScore j * p j)
         = (1/2) * st.p0 + (-1/2) * st.p1 := by
      simp only [gScore, hp, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
    rw [this, hatt]
  have hlo : ∀ j ∈ (Finset.univ : Finset (Fin 2)), pLo j ≤ p j := by
    intro j _; fin_cases j
    · simpa [pLo, hp] using hp0l
    · simpa [pLo, hp] using hp1l
  have hhi : ∀ j ∈ (Finset.univ : Finset (Fin 2)), p j ≤ pHi j := by
    intro j _; fin_cases j
    · simpa [pHi, hp] using hp0u
    · simpa [pHi, hp] using hp1u
  have hsxp : ∑ j ∈ (Finset.univ : Finset (Fin 2)), p j = 1 := by
    simp only [hp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]; exact hsx
  refine ⟨?_, ?_⟩
  · have := att_lower_cert p hlo hhi hsxp; rw [hsum] at this; exact this
  · have := att_upper_cert p hlo hhi hsxp; rw [hsum] at this; exact this

/-- On a genuine execution, the residual `h = x + att` lies in `[−1/2, 3/2]`. -/
theorem h_box (st : TBState) (hv : st.valid) :
    (-1/2 : ℚ) ≤ st.h ∧ st.h ≤ (3/2 : ℚ) := by
  have ⟨hal, hau⟩ := att_box st hv
  obtain ⟨hxl, hxu, _, _, _, _, _, _, _, _, hheq, _, _, _, _, _, _⟩ := hv
  rw [hheq]; constructor <;> linarith

/-- On a genuine execution, the MLP pre-activation `z` lies in `[−1, 1]`.
    This needs the McCormick product range for `p = h·t`, hence the imported
    `mccormick_lower1`/`mccormick_upper1` instantiated at `(h, t)`. -/
theorem z_box (st : TBState) (hv : st.valid) :
    (-1 : ℚ) ≤ st.z ∧ st.z ≤ (1 : ℚ) := by
  have ⟨hhl, hhh⟩ := h_box st hv
  obtain ⟨_, _, _, _, _, _, _, _, htl, hth, _, hpeq, hlneq, hzeq, _, _, _⟩ := hv
  -- p = h*t, with h ∈ [-1/2,3/2], t ∈ [1/2,1].
  -- lower:  mccormick_lower1 :  hl*t + h*tl - hl*tl ≤ h*t   (hl=-1/2, tl=1/2)
  -- upper:  mccormick_upper1 :  h*t ≤ hh*t + h*tl - hh*tl   (hh=3/2,  tl=1/2)
  have hlo := mccormick_lower1 (a := st.h) (b := st.t)
      (al := (-1/2 : ℚ)) (bl := (1/2 : ℚ)) (ah := (3/2 : ℚ)) (bh := (1 : ℚ)) hhl htl
  have hup := mccormick_upper1 (a := st.h) (b := st.t)
      (al := (-1/2 : ℚ)) (bl := (1/2 : ℚ)) (ah := (3/2 : ℚ)) (bh := (1 : ℚ)) hhh htl
  -- z = ln - 1/2 = p - 1/2 = h*t - 1/2
  rw [hzeq, hlneq, hpeq]
  -- now goal is in h*t; bound h*t using the McCormick planes and the boxes on h,t.
  constructor
  · -- lower: h*t ≥ (-1/2)*t + h*(1/2) - (-1/2)*(1/2) ; with t≥1/2,h≥-1/2 ⇒ ≥ -1/2 ⇒ z≥-1
    nlinarith [hlo, hhl, hhh, htl, hth]
  · -- upper: h*t ≤ (3/2)*t + h*(1/2) - (3/2)*(1/2) ; with t≤1,h≤3/2 ⇒ ≤ 3/2 ⇒ z≤1
    nlinarith [hup, hhl, hhh, htl, hth]

/-! ## 2. The block premise family (`Fin 16`, each `lhs ≤ 0`).

The premises are the UNION of the four component families, normalised to
`lhs ≤ 0`, plus the affine/residual equalities split into `±`-pairs so the
Farkas certificate can fold them in (an equality `E = 0` contributes the two
sound premises `E ≤ 0` and `−E ≤ 0`):

  idx  premise                                    source
  ---  -----------------------------------------  ------------------------------
   0   0 − x                          ≤ 0          input box lo
   1   x − 1                          ≤ 0          input box hi
   2   (−1/2) − att                   ≤ 0          SBAR att box lo (att_box)
   3   att − (1/2)                    ≤ 0          SBAR att box hi (att_box)
   4   (1/2) − t                      ≤ 0          rsqrt box lo (‡)
   5   t − 1                          ≤ 0          rsqrt box hi (‡)
   6   ((−1/2)t + h(1/2) − (−1/2)(1/2)) − p  ≤ 0   McCormick lower1 (p=h·t)
   7   p − ((3/2)t + h(1/2) − (3/2)(1/2))    ≤ 0   McCormick upper1 (p=h·t)
   8   0·z − mr                       ≤ 0          ReLU lower (α=0)
   9   mr − (1/2)(z − (−1))           ≤ 0          ReLU upper chord (z∈[−1,1])
  10   (h − x − att)                  ≤ 0          residual 1  (E≤0)
  11   −(h − x − att)                 ≤ 0          residual 1  (−E≤0)
  12   (ln − p)                       ≤ 0          LN affine   (E≤0)   ln=p
  13   −(ln − p)                      ≤ 0          LN affine   (−E≤0)
  14   (z − ln + 1/2)                 ≤ 0          MLP pre-act (E≤0)   z=ln−1/2
  15   −(z − ln + 1/2)                ≤ 0          MLP pre-act (−E≤0)
  16   (m − mr)                       ≤ 0          MLP out     (E≤0)   m=mr
  17   −(m − mr)                      ≤ 0          MLP out     (−E≤0)
  18   (o − h − m)                    ≤ 0          residual 2  (E≤0)
  19   −(o − h − m)                   ≤ 0          residual 2  (−E≤0)

This is the full UNION of the attention / LayerNorm / MLP premise families on
the shared block state; every premise is proven `≤ 0` on genuine executions in
`premiseFun_sound` below (the nonlinear ones via the imported component lemmas,
the affine ones because the equality holds exactly). -/
def tbPremise (i : Fin 20) (st : TBState) : ℚ :=
  if i.val = 0 then 0 - st.x
  else if i.val = 1 then st.x - 1
  else if i.val = 2 then (-1/2) - st.att
  else if i.val = 3 then st.att - (1/2)
  else if i.val = 4 then (1/2) - st.t
  else if i.val = 5 then st.t - 1
  else if i.val = 6 then ((-1/2) * st.t + st.h * (1/2) - (-1/2) * (1/2)) - st.p
  else if i.val = 7 then st.p - ((3/2) * st.t + st.h * (1/2) - (3/2) * (1/2))
  else if i.val = 8 then (0 : ℚ) * st.z - st.mr
  else if i.val = 9 then st.mr - (1/2) * (st.z - (-1))
  else if i.val = 10 then st.h - st.x - st.att
  else if i.val = 11 then -(st.h - st.x - st.att)
  else if i.val = 12 then st.ln - st.p
  else if i.val = 13 then -(st.ln - st.p)
  else if i.val = 14 then st.z - st.ln + (1/2)
  else if i.val = 15 then -(st.z - st.ln + (1/2))
  else if i.val = 16 then st.m - st.mr
  else if i.val = 17 then -(st.m - st.mr)
  else if i.val = 18 then st.o - st.h - st.m
  else -(st.o - st.h - st.m)

/-- Every premise is `≤ 0` on every genuine execution.  The box premises are the
    input box, the SBAR att box (`att_box`), the rsqrt box (‡).  The McCormick
    premises are `mccormick_lower1`/`mccormick_upper1` at `(h,t)`.  The two ReLU
    premises are `relu_lower` (α=0) and `relu_upper` (slope 1/2, z∈[−1,1], using
    `z_box`).  The ten affine premises hold because the structural equalities are
    exact, so each `±E` evaluates to a quantity `≤ 0` (in fact `= 0`). -/
theorem tbPremise_sound :
    ∀ i : Fin 20, ∀ st : TBState, st.valid → tbPremise i st ≤ 0 := by
  intro i st hv
  have hattb := att_box st hv
  have hzb := z_box st hv
  have hhb := h_box st hv
  obtain ⟨hxl, hxu, _hp0l,_hp0u, _hp1l,_hp1u, _hsx, _hatt,
          htl, hth, hheq, hpeq, hlneq, hzeq, hmreq, hmeq, hoeq⟩ := hv
  fin_cases i
  · show (0 : ℚ) - st.x ≤ 0; linarith
  · show st.x - 1 ≤ 0; linarith
  · show (-1/2 : ℚ) - st.att ≤ 0; linarith [hattb.1]
  · show st.att - (1/2 : ℚ) ≤ 0; linarith [hattb.2]
  · show (1/2 : ℚ) - st.t ≤ 0; linarith
  · show st.t - 1 ≤ 0; linarith
  · -- McCormick lower1
    show ((-1/2) * st.t + st.h * (1/2) - (-1/2) * (1/2)) - st.p ≤ 0
    rw [hpeq]
    have := mccormick_lower1 (a := st.h) (b := st.t)
        (al := (-1/2:ℚ)) (bl := (1/2:ℚ)) (ah := (3/2:ℚ)) (bh := (1:ℚ)) hhb.1 htl
    linarith
  · -- McCormick upper1
    show st.p - ((3/2) * st.t + st.h * (1/2) - (3/2) * (1/2)) ≤ 0
    rw [hpeq]
    have := mccormick_upper1 (a := st.h) (b := st.t)
        (al := (-1/2:ℚ)) (bl := (1/2:ℚ)) (ah := (3/2:ℚ)) (bh := (1:ℚ)) hhb.2 htl
    linarith
  · -- ReLU lower (α = 0):  0·z − mr ≤ 0
    show (0 : ℚ) * st.z - st.mr ≤ 0
    rw [hmreq]
    have := relu_lower 0 st.z (le_refl 0) (by norm_num)
    linarith
  · -- ReLU upper chord (slope 1/2, lz=−1, uz=1):  mr − (1/2)(z+1) ≤ 0
    show st.mr - (1/2) * (st.z - (-1)) ≤ 0
    rw [hmreq]
    have := relu_upper (-1 : ℚ) (1 : ℚ) (1/2 : ℚ) st.z
        (by norm_num) (by norm_num) (by norm_num) hzb.1 hzb.2
    linarith
  · show st.h - st.x - st.att ≤ 0; rw [hheq]; ring_nf; rfl
  · show -(st.h - st.x - st.att) ≤ 0; rw [hheq]; ring_nf; rfl
  · show st.ln - st.p ≤ 0; rw [hlneq]; linarith
  · show -(st.ln - st.p) ≤ 0; rw [hlneq]; linarith
  · show st.z - st.ln + (1/2) ≤ 0; rw [hzeq]; linarith
  · show -(st.z - st.ln + (1/2)) ≤ 0; rw [hzeq]; linarith
  · show st.m - st.mr ≤ 0; rw [hmeq]; linarith
  · show -(st.m - st.mr) ≤ 0; rw [hmeq]; linarith
  · show st.o - st.h - st.m ≤ 0; rw [hoeq]; linarith
  · show -(st.o - st.h - st.m) ≤ 0; rw [hoeq]; linarith

/-! ## 3. The two kernel-checked bounds, via `farkas_premise_combination`.

Each bound supplies a non-negative multiplier vector `μ : Fin 20 → ℚ` and the
certificate identity `Σ μ i · premiseFun i st = −(out st) − c`, then invokes the
abstract Farkas core.  The multipliers were produced by the exact-rational
certifier and are checked here by the kernel (`Fin.sum_univ` + `ring`/`linarith`).

Lower bound `o ≥ −1/2`.  Certificate (only the nonzero multipliers):
  residual-2 eq (−1):  μ₁₉ = 1      [−(o−h−m)]
  MLP-out  eq  (−1):  μ₁₇ = 1      [−(m−mr)]
  residual-1 eq (−1):  μ₁₁ = 1      [−(h−x−att)]
  ReLU lower:          μ₈  = 1
  input box lo:        μ₀  = 1
  SBAR att box lo:     μ₂  = 1
Identity: combo = −o − 1/2. -/
theorem tinyblock_lower :
    ∀ st : TBState, st.valid → -(1/2 : ℚ) ≤ st.o := by
  refine farkas_premise_combination (S := TBState) (ι := Fin 20)
        (premises := Finset.univ)
        (g := tbPremise) (out := fun st => st.o)
        (μ := ![ 1, 0, 1, 0, 0, 0, 0, 0,   1, 0, 0, 1, 0, 0, 0, 0,   0, 1, 0, 1 ])
        (c := (1/2 : ℚ)) (valid := TBState.valid)
        ?hμ ?hg ?hcert
  case hμ =>
    intro i _; fin_cases i <;> norm_num
  case hg =>
    intro i _ st hv; exact tbPremise_sound i st hv
  case hcert =>
    intro st
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, tbPremise, Fin.val_succ,
               Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
               Matrix.cons_val_fin_one]
    norm_num
    ring

/-! Upper bound `o ≤ 5/2`.  Apply the core to `out := −o`, giving `−o ≥ −5/2`,
i.e. `o ≤ 5/2`.  Certificate (nonzero multipliers; produced by the certifier):
  residual-2 eq (+1):  μ₁₈ = 1
  MLP-out  eq  (+1):  μ₁₆ = 1
  LN affine eq (+1/2): μ₁₂ = 1/2
  MLP pre  eq  (+1/2): μ₁₄ = 1/2
  residual-1 eq (+5/4):μ₁₀ = 5/4
  ReLU upper chord:    μ₉  = 1
  McCormick upper1:    μ₇  = 1/2
  input box hi:        μ₁  = 5/4
  SBAR att box hi:     μ₃  = 5/4
  rsqrt box hi:        μ₅  = 3/4
Identity: combo = (−(−o)) − 5/2 = o − 5/2. -/
theorem tinyblock_upper :
    ∀ st : TBState, st.valid → st.o ≤ (5/2 : ℚ) := by
  have key : ∀ st : TBState, st.valid → (-(5/2) : ℚ) ≤ (fun st => -st.o) st := by
    refine farkas_premise_combination (S := TBState) (ι := Fin 20)
          (premises := Finset.univ)
          (g := tbPremise) (out := fun st => -st.o)
          (μ := ![ 0, (5/4), 0, (5/4), 0, (3/4), 0, (1/2),
                   0, 1, (5/4), 0, (1/2), 0, (1/2), 0,   1, 0, 1, 0 ])
          (c := (5/2 : ℚ)) (valid := TBState.valid)
          ?hμ ?hg ?hcert
    case hμ =>
      intro i _; fin_cases i <;> norm_num
    case hg =>
      intro i _ st hv; exact tbPremise_sound i st hv
    case hcert =>
      intro st
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, tbPremise, Fin.val_succ,
                 Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
                 Matrix.cons_val_fin_one]
      norm_num
      ring
  intro st hv
  have := key st hv
  simp only at this
  linarith

/-! ## 4. The end-to-end interval bound, stated on the raw output. -/

/-- **First kernel-checked transformer-block bound.**  Every genuine execution
    of the concrete tiny block satisfies `o ∈ [−1/2, 5/2]`.  Both endpoints are
    tight (attained at the input-box corners noted in the file header). -/
theorem tinyblock_bound (st : TBState) (hv : st.valid) :
    (-1/2 : ℚ) ≤ st.o ∧ st.o ≤ (5/2 : ℚ) := by
  refine ⟨?_, tinyblock_upper st hv⟩
  have := tinyblock_lower st hv; linarith

/-! ## 5. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms att_upper_cert
#print axioms att_lower_cert
#print axioms tbPremise_sound
#print axioms tinyblock_lower
#print axioms tinyblock_upper
#print axioms tinyblock_bound

end Crownproof.TinyBlock
