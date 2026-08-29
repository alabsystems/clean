/-
  # Width-One Depth Immunity — scalar-chain IBP is exact at every depth
  # (closes crown_bridge_deepK's hbox_z constructively)

  Invention-wave-2 PROVE lane (cross-layer #1).  Sealed conjecture record:
  `data/provenance/invention-wave-1-conjectures-2026-06-11.json`
  (set sha256 00b2f585d355e1b4abc2eb2ab6722dd1375ff65619a905d722da5c7cd4b6e8b4),
  conjecture "Width-One Depth Immunity: scalar-chain IBP is exact at every
  depth (closes crown_bridge_deepK's hbox_z constructively)", angle
  cross-layer, per-conjecture sha256
  fdca362073aec224e50e4211d1e1f71fee8723f748b5d590a474bf1af0015cbb.

  ## Statement (as conjectured)

  For the width-1 depth-k ReLU chain of `DeepK.lean`
  (`DeepKState k`: x → z₁ → a₁ → … → z_k → a_k → y), forward endpoint interval
  propagation (IBP) is simultaneously SOUND and EXACT at every layer and depth:

    (a) `ibpZ_sound`  — the recursively computed per-layer pre-activation
        interval `[(ibpZ j).1, (ibpZ j).2]` contains `st.z j` for EVERY genuine
        execution: this DERIVES the `hbox_z` hypothesis that
        `crown_bridge_deepK` (DeepK.lean) takes as an ASSUMED premise.
    (b) `ibpZ_exact`  — BOTH interval endpoints are ATTAINED by genuine
        executions whose input is an endpoint of `[l,u]`.

  Corollaries:
    * `crown_bridge_deepK_closed` — the arbitrary-depth CROWN bridge with
      `hbox_z` DERIVED (from `ibpZ_sound`), not assumed: the first in-tree
      discharge of a W2-flavor assumed-as-premise intermediate-bounds gap.
    * `ibpOut_isLeast` — output-level exactness: the IBP output lower bound is
      the GENUINE least element of `{st.y | st valid}` (relaxedBound = trueMin
      on width-1 chains, as an `IsLeast`, attained at a box endpoint).
    * `widthOneRelaxation` + `widthOne_zero_splits` — an L = 0
      `Complete.Relaxation` instance for the generic width-1 chain: BaB
      provably needs ZERO splits — the depth-0 leaf list has length 1 (a
      theorem, not a measurement), every leaf closes, and the root box is
      decided.  An exactly-counted Δdomains statement (leaf count 1 = 2^0).
    * `width_two_ibp_strictly_loose` — the converse leg, citing the in-tree
      `CompleteIBP` width-2 witness: on the 1→2→1 net's root box `[0,2]` the
      IBP bound is STRICTLY below the true minimum.  Together: deep
      composition loses NOTHING at width 1 (any depth), and width 2 already
      suffices for strict loss at depth 2 — the exact width threshold where
      the deep-composition problem begins.

  ## Formalization deltas vs the sealed sketch (all documented)

  1. `hlu : l ≤ u` is DROPPED from `ibpZ_sound` and `crown_bridge_deepK_closed`
     (strictly stronger statements): validity of an execution already forces
     `l ≤ st.x ≤ u`, so soundness needs no box-nonemptiness.  `hlu` is kept in
     `ibpZ_exact` (and the IsLeast/Relaxation corollaries) where the witness
     executions genuinely need it.
  2. `ibpZ` is defined through an explicit activation-interval prefix recursion
     `ibpA : ℕ → ℚ × ℚ` (mirroring `DeepKState.prevAct`'s match shape:
     `ibpA 0 = (l,u)`, `ibpA (n+1) = relu image of layer-n's z-interval`),
     with `ibpZ j` the sign-split affine image of `ibpA j.val` — semantically
     identical to the sketch's `(aLo,aHi)`/`(zLo,zHi)` recursion.  `ibpA` is
     totalized with an out-of-range value `(0,0)` for `n > k`, never reached
     from any `j : Fin k` (standard totalization, no mathematical content).
  3. The "envelope side conditions stated against `(ibpZ l u w b j).1/.2`"
     elided in the sketch are spelled exactly as `crown_bridge_deepK`'s
     `hlz`/`huz`/`hs` at the ibpZ values.
  4. The L = 0 instance uses `Box := {p : ℚ × ℚ // p.1 ≤ p.2}` (the subtype of
     genuine ordered boxes, so every `Relaxation` law quantifies over real
     boxes only) and `trueMin := sInf` of the ℝ-cast image of the chain output
     over the box's rational points — the genuine minimum, proved EQUAL to the
     IBP bound (`chainTrueMin_eq_relaxed`), which is what makes `L = 0` honest
     rather than definitional.
  5. The width-2 converse leg cites the in-tree `CompleteIBP` machinery
     (`relaxedBound_root_zero` + `margin_pos`), restated here as a strict
     inequality; the seal's optional "decidable no-coherent-sign check" is NOT
     included (allowed "only if cheap"; it is orthogonal to the theorem).

  ## Honesty / novelty tier

  N1 AT MOST — "first formalization against a kernel-checked CROWN substrate,
  pending index check" — NOT new mathematics.  Endpoint evaluation of monotone
  scalar compositions is interval-arithmetic folklore (Moore 1966); isomorphic
  statements may exist in Coq/Isabelle interval libraries.  Honesty bound from
  the seal, restated: this discharges the intermediate-bounds premise
  (width_error-flavor gap) for the EXACT-IBP SCALAR FAMILY ONLY — NOT for real
  backward CROWN.  The W4 gate ("no decision-procedure claim until a
  width_error instance is discharged for real CROWN") STAYS CLOSED.  The only
  counted quantity is Δdomains-class (leaf count 1, proven); no wall-clock, no
  GPU, no solved-instance claims.

  ## Axioms

  All `#print axioms` below report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`,
  no extra axioms (verified via `lake build`; see the commands at the bottom).
-/
import Crownproof.DeepK
import Crownproof.DeepPair
import Crownproof.CompleteIBP

namespace Crownproof

/-! ## 1.  Forward endpoint (IBP) propagation for the width-1 chain

`ibpA l u w b n` is the IBP interval for the activation FEEDING layer `n`
(the interval analogue of `DeepKState.prevAct`): `(l,u)` for `n = 0`, and the
relu image of layer `n-1`'s pre-activation interval afterwards.  `ibpZ j` is
the pre-activation interval of layer `j`: the affine image of `ibpA j.val`,
endpoints ordered by the sign of `w j`. -/

/-- IBP activation interval entering layer `n` (out-of-range totalization
`(0,0)` for `n > k`, never reached from a `Fin k` index). -/
def ibpA {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) : ℕ → ℚ × ℚ
  | 0 => (l, u)
  | n + 1 =>
    if h : n < k then
      if 0 ≤ w ⟨n, h⟩ then
        (relu (w ⟨n, h⟩ * (ibpA l u w b n).1 + b ⟨n, h⟩),
         relu (w ⟨n, h⟩ * (ibpA l u w b n).2 + b ⟨n, h⟩))
      else
        (relu (w ⟨n, h⟩ * (ibpA l u w b n).2 + b ⟨n, h⟩),
         relu (w ⟨n, h⟩ * (ibpA l u w b n).1 + b ⟨n, h⟩))
    else (0, 0)

/-- The IBP pre-activation interval `(zLo j, zHi j)` of layer `j`:
`(w j * aLo + b j, w j * aHi + b j)` when `0 ≤ w j`, swapped otherwise. -/
def ibpZ {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (j : Fin k) : ℚ × ℚ :=
  if 0 ≤ w j then
    (w j * (ibpA l u w b j.val).1 + b j, w j * (ibpA l u w b j.val).2 + b j)
  else
    (w j * (ibpA l u w b j.val).2 + b j, w j * (ibpA l u w b j.val).1 + b j)

/-- The recursion step, in `ibpZ` form: the next activation interval is the
relu image of the current pre-activation interval. -/
theorem ibpA_succ {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) {n : ℕ} (h : n < k) :
    ibpA l u w b (n + 1) =
      (relu (ibpZ l u w b ⟨n, h⟩).1, relu (ibpZ l u w b ⟨n, h⟩).2) := by
  by_cases hw : 0 ≤ w ⟨n, h⟩
  · simp only [ibpA, ibpZ, dif_pos h, if_pos hw]
  · simp only [ibpA, ibpZ, dif_pos h, if_neg hw]

/-- Sign-split affine step: if `t` lies in the incoming activation interval,
`w j * t + b j` lies in the `ibpZ` interval. -/
theorem ibpZ_affine_bounds {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (j : Fin k)
    (t : ℚ) (h1 : (ibpA l u w b j.val).1 ≤ t) (h2 : t ≤ (ibpA l u w b j.val).2) :
    (ibpZ l u w b j).1 ≤ w j * t + b j ∧ w j * t + b j ≤ (ibpZ l u w b j).2 := by
  unfold ibpZ
  by_cases hw : 0 ≤ w j
  · rw [if_pos hw]
    constructor
    · show w j * (ibpA l u w b j.val).1 + b j ≤ w j * t + b j
      have := mul_le_mul_of_nonneg_left h1 hw
      linarith
    · show w j * t + b j ≤ w j * (ibpA l u w b j.val).2 + b j
      have := mul_le_mul_of_nonneg_left h2 hw
      linarith
  · rw [if_neg hw]
    have hw' : w j ≤ 0 := (not_le.mp hw).le
    constructor
    · show w j * (ibpA l u w b j.val).2 + b j ≤ w j * t + b j
      have := mul_le_mul_of_nonpos_left h2 hw'
      linarith
    · show w j * t + b j ≤ w j * (ibpA l u w b j.val).1 + b j
      have := mul_le_mul_of_nonpos_left h1 hw'
      linarith

/-! ## 2.  (a) SOUNDNESS — `ibpZ` contains every genuine execution

Induction over the layer index: affine step by sign-split (`ibpZ_affine_bounds`),
relu step by `relu_mono` (DeepPair.lean). -/

/-- The activation feeding layer `n` of any genuine execution lies in `ibpA n`. -/
theorem ibpA_sound {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) (st : DeepKState k)
    (hv : DeepKState.valid l u w b wout bout hk st) :
    ∀ n, (hn : n < k) →
      (ibpA l u w b n).1 ≤ st.prevAct ⟨n, hn⟩ ∧
        st.prevAct ⟨n, hn⟩ ≤ (ibpA l u w b n).2 := by
  obtain ⟨hxl, hxu, hz, ha, _hy⟩ := hv
  intro n
  induction n with
  | zero =>
    intro hn
    exact ⟨hxl, hxu⟩
  | succ n ih =>
    intro hn
    have hn' : n < k := Nat.lt_of_succ_lt hn
    have hprev : st.prevAct ⟨n + 1, hn⟩ = st.a ⟨n, hn'⟩ := rfl
    obtain ⟨ih1, ih2⟩ := ih hn'
    have hzbnd := ibpZ_affine_bounds l u w b ⟨n, hn'⟩ (st.prevAct ⟨n, hn'⟩) ih1 ih2
    rw [← hz ⟨n, hn'⟩] at hzbnd
    rw [hprev, ha ⟨n, hn'⟩, ibpA_succ l u w b hn']
    exact ⟨relu_mono hzbnd.1, relu_mono hzbnd.2⟩

/-- **(a) SOUNDNESS — the derived `hbox_z`.**  For every genuine execution of
the width-1 depth-`k` chain, every layer's pre-activation lies in its IBP
interval.  This is EXACTLY the `hbox_z` hypothesis of `crown_bridge_deepK`
(DeepK.lean), here a THEOREM instead of an assumption.

Delta vs the sealed sketch: `hlu : l ≤ u` dropped (strictly stronger) —
validity already forces `l ≤ st.x ≤ u`. -/
theorem ibpZ_sound {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) :
    ∀ st : DeepKState k, DeepKState.valid l u w b wout bout hk st →
      ∀ j, (ibpZ l u w b j).1 ≤ st.z j ∧ st.z j ≤ (ibpZ l u w b j).2 := by
  intro st hv j
  have hA := ibpA_sound l u w b wout bout hk st hv j.val j.isLt
  have hzeq := hv.2.2.1 j
  rw [hzeq]
  exact ibpZ_affine_bounds l u w b j (st.prevAct j) hA.1 hA.2

/-! ## 3.  The canonical (endpoint) executions

`chainRun w b x n` is the deterministic forward evaluation of the chain on
input `x` (the activation entering layer `n`); `chainState x` packages it as a
genuine `DeepKState`.  Attainment is witnessed by `chainState l`/`chainState u`. -/

/-- Forward evaluation: activation entering layer `n` on input `x`. -/
def chainRun {k : ℕ} (w b : Fin k → ℚ) (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
    if h : n < k then relu (w ⟨n, h⟩ * chainRun w b x n + b ⟨n, h⟩) else 0

/-- The chain's scalar output on input `x`. -/
def chainOut {k : ℕ} (w b : Fin k → ℚ) (wout bout : ℚ) (x : ℚ) : ℚ :=
  wout * chainRun w b x k + bout

/-- The canonical execution of the chain on input `x`. -/
def chainState {k : ℕ} (w b : Fin k → ℚ) (wout bout x : ℚ) (hk : 0 < k) :
    DeepKState k :=
  { x := x
    z := fun j => w j * chainRun w b x j.val + b j
    a := fun j => relu (w j * chainRun w b x j.val + b j)
    y := wout * relu (w ⟨k - 1, by omega⟩ * chainRun w b x (k - 1)
           + b ⟨k - 1, by omega⟩) + bout }

theorem chainState_prevAct {k : ℕ} (w b : Fin k → ℚ) (wout bout x : ℚ)
    (hk : 0 < k) (j : Fin k) :
    (chainState w b wout bout x hk).prevAct j = chainRun w b x j.val := by
  obtain ⟨n, hn⟩ := j
  cases n with
  | zero => rfl
  | succ m =>
    have hm : m < k := by omega
    simp only [chainRun, dif_pos hm]
    rfl

/-- The canonical execution is a genuine execution whenever `x` is in the box. -/
theorem chainState_valid {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ)
    (wout bout x : ℚ) (hk : 0 < k) (hxl : l ≤ x) (hxu : x ≤ u) :
    DeepKState.valid l u w b wout bout hk (chainState w b wout bout x hk) := by
  refine ⟨hxl, hxu, fun j => ?_, fun j => rfl, rfl⟩
  rw [chainState_prevAct]
  rfl

/-- The canonical execution's output is `chainOut`. -/
theorem chainState_y {k : ℕ} (w b : Fin k → ℚ) (wout bout x : ℚ) (hk : 0 < k) :
    (chainState w b wout bout x hk).y = chainOut w b wout bout x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [chainOut, chainRun, dif_pos (Nat.lt_succ_self m)]
  rfl

/-! ## 4.  (b) EXACTNESS — both endpoints are attained from box endpoints

The key invariant (induction over the layer index): `(ibpA n).1, (ibpA n).2`
are the images of the TWO ENDPOINT executions `chainRun l`, `chainRun u` in
some order — the order tracked by the accumulated sign (each width-1 layer map
is monotone or antitone in `x`, so extremes sit at `{l, u}`). -/

/-- The endpoint invariant for the activation intervals. -/
theorem ibpA_endpoints {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) :
    ∀ n,
      ((ibpA l u w b n).1 = chainRun w b l n ∧
       (ibpA l u w b n).2 = chainRun w b u n) ∨
      ((ibpA l u w b n).1 = chainRun w b u n ∧
       (ibpA l u w b n).2 = chainRun w b l n) := by
  intro n
  induction n with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    by_cases h : n < k
    · rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases hw : 0 ≤ w ⟨n, h⟩
        · refine Or.inl ⟨?_, ?_⟩ <;>
            simp only [ibpA, chainRun, dif_pos h, if_pos hw, h1, h2]
        · refine Or.inr ⟨?_, ?_⟩ <;>
            simp only [ibpA, chainRun, dif_pos h, if_neg hw, h1, h2]
      · by_cases hw : 0 ≤ w ⟨n, h⟩
        · refine Or.inr ⟨?_, ?_⟩ <;>
            simp only [ibpA, chainRun, dif_pos h, if_pos hw, h1, h2]
        · refine Or.inl ⟨?_, ?_⟩ <;>
            simp only [ibpA, chainRun, dif_pos h, if_neg hw, h1, h2]
    · refine Or.inl ⟨?_, ?_⟩ <;> simp only [ibpA, chainRun, dif_neg h]

/-- The endpoint invariant at the `z`-level: `(ibpZ j).1/.2` are the layer-`j`
pre-activations of the two endpoint executions, in some order. -/
theorem ibpZ_endpoints {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (j : Fin k) :
    ((ibpZ l u w b j).1 = w j * chainRun w b l j.val + b j ∧
     (ibpZ l u w b j).2 = w j * chainRun w b u j.val + b j) ∨
    ((ibpZ l u w b j).1 = w j * chainRun w b u j.val + b j ∧
     (ibpZ l u w b j).2 = w j * chainRun w b l j.val + b j) := by
  unfold ibpZ
  rcases ibpA_endpoints l u w b j.val with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hw : 0 ≤ w j
    · exact Or.inl ⟨by rw [if_pos hw, h1], by rw [if_pos hw, h2]⟩
    · exact Or.inr ⟨by rw [if_neg hw, h2], by rw [if_neg hw, h1]⟩
  · by_cases hw : 0 ≤ w j
    · exact Or.inr ⟨by rw [if_pos hw, h1], by rw [if_pos hw, h2]⟩
    · exact Or.inl ⟨by rw [if_neg hw, h2], by rw [if_neg hw, h1]⟩

/-- **(b) EXACTNESS.**  Both ends of every layer's IBP interval are ATTAINED by
genuine executions whose input is an endpoint of `[l,u]`.  Width-1 IBP loses
nothing, at any depth. -/
theorem ibpZ_exact {k : ℕ} (l u : ℚ) (hlu : l ≤ u) (w b : Fin k → ℚ)
    (wout bout : ℚ) (hk : 0 < k) (j : Fin k) :
    (∃ st : DeepKState k, DeepKState.valid l u w b wout bout hk st ∧
        st.z j = (ibpZ l u w b j).2 ∧ (st.x = l ∨ st.x = u)) ∧
    (∃ st : DeepKState k, DeepKState.valid l u w b wout bout hk st ∧
        st.z j = (ibpZ l u w b j).1 ∧ (st.x = l ∨ st.x = u)) := by
  have hL := chainState_valid l u w b wout bout l hk le_rfl hlu
  have hU := chainState_valid l u w b wout bout u hk hlu le_rfl
  have hzL : (chainState w b wout bout l hk).z j
      = w j * chainRun w b l j.val + b j := rfl
  have hzU : (chainState w b wout bout u hk).z j
      = w j * chainRun w b u j.val + b j := rfl
  rcases ibpZ_endpoints l u w b j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨chainState w b wout bout u hk, hU, by rw [hzU, h2], Or.inr rfl⟩,
           ⟨chainState w b wout bout l hk, hL, by rw [hzL, h1], Or.inl rfl⟩⟩
  · exact ⟨⟨chainState w b wout bout l hk, hL, by rw [hzL, h2], Or.inl rfl⟩,
           ⟨chainState w b wout bout u hk, hU, by rw [hzU, h1], Or.inr rfl⟩⟩

/-! ## 5.  Corollary: the depth-`k` CROWN bridge with `hbox_z` DERIVED

`crown_bridge_deepK` (DeepK.lean:177) instantiated at `lz := (ibpZ ·).1`,
`uz := (ibpZ ·).2`, with its `hbox_z` premise discharged by `ibpZ_sound`.
First in-tree case where the intermediate-bounds premise of a deep CROWN
bridge is derived inside the kernel rather than carried as a hypothesis —
for the exact-IBP scalar family ONLY (see the honesty bound in the header). -/

theorem crown_bridge_deepK_closed {k : ℕ}
    (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ) (hk : 0 < k)
    (alpha s : Fin k → ℚ) (c : ℚ) (μ : Fin (2 * k + 2) → ℚ)
    (ha0 : ∀ j, 0 ≤ alpha j) (ha1 : ∀ j, alpha j ≤ 1)
    (hlz : ∀ j, (ibpZ l u w b j).1 < 0)
    (huz : ∀ j, 0 < (ibpZ l u w b j).2)
    (hs : ∀ j, s j * ((ibpZ l u w b j).2 - (ibpZ l u w b j).1)
            = (ibpZ l u w b j).2)
    (hμ : ∀ i, 0 ≤ μ i)
    (hcert : ∀ st : DeepKState k,
        (∑ i, μ i * premiseFunK l u alpha s (fun j => (ibpZ l u w b j).1) i st)
          = -(st.y) - c) :
    ∀ st : DeepKState k,
      DeepKState.valid l u w b wout bout hk st → -c ≤ st.y :=
  crown_bridge_deepK l u w b wout bout hk alpha s
    (fun j => (ibpZ l u w b j).1) (fun j => (ibpZ l u w b j).2) c μ
    ha0 ha1 hlz huz hs
    (fun st hv j => ibpZ_sound l u w b wout bout hk st hv j)
    hμ hcert

/-! ## 6.  Output-level exactness: relaxedBound = trueMin on width-1 chains

`ibpOut` is the IBP lower bound on the chain output; it is SOUND
(`ibpOut_sound`), ATTAINED at a box endpoint (`ibpOut_attained`), and hence
the GENUINE least element of the output set over executions
(`ibpOut_isLeast`). -/

/-- IBP lower bound on the chain output: the output activation interval is
`ibpA k`; the read-out picks the side by the sign of `wout`. -/
def ibpOut {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ) : ℚ :=
  if 0 ≤ wout then wout * (ibpA l u w b k).1 + bout
  else wout * (ibpA l u w b k).2 + bout

/-- IBP output soundness: `ibpOut ≤ st.y` for every genuine execution. -/
theorem ibpOut_sound {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) (st : DeepKState k)
    (hv : DeepKState.valid l u w b wout bout hk st) :
    ibpOut l u w b wout bout ≤ st.y := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hz := ibpZ_sound l u w b wout bout hk st hv ⟨m, hm⟩
  have ha : st.a ⟨m, hm⟩ = relu (st.z ⟨m, hm⟩) := hv.2.2.2.1 ⟨m, hm⟩
  have hy : st.y = wout * st.a ⟨m, hm⟩ + bout := hv.2.2.2.2
  have hA := ibpA_succ l u w b hm
  have hlo : (ibpA l u w b (m + 1)).1 ≤ st.a ⟨m, hm⟩ := by
    rw [hA, ha]; exact relu_mono hz.1
  have hhi : st.a ⟨m, hm⟩ ≤ (ibpA l u w b (m + 1)).2 := by
    rw [hA, ha]; exact relu_mono hz.2
  unfold ibpOut
  by_cases hw : 0 ≤ wout
  · rw [if_pos hw, hy]
    have := mul_le_mul_of_nonneg_left hlo hw
    linarith
  · rw [if_neg hw, hy]
    have := mul_le_mul_of_nonpos_left hhi ((not_le.mp hw).le)
    linarith

/-- IBP output attainment: `ibpOut` is the chain output at `l` or at `u`. -/
theorem ibpOut_attained {k : ℕ} (l u : ℚ) (w b : Fin k → ℚ) (wout bout : ℚ) :
    ibpOut l u w b wout bout = chainOut w b wout bout l ∨
    ibpOut l u w b wout bout = chainOut w b wout bout u := by
  unfold ibpOut chainOut
  rcases ibpA_endpoints l u w b k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hw : 0 ≤ wout
    · exact Or.inl (by rw [if_pos hw, h1])
    · exact Or.inr (by rw [if_neg hw, h2])
  · by_cases hw : 0 ≤ wout
    · exact Or.inr (by rw [if_pos hw, h1])
    · exact Or.inl (by rw [if_neg hw, h2])

/-- **Output-level exactness over genuine executions.**  The IBP output bound
is the LEAST ELEMENT (not merely a lower bound) of `{st.y | st valid}`:
`relaxedBound = trueMin` on width-1 chains, attainment included. -/
theorem ibpOut_isLeast {k : ℕ} (l u : ℚ) (hlu : l ≤ u) (w b : Fin k → ℚ)
    (wout bout : ℚ) (hk : 0 < k) :
    IsLeast {y : ℚ | ∃ st : DeepKState k,
        DeepKState.valid l u w b wout bout hk st ∧ st.y = y}
      (ibpOut l u w b wout bout) := by
  constructor
  · rcases ibpOut_attained l u w b wout bout with h | h
    · exact ⟨chainState w b wout bout l hk,
        chainState_valid l u w b wout bout l hk le_rfl hlu,
        by rw [chainState_y]; exact h.symm⟩
    · exact ⟨chainState w b wout bout u hk,
        chainState_valid l u w b wout bout u hk hlu le_rfl,
        by rw [chainState_y]; exact h.symm⟩
  · rintro y ⟨st, hv, rfl⟩
    exact ibpOut_sound l u w b wout bout hk st hv

/-- Input-level form: `ibpOut` is the least value of `chainOut` over the box. -/
theorem ibpOut_isLeast_inputs {k : ℕ} (l u : ℚ) (hlu : l ≤ u)
    (w b : Fin k → ℚ) (wout bout : ℚ) (hk : 0 < k) :
    IsLeast (chainOut w b wout bout '' {x : ℚ | l ≤ x ∧ x ≤ u})
      (ibpOut l u w b wout bout) := by
  constructor
  · rcases ibpOut_attained l u w b wout bout with h | h
    · exact ⟨l, ⟨le_rfl, hlu⟩, h.symm⟩
    · exact ⟨u, ⟨hlu, le_rfl⟩, h.symm⟩
  · rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have h := ibpOut_sound l u w b wout bout hk
      (chainState w b wout bout x hk)
      (chainState_valid l u w b wout bout x hk hx1 hx2)
    rwa [chainState_y] at h

/-- IBP monotonicity under box inclusion — a one-line consequence of
exactness: the sub-box bound is attained at a point of the parent box. -/
theorem ibpOut_mono_subbox {k : ℕ} (l u l' u' : ℚ) (hl : l ≤ l')
    (h' : l' ≤ u') (hu : u' ≤ u) (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) :
    ibpOut l u w b wout bout ≤ ibpOut l' u' w b wout bout := by
  rcases ibpOut_attained l' u' w b wout bout with h | h <;> rw [h]
  · have hv := chainState_valid l u w b wout bout l' hk hl (h'.trans hu)
    have hs := ibpOut_sound l u w b wout bout hk _ hv
    rwa [chainState_y] at hs
  · have hv := chainState_valid l u w b wout bout u' hk (hl.trans h') hu
    have hs := ibpOut_sound l u w b wout bout hk _ hv
    rwa [chainState_y] at hs

/-! ## 7.  The L = 0 `Complete.Relaxation` instance — zero splits as a theorem

Boxes are GENUINE ordered rational pairs (subtype — no empty boxes, see header
delta 4).  `trueMin` is the genuine `sInf` of the chain output over the box's
rational points (cast to ℝ); exactness (`chainTrueMin_eq_relaxed`) makes the
width-error law hold with `L = 0`. -/

/-- A genuine (ordered) rational box. -/
abbrev RatBox := {p : ℚ × ℚ // p.1 ≤ p.2}

/-- Genuine true minimum: `sInf` of the ℝ-cast chain output over the box. -/
noncomputable def chainTrueMin {k : ℕ} (w b : Fin k → ℚ) (wout bout : ℚ)
    (B : RatBox) : ℝ :=
  sInf ((fun x : ℚ => (chainOut w b wout bout x : ℝ)) ''
    {x : ℚ | B.val.1 ≤ x ∧ x ≤ B.val.2})

/-- The relaxation's computed bound: the (cast) IBP output bound. -/
def chainRelaxed {k : ℕ} (w b : Fin k → ℚ) (wout bout : ℚ) (B : RatBox) : ℝ :=
  ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ)

/-- Midpoint bisection of a genuine box (children are genuine). -/
def chainSplit (B : RatBox) : RatBox × RatBox :=
  ⟨⟨(B.val.1, (B.val.1 + B.val.2) / 2), by
      have := B.property; dsimp only; linarith⟩,
   ⟨((B.val.1 + B.val.2) / 2, B.val.2), by
      have := B.property; dsimp only; linarith⟩⟩

/-- **EXACTNESS as an equation: `trueMin = relaxedBound` on every box.**
This is what makes the `L = 0` instance honest: the relaxation error of
width-1 IBP is identically zero. -/
theorem chainTrueMin_eq_relaxed {k : ℕ} (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) (B : RatBox) :
    chainTrueMin w b wout bout B = chainRelaxed w b wout bout B := by
  have hL := ibpOut_isLeast_inputs B.val.1 B.val.2 B.property w b wout bout hk
  have hR : IsLeast
      ((fun x : ℚ => (chainOut w b wout bout x : ℝ)) ''
        {x : ℚ | B.val.1 ≤ x ∧ x ≤ B.val.2})
      ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ) := by
    constructor
    · obtain ⟨x, hx, hxe⟩ := hL.1
      refine ⟨x, hx, ?_⟩
      show ((chainOut w b wout bout x : ℚ) : ℝ)
        = ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ)
      exact_mod_cast hxe
    · rintro y ⟨x, hx, rfl⟩
      show ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ)
        ≤ ((chainOut w b wout bout x : ℚ) : ℝ)
      exact_mod_cast hL.2 ⟨x, hx, rfl⟩
  exact hR.csInf_eq

/-- The width-1 chain's exact relaxation: an `L = 0` instance of
`Complete.Relaxation` with every field discharged. -/
noncomputable def widthOneRelaxation {k : ℕ} (w b : Fin k → ℚ)
    (wout bout : ℚ) (hk : 0 < k) : Complete.Relaxation RatBox ℚ where
  diam B := ((B.val.2 - B.val.1 : ℚ) : ℝ)
  trueMin := chainTrueMin w b wout bout
  relaxedBound := chainRelaxed w b wout bout
  split := chainSplit
  mem B x := B.val.1 ≤ x ∧ x ≤ B.val.2
  safe x := 0 < chainOut w b wout bout x
  L := 0
  L_nonneg := le_refl 0
  diam_nonneg B := by
    have h := B.property
    have h' : (0 : ℚ) ≤ B.val.2 - B.val.1 := by linarith
    exact_mod_cast h'
  width_error B := by
    rw [chainTrueMin_eq_relaxed w b wout bout hk B, zero_mul, sub_zero]
  diam_contract B := by
    have h := B.property
    constructor
    · show (((B.val.1 + B.val.2) / 2 - B.val.1 : ℚ) : ℝ)
        ≤ ((B.val.2 - B.val.1 : ℚ) : ℝ) / 2
      push_cast
      linarith
    · show ((B.val.2 - (B.val.1 + B.val.2) / 2 : ℚ) : ℝ)
        ≤ ((B.val.2 - B.val.1 : ℚ) : ℝ) / 2
      push_cast
      linarith
  trueMin_mono B := by
    have h := B.property
    rw [chainTrueMin_eq_relaxed w b wout bout hk B,
      chainTrueMin_eq_relaxed w b wout bout hk (chainSplit B).1,
      chainTrueMin_eq_relaxed w b wout bout hk (chainSplit B).2]
    constructor
    · show ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ)
        ≤ ((ibpOut B.val.1 ((B.val.1 + B.val.2) / 2) w b wout bout : ℚ) : ℝ)
      exact_mod_cast ibpOut_mono_subbox B.val.1 B.val.2 B.val.1
        ((B.val.1 + B.val.2) / 2) le_rfl (by linarith) (by linarith)
        w b wout bout hk
    · show ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ)
        ≤ ((ibpOut ((B.val.1 + B.val.2) / 2) B.val.2 w b wout bout : ℚ) : ℝ)
      exact_mod_cast ibpOut_mono_subbox B.val.1 B.val.2
        ((B.val.1 + B.val.2) / 2) B.val.2 (by linarith) (by linarith) le_rfl
        w b wout bout hk
  decides B hpos x hx := by
    have hq : 0 < ibpOut B.val.1 B.val.2 w b wout bout := by
      have hpos' : (0 : ℝ) < ((ibpOut B.val.1 B.val.2 w b wout bout : ℚ) : ℝ) := hpos
      exact_mod_cast hpos'
    have hs := ibpOut_sound B.val.1 B.val.2 w b wout bout hk
      (chainState w b wout bout x hk)
      (chainState_valid B.val.1 B.val.2 w b wout bout x hk hx.1 hx.2)
    rw [chainState_y] at hs
    exact lt_of_lt_of_le hq hs
  cover B x hx := by
    rcases le_total x ((B.val.1 + B.val.2) / 2) with hm | hm
    · exact Or.inl ⟨hx.1, hm⟩
    · exact Or.inr ⟨hm, hx.2⟩

/-- **ZERO SPLITS — the exactly-counted Δdomains statement.**  For the width-1
chain's exact relaxation, a positive margin is decided at bisection depth 0:
the leaf list is literally `[B]` — LEAF COUNT 1 AS A THEOREM (`2^0`, not a
measurement) — every leaf closes, and the whole root box is decided.  Compare
`CompleteIBP.decisive_depth_one`: the in-tree width-2 net needs depth 1
(leaf count 2) on its root box.  BaB provably needs zero splits at width 1. -/
theorem widthOne_zero_splits {k : ℕ} (w b : Fin k → ℚ) (wout bout : ℚ)
    (hk : 0 < k) (B : RatBox) {δ : ℝ} (hδ : 0 < δ)
    (hmin : δ ≤ (widthOneRelaxation w b wout bout hk).trueMin B) :
    (Complete.leafBoxes (widthOneRelaxation w b wout bout hk) B 0).length = 1 ∧
    (∀ C ∈ Complete.leafBoxes (widthOneRelaxation w b wout bout hk) B 0,
        0 < (widthOneRelaxation w b wout bout hk).relaxedBound C) ∧
    (∀ s : ℚ, (widthOneRelaxation w b wout bout hk).mem B s →
        (widthOneRelaxation w b wout bout hk).safe s) := by
  have hclose : ∀ C ∈ Complete.leafBoxes (widthOneRelaxation w b wout bout hk) B 0,
      0 < (widthOneRelaxation w b wout bout hk).relaxedBound C := by
    intro C hC
    simp only [Complete.leafBoxes, List.mem_singleton] at hC
    subst hC
    have heq : (widthOneRelaxation w b wout bout hk).trueMin C
        = (widthOneRelaxation w b wout bout hk).relaxedBound C :=
      chainTrueMin_eq_relaxed w b wout bout hk C
    rw [heq] at hmin
    linarith
  refine ⟨rfl, hclose, ?_⟩
  exact Complete.box_safe_of_leaves (widthOneRelaxation w b wout bout hk) B 0
    (fun C hC s hs =>
      (widthOneRelaxation w b wout bout hk).decides C (hclose C hC) s hs)

/-! ## 8.  The width threshold: width 2 already loses (in-tree witness)

Width 1 is depth-immune (`chainTrueMin_eq_relaxed`: relaxation error ≡ 0 on
every chain, every box, every depth).  The in-tree `CompleteIBP` 1→2→1 net
witnesses that width 2 already suffices for STRICT loss at depth 2: on its
root box the IBP bound is strictly below the true minimum.  The
deep-composition problem provably begins at width 2. -/

theorem width_two_ibp_strictly_loose :
    CompleteIBP.relaxedBound ((0 : ℝ), 2) < CompleteIBP.trueMin ((0 : ℝ), 2) := by
  have h0 := CompleteIBP.relaxedBound_root_zero
  have h1 := CompleteIBP.margin_pos
  rw [h0]
  linarith

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`
and NO `native_decide`. -/

#print axioms ibpZ_sound
#print axioms ibpZ_exact
#print axioms crown_bridge_deepK_closed
#print axioms ibpOut_isLeast
#print axioms ibpOut_isLeast_inputs
#print axioms chainTrueMin_eq_relaxed
#print axioms widthOneRelaxation
#print axioms widthOne_zero_splits
#print axioms width_two_ibp_strictly_loose

end Crownproof
