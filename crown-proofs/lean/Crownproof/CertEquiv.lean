/-
  Certificate-equivalence theorem for proof-carrying NN verification.

  NY emits an entailment certificate as a *list* of premises (linear
  functionals `g_k : S → ℚ` that are `≤ 0` on valid states) each paired with a
  non-negative multiplier `μ_k`, together with a conclusion `out ≥ -c`.  The
  abstract Farkas core `farkas_premise_combination` (in `Bridge.lean`) is phrased
  over a `Finset ι` indexed family.  This file proves the SAME entailment over
  the LIST schema NY actually emits, so an emitted certificate plugs in directly
  without re-indexing.

  * `cert_list_sound` : list-schema Farkas premise-combination.  Given
      - `premises : List (S → ℚ)` and `mu : List ℚ` of equal length,
      - every `μ_k ≥ 0`,
      - every premise `g_k ≤ 0` on valid states,
      - the pointwise certificate identity
            `(∑ k, μ_k * g_k s) = -(out s) - c`   for all valid `s`,
    conclude `-c ≤ out s` for every valid `s`.

    Proved by induction on the zipped `(μ_k, g_k)` list, mirroring `farkas_comb`
    in `Basic.lean`: the per-state μ-combination is `≤ 0`, then the certificate
    identity rewrites that bound to `-(out s) - c ≤ 0`.

  * `crown_cert_instance` : ONE worked instance.  The concrete one-ReLU-layer
    `crown_bridge` hypotheses repackage into `cert_list_sound`, demonstrating
    the emitted one-hidden-layer certificate is an instance of the list schema.

  Sorry-free; trust base reported by `#print axioms` at the bottom must list
  only `[propext, Classical.choice, Quot.sound]`.
-/

import Crownproof.Bridge

namespace Crownproof

/-! ## 1. The list-schema certificate sum.

`certSum premises mu s` is the μ-combination of the premise functionals at the
state `s`, computed by walking the two lists in lockstep.  When the lists have
the same length this is exactly `∑ k, μ_k * g_k s`. -/

/-- The μ-combination `∑ k, μ_k * g_k s`, defined by zipping the multiplier list
    `mu` with the premise list `premises` and summing the products at state `s`. -/
def certSum {S : Type*} (premises : List (S → ℚ)) (mu : List ℚ) (s : S) : ℚ :=
  ((mu.zip premises).map (fun p => p.1 * p.2 s)).sum

@[simp] theorem certSum_nil {S : Type*} (mu : List ℚ) (s : S) :
    certSum ([] : List (S → ℚ)) mu s = 0 := by
  simp [certSum]

@[simp] theorem certSum_nil_mu {S : Type*} (premises : List (S → ℚ)) (s : S) :
    certSum premises ([] : List ℚ) s = 0 := by
  cases premises <;> simp [certSum]

@[simp] theorem certSum_cons {S : Type*} (m : ℚ) (g : S → ℚ)
    (mu : List ℚ) (premises : List (S → ℚ)) (s : S) :
    certSum (g :: premises) (m :: mu) s
      = m * g s + certSum premises mu s := by
  simp [certSum]

/-! ## 2. The list-schema Farkas premise-combination core. -/

/--
**Certificate-equivalence (list schema).**

This is `farkas_premise_combination` over the LIST of premises/multipliers that
NY emits, rather than an indexed `Finset` family.

Given a list of premise functionals `premises : List (S → ℚ)`, a list of
multipliers `mu : List ℚ` of the *same length*, an output functional
`out : S → ℚ`, a constant `c`, and a validity predicate `valid` such that:

  * every multiplier is non-negative,
  * every premise is `≤ 0` on valid states, and
  * the pointwise certificate identity
        `(∑ k, μ_k * g_k s) = -(out s) - c`   holds for every valid `s`,

then on every valid state `out s ≥ -c`.

The hypotheses are stated exactly as NY emits them (membership in the list, the
zipped sum `certSum`), so an emitted certificate instantiates this lemma
directly.  Proved by induction on the zipped list.
-/
theorem cert_list_sound {S : Type*}
    (premises : List (S → ℚ)) (mu : List ℚ) (out : S → ℚ) (c : ℚ)
    (valid : S → Prop)
    (hlen : mu.length = premises.length)
    (hμ : ∀ m ∈ mu, 0 ≤ m)
    (hg : ∀ g ∈ premises, ∀ s, valid s → g s ≤ 0)
    (hcert : ∀ s, valid s → certSum premises mu s = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  intro s hs
  -- Step 1: the per-state μ-combination is ≤ 0.
  have hsum_le : certSum premises mu s ≤ 0 := by
    clear hcert
    -- Induct on the two lists in lockstep.
    induction premises generalizing mu with
    | nil => simp
    | cons g premises ih =>
      cases mu with
      | nil => simp at hlen
      | cons m mu =>
        rw [certSum_cons]
        have hm : 0 ≤ m := hμ m (List.mem_cons_self ..)
        have hgs : g s ≤ 0 := hg g (List.mem_cons_self ..) s hs
        have hhead : m * g s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hgs
        have htail : certSum premises mu s ≤ 0 := by
          apply ih
          · simpa using hlen
          · intro x hx; exact hμ x (List.mem_cons_of_mem _ hx)
          · intro x hx; exact hg x (List.mem_cons_of_mem _ hx)
        linarith
  -- Step 2: rewrite with the certificate identity to get -(out s) - c ≤ 0.
  rw [hcert s hs] at hsum_le
  linarith

/-! ## 3. Worked instance: the emitted one-ReLU-layer certificate.

We repackage the concrete `crown_bridge` hypotheses (the one-hidden-layer
unstable-ReLU network from `Bridge.lean`) into the list schema, showing the
emitted certificate is a genuine instance of `cert_list_sound`.

The emitted certificate for that network is the list of four premise
functionals paired with the four non-negative multipliers `m_bl, m_bu, m_rl,
m_ru`, with conclusion `y ≥ -c`. -/

/-- The emitted premise list for the one-ReLU-layer network, in the exact order
    NY emits them: box-lower, box-upper, ReLU lower envelope, ReLU upper
    envelope.  (Same four functionals as `premiseFun` in `Bridge.lean`, but as a
    `List` rather than a `Fin 4`-indexed family.) -/
def emittedPremises (l u alpha s lz : ℚ) : List (NetState → ℚ) :=
  [ fun st => l - st.x,
    fun st => st.x - u,
    fun st => alpha * st.z - st.a,
    fun st => st.a - s * (st.z - lz) ]

/-- The emitted multiplier list, paired one-to-one with `emittedPremises`. -/
def emittedMultipliers (m_bl m_bu m_rl m_ru : ℚ) : List ℚ :=
  [m_bl, m_bu, m_rl, m_ru]

/--
**Worked instance.**

The concrete one-ReLU-layer `crown_bridge` hypotheses repackage directly into
`cert_list_sound`: the emitted four-premise / four-multiplier certificate is an
instance of the general list schema.  Conclusion is identical to `crown_bridge`:
every genuine execution satisfies `y ≥ -c`.
-/
theorem crown_cert_instance
    (l u w1 b1 w2 b2 alpha s lz u_z c : ℚ)
    (m_bl m_bu m_rl m_ru : ℚ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hlz : lz < 0) (huz : 0 < u_z) (hs : s * (u_z - lz) = u_z)
    (hbox_z : ∀ st : NetState, NetState.valid l u w1 b1 w2 b2 st →
                lz ≤ st.z ∧ st.z ≤ u_z)
    (hm_bl : 0 ≤ m_bl) (hm_bu : 0 ≤ m_bu)
    (hm_rl : 0 ≤ m_rl) (hm_ru : 0 ≤ m_ru)
    (hcert : ∀ st : NetState,
        m_bl * (l - st.x)
      + m_bu * (st.x - u)
      + m_rl * (alpha * st.z - st.a)
      + m_ru * (st.a - s * (st.z - lz))
        = -(st.y) - c) :
    ∀ st : NetState, NetState.valid l u w1 b1 w2 b2 st → -c ≤ st.y := by
  refine cert_list_sound
        (premises := emittedPremises l u alpha s lz)
        (mu := emittedMultipliers m_bl m_bu m_rl m_ru)
        (out := fun st => st.y) (c := c)
        (valid := NetState.valid l u w1 b1 w2 b2)
        ?hlen ?hμ ?hg ?hcert
  case hlen =>
    -- both lists have length 4
    rfl
  case hμ =>
    -- non-negativity of every emitted multiplier
    intro m hm
    simp only [emittedMultipliers, List.mem_cons,
               List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h <;> subst h
    · exact hm_bl
    · exact hm_bu
    · exact hm_rl
    · exact hm_ru
  case hg =>
    -- soundness of every emitted premise, reusing `premiseFun_sound`
    intro g hg st hv
    have hsound := premiseFun_sound l u w1 b1 w2 b2 alpha s lz u_z
                      ha0 ha1 hlz huz hs hbox_z
    simp only [emittedPremises, List.mem_cons,
               List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> subst h
    · simpa [premiseFun] using hsound 0 st hv
    · simpa [premiseFun] using hsound 1 st hv
    · simpa [premiseFun] using hsound 2 st hv
    · simpa [premiseFun] using hsound 3 st hv
  case hcert =>
    -- the emitted μ-combination IS -(y) - c
    intro st hv
    simp only [emittedPremises, emittedMultipliers, certSum, List.zip_cons_cons,
               List.zip_nil_right, List.map_cons, List.map_nil, List.sum_cons,
               List.sum_nil, add_zero]
    have h := hcert st
    linarith [h]

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms cert_list_sound
#print axioms crown_cert_instance

end Crownproof
