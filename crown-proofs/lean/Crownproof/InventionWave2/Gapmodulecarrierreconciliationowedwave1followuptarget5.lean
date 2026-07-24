/-
  INVENTION WAVE 2 — target #5: gap-module carrier reconciliation
  (the owed wave-1 follow-up).

  ## Binding requirement (NOT a sealed conjecture — a report-mandated follow-up)

  The wave-1 verification report `reports/invention-wave-1-2026-06-11.md`
  (§3.2 "Consolidation debt", §6 merge-readiness item 2) requires, before any
  external claim cites the gap module's gap as "gap to the EXACT bound":

      land the one-lemma carrier reconciliation
      `Crownproof.InventionWave1.patternBound = Crownproof.patternBound`
      (under `hbox`), so the gap theorems formally connect to the exactness
      theorem (`multiReluCut_box_exact`) they cite informally.

  Background: the two wave-1 lanes raced and landed TWO carriers for the same
  closed form —

    * `Crownproof.boxMaxAffine`              (multiReluCutboxexact.lean:88)
      mid/rad form: `rr + ∑_j (w_j·mid_j + |w_j|·rad_j)`;
    * `Crownproof.InventionWave1.boxMaxAffine` (gapclosedform…lean:112)
      endpoint-max form: `(∑_j max (w_j·xl_j) (w_j·xu_j)) + r`;

  and the corresponding two `patternBound`s.  The gap module's own
  `boxMaxAffine_midrad` (gapclosedform…lean:169) is already the bridge: under
  `hbox` the endpoint-max form equals the mid/rad expansion; the residual
  difference vs `Crownproof.boxMaxAffine` is the placement of the intercept
  (`… + r` vs `r + …`) and `xl+xu` vs `xu+xl` — pure `add_comm`/`ring`.

  ## What this file proves, sorry-free

  1. `boxMaxAffine_carrier_eq` — the two `boxMaxAffine` carriers agree under
     `hbox` (the requested one-lemma reconciliation, at the `boxMaxAffine`
     level).
  2. `patternBound_carrier_eq` / `patternBound_carrier_funext` — the requested
     reconciliation `InventionWave1.patternBound = Crownproof.patternBound`
     under `hbox` (per-pattern and as a function equality).
  3. `patternSup_carrier_eq` — the gap module's pattern-sup (the exact term
     subtracted in `gap_closed_form` / tested in `gap_pos_iff_sign_disagree`)
     equals the pattern-max of `multiReluCut_box_exact`.
  4. `gapModule_patternSup_exact` — the EXACTNESS corollary: the sup the gap
     theorems reference satisfies `multiReluCut_box_exact`'s `IsGreatest` —
     it IS the exact supremum of `∑ cc_i·relu z_i` over the box (validity AND
     attainment), upgrading `jointCut_le_patternSup` (validity only).
  5. `gapModule_patternSup_least_valid` — the matching tightness transport of
     `patternMax_le_of_valid_bound`: every valid joint bound dominates the gap
     module's pattern-sup.
  6. `gap_closed_form_exact` — the re-grounded reading of `gap_closed_form`:
     the closed-form gap equality holds AND the bound being subtracted is the
     exact joint-cut supremum (`IsGreatest`).  This is the formal content of
     the informal sentence "the gap to the exact joint-cut bound of
     Conjecture 1" in the gap module's header.

  ## Faithfulness / honesty

  * Statements 1–2 are verbatim the report's named requirement; 3–6 are the
    transports the requirement exists to enable, each stated against the
    UNCHANGED wave-1 theorems (`multiReluCut_box_exact`
    multiReluCutboxexact.lean:219, `patternMax_le_of_valid_bound` :260,
    `gap_closed_form` gapclosedform…lean:426).  Nothing in either wave-1
    module is re-proved or restated; both are imported as-is.
  * `hbox` is genuinely needed: WITHOUT it the two carriers differ (on an
    empty box `xl_j > xu_j`, max-of-endpoints and mid/rad disagree), so the
    reconciliation is stated exactly at the hypothesis strength the report
    names.  All gap-module theorems carry `hbox`, so every one of them now has
    an exactness reading through lemma 3.
  * NOVELTY: none claimed.  This is consolidation glue (below N1 — no "first
    formalization" claim is made for these lemmas; they identify two spellings
    of one folklore closed form).  Zero Δdomains / runtime / VNN-COMP claims.
  * Sealed wave-1 record (for the two carrier definitions' provenance only):
    `data/provenance/invention-wave-1-conjectures-2026-06-11.json`
    (set sha256 00b2f585d355e1b4abc2eb2ab6722dd1375ff65619a905d722da5c7cd4b6e8b4).

  All `#print axioms` below must report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extras.
-/

import Crownproof.InventionWave1.multiReluCutboxexact
import Crownproof.InventionWave1.gapclosedformgapposiffsigndisagree

namespace Crownproof
namespace InventionWave2

open Finset

/-! ## 1.  The one-lemma reconciliation: the two `boxMaxAffine` carriers agree. -/

/-- **Carrier reconciliation, `boxMaxAffine` level.**  Under `hbox` the gap
module's endpoint-max carrier equals the exactness lane's mid/rad carrier:
`InventionWave1.boxMaxAffine = Crownproof.boxMaxAffine`.  Proof: the gap
module's own bridge `boxMaxAffine_midrad` plus `add_comm` (intercept placement
`… + r` vs `r + …`, and `xl+xu` vs `xu+xl` inside the mid term). -/
theorem boxMaxAffine_carrier_eq {n : ℕ} (w : Fin n → ℚ) (r : ℚ) (xl xu : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ xu j) :
    InventionWave1.boxMaxAffine w r xl xu = Crownproof.boxMaxAffine w r xl xu := by
  rw [InventionWave1.boxMaxAffine_midrad w r xl xu hbox]
  unfold Crownproof.boxMaxAffine
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **The requested reconciliation** (wave-1 report §6.2 item 2), per pattern:
`InventionWave1.patternBound cc p r xl xu S = Crownproof.patternBound cc p r xl xu S`
under `hbox` — `boxMaxAffine_carrier_eq` applied to the assembled pattern row. -/
theorem patternBound_carrier_eq {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (hbox : ∀ j, xl j ≤ xu j)
    (S : Finset (Fin k)) :
    InventionWave1.patternBound cc p r xl xu S
      = Crownproof.patternBound cc p r xl xu S := by
  unfold InventionWave1.patternBound Crownproof.patternBound
  exact boxMaxAffine_carrier_eq _ _ xl xu hbox

/-- The reconciliation as a function equality (the report's literal spelling
`InventionWave1.patternBound = Crownproof.patternBound`, with the box data
fixed and `hbox` assumed). -/
theorem patternBound_carrier_funext {n k : ℕ} (cc : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hbox : ∀ j, xl j ≤ xu j) :
    InventionWave1.patternBound cc p r xl xu = Crownproof.patternBound cc p r xl xu :=
  funext fun S => patternBound_carrier_eq cc p r xl xu hbox S

/-- The gap module's pattern-sup — the exact term subtracted in
`gap_closed_form` and tested in `gap_pos_iff_sign_disagree` — IS the
pattern-max of `multiReluCut_box_exact`. -/
theorem patternSup_carrier_eq {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (hbox : ∀ j, xl j ≤ xu j) :
    Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc p r xl xu)
      = Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
          (Crownproof.patternBound cc p r xl xu) := by
  rw [patternBound_carrier_funext cc p r xl xu hbox]

/-! ## 2.  The exactness corollaries: the gap module's sup re-grounded as the
EXACT joint-cut bound. -/

/-- **Exactness of the gap module's pattern-sup.**  The sup the gap theorems
reference satisfies `multiReluCut_box_exact`'s `IsGreatest`: it is the EXACT
supremum of `∑_i cc_i · relu (z_i x)` over the box — both a valid upper bound
(which `jointCut_le_patternSup` already gave) AND attained at a box point.
This upgrades the gap module's grounding from validity to exactness. -/
theorem gapModule_patternSup_exact {n k : ℕ} (cc : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (hbox : ∀ j, xl j ≤ xu j) :
    IsGreatest
      {v : ℚ | ∃ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
               v = ∑ i, cc i * relu (linVal (p i) x (r i))}
      (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc p r xl xu)) := by
  rw [patternSup_carrier_eq cc p r xl xu hbox]
  exact multiReluCut_box_exact cc p r xl xu hcc hbox

/-- Tightness transport: every bound `B` valid for the weighted ReLU sum on the
whole box dominates the gap module's pattern-sup (the gap module's sup is the
LEAST valid joint bound — `patternMax_le_of_valid_bound` across the carrier
equality). -/
theorem gapModule_patternSup_least_valid {n k : ℕ} (cc : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hvalid : ∀ x : Fin n → ℚ, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) →
              (∑ i, cc i * relu (linVal (p i) x (r i))) ≤ B) :
    Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc p r xl xu) ≤ B := by
  rw [patternSup_carrier_eq cc p r xl xu hbox]
  exact patternMax_le_of_valid_bound cc p r xl xu B hcc hbox hvalid

/-- **`gap_closed_form`, re-grounded reading.**  Under the gap module's own
hypotheses, BOTH: (i) the bound subtracted in `gap_closed_form` is the EXACT
joint-cut supremum over the box (`IsGreatest` — validity and attainment), and
(ii) the gap to it has the closed form `inf'_S [off-pattern decoupled mass +
coordinate defect]`.  This is the formal statement of "the gap to the exact
joint-cut bound" that the gap module's header cites informally — the wave-1
report's §3.2 connection, now a theorem. -/
theorem gap_closed_form_exact {n k : ℕ} (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ)
    (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < InventionWave1.uzExact p r xl xu i) :
    IsGreatest
      {v : ℚ | ∃ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
               v = ∑ i, cc i * relu (linVal (p i) x (r i))}
      (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc p r xl xu))
    ∧ (∑ i, cc i * relu (InventionWave1.uzExact p r xl xu i))
        - (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (InventionWave1.patternBound cc p r xl xu))
      = Finset.univ.powerset.inf' ⟨∅, Finset.empty_mem_powerset _⟩
          (fun S => (∑ i ∈ Sᶜ, cc i * InventionWave1.uzExact p r xl xu i)
                    + InventionWave1.coordDefect cc p xl xu S) :=
  ⟨gapModule_patternSup_exact cc p r xl xu (fun i => le_of_lt (hcc i)) hbox,
   InventionWave1.gap_closed_form cc p r xl xu hcc hbox hunst⟩

/-
  Expected output of every `#print axioms` below (verified via `lake build`):

    '…' depends on axioms: [propext, Classical.choice, Quot.sound]

  No `sorryAx`, no domain-specific axioms.
-/
#print axioms boxMaxAffine_carrier_eq
#print axioms patternBound_carrier_eq
#print axioms patternBound_carrier_funext
#print axioms patternSup_carrier_eq
#print axioms gapModule_patternSup_exact
#print axioms gapModule_patternSup_least_valid
#print axioms gap_closed_form_exact

end InventionWave2
end Crownproof
