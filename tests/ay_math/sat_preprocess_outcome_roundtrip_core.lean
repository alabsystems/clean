-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for round-tripping solver SAT/UNSAT outcomes through
-- preprocessing and visible projection. The propositions stand for formula
-- satisfiability, visible model payloads, replay certificates, and conflicts.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySolverSat (formula : Prop) (model : Prop) :=
  AyConj formula model

def AyProofReplay (formula : Prop) (certificate : Prop) (conflict : Prop) :=
  formula -> certificate -> conflict

def AyPreprocessRoundtripCertificate
    (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyConj
    (AyEquisat original preprocessed)
    (AyEquisat preprocessed visible)

def AyVisibleSatOutcome
    (original : Prop) (visible : Prop) (model : Prop) :=
  AyConj original (AyConj visible model)

def AyVisibleUnsatOutcome
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj original (AyConj visible (AyConj certificate conflict))

def AyOutcomeRoundtrip
    (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

theorem ay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before -> after := by
  intro equisat
  exact ay_conj_left (before -> after) (after -> before) equisat

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after -> before := by
  intro equisat
  exact ay_conj_right (before -> after) (after -> before) equisat

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_roundtrip_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyOutcomeRoundtrip before after := by
  intro forward
  intro backward
  exact ay_conj_intro (before -> after) (after -> before)
    forward backward

theorem ay_roundtrip_forward
    (before : Prop) (after : Prop) :
    AyOutcomeRoundtrip before after ->
    before -> after := by
  intro roundtrip
  exact ay_conj_left (before -> after) (after -> before) roundtrip

theorem ay_roundtrip_backward
    (before : Prop) (after : Prop) :
    AyOutcomeRoundtrip before after ->
    after -> before := by
  intro roundtrip
  exact ay_conj_right (before -> after) (after -> before) roundtrip

theorem ay_preprocess_internal_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyEquisat original preprocessed := by
  intro cert
  exact ay_conj_left
    (AyEquisat original preprocessed)
    (AyEquisat preprocessed visible)
    cert

theorem ay_preprocess_visible_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyEquisat preprocessed visible := by
  intro cert
  exact ay_conj_right
    (AyEquisat original preprocessed)
    (AyEquisat preprocessed visible)
    cert

theorem ay_preprocess_original_visible_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyEquisat original visible := by
  intro cert
  exact ay_equisat_trans original preprocessed visible
    (ay_preprocess_internal_equisat original preprocessed visible cert)
    (ay_preprocess_visible_equisat original preprocessed visible cert)

theorem ay_original_to_preprocessed
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    original ->
    preprocessed := by
  intro cert
  exact ay_equisat_forward original preprocessed
    (ay_preprocess_internal_equisat original preprocessed visible cert)

theorem ay_preprocessed_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    preprocessed ->
    original := by
  intro cert
  exact ay_equisat_backward original preprocessed
    (ay_preprocess_internal_equisat original preprocessed visible cert)

theorem ay_preprocessed_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    preprocessed ->
    visible := by
  intro cert
  exact ay_equisat_forward preprocessed visible
    (ay_preprocess_visible_equisat original preprocessed visible cert)

theorem ay_visible_to_preprocessed
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    visible ->
    preprocessed := by
  intro cert
  exact ay_equisat_backward preprocessed visible
    (ay_preprocess_visible_equisat original preprocessed visible cert)

theorem ay_original_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    original ->
    visible := by
  intro cert
  intro horiginal
  exact ay_equisat_forward original visible
    (ay_preprocess_original_visible_equisat
      original preprocessed visible cert)
    horiginal

theorem ay_visible_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    visible ->
    original := by
  intro cert
  intro hvisible
  exact ay_equisat_backward original visible
    (ay_preprocess_original_visible_equisat
      original preprocessed visible cert)
    hvisible

theorem ay_solver_sat_formula
    (formula : Prop) (model : Prop) :
    AySolverSat formula model ->
    formula := by
  intro sat
  exact ay_conj_left formula model sat

theorem ay_solver_sat_model
    (formula : Prop) (model : Prop) :
    AySolverSat formula model ->
    model := by
  intro sat
  exact ay_conj_right formula model sat

theorem ay_visible_sat_original
    (original : Prop) (visible : Prop) (model : Prop) :
    AyVisibleSatOutcome original visible model ->
    original := by
  intro outcome
  exact ay_conj_left original (AyConj visible model) outcome

theorem ay_visible_sat_visible
    (original : Prop) (visible : Prop) (model : Prop) :
    AyVisibleSatOutcome original visible model ->
    visible := by
  intro outcome
  exact ay_conj_left visible model
    (ay_conj_right original (AyConj visible model) outcome)

theorem ay_visible_sat_model
    (original : Prop) (visible : Prop) (model : Prop) :
    AyVisibleSatOutcome original visible model ->
    model := by
  intro outcome
  exact ay_conj_right visible model
    (ay_conj_right original (AyConj visible model) outcome)

theorem ay_preprocessed_sat_to_visible_outcome
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AySolverSat preprocessed model ->
    AyVisibleSatOutcome original visible model := by
  intro cert
  intro sat
  exact ay_conj_intro original (AyConj visible model)
    (ay_preprocessed_to_original original preprocessed visible cert
      (ay_solver_sat_formula preprocessed model sat))
    (ay_conj_intro visible model
      (ay_preprocessed_to_visible original preprocessed visible cert
        (ay_solver_sat_formula preprocessed model sat))
      (ay_solver_sat_model preprocessed model sat))

theorem ay_visible_outcome_to_preprocessed_sat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyVisibleSatOutcome original visible model ->
    AySolverSat preprocessed model := by
  intro cert
  intro outcome
  exact ay_conj_intro preprocessed model
    (ay_visible_to_preprocessed original preprocessed visible cert
      (ay_visible_sat_visible original visible model outcome))
    (ay_visible_sat_model original visible model outcome)

theorem ay_sat_branch_roundtrip
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyOutcomeRoundtrip
      (AySolverSat preprocessed model)
      (AyVisibleSatOutcome original visible model) := by
  intro cert
  exact ay_roundtrip_intro
    (AySolverSat preprocessed model)
    (AyVisibleSatOutcome original visible model)
    (ay_preprocessed_sat_to_visible_outcome
      original preprocessed visible model cert)
    (ay_visible_outcome_to_preprocessed_sat
      original preprocessed visible model cert)

theorem ay_sat_roundtrip_identity_witness
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AySolverSat preprocessed model ->
    AySolverSat preprocessed model := by
  intro cert
  intro sat
  exact ay_roundtrip_backward
    (AySolverSat preprocessed model)
    (AyVisibleSatOutcome original visible model)
    (ay_sat_branch_roundtrip original preprocessed visible model cert)
    (ay_roundtrip_forward
      (AySolverSat preprocessed model)
      (AyVisibleSatOutcome original visible model)
      (ay_sat_branch_roundtrip original preprocessed visible model cert)
      sat)

theorem ay_visible_sat_roundtrip_identity_witness
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyVisibleSatOutcome original visible model ->
    AyVisibleSatOutcome original visible model := by
  intro cert
  intro outcome
  exact ay_roundtrip_forward
    (AySolverSat preprocessed model)
    (AyVisibleSatOutcome original visible model)
    (ay_sat_branch_roundtrip original preprocessed visible model cert)
    (ay_roundtrip_backward
      (AySolverSat preprocessed model)
      (AyVisibleSatOutcome original visible model)
      (ay_sat_branch_roundtrip original preprocessed visible model cert)
      outcome)

theorem ay_replay_preprocessed_to_original_conflict
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (certificate : Prop) (conflict : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    original ->
    conflict := by
  intro cert
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_original_to_preprocessed original preprocessed visible cert
      horiginal)
    hcertificate

theorem ay_unsat_to_visible_outcome
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (certificate : Prop) (conflict : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    original ->
    AyVisibleUnsatOutcome original visible certificate conflict := by
  intro cert
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_conj_intro original
    (AyConj visible (AyConj certificate conflict))
    horiginal
    (ay_conj_intro visible (AyConj certificate conflict)
      (ay_original_to_visible original preprocessed visible cert horiginal)
      (ay_conj_intro certificate conflict
        hcertificate
        (ay_replay_preprocessed_to_original_conflict
          original preprocessed visible certificate conflict
          cert replay hcertificate horiginal)))

theorem ay_visible_unsat_original
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsatOutcome original visible certificate conflict ->
    original := by
  intro outcome
  exact ay_conj_left original
    (AyConj visible (AyConj certificate conflict))
    outcome

theorem ay_visible_unsat_visible
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsatOutcome original visible certificate conflict ->
    visible := by
  intro outcome
  exact ay_conj_left visible (AyConj certificate conflict)
    (ay_conj_right original
      (AyConj visible (AyConj certificate conflict))
      outcome)

theorem ay_visible_unsat_certificate
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsatOutcome original visible certificate conflict ->
    certificate := by
  intro outcome
  exact ay_conj_left certificate conflict
    (ay_conj_right visible (AyConj certificate conflict)
      (ay_conj_right original
        (AyConj visible (AyConj certificate conflict))
        outcome))

theorem ay_visible_unsat_conflict
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsatOutcome original visible certificate conflict ->
    conflict := by
  intro outcome
  exact ay_conj_right certificate conflict
    (ay_conj_right visible (AyConj certificate conflict)
      (ay_conj_right original
        (AyConj visible (AyConj certificate conflict))
        outcome))

theorem ay_visible_unsat_roundtrip_identity_witness
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsatOutcome original visible certificate conflict ->
    AyVisibleUnsatOutcome original visible certificate conflict := by
  intro outcome
  exact ay_conj_intro original
    (AyConj visible (AyConj certificate conflict))
    (ay_visible_unsat_original original visible certificate conflict outcome)
    (ay_conj_intro visible (AyConj certificate conflict)
      (ay_visible_unsat_visible original visible certificate conflict outcome)
      (ay_conj_intro certificate conflict
        (ay_visible_unsat_certificate
          original visible certificate conflict outcome)
        (ay_visible_unsat_conflict
          original visible certificate conflict outcome)))

theorem ay_unsat_certificate_roundtrip_from_original
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (certificate : Prop) (conflict : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    original ->
    AyConj certificate conflict := by
  intro cert
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_conj_intro certificate conflict
    hcertificate
    (ay_replay_preprocessed_to_original_conflict
      original preprocessed visible certificate conflict
      cert replay hcertificate horiginal)

theorem ay_outcome_choice_roundtrip_sat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) (unsatBranch : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyDisj (AySolverSat preprocessed model) unsatBranch ->
    AyDisj (AyVisibleSatOutcome original visible model) unsatBranch := by
  intro cert
  intro choice
  intro result
  intro sat_case
  intro unsat_case
  exact choice result
    (fun sat =>
      sat_case
        (ay_preprocessed_sat_to_visible_outcome
          original preprocessed visible model cert sat))
    unsat_case

theorem ay_outcome_choice_roundtrip_back_sat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) (unsatBranch : Prop) :
    AyPreprocessRoundtripCertificate original preprocessed visible ->
    AyDisj (AyVisibleSatOutcome original visible model) unsatBranch ->
    AyDisj (AySolverSat preprocessed model) unsatBranch := by
  intro cert
  intro choice
  intro result
  intro sat_case
  intro unsat_case
  exact choice result
    (fun outcome =>
      sat_case
        (ay_visible_outcome_to_preprocessed_sat
          original preprocessed visible model cert outcome))
    unsat_case
