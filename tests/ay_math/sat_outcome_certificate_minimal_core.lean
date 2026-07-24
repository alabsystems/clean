-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal final-outcome certificate. The SAT branch keeps only visible-model
-- reconstruction; the UNSAT branch keeps only original-to-visible transport
-- and final-clause replay.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyOriginalToVisible (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyFinalClauseReplay (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AyMinimalSatCertificate (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel (AyVisibleModelReconstruction visibleModel originalModel)

def AyMinimalUnsatCertificate
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj
    finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))

def AyMinimalOutcomeCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyDisj
    (AyMinimalSatCertificate visibleModel originalModel)
    (AyMinimalUnsatCertificate originalFormula visibleFormula finalClause)

def AyFinalOutcome (originalModel : Prop) (originalUnsat : Prop) :=
  AyDisj originalModel originalUnsat

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun hp _hq => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

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
    AyOriginalToVisible before after := by
  intro equisat
  exact ay_conj_left
    (before -> after)
    (after -> before)
    equisat

theorem ay_minimal_sat_certificate_intro
    (visibleModel : Prop) (originalModel : Prop) :
    visibleModel ->
    AyVisibleModelReconstruction visibleModel originalModel ->
    AyMinimalSatCertificate visibleModel originalModel := by
  intro hvisible
  intro reconstruct
  exact ay_conj_intro
    visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    hvisible
    reconstruct

theorem ay_minimal_sat_certificate_model
    (visibleModel : Prop) (originalModel : Prop) :
    AyMinimalSatCertificate visibleModel originalModel ->
    originalModel := by
  intro sat_cert
  exact sat_cert originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_minimal_unsat_certificate_intro
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    finalClause ->
    AyOriginalToVisible originalFormula visibleFormula ->
    AyFinalClauseReplay visibleFormula finalClause ->
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause := by
  intro hfinal
  intro original_to_visible
  intro replay
  exact ay_conj_intro
    finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    hfinal
    (ay_conj_intro
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause)
      original_to_visible
      replay)

theorem ay_minimal_unsat_project_final_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    finalClause := by
  intro unsat_cert
  exact ay_conj_left finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    unsat_cert

theorem ay_minimal_unsat_project_original_to_visible
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro unsat_cert
  exact unsat_cert (AyOriginalToVisible originalFormula visibleFormula)
    (fun _hfinal tail =>
      tail (AyOriginalToVisible originalFormula visibleFormula)
        (fun original_to_visible _replay => original_to_visible))

theorem ay_minimal_unsat_project_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    AyFinalClauseReplay visibleFormula finalClause := by
  intro unsat_cert
  exact unsat_cert (AyFinalClauseReplay visibleFormula finalClause)
    (fun _hfinal tail =>
      tail (AyFinalClauseReplay visibleFormula finalClause)
        (fun _original_to_visible replay => replay))

theorem ay_minimal_unsat_certificate_sound
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro unsat_cert
  intro horiginal
  exact
    (ay_minimal_unsat_project_replay
      originalFormula visibleFormula finalClause unsat_cert)
    (ay_minimal_unsat_project_final_clause
      originalFormula visibleFormula finalClause unsat_cert)
    ((ay_minimal_unsat_project_original_to_visible
      originalFormula visibleFormula finalClause unsat_cert)
      horiginal)

theorem ay_minimal_outcome_sat
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyMinimalSatCertificate visibleModel originalModel ->
    AyMinimalOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro sat_cert
  exact ay_disj_left
    (AyMinimalSatCertificate visibleModel originalModel)
    (AyMinimalUnsatCertificate
      originalFormula visibleFormula finalClause)
    sat_cert

theorem ay_minimal_outcome_unsat
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    AyMinimalOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro unsat_cert
  exact ay_disj_right
    (AyMinimalSatCertificate visibleModel originalModel)
    (AyMinimalUnsatCertificate
      originalFormula visibleFormula finalClause)
    unsat_cert

theorem ay_minimal_outcome_final
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyMinimalOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFinalOutcome originalModel (Not originalFormula) := by
  intro outcome
  exact outcome (AyFinalOutcome originalModel (Not originalFormula))
    (fun sat_cert =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_minimal_sat_certificate_model
          visibleModel originalModel sat_cert))
    (fun unsat_cert =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_minimal_unsat_certificate_sound
          originalFormula visibleFormula finalClause unsat_cert))

theorem ay_minimal_sat_soundness
    (visibleModel : Prop) (originalModel : Prop) :
    AyMinimalSatCertificate visibleModel originalModel ->
    originalModel := by
  intro sat_cert
  exact ay_minimal_sat_certificate_model
    visibleModel originalModel sat_cert

theorem ay_minimal_unsat_soundness
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro unsat_cert
  exact ay_minimal_unsat_certificate_sound
    originalFormula visibleFormula finalClause unsat_cert

theorem ay_equisat_to_minimal_unsat_certificate
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyEquisat originalFormula visibleFormula ->
    finalClause ->
    AyFinalClauseReplay visibleFormula finalClause ->
    AyMinimalUnsatCertificate originalFormula visibleFormula finalClause := by
  intro equisat
  intro hfinal
  intro replay
  exact ay_minimal_unsat_certificate_intro
    originalFormula visibleFormula finalClause
    hfinal
    (ay_equisat_forward originalFormula visibleFormula equisat)
    replay
