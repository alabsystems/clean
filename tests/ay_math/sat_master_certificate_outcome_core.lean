-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Master certificate outcome skeleton. Formula propositions stand for
-- satisfiable states; solver-loop SAT/UNSAT outcomes and proof replay are
-- abstract checker facts transported through preprocessing equisat maps.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyMasterPreprocessingCertificate (original : Prop) (visible : Prop) :=
  AyEquisat original visible

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyProofReplay (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AyCdclSolverOutcome (visibleModel : Prop) (finalClause : Prop) :=
  AyDisj visibleModel finalClause

def AySatSoundOutcome (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatSoundOutcome (finalClause : Prop) (originalUnsat : Prop) :=
  AyConj finalClause (finalClause -> originalUnsat)

def AyCertifiedFinalOutcome (originalModel : Prop) (originalUnsat : Prop) :=
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
    before -> after := by
  intro equisat
  exact ay_conj_left
    (before -> after)
    (after -> before)
    equisat

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after -> before := by
  intro equisat
  exact equisat (after -> before)
    (fun _forward backward => backward)

theorem ay_master_preprocessing_forward
    (original : Prop) (visible : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    original -> visible := by
  intro master
  exact ay_equisat_forward original visible master

theorem ay_master_preprocessing_backward
    (original : Prop) (visible : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    visible -> original := by
  intro master
  exact ay_equisat_backward original visible master

theorem ay_visible_model_reconstruction_for_sat
    (original : Prop) (visible : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    visible ->
    original := by
  intro master
  exact ay_master_preprocessing_backward original visible master

theorem ay_sat_sound_outcome_intro
    (visibleModel : Prop) (originalModel : Prop) :
    AyVisibleModelReconstruction visibleModel originalModel ->
    visibleModel ->
    AySatSoundOutcome visibleModel originalModel := by
  intro reconstruct
  intro hvisible
  exact ay_conj_intro
    visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    hvisible
    reconstruct

theorem ay_sat_sound_outcome_original_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatSoundOutcome visibleModel originalModel ->
    originalModel := by
  intro outcome
  exact outcome originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_proof_replay_final_clause_sound_visible
    (visibleFormula : Prop) (finalClause : Prop) :
    AyProofReplay visibleFormula finalClause ->
    finalClause ->
    visibleFormula -> False := by
  intro replay
  intro hfinal
  intro hvisible
  exact replay hfinal hvisible

theorem ay_final_clause_sound_for_unsat
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    AyProofReplay visible finalClause ->
    finalClause ->
    original -> False := by
  intro master
  intro replay
  intro hfinal
  intro horiginal
  exact replay hfinal
    (ay_master_preprocessing_forward original visible master horiginal)

theorem ay_unsat_sound_outcome_intro
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    AyProofReplay visible finalClause ->
    finalClause ->
    AyUnsatSoundOutcome finalClause (Not original) := by
  intro master
  intro replay
  intro hfinal
  exact ay_conj_intro finalClause (finalClause -> Not original)
    hfinal
    (fun hfinal_again =>
      ay_final_clause_sound_for_unsat
        original visible finalClause master replay hfinal_again)

theorem ay_unsat_sound_outcome_original_unsat
    (finalClause : Prop) (originalUnsat : Prop) :
    AyUnsatSoundOutcome finalClause originalUnsat ->
    originalUnsat := by
  intro outcome
  exact outcome originalUnsat
    (fun hfinal final_to_unsat => final_to_unsat hfinal)

theorem ay_cdcl_sat_branch_sound
    (original : Prop) (visible : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    visible ->
    AyCertifiedFinalOutcome original (Not original) := by
  intro master
  intro hvisible
  exact ay_disj_left original (Not original)
    (ay_visible_model_reconstruction_for_sat original visible master hvisible)

theorem ay_cdcl_unsat_branch_sound
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    AyProofReplay visible finalClause ->
    finalClause ->
    AyCertifiedFinalOutcome original (Not original) := by
  intro master
  intro replay
  intro hfinal
  exact ay_disj_right original (Not original)
    (ay_final_clause_sound_for_unsat
      original visible finalClause master replay hfinal)

theorem ay_cdcl_solver_outcome_sound
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    AyProofReplay visible finalClause ->
    AyCdclSolverOutcome visible finalClause ->
    AyCertifiedFinalOutcome original (Not original) := by
  intro master
  intro replay
  intro outcome
  exact outcome (AyCertifiedFinalOutcome original (Not original))
    (fun hvisible =>
      ay_cdcl_sat_branch_sound original visible master hvisible)
    (fun hfinal =>
      ay_cdcl_unsat_branch_sound
        original visible finalClause master replay hfinal)

theorem ay_master_certificate_sat_soundness
    (original : Prop) (visible : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    visible ->
    original := by
  intro master
  exact ay_visible_model_reconstruction_for_sat original visible master

theorem ay_master_certificate_unsat_soundness
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyMasterPreprocessingCertificate original visible ->
    AyProofReplay visible finalClause ->
    finalClause ->
    Not original := by
  intro master
  intro replay
  exact ay_final_clause_sound_for_unsat
    original visible finalClause master replay
