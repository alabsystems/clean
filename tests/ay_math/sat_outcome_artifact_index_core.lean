-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Artifact index for final SAT/UNSAT certificates. The index stores the
-- compressed outcome plus separately addressable replay, visible-model, and
-- preprocessing artifacts.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyOriginalToVisible (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyFinalClauseReplay (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AyCompressedSatCertificate (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyCompressedUnsatCertificate
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))

def AyCompressedOutcomeCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyDisj
    (AyCompressedSatCertificate visibleModel originalModel)
    (AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause)

def AyOutcomeArtifactIndex
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyConj
    (AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (AyConj
      (AyFinalClauseReplay visibleFormula finalClause)
      (AyConj
        visibleModel
        (AyConj
          (AyVisibleModelReconstruction visibleModel originalModel)
          (AyOriginalToVisible originalFormula visibleFormula))))

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

theorem ay_index_lookup_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro index
  exact index
    (AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun outcome _tail => outcome)

theorem ay_index_lookup_replay
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFinalClauseReplay visibleFormula finalClause := by
  intro index
  exact index (AyFinalClauseReplay visibleFormula finalClause)
    (fun _outcome tail =>
      tail (AyFinalClauseReplay visibleFormula finalClause)
        (fun replay _tail2 => replay))

theorem ay_index_lookup_visible_model
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    visibleModel := by
  intro index
  exact index visibleModel
    (fun _outcome tail =>
      tail visibleModel
        (fun _replay tail2 =>
          tail2 visibleModel
            (fun hvisible _tail3 => hvisible)))

theorem ay_index_lookup_model_reconstruction
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro index
  exact index (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _outcome tail =>
      tail (AyVisibleModelReconstruction visibleModel originalModel)
        (fun _replay tail2 =>
          tail2 (AyVisibleModelReconstruction visibleModel originalModel)
            (fun _hvisible tail3 =>
              tail3 (AyVisibleModelReconstruction visibleModel originalModel)
                (fun reconstruct _preprocess => reconstruct))))

theorem ay_index_lookup_preprocessing_map
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro index
  exact index (AyOriginalToVisible originalFormula visibleFormula)
    (fun _outcome tail =>
      tail (AyOriginalToVisible originalFormula visibleFormula)
        (fun _replay tail2 =>
          tail2 (AyOriginalToVisible originalFormula visibleFormula)
            (fun _hvisible tail3 =>
              tail3 (AyOriginalToVisible originalFormula visibleFormula)
                (fun _reconstruct preprocess => preprocess))))

theorem ay_index_reconstruct_sat_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedSatCertificate visibleModel originalModel := by
  intro index
  exact ay_conj_intro visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    (ay_index_lookup_visible_model
      originalFormula visibleFormula visibleModel originalModel finalClause
      index)
    (ay_index_lookup_model_reconstruction
      originalFormula visibleFormula visibleModel originalModel finalClause
      index)

theorem ay_index_reconstruct_unsat_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    finalClause ->
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause := by
  intro hfinal
  intro index
  exact ay_conj_intro finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    hfinal
    (ay_conj_intro
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause)
      (ay_index_lookup_preprocessing_map
        originalFormula visibleFormula visibleModel originalModel finalClause
        index)
      (ay_index_lookup_replay
        originalFormula visibleFormula visibleModel originalModel finalClause
        index))

theorem ay_compressed_sat_reconstructs_model
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSatCertificate visibleModel originalModel ->
    originalModel := by
  intro sat_cert
  exact sat_cert originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_compressed_unsat_project_final_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    finalClause := by
  intro unsat_cert
  exact ay_conj_left finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    unsat_cert

theorem ay_compressed_unsat_project_original_to_visible
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro unsat_cert
  exact unsat_cert (AyOriginalToVisible originalFormula visibleFormula)
    (fun _hfinal maps =>
      maps (AyOriginalToVisible originalFormula visibleFormula)
        (fun original_to_visible _replay => original_to_visible))

theorem ay_compressed_unsat_project_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    AyFinalClauseReplay visibleFormula finalClause := by
  intro unsat_cert
  exact unsat_cert (AyFinalClauseReplay visibleFormula finalClause)
    (fun _hfinal maps =>
      maps (AyFinalClauseReplay visibleFormula finalClause)
        (fun _original_to_visible replay => replay))

theorem ay_compressed_unsat_final_clause_sound
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro unsat_cert
  intro horiginal
  exact
    (ay_compressed_unsat_project_replay
      originalFormula visibleFormula finalClause unsat_cert)
    (ay_compressed_unsat_project_final_clause
      originalFormula visibleFormula finalClause unsat_cert)
    ((ay_compressed_unsat_project_original_to_visible
      originalFormula visibleFormula finalClause unsat_cert)
      horiginal)

theorem ay_index_sat_reconstructs_model
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    originalModel := by
  intro index
  exact ay_compressed_sat_reconstructs_model
    visibleModel originalModel
    (ay_index_reconstruct_sat_certificate
      originalFormula visibleFormula visibleModel originalModel finalClause
      index)

theorem ay_index_unsat_sound_from_final_clause
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    finalClause ->
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    Not originalFormula := by
  intro hfinal
  intro index
  exact ay_compressed_unsat_final_clause_sound
    originalFormula visibleFormula finalClause
    (ay_index_reconstruct_unsat_certificate
      originalFormula visibleFormula visibleModel originalModel finalClause
      hfinal index)

theorem ay_index_final_outcome_from_artifacts
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyOutcomeArtifactIndex
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFinalOutcome originalModel (Not originalFormula) := by
  intro index
  exact
    (ay_index_lookup_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      index)
      (AyFinalOutcome originalModel (Not originalFormula))
      (fun sat_cert =>
        ay_disj_left originalModel (Not originalFormula)
          (ay_compressed_sat_reconstructs_model
            visibleModel originalModel sat_cert))
      (fun unsat_cert =>
        ay_disj_right originalModel (Not originalFormula)
          (ay_compressed_unsat_final_clause_sound
            originalFormula visibleFormula finalClause unsat_cert))

theorem ay_equisat_to_preprocessing_artifact
    (originalFormula : Prop) (visibleFormula : Prop) :
    AyEquisat originalFormula visibleFormula ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro equisat
  exact ay_equisat_forward originalFormula visibleFormula equisat
