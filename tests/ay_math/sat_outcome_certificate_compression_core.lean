-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact final-outcome certificate compression. Full certificates may carry
-- redundant trace/model metadata; compression keeps only the boundary facts
-- needed for SAT model reconstruction and UNSAT final-clause soundness.

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

def AyFullSatCertificate
    (visibleModel : Prop) (originalModel : Prop) (metadata : Prop) :=
  AyConj
    metadata
    (AyConj visibleModel
      (AyVisibleModelReconstruction visibleModel originalModel))

def AyCompressedSatCertificate (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyFullUnsatCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :=
  AyConj
    proofMetadata
    (AyConj finalClause
      (AyConj
        (AyOriginalToVisible originalFormula visibleFormula)
        (AyFinalClauseReplay visibleFormula finalClause)))

def AyCompressedUnsatCertificate
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))

def AyFullOutcomeCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :=
  AyDisj
    (AyFullSatCertificate visibleModel originalModel satMetadata)
    (AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata)

def AyCompressedOutcomeCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyDisj
    (AyCompressedSatCertificate visibleModel originalModel)
    (AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause)

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

theorem ay_full_sat_project_metadata
    (visibleModel : Prop) (originalModel : Prop) (metadata : Prop) :
    AyFullSatCertificate visibleModel originalModel metadata ->
    metadata := by
  intro full
  exact ay_conj_left metadata
    (AyConj visibleModel
      (AyVisibleModelReconstruction visibleModel originalModel))
    full

theorem ay_full_sat_project_visible
    (visibleModel : Prop) (originalModel : Prop) (metadata : Prop) :
    AyFullSatCertificate visibleModel originalModel metadata ->
    visibleModel := by
  intro full
  exact full visibleModel
    (fun _metadata tail =>
      tail visibleModel
        (fun hvisible _reconstruct => hvisible))

theorem ay_full_sat_project_reconstruction
    (visibleModel : Prop) (originalModel : Prop) (metadata : Prop) :
    AyFullSatCertificate visibleModel originalModel metadata ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro full
  exact full
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _metadata tail =>
      tail (AyVisibleModelReconstruction visibleModel originalModel)
        (fun _hvisible reconstruct => reconstruct))

theorem ay_compress_sat_certificate
    (visibleModel : Prop) (originalModel : Prop) (metadata : Prop) :
    AyFullSatCertificate visibleModel originalModel metadata ->
    AyCompressedSatCertificate visibleModel originalModel := by
  intro full
  exact ay_conj_intro visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    (ay_full_sat_project_visible visibleModel originalModel metadata full)
    (ay_full_sat_project_reconstruction
      visibleModel originalModel metadata full)

theorem ay_compressed_sat_reconstructs_model
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSatCertificate visibleModel originalModel ->
    originalModel := by
  intro compressed
  exact compressed originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_full_unsat_project_metadata
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    proofMetadata := by
  intro full
  exact ay_conj_left proofMetadata
    (AyConj finalClause
      (AyConj
        (AyOriginalToVisible originalFormula visibleFormula)
        (AyFinalClauseReplay visibleFormula finalClause)))
    full

theorem ay_full_unsat_project_final_clause
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    finalClause := by
  intro full
  exact full finalClause
    (fun _metadata tail =>
      tail finalClause
        (fun hfinal _maps => hfinal))

theorem ay_full_unsat_project_original_to_visible
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro full
  exact full (AyOriginalToVisible originalFormula visibleFormula)
    (fun _metadata tail =>
      tail (AyOriginalToVisible originalFormula visibleFormula)
        (fun _hfinal maps =>
          maps (AyOriginalToVisible originalFormula visibleFormula)
            (fun original_to_visible _replay => original_to_visible)))

theorem ay_full_unsat_project_replay
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    AyFinalClauseReplay visibleFormula finalClause := by
  intro full
  exact full (AyFinalClauseReplay visibleFormula finalClause)
    (fun _metadata tail =>
      tail (AyFinalClauseReplay visibleFormula finalClause)
        (fun _hfinal maps =>
          maps (AyFinalClauseReplay visibleFormula finalClause)
            (fun _original_to_visible replay => replay)))

theorem ay_compress_unsat_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause := by
  intro full
  exact ay_conj_intro finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    (ay_full_unsat_project_final_clause
      originalFormula visibleFormula finalClause proofMetadata full)
    (ay_conj_intro
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause)
      (ay_full_unsat_project_original_to_visible
        originalFormula visibleFormula finalClause proofMetadata full)
      (ay_full_unsat_project_replay
        originalFormula visibleFormula finalClause proofMetadata full))

theorem ay_compressed_unsat_project_final_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    finalClause := by
  intro compressed
  exact ay_conj_left finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    compressed

theorem ay_compressed_unsat_project_original_to_visible
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    AyOriginalToVisible originalFormula visibleFormula := by
  intro compressed
  exact compressed (AyOriginalToVisible originalFormula visibleFormula)
    (fun _hfinal maps =>
      maps (AyOriginalToVisible originalFormula visibleFormula)
        (fun original_to_visible _replay => original_to_visible))

theorem ay_compressed_unsat_project_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    AyFinalClauseReplay visibleFormula finalClause := by
  intro compressed
  exact compressed (AyFinalClauseReplay visibleFormula finalClause)
    (fun _hfinal maps =>
      maps (AyFinalClauseReplay visibleFormula finalClause)
        (fun _original_to_visible replay => replay))

theorem ay_compressed_unsat_final_clause_sound
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro compressed
  intro horiginal
  exact
    (ay_compressed_unsat_project_replay
      originalFormula visibleFormula finalClause compressed)
    (ay_compressed_unsat_project_final_clause
      originalFormula visibleFormula finalClause compressed)
    ((ay_compressed_unsat_project_original_to_visible
      originalFormula visibleFormula finalClause compressed)
      horiginal)

theorem ay_compress_outcome_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause := by
  intro outcome
  exact outcome
    (AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun full_sat =>
      ay_disj_left
        (AyCompressedSatCertificate visibleModel originalModel)
        (AyCompressedUnsatCertificate
          originalFormula visibleFormula finalClause)
        (ay_compress_sat_certificate
          visibleModel originalModel satMetadata full_sat))
    (fun full_unsat =>
      ay_disj_right
        (AyCompressedSatCertificate visibleModel originalModel)
        (AyCompressedUnsatCertificate
          originalFormula visibleFormula finalClause)
        (ay_compress_unsat_certificate
          originalFormula visibleFormula finalClause proofMetadata
          full_unsat))

theorem ay_compressed_outcome_final
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFinalOutcome originalModel (Not originalFormula) := by
  intro compressed
  exact compressed (AyFinalOutcome originalModel (Not originalFormula))
    (fun sat_cert =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_compressed_sat_reconstructs_model
          visibleModel originalModel sat_cert))
    (fun unsat_cert =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_compressed_unsat_final_clause_sound
          originalFormula visibleFormula finalClause unsat_cert))

theorem ay_full_outcome_final_after_compression
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata ->
    AyFinalOutcome originalModel (Not originalFormula) := by
  intro full
  exact ay_compressed_outcome_final
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_compress_outcome_certificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata full)

theorem ay_equisat_to_compressed_unsat_certificate
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyEquisat originalFormula visibleFormula ->
    finalClause ->
    AyFinalClauseReplay visibleFormula finalClause ->
    AyCompressedUnsatCertificate
      originalFormula visibleFormula finalClause := by
  intro equisat
  intro hfinal
  intro replay
  exact ay_conj_intro finalClause
    (AyConj
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause))
    hfinal
    (ay_conj_intro
      (AyOriginalToVisible originalFormula visibleFormula)
      (AyFinalClauseReplay visibleFormula finalClause)
      (ay_equisat_forward originalFormula visibleFormula equisat)
      replay)
