-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Roundtripping compressed SAT/UNSAT outcome certificates back to full
-- certificates. Compression discards metadata; inflation restores it from
-- explicit metadata witnesses while preserving the boundary soundness facts.

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
    (visibleModel : Prop) (originalModel : Prop) (satMetadata : Prop) :=
  AyConj satMetadata
    (AyConj visibleModel
      (AyVisibleModelReconstruction visibleModel originalModel))

def AyCompressedSatCertificate (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyFullUnsatCertificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :=
  AyConj proofMetadata
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

def AyRoundtripMetadata (satMetadata : Prop) (proofMetadata : Prop) :=
  AyConj satMetadata proofMetadata

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

theorem ay_metadata_project_sat
    (satMetadata : Prop) (proofMetadata : Prop) :
    AyRoundtripMetadata satMetadata proofMetadata ->
    satMetadata := by
  intro metadata
  exact ay_conj_left satMetadata proofMetadata metadata

theorem ay_metadata_project_proof
    (satMetadata : Prop) (proofMetadata : Prop) :
    AyRoundtripMetadata satMetadata proofMetadata ->
    proofMetadata := by
  intro metadata
  exact metadata proofMetadata
    (fun _sat proof => proof)

theorem ay_compressed_sat_project_visible
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSatCertificate visibleModel originalModel ->
    visibleModel := by
  intro compressed
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    compressed

theorem ay_compressed_sat_project_reconstruction
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSatCertificate visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro compressed
  exact compressed
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_inflate_sat_certificate
    (visibleModel : Prop) (originalModel : Prop) (satMetadata : Prop) :
    satMetadata ->
    AyCompressedSatCertificate visibleModel originalModel ->
    AyFullSatCertificate visibleModel originalModel satMetadata := by
  intro hsmetadata
  intro compressed
  exact ay_conj_intro satMetadata
    (AyConj visibleModel
      (AyVisibleModelReconstruction visibleModel originalModel))
    hsmetadata
    compressed

theorem ay_full_sat_project_metadata
    (visibleModel : Prop) (originalModel : Prop) (satMetadata : Prop) :
    AyFullSatCertificate visibleModel originalModel satMetadata ->
    satMetadata := by
  intro full
  exact ay_conj_left satMetadata
    (AyConj visibleModel
      (AyVisibleModelReconstruction visibleModel originalModel))
    full

theorem ay_full_sat_compress
    (visibleModel : Prop) (originalModel : Prop) (satMetadata : Prop) :
    AyFullSatCertificate visibleModel originalModel satMetadata ->
    AyCompressedSatCertificate visibleModel originalModel := by
  intro full
  exact full (AyCompressedSatCertificate visibleModel originalModel)
    (fun _metadata compressed => compressed)

theorem ay_sat_compress_inflate_roundtrip
    (visibleModel : Prop) (originalModel : Prop) (satMetadata : Prop) :
    AyFullSatCertificate visibleModel originalModel satMetadata ->
    AyFullSatCertificate visibleModel originalModel satMetadata := by
  intro full
  exact ay_inflate_sat_certificate
    visibleModel originalModel satMetadata
    (ay_full_sat_project_metadata
      visibleModel originalModel satMetadata full)
    (ay_full_sat_compress
      visibleModel originalModel satMetadata full)

theorem ay_compressed_sat_reconstructs_model
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSatCertificate visibleModel originalModel ->
    originalModel := by
  intro compressed
  exact
    (ay_compressed_sat_project_reconstruction
      visibleModel originalModel compressed)
    (ay_compressed_sat_project_visible
      visibleModel originalModel compressed)

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

theorem ay_inflate_unsat_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    proofMetadata ->
    AyCompressedUnsatCertificate originalFormula visibleFormula finalClause ->
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata := by
  intro hmetadata
  intro compressed
  exact ay_conj_intro proofMetadata
    (AyConj finalClause
      (AyConj
        (AyOriginalToVisible originalFormula visibleFormula)
        (AyFinalClauseReplay visibleFormula finalClause)))
    hmetadata
    compressed

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

theorem ay_full_unsat_compress
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    AyCompressedUnsatCertificate originalFormula visibleFormula finalClause := by
  intro full
  exact full
    (AyCompressedUnsatCertificate originalFormula visibleFormula finalClause)
    (fun _metadata compressed => compressed)

theorem ay_unsat_compress_inflate_roundtrip
    (originalFormula : Prop) (visibleFormula : Prop)
    (finalClause : Prop) (proofMetadata : Prop) :
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata ->
    AyFullUnsatCertificate
      originalFormula visibleFormula finalClause proofMetadata := by
  intro full
  exact ay_inflate_unsat_certificate
    originalFormula visibleFormula finalClause proofMetadata
    (ay_full_unsat_project_metadata
      originalFormula visibleFormula finalClause proofMetadata full)
    (ay_full_unsat_compress
      originalFormula visibleFormula finalClause proofMetadata full)

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

theorem ay_inflate_outcome_certificate
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyRoundtripMetadata satMetadata proofMetadata ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata := by
  intro metadata
  intro compressed
  exact compressed
    (AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata)
    (fun sat_cert =>
      ay_disj_left
        (AyFullSatCertificate visibleModel originalModel satMetadata)
        (AyFullUnsatCertificate
          originalFormula visibleFormula finalClause proofMetadata)
        (ay_inflate_sat_certificate
          visibleModel originalModel satMetadata
          (ay_metadata_project_sat satMetadata proofMetadata metadata)
          sat_cert))
    (fun unsat_cert =>
      ay_disj_right
        (AyFullSatCertificate visibleModel originalModel satMetadata)
        (AyFullUnsatCertificate
          originalFormula visibleFormula finalClause proofMetadata)
        (ay_inflate_unsat_certificate
          originalFormula visibleFormula finalClause proofMetadata
          (ay_metadata_project_proof satMetadata proofMetadata metadata)
          unsat_cert))

theorem ay_full_outcome_compress
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro full
  exact full
    (AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun sat_cert =>
      ay_disj_left
        (AyCompressedSatCertificate visibleModel originalModel)
        (AyCompressedUnsatCertificate
          originalFormula visibleFormula finalClause)
        (ay_full_sat_compress
          visibleModel originalModel satMetadata sat_cert))
    (fun unsat_cert =>
      ay_disj_right
        (AyCompressedSatCertificate visibleModel originalModel)
        (AyCompressedUnsatCertificate
          originalFormula visibleFormula finalClause)
        (ay_full_unsat_compress
          originalFormula visibleFormula finalClause proofMetadata
          unsat_cert))

theorem ay_full_outcome_roundtrip
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata ->
    AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata := by
  intro full
  exact full
    (AyFullOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata)
    (fun sat_cert =>
      ay_disj_left
        (AyFullSatCertificate visibleModel originalModel satMetadata)
        (AyFullUnsatCertificate
          originalFormula visibleFormula finalClause proofMetadata)
        (ay_sat_compress_inflate_roundtrip
          visibleModel originalModel satMetadata sat_cert))
    (fun unsat_cert =>
      ay_disj_right
        (AyFullSatCertificate visibleModel originalModel satMetadata)
        (AyFullUnsatCertificate
          originalFormula visibleFormula finalClause proofMetadata)
        (ay_unsat_compress_inflate_roundtrip
          originalFormula visibleFormula finalClause proofMetadata
          unsat_cert))

theorem ay_compressed_outcome_roundtrip_with_metadata
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (satMetadata : Prop) (proofMetadata : Prop) :
    AyRoundtripMetadata satMetadata proofMetadata ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedOutcomeCertificate
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro metadata
  intro compressed
  exact ay_full_outcome_compress
    originalFormula visibleFormula visibleModel originalModel
    finalClause satMetadata proofMetadata
    (ay_inflate_outcome_certificate
      originalFormula visibleFormula visibleModel originalModel
      finalClause satMetadata proofMetadata metadata compressed)

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
