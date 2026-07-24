-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-activity normalization/reindex replay soundness for preprocessing.
-- The propositions stand for activity snapshot digests, variable map manifests,
-- normalization epochs, affected occurrence coverage, transform witnesses,
-- reconstruction hooks, fingerprints, checker replay, fallback/build/validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pvan_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pvan_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pvan_Equisat (before : Prop) (after : Prop) :=
  ay_pvan_Conj (before -> after) (after -> before)

def ay_pvan_Sat (cnf : Prop) (model : Prop) :=
  ay_pvan_Conj cnf model

def ay_pvan_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pvan_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pvan_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pvan_ActivitySnapshotDigest
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop) :=
  ay_pvan_Conj activityDigestWitness
    (activitySnapshot -> activityDigest)

def ay_pvan_VariableMapManifest
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop) :=
  ay_pvan_Conj mapWitness
    (ay_pvan_IdMatch sourceVariable mappedVariable)

def ay_pvan_NormalizationEpoch
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop) :=
  ay_pvan_Conj epochWitness (normalizationEpoch -> epochDigest)

def ay_pvan_AffectedOccurrenceCoverage
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop) :=
  ay_pvan_Conj coverageWitness
    (affectedOccurrence -> coveredOccurrence)

def ay_pvan_TransformWitnessLedger
    (affectedOccurrence : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pvan_Conj transformLedger
    (affectedOccurrence -> transformWitness)

def ay_pvan_ModelReconstruction
    (normalizedCnf : Prop) (originalCnf : Prop)
    (normalizedModel : Prop) (originalModel : Prop) :=
  ay_pvan_Sat normalizedCnf normalizedModel ->
    ay_pvan_Sat originalCnf originalModel

def ay_pvan_ProofReconstruction
    (originalCnf : Prop) (normalizedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pvan_Replay normalizedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pvan_FingerprintAgreement
    (originalFingerprint : Prop) (normalizedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pvan_Conj fingerprintWitness
    (ay_pvan_IdMatch originalFingerprint normalizedFingerprint)

def ay_pvan_CheckerReplay
    (normalizationCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pvan_Conj normalizationCertificate checkerAccepted

def ay_pvan_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pvan_Conj baselineSolver baselineAvailable

def ay_pvan_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pvan_Conj binaryFingerprint buildReproducible

def ay_pvan_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pvan_Conj validatorAccepted validatorVersion

def ay_pvan_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pvan_Conj auditAppended auditAppendOnly

def ay_pvan_AcceptedVariableActivityNormalizationReplay
    (originalCnf : Prop) (normalizedCnf : Prop)
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop)
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop)
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop)
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (normalizedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (normalizedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (normalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pvan_ActivitySnapshotDigest
       activitySnapshot activityDigest activityDigestWitness ->
     ay_pvan_VariableMapManifest
       sourceVariable mappedVariable mapWitness ->
     ay_pvan_NormalizationEpoch
       normalizationEpoch epochDigest epochWitness ->
     ay_pvan_AffectedOccurrenceCoverage
       affectedOccurrence coveredOccurrence coverageWitness ->
     ay_pvan_TransformWitnessLedger
       affectedOccurrence transformWitness transformLedger ->
     ay_pvan_Equisat originalCnf normalizedCnf ->
     ay_pvan_ModelReconstruction
       normalizedCnf originalCnf normalizedModel originalModel ->
     ay_pvan_ProofReconstruction
       originalCnf normalizedCnf certificate conflict ->
     ay_pvan_FingerprintAgreement
       originalFingerprint normalizedFingerprint fingerprintWitness ->
     ay_pvan_CheckerReplay normalizationCertificate checkerAccepted ->
     ay_pvan_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pvan_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pvan_ValidatorGate validatorAccepted validatorVersion ->
     ay_pvan_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pvan_VariableActivityNormalizationFailure
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :=
  forall result : Prop,
    (activityDigestDrift -> result) ->
    (variableMapMismatch -> result) ->
    (normalizationEpochDrift -> result) ->
    (coverageGap -> result) ->
    (transformWitnessMismatch -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pvan_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pvan_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pvan_Conj currentCnf recompute

def ay_pvan_DiagnosticVariableActivityNormalizationReplay
    (currentCnf : Prop)
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pvan_Conj
    (ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction)
    (ay_pvan_Conj
      (ay_pvan_RecomputeObligation currentCnf recompute)
      (ay_pvan_NoSemanticClaim diagnostic))

def ay_pvan_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pvan_Conj exitCode claim

def ay_pvan_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pvan_Disj
    (ay_pvan_ExitCodeSound exitCode (ay_pvan_Sat originalCnf model))
    (ay_pvan_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pvan_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pvan_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pvan_conj_left
    (left : Prop) (right : Prop) :
    ay_pvan_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pvan_conj_right
    (left : Prop) (right : Prop) :
    ay_pvan_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pvan_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pvan_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pvan_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pvan_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pvan_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pvan_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pvan_conj_left (before -> after) (after -> before) eq

theorem ay_pvan_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pvan_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pvan_conj_right (before -> after) (after -> before) eq

theorem ay_pvan_activity_snapshot_digest_applies
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop) :
    ay_pvan_ActivitySnapshotDigest
      activitySnapshot activityDigest activityDigestWitness ->
    activitySnapshot ->
    activityDigest := by
  intro accepted snapshot
  exact
    (ay_pvan_conj_right activityDigestWitness
      (activitySnapshot -> activityDigest) accepted) snapshot

theorem ay_pvan_variable_map_forward
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop) :
    ay_pvan_VariableMapManifest
      sourceVariable mappedVariable mapWitness ->
    sourceVariable ->
    mappedVariable := by
  intro accepted source
  exact accepted mappedVariable
    (fun _witness ids =>
      ids mappedVariable
        (fun forward _backward => forward source))

theorem ay_pvan_variable_map_backward
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop) :
    ay_pvan_VariableMapManifest
      sourceVariable mappedVariable mapWitness ->
    mappedVariable ->
    sourceVariable := by
  intro accepted mapped
  exact accepted sourceVariable
    (fun _witness ids =>
      ids sourceVariable
        (fun _forward backward => backward mapped))

theorem ay_pvan_normalization_epoch_records
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop) :
    ay_pvan_NormalizationEpoch
      normalizationEpoch epochDigest epochWitness ->
    normalizationEpoch ->
    epochDigest := by
  intro accepted epoch
  exact
    (ay_pvan_conj_right epochWitness
      (normalizationEpoch -> epochDigest) accepted) epoch

theorem ay_pvan_affected_occurrence_coverage
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop) :
    ay_pvan_AffectedOccurrenceCoverage
      affectedOccurrence coveredOccurrence coverageWitness ->
    affectedOccurrence ->
    coveredOccurrence := by
  intro accepted affected
  exact
    (ay_pvan_conj_right coverageWitness
      (affectedOccurrence -> coveredOccurrence) accepted) affected

theorem ay_pvan_transform_witness_ledger
    (affectedOccurrence : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pvan_TransformWitnessLedger
      affectedOccurrence transformWitness transformLedger ->
    affectedOccurrence ->
    transformWitness := by
  intro accepted affected
  exact
    (ay_pvan_conj_right transformLedger
      (affectedOccurrence -> transformWitness) accepted) affected

theorem ay_pvan_accepted_equisat
    (originalCnf : Prop) (normalizedCnf : Prop)
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop)
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop)
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop)
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (normalizedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (normalizedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (normalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pvan_AcceptedVariableActivityNormalizationReplay
      originalCnf normalizedCnf activitySnapshot activityDigest
      activityDigestWitness sourceVariable mappedVariable mapWitness
      normalizationEpoch epochDigest epochWitness affectedOccurrence
      coveredOccurrence coverageWitness transformWitness transformLedger
      normalizedModel originalModel certificate conflict originalFingerprint
      normalizedFingerprint fingerprintWitness normalizationCertificate
      checkerAccepted baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pvan_Equisat originalCnf normalizedCnf := by
  intro accepted
  exact accepted (ay_pvan_Equisat originalCnf normalizedCnf)
    (fun _activity _map _epoch _coverage _transform eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pvan_accepted_checker_replay
    (originalCnf : Prop) (normalizedCnf : Prop)
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop)
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop)
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop)
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (normalizedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (normalizedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (normalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pvan_AcceptedVariableActivityNormalizationReplay
      originalCnf normalizedCnf activitySnapshot activityDigest
      activityDigestWitness sourceVariable mappedVariable mapWitness
      normalizationEpoch epochDigest epochWitness affectedOccurrence
      coveredOccurrence coverageWitness transformWitness transformLedger
      normalizedModel originalModel certificate conflict originalFingerprint
      normalizedFingerprint fingerprintWitness normalizationCertificate
      checkerAccepted baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pvan_CheckerReplay normalizationCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pvan_CheckerReplay normalizationCertificate checkerAccepted)
    (fun _activity _map _epoch _coverage _transform _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pvan_accepted_audit_evidence
    (originalCnf : Prop) (normalizedCnf : Prop)
    (activitySnapshot : Prop) (activityDigest : Prop)
    (activityDigestWitness : Prop)
    (sourceVariable : Prop) (mappedVariable : Prop)
    (mapWitness : Prop)
    (normalizationEpoch : Prop) (epochDigest : Prop)
    (epochWitness : Prop)
    (affectedOccurrence : Prop) (coveredOccurrence : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (normalizedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (normalizedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (normalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pvan_AcceptedVariableActivityNormalizationReplay
      originalCnf normalizedCnf activitySnapshot activityDigest
      activityDigestWitness sourceVariable mappedVariable mapWitness
      normalizationEpoch epochDigest epochWitness affectedOccurrence
      coveredOccurrence coverageWitness transformWitness transformLedger
      normalizedModel originalModel certificate conflict originalFingerprint
      normalizedFingerprint fingerprintWitness normalizationCertificate
      checkerAccepted baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pvan_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pvan_AuditEvidence auditAppended auditAppendOnly)
    (fun _activity _map _epoch _coverage _transform _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pvan_sat_pullback
    (normalizedCnf : Prop) (originalCnf : Prop)
    (normalizedModel : Prop) (originalModel : Prop) :
    ay_pvan_ModelReconstruction
      normalizedCnf originalCnf normalizedModel originalModel ->
    ay_pvan_Sat normalizedCnf normalizedModel ->
    ay_pvan_Sat originalCnf originalModel := by
  intro reconstruct normalizedSat
  exact reconstruct normalizedSat

theorem ay_pvan_unsat_pushback
    (originalCnf : Prop) (normalizedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pvan_ProofReconstruction
      originalCnf normalizedCnf certificate conflict ->
    ay_pvan_Replay normalizedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pvan_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pvan_Sat originalCnf model ->
    ay_pvan_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pvan_disj_left
    (ay_pvan_ExitCodeSound exitCode (ay_pvan_Sat originalCnf model))
    (ay_pvan_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pvan_conj_intro exitCode
      (ay_pvan_Sat originalCnf model) exit sat)

theorem ay_pvan_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pvan_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pvan_disj_right
    (ay_pvan_ExitCodeSound exitCode (ay_pvan_Sat originalCnf model))
    (ay_pvan_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pvan_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pvan_failure_activity_digest_drift
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    activityDigestDrift ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hActivity h

theorem ay_pvan_failure_variable_map_mismatch
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    variableMapMismatch ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hMap h

theorem ay_pvan_failure_normalization_epoch_drift
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    normalizationEpochDrift ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hEpoch h

theorem ay_pvan_failure_coverage_gap
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    coverageGap ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_pvan_failure_transform_witness_mismatch
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    transformWitnessMismatch ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hTransform h

theorem ay_pvan_failure_reconstruction_gap
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pvan_failure_stale_fingerprint
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hStale h

theorem ay_pvan_failure_unchecked_replay
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pvan_failure_build_drift
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    buildDrift ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pvan_failure_audit_contradiction
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    auditContradiction ->
    ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro h result hActivity hMap hEpoch hCoverage hTransform hReconstruction
    hStale hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pvan_diagnostic_no_claim
    (currentCnf : Prop)
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pvan_DiagnosticVariableActivityNormalizationReplay
      currentCnf activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic ->
    ay_pvan_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pvan_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pvan_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pvan_diagnostic_recompute
    (currentCnf : Prop)
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pvan_DiagnosticVariableActivityNormalizationReplay
      currentCnf activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic ->
    ay_pvan_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pvan_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pvan_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pvan_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (activityDigestDrift : Prop) (variableMapMismatch : Prop)
    (normalizationEpochDrift : Prop) (coverageGap : Prop)
    (transformWitnessMismatch : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pvan_RecomputeObligation currentCnf recompute ->
    ay_pvan_NoSemanticClaim diagnostic ->
    ay_pvan_DiagnosticVariableActivityNormalizationReplay
      currentCnf activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pvan_conj_intro
    (ay_pvan_VariableActivityNormalizationFailure
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction)
    (ay_pvan_Conj
      (ay_pvan_RecomputeObligation currentCnf recompute)
      (ay_pvan_NoSemanticClaim diagnostic))
    (ay_pvan_failure_unchecked_replay
      activityDigestDrift variableMapMismatch normalizationEpochDrift
      coverageGap transformWitnessMismatch reconstructionGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction unchecked)
    (ay_pvan_conj_intro
      (ay_pvan_RecomputeObligation currentCnf recompute)
      (ay_pvan_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
