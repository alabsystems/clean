-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-range compression guard soundness.
-- The propositions stand for original-variable domain manifests, compressed-variable map digests, inverse map
-- witnesses, clause remap coverage digests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_vrcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrcg_Equisat (before : Prop) (after : Prop) :=
  ay_vrcg_Conj (before -> after) (after -> before)

def ay_vrcg_Sat (cnf : Prop) (model : Prop) :=
  ay_vrcg_Conj cnf model

def ay_vrcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_vrcg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_vrcg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_vrcg_OriginalVariableDomainManifest
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop)
    (originalVariableDomainManifest : Prop) :=
  ay_vrcg_Conj originalVariableDomainManifest (originalVariableDomain -> originalDomainAccepted)

def ay_vrcg_CompressedVariableMapDigest
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop)
    (compressedVariableMapDigest : Prop) :=
  ay_vrcg_Conj compressedVariableMapDigest (compressedVariableMap -> compressedMapAccepted)

def ay_vrcg_InverseMapWitness
    (inverseMap : Prop) (inverseMapAccepted : Prop)
    (inverseMapManifest : Prop) :=
  ay_vrcg_Conj inverseMapManifest (inverseMap -> inverseMapAccepted)

def ay_vrcg_ClauseRemapCoverageDigest
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop) :=
  ay_vrcg_Conj clauseRemapDigest (clauseRemap -> clauseRemapAccepted)

def ay_vrcg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_vrcg_Sat replayedCnf replayedModel ->
    ay_vrcg_Sat originalCnf originalModel

def ay_vrcg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_vrcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_vrcg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_vrcg_Conj
    (ay_vrcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_vrcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_vrcg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_vrcg_Conj fingerprintWitness
    (ay_vrcg_IdMatch originalFingerprint replayedFingerprint)

def ay_vrcg_CheckerReplay
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_vrcg_Conj compressionReplayCertificate checkerAccepted

def ay_vrcg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_vrcg_Conj baselineSolver baselineAvailable

def ay_vrcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_vrcg_Conj binaryFingerprint buildReproducible

def ay_vrcg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_vrcg_Conj validatorAccepted validatorVersion

def ay_vrcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_vrcg_Conj auditAppended auditAppendOnly

def ay_vrcg_AcceptedVariableRangeCompressionGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_vrcg_OriginalVariableDomainManifest
       originalVariableDomain originalDomainAccepted originalVariableDomainManifest ->
     ay_vrcg_CompressedVariableMapDigest
       compressedVariableMap compressedMapAccepted compressedVariableMapDigest ->
     ay_vrcg_InverseMapWitness
       inverseMap inverseMapAccepted inverseMapManifest ->
     ay_vrcg_ClauseRemapCoverageDigest
       clauseRemap clauseRemapAccepted clauseRemapDigest ->
     ay_vrcg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_vrcg_Equisat originalCnf replayedCnf ->
     ay_vrcg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_vrcg_CheckerReplay compressionReplayCertificate checkerAccepted ->
     ay_vrcg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_vrcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_vrcg_ValidatorGate validatorAccepted validatorVersion ->
     ay_vrcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_vrcg_VariableRangeCompressionGuardFailure
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleOriginalVariableDomainManifest -> result) ->
    (compressedMapMismatch -> result) ->
    (inverseMapMismatch -> result) ->
    (clauseRemapGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_vrcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_vrcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_vrcg_Conj currentCnf recompute

def ay_vrcg_DiagnosticVariableRangeCompressionGuard
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_vrcg_Conj
    (ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_vrcg_Conj
      (ay_vrcg_RecomputeObligation currentCnf recompute)
      (ay_vrcg_NoSemanticClaim diagnostic))

def ay_vrcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_vrcg_Conj exitCode claim

def ay_vrcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_vrcg_Disj
    (ay_vrcg_ExitCodeSound exitCode (ay_vrcg_Sat originalCnf model))
    (ay_vrcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_vrcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_vrcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_vrcg_conj_left
    (left : Prop) (right : Prop) :
    ay_vrcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vrcg_conj_right
    (left : Prop) (right : Prop) :
    ay_vrcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vrcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_vrcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_vrcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_vrcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_vrcg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_vrcg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_vrcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_vrcg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_vrcg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_vrcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_vrcg_original_variable_domain_manifest_applies
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop)
    (originalVariableDomainManifest : Prop) :
    ay_vrcg_OriginalVariableDomainManifest
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest ->
    originalVariableDomain -> originalDomainAccepted := by
  intro digest
  exact ay_vrcg_conj_right originalVariableDomainManifest
    (originalVariableDomain -> originalDomainAccepted) digest

theorem ay_vrcg_compressed_variable_map_digest_applies
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop)
    (compressedVariableMapDigest : Prop) :
    ay_vrcg_CompressedVariableMapDigest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest ->
    compressedVariableMap -> compressedMapAccepted := by
  intro digest
  exact ay_vrcg_conj_right compressedVariableMapDigest
    (compressedVariableMap -> compressedMapAccepted) digest

theorem ay_vrcg_inverse_map_witness_applies
    (inverseMap : Prop) (inverseMapAccepted : Prop)
    (inverseMapManifest : Prop) :
    ay_vrcg_InverseMapWitness
      inverseMap inverseMapAccepted inverseMapManifest ->
    inverseMap -> inverseMapAccepted := by
  intro ledger
  exact ay_vrcg_conj_right inverseMapManifest
    (inverseMap -> inverseMapAccepted) ledger

theorem ay_vrcg_clause_remap_coverage_digest_applies
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop) :
    ay_vrcg_ClauseRemapCoverageDigest
      clauseRemap clauseRemapAccepted clauseRemapDigest ->
    clauseRemap -> clauseRemapAccepted := by
  intro coverage
  exact ay_vrcg_conj_right clauseRemapDigest
    (clauseRemap -> clauseRemapAccepted) coverage

theorem ay_vrcg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_vrcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_vrcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_vrcg_conj_left
    (ay_vrcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_vrcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_vrcg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_vrcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_vrcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_vrcg_conj_right
    (ay_vrcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_vrcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_vrcg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_vrcg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_vrcg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_vrcg_accepted_forward_map
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_vrcg_equisat_forward originalCnf replayedCnf
    (ay_vrcg_accepted_equisat
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_vrcg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_vrcg_CheckerReplay compressionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_vrcg_CheckerReplay compressionReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_vrcg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_vrcg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_vrcg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_vrcg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_vrcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_vrcg_Sat replayedCnf replayedModel ->
    ay_vrcg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_vrcg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_vrcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_vrcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_vrcg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_vrcg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_vrcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_vrcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_vrcg_disj_left
        (ay_vrcg_ExitCodeSound exitCode
          (ay_vrcg_Sat originalCnf originalModel))
        (ay_vrcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_vrcg_conj_intro exitCode
          (ay_vrcg_Sat originalCnf originalModel)
          hexit
          ((ay_vrcg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_vrcg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (originalVariableDomain : Prop) (originalDomainAccepted : Prop) (originalVariableDomainManifest : Prop)
    (compressedVariableMap : Prop) (compressedMapAccepted : Prop) (compressedVariableMapDigest : Prop)
    (inverseMap : Prop) (inverseMapAccepted : Prop) (inverseMapManifest : Prop)
    (clauseRemap : Prop) (clauseRemapAccepted : Prop)
    (clauseRemapDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (compressionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_vrcg_AcceptedVariableRangeCompressionGuard
      originalCnf replayedCnf
      originalVariableDomain originalDomainAccepted originalVariableDomainManifest
      compressedVariableMap compressedMapAccepted compressedVariableMapDigest
      inverseMap inverseMapAccepted inverseMapManifest
      clauseRemap clauseRemapAccepted clauseRemapDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      compressionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_vrcg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_vrcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_vrcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_vrcg_disj_right
        (ay_vrcg_ExitCodeSound exitCode
          (ay_vrcg_Sat originalCnf originalModel))
        (ay_vrcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_vrcg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_vrcg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_vrcg_failure_stale_original_variable_domain_manifest
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleOriginalVariableDomainManifest ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_vrcg_failure_compressed_variable_map_digest
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    compressedMapMismatch ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_vrcg_failure_inverse_map_witness
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    inverseMapMismatch ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_vrcg_failure_clause_remap_coverage
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    clauseRemapGap ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_vrcg_failure_reconstruction
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_vrcg_failure_stale_fingerprint
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_vrcg_failure_unchecked_replay
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_vrcg_failure_missing_baseline
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_vrcg_failure_build
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_vrcg_failure_validator
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_vrcg_failure_audit
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_vrcg_VariableRangeCompressionGuardFailure
      staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_vrcg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_vrcg_DiagnosticVariableRangeCompressionGuard
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_vrcg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_vrcg_conj_right
    (ay_vrcg_RecomputeObligation currentCnf recompute)
    (ay_vrcg_NoSemanticClaim diagnostic)
    (ay_vrcg_conj_right
      (ay_vrcg_VariableRangeCompressionGuardFailure
        staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_vrcg_Conj
        (ay_vrcg_RecomputeObligation currentCnf recompute)
        (ay_vrcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_vrcg_diagnostic_recompute
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_vrcg_DiagnosticVariableRangeCompressionGuard
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_vrcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_vrcg_conj_left
    (ay_vrcg_RecomputeObligation currentCnf recompute)
    (ay_vrcg_NoSemanticClaim diagnostic)
    (ay_vrcg_conj_right
      (ay_vrcg_VariableRangeCompressionGuardFailure
        staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_vrcg_Conj
        (ay_vrcg_RecomputeObligation currentCnf recompute)
        (ay_vrcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_vrcg_unchecked_compression_cannot_bless_public_result
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_vrcg_DiagnosticVariableRangeCompressionGuard
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_vrcg_Conj
      (ay_vrcg_NoSemanticClaim diagnostic)
      (ay_vrcg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_vrcg_conj_intro
    (ay_vrcg_NoSemanticClaim diagnostic)
    (ay_vrcg_RecomputeObligation currentCnf recompute)
    (ay_vrcg_diagnostic_no_claim
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_vrcg_diagnostic_recompute
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_vrcg_unchecked_compression_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_vrcg_DiagnosticVariableRangeCompressionGuard
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_vrcg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_vrcg_diagnostic_no_claim
    currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_vrcg_unchecked_compression_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleOriginalVariableDomainManifest : Prop) (compressedMapMismatch : Prop)
    (inverseMapMismatch : Prop)
    (clauseRemapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_vrcg_DiagnosticVariableRangeCompressionGuard
      currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_vrcg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_vrcg_diagnostic_recompute
    currentCnf staleOriginalVariableDomainManifest compressedMapMismatch inverseMapMismatch clauseRemapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
