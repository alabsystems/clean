-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Tseitin/gate extraction guard soundness.
-- The propositions stand for gate detection manifests, definitional extension witnesses, auxiliary-variable
-- domain manifests, clause coverage digests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_tgeg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_tgeg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_tgeg_Equisat (before : Prop) (after : Prop) :=
  ay_tgeg_Conj (before -> after) (after -> before)

def ay_tgeg_Sat (cnf : Prop) (model : Prop) :=
  ay_tgeg_Conj cnf model

def ay_tgeg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_tgeg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_tgeg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_tgeg_GateDetectionManifest
    (gateDetection : Prop) (gateDetectionAccepted : Prop)
    (gateDetectionManifest : Prop) :=
  ay_tgeg_Conj gateDetectionManifest (gateDetection -> gateDetectionAccepted)

def ay_tgeg_DefinitionalExtensionWitness
    (definitionalExtension : Prop) (definitionAccepted : Prop)
    (definitionalExtensionWitness : Prop) :=
  ay_tgeg_Conj definitionalExtensionWitness (definitionalExtension -> definitionAccepted)

def ay_tgeg_AuxiliaryVariableDomainManifest
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainManifest : Prop) :=
  ay_tgeg_Conj auxiliaryDomainManifest (auxiliaryDomain -> auxiliaryDomainAccepted)

def ay_tgeg_ClauseCoverageDigest
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop) :=
  ay_tgeg_Conj clauseCoverageDigest (clauseCoverage -> clauseCoverageAccepted)

def ay_tgeg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_tgeg_Sat replayedCnf replayedModel ->
    ay_tgeg_Sat originalCnf originalModel

def ay_tgeg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_tgeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_tgeg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_tgeg_Conj
    (ay_tgeg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_tgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_tgeg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_tgeg_Conj fingerprintWitness
    (ay_tgeg_IdMatch originalFingerprint replayedFingerprint)

def ay_tgeg_CheckerReplay
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_tgeg_Conj gateExtractionReplayCertificate checkerAccepted

def ay_tgeg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_tgeg_Conj baselineSolver baselineAvailable

def ay_tgeg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_tgeg_Conj binaryFingerprint buildReproducible

def ay_tgeg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_tgeg_Conj validatorAccepted validatorVersion

def ay_tgeg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_tgeg_Conj auditAppended auditAppendOnly

def ay_tgeg_AcceptedTseitinGateExtractionGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_tgeg_GateDetectionManifest
       gateDetection gateDetectionAccepted gateDetectionManifest ->
     ay_tgeg_DefinitionalExtensionWitness
       definitionalExtension definitionAccepted definitionalExtensionWitness ->
     ay_tgeg_AuxiliaryVariableDomainManifest
       auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest ->
     ay_tgeg_ClauseCoverageDigest
       clauseCoverage clauseCoverageAccepted clauseCoverageDigest ->
     ay_tgeg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_tgeg_Equisat originalCnf replayedCnf ->
     ay_tgeg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_tgeg_CheckerReplay gateExtractionReplayCertificate checkerAccepted ->
     ay_tgeg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_tgeg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_tgeg_ValidatorGate validatorAccepted validatorVersion ->
     ay_tgeg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_tgeg_TseitinGateExtractionGuardFailure
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleGateDetectionManifest -> result) ->
    (definitionMismatch -> result) ->
    (auxiliaryDomainMismatch -> result) ->
    (clauseCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_tgeg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_tgeg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_tgeg_Conj currentCnf recompute

def ay_tgeg_DiagnosticTseitinGateExtractionGuard
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_tgeg_Conj
    (ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_tgeg_Conj
      (ay_tgeg_RecomputeObligation currentCnf recompute)
      (ay_tgeg_NoSemanticClaim diagnostic))

def ay_tgeg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_tgeg_Conj exitCode claim

def ay_tgeg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_tgeg_Disj
    (ay_tgeg_ExitCodeSound exitCode (ay_tgeg_Sat originalCnf model))
    (ay_tgeg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_tgeg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_tgeg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_tgeg_conj_left
    (left : Prop) (right : Prop) :
    ay_tgeg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_tgeg_conj_right
    (left : Prop) (right : Prop) :
    ay_tgeg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_tgeg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_tgeg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_tgeg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_tgeg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_tgeg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_tgeg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_tgeg_conj_left (before -> after) (after -> before) eqsat

theorem ay_tgeg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_tgeg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_tgeg_conj_right (before -> after) (after -> before) eqsat

theorem ay_tgeg_gate_detection_manifest_applies
    (gateDetection : Prop) (gateDetectionAccepted : Prop)
    (gateDetectionManifest : Prop) :
    ay_tgeg_GateDetectionManifest
      gateDetection gateDetectionAccepted gateDetectionManifest ->
    gateDetection -> gateDetectionAccepted := by
  intro digest
  exact ay_tgeg_conj_right gateDetectionManifest
    (gateDetection -> gateDetectionAccepted) digest

theorem ay_tgeg_definitional_extension_witness_applies
    (definitionalExtension : Prop) (definitionAccepted : Prop)
    (definitionalExtensionWitness : Prop) :
    ay_tgeg_DefinitionalExtensionWitness
      definitionalExtension definitionAccepted definitionalExtensionWitness ->
    definitionalExtension -> definitionAccepted := by
  intro digest
  exact ay_tgeg_conj_right definitionalExtensionWitness
    (definitionalExtension -> definitionAccepted) digest

theorem ay_tgeg_auxiliary_variable_domain_manifest_applies
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainManifest : Prop) :
    ay_tgeg_AuxiliaryVariableDomainManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest ->
    auxiliaryDomain -> auxiliaryDomainAccepted := by
  intro ledger
  exact ay_tgeg_conj_right auxiliaryDomainManifest
    (auxiliaryDomain -> auxiliaryDomainAccepted) ledger

theorem ay_tgeg_clause_coverage_digest_applies
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop) :
    ay_tgeg_ClauseCoverageDigest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest ->
    clauseCoverage -> clauseCoverageAccepted := by
  intro coverage
  exact ay_tgeg_conj_right clauseCoverageDigest
    (clauseCoverage -> clauseCoverageAccepted) coverage

theorem ay_tgeg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_tgeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_tgeg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_tgeg_conj_left
    (ay_tgeg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_tgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_tgeg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_tgeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_tgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_tgeg_conj_right
    (ay_tgeg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_tgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_tgeg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_tgeg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_tgeg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_tgeg_accepted_forward_map
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_tgeg_equisat_forward originalCnf replayedCnf
    (ay_tgeg_accepted_equisat
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_tgeg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_tgeg_CheckerReplay gateExtractionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_tgeg_CheckerReplay gateExtractionReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_tgeg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_tgeg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_tgeg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_tgeg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_tgeg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_tgeg_Sat replayedCnf replayedModel ->
    ay_tgeg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_tgeg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_tgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_tgeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_tgeg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_tgeg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_tgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_tgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_tgeg_disj_left
        (ay_tgeg_ExitCodeSound exitCode
          (ay_tgeg_Sat originalCnf originalModel))
        (ay_tgeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_tgeg_conj_intro exitCode
          (ay_tgeg_Sat originalCnf originalModel)
          hexit
          ((ay_tgeg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_tgeg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateDetection : Prop) (gateDetectionAccepted : Prop) (gateDetectionManifest : Prop)
    (definitionalExtension : Prop) (definitionAccepted : Prop) (definitionalExtensionWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (gateExtractionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_tgeg_AcceptedTseitinGateExtractionGuard
      originalCnf replayedCnf
      gateDetection gateDetectionAccepted gateDetectionManifest
      definitionalExtension definitionAccepted definitionalExtensionWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      gateExtractionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_tgeg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_tgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_tgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_tgeg_disj_right
        (ay_tgeg_ExitCodeSound exitCode
          (ay_tgeg_Sat originalCnf originalModel))
        (ay_tgeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_tgeg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_tgeg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_tgeg_failure_stale_gate_detection_manifest
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleGateDetectionManifest ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_tgeg_failure_definitional_extension_witness
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    definitionMismatch ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_tgeg_failure_auxiliary_variable_domain_manifest
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auxiliaryDomainMismatch ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_tgeg_failure_clause_coverage
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    clauseCoverageGap ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_tgeg_failure_reconstruction
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_tgeg_failure_stale_fingerprint
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_tgeg_failure_unchecked_replay
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_tgeg_failure_missing_baseline
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_tgeg_failure_build
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_tgeg_failure_validator
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_tgeg_failure_audit
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_tgeg_TseitinGateExtractionGuardFailure
      staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_tgeg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_tgeg_DiagnosticTseitinGateExtractionGuard
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_tgeg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_tgeg_conj_right
    (ay_tgeg_RecomputeObligation currentCnf recompute)
    (ay_tgeg_NoSemanticClaim diagnostic)
    (ay_tgeg_conj_right
      (ay_tgeg_TseitinGateExtractionGuardFailure
        staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_tgeg_Conj
        (ay_tgeg_RecomputeObligation currentCnf recompute)
        (ay_tgeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_tgeg_diagnostic_recompute
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_tgeg_DiagnosticTseitinGateExtractionGuard
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_tgeg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_tgeg_conj_left
    (ay_tgeg_RecomputeObligation currentCnf recompute)
    (ay_tgeg_NoSemanticClaim diagnostic)
    (ay_tgeg_conj_right
      (ay_tgeg_TseitinGateExtractionGuardFailure
        staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_tgeg_Conj
        (ay_tgeg_RecomputeObligation currentCnf recompute)
        (ay_tgeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_tgeg_unchecked_gate_extraction_cannot_bless_public_result
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_tgeg_DiagnosticTseitinGateExtractionGuard
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_tgeg_Conj
      (ay_tgeg_NoSemanticClaim diagnostic)
      (ay_tgeg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_tgeg_conj_intro
    (ay_tgeg_NoSemanticClaim diagnostic)
    (ay_tgeg_RecomputeObligation currentCnf recompute)
    (ay_tgeg_diagnostic_no_claim
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_tgeg_diagnostic_recompute
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_tgeg_unchecked_gate_extraction_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_tgeg_DiagnosticTseitinGateExtractionGuard
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_tgeg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_tgeg_diagnostic_no_claim
    currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_tgeg_unchecked_gate_extraction_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleGateDetectionManifest : Prop) (definitionMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_tgeg_DiagnosticTseitinGateExtractionGuard
      currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_tgeg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_tgeg_diagnostic_recompute
    currentCnf staleGateDetectionManifest definitionMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
