-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption/self-subsuming-resolution signature replay guard soundness.
-- The propositions stand for clause signature digests, subsumption witnesses,
-- removed-literal coverage, affected-clause coverage, transform witnesses,
-- reconstruction hooks, fingerprints, checker replay, fallback/build/validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pssr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pssr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pssr_Equisat (before : Prop) (after : Prop) :=
  ay_pssr_Conj (before -> after) (after -> before)

def ay_pssr_Sat (cnf : Prop) (model : Prop) :=
  ay_pssr_Conj cnf model

def ay_pssr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pssr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pssr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pssr_ClauseSignatureDigest
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop) :=
  ay_pssr_Conj signatureWitness (clauseSignature -> signatureDigest)

def ay_pssr_SubsumptionWitnessLedger
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :=
  ay_pssr_Conj witnessLedger (subsumedClause -> subsumptionWitness)

def ay_pssr_RemovedLiteralCoverage
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop) :=
  ay_pssr_Conj literalCoverageWitness (removedLiteral -> coveredLiteral)

def ay_pssr_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop) :=
  ay_pssr_Conj clauseCoverageWitness (affectedClause -> coveredClause)

def ay_pssr_TransformWitnessLedger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pssr_Conj transformLedger (affectedClause -> transformWitness)

def ay_pssr_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pssr_Sat replayedCnf replayedModel ->
    ay_pssr_Sat originalCnf originalModel

def ay_pssr_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pssr_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pssr_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pssr_Conj fingerprintWitness
    (ay_pssr_IdMatch originalFingerprint replayedFingerprint)

def ay_pssr_CheckerReplay
    (replayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pssr_Conj replayCertificate checkerAccepted

def ay_pssr_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pssr_Conj baselineSolver baselineAvailable

def ay_pssr_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pssr_Conj binaryFingerprint buildReproducible

def ay_pssr_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pssr_Conj validatorAccepted validatorVersion

def ay_pssr_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pssr_Conj auditAppended auditAppendOnly

def ay_pssr_AcceptedSubsumptionSignatureReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pssr_ClauseSignatureDigest
       clauseSignature signatureDigest signatureWitness ->
     ay_pssr_SubsumptionWitnessLedger
       subsumedClause subsumptionWitness witnessLedger ->
     ay_pssr_RemovedLiteralCoverage
       removedLiteral coveredLiteral literalCoverageWitness ->
     ay_pssr_AffectedClauseCoverage
       affectedClause coveredClause clauseCoverageWitness ->
     ay_pssr_TransformWitnessLedger
       affectedClause transformWitness transformLedger ->
     ay_pssr_Equisat originalCnf replayedCnf ->
     ay_pssr_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_pssr_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_pssr_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pssr_CheckerReplay replayCertificate checkerAccepted ->
     ay_pssr_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pssr_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pssr_ValidatorGate validatorAccepted validatorVersion ->
     ay_pssr_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pssr_ReplayGuardFailure
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (signatureDrift -> result) ->
    (witnessMismatch -> result) ->
    (literalCoverageGap -> result) ->
    (clauseCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pssr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pssr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pssr_Conj currentCnf recompute

def ay_pssr_DiagnosticReplayGuard
    (currentCnf : Prop)
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pssr_Conj
    (ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pssr_Conj
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic))

def ay_pssr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pssr_Conj exitCode claim

def ay_pssr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pssr_Disj
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pssr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pssr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pssr_conj_left
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pssr_conj_right
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pssr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pssr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pssr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pssr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pssr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pssr_conj_left (before -> after) (after -> before) eq

theorem ay_pssr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pssr_conj_right (before -> after) (after -> before) eq

theorem ay_pssr_clause_signature_digest_applies
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop) :
    ay_pssr_ClauseSignatureDigest
      clauseSignature signatureDigest signatureWitness ->
    clauseSignature ->
    signatureDigest := by
  intro accepted signature
  exact
    (ay_pssr_conj_right signatureWitness
      (clauseSignature -> signatureDigest) accepted) signature

theorem ay_pssr_subsumption_witness_ledger
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :
    ay_pssr_SubsumptionWitnessLedger
      subsumedClause subsumptionWitness witnessLedger ->
    subsumedClause ->
    subsumptionWitness := by
  intro accepted subsumed
  exact
    (ay_pssr_conj_right witnessLedger
      (subsumedClause -> subsumptionWitness) accepted) subsumed

theorem ay_pssr_removed_literal_coverage
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop) :
    ay_pssr_RemovedLiteralCoverage
      removedLiteral coveredLiteral literalCoverageWitness ->
    removedLiteral ->
    coveredLiteral := by
  intro accepted removed
  exact
    (ay_pssr_conj_right literalCoverageWitness
      (removedLiteral -> coveredLiteral) accepted) removed

theorem ay_pssr_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop) :
    ay_pssr_AffectedClauseCoverage
      affectedClause coveredClause clauseCoverageWitness ->
    affectedClause ->
    coveredClause := by
  intro accepted affected
  exact
    (ay_pssr_conj_right clauseCoverageWitness
      (affectedClause -> coveredClause) accepted) affected

theorem ay_pssr_transform_witness_ledger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pssr_TransformWitnessLedger
      affectedClause transformWitness transformLedger ->
    affectedClause ->
    transformWitness := by
  intro accepted affected
  exact
    (ay_pssr_conj_right transformLedger
      (affectedClause -> transformWitness) accepted) affected

theorem ay_pssr_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSubsumptionSignatureReplayGuard
      originalCnf replayedCnf clauseSignature signatureDigest
      signatureWitness subsumedClause subsumptionWitness witnessLedger
      removedLiteral coveredLiteral literalCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness replayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pssr_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pssr_Equisat originalCnf replayedCnf)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      eq _model _proof _fingerprint _checker _fallback _build _validator
      _audit => eq)

theorem ay_pssr_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSubsumptionSignatureReplayGuard
      originalCnf replayedCnf clauseSignature signatureDigest
      signatureWitness subsumedClause subsumptionWitness witnessLedger
      removedLiteral coveredLiteral literalCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness replayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pssr_CheckerReplay replayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pssr_CheckerReplay replayCertificate checkerAccepted)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      _eq _model _proof _fingerprint checker _fallback _build _validator
      _audit => checker)

theorem ay_pssr_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseSignature : Prop) (signatureDigest : Prop)
    (signatureWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (removedLiteral : Prop) (coveredLiteral : Prop)
    (literalCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSubsumptionSignatureReplayGuard
      originalCnf replayedCnf clauseSignature signatureDigest
      signatureWitness subsumedClause subsumptionWitness witnessLedger
      removedLiteral coveredLiteral literalCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness replayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pssr_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pssr_AuditEvidence auditAppended auditAppendOnly)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      _eq _model _proof _fingerprint _checker _fallback _build _validator
      audit => audit)

theorem ay_pssr_sat_pullback
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pssr_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pssr_Sat replayedCnf replayedModel ->
    ay_pssr_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pssr_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pssr_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pssr_Replay replayedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pssr_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pssr_Sat originalCnf model ->
    ay_pssr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pssr_disj_left
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (ay_pssr_Sat originalCnf model) exit sat)

theorem ay_pssr_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pssr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pssr_disj_right
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pssr_failure_signature_drift
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    signatureDrift ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hSignature h

theorem ay_pssr_failure_witness_mismatch
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    witnessMismatch ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_pssr_failure_literal_coverage_gap
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    literalCoverageGap ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hLiteralCoverage h

theorem ay_pssr_failure_clause_coverage_gap
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    clauseCoverageGap ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hClauseCoverage h

theorem ay_pssr_failure_reconstruction_gap
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pssr_failure_stale_fingerprint
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hStale h

theorem ay_pssr_failure_unchecked_replay
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pssr_failure_build_drift
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pssr_failure_audit_contradiction
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pssr_diagnostic_no_claim
    (currentCnf : Prop)
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticReplayGuard
      currentCnf signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pssr_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pssr_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pssr_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pssr_diagnostic_recompute
    (currentCnf : Prop)
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticReplayGuard
      currentCnf signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pssr_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pssr_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pssr_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pssr_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (signatureDrift : Prop) (witnessMismatch : Prop)
    (literalCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pssr_RecomputeObligation currentCnf recompute ->
    ay_pssr_NoSemanticClaim diagnostic ->
    ay_pssr_DiagnosticReplayGuard
      currentCnf signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pssr_conj_intro
    (ay_pssr_ReplayGuardFailure
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pssr_Conj
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic))
    (ay_pssr_failure_unchecked_replay
      signatureDrift witnessMismatch literalCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_pssr_conj_intro
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
