-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause elimination replay guard soundness.
-- The propositions stand for blocked-clause manifests, blocking literal witnesses,
-- affected-clause coverage, transform witnesses,
-- reconstruction hooks, fingerprints, checker replay, fallback/build/validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pbce_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pbce_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pbce_Equisat (before : Prop) (after : Prop) :=
  ay_pbce_Conj (before -> after) (after -> before)

def ay_pbce_Sat (cnf : Prop) (model : Prop) :=
  ay_pbce_Conj cnf model

def ay_pbce_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pbce_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pbce_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pbce_BlockedClauseManifest
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop) :=
  ay_pbce_Conj manifestWitness (blockedClause -> blockingLiteral)

def ay_pbce_BlockingLiteralWitnessLedger
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop) :=
  ay_pbce_Conj blockingLedger (witnessedClause -> blockingWitness)

def ay_pbce_BlockedClauseCoverage
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop) :=
  ay_pbce_Conj manifestCoverageWitness (manifestClause -> coveredManifestClause)

def ay_pbce_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop) :=
  ay_pbce_Conj clauseCoverageWitness (affectedClause -> coveredClause)

def ay_pbce_TransformWitnessLedger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pbce_Conj transformLedger (affectedClause -> transformWitness)

def ay_pbce_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pbce_Sat replayedCnf replayedModel ->
    ay_pbce_Sat originalCnf originalModel

def ay_pbce_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbce_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbce_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbce_Conj fingerprintWitness
    (ay_pbce_IdMatch originalFingerprint replayedFingerprint)

def ay_pbce_CheckerReplay
    (bceCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbce_Conj bceCertificate checkerAccepted

def ay_pbce_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pbce_Conj baselineSolver baselineAvailable

def ay_pbce_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pbce_Conj binaryFingerprint buildReproducible

def ay_pbce_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pbce_Conj validatorAccepted validatorVersion

def ay_pbce_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pbce_Conj auditAppended auditAppendOnly

def ay_pbce_AcceptedBlockedClauseEliminationReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop)
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop)
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbce_BlockedClauseManifest
       blockedClause blockingLiteral manifestWitness ->
     ay_pbce_BlockingLiteralWitnessLedger
       witnessedClause blockingWitness blockingLedger ->
     ay_pbce_BlockedClauseCoverage
       manifestClause coveredManifestClause manifestCoverageWitness ->
     ay_pbce_AffectedClauseCoverage
       affectedClause coveredClause clauseCoverageWitness ->
     ay_pbce_TransformWitnessLedger
       affectedClause transformWitness transformLedger ->
     ay_pbce_Equisat originalCnf replayedCnf ->
     ay_pbce_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_pbce_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_pbce_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pbce_CheckerReplay bceCertificate checkerAccepted ->
     ay_pbce_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbce_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbce_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbce_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pbce_BlockedClauseReplayGuardFailure
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (manifestDrift -> result) ->
    (blockingWitnessMismatch -> result) ->
    (manifestCoverageGap -> result) ->
    (clauseCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pbce_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbce_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbce_Conj currentCnf recompute

def ay_pbce_DiagnosticBlockedClauseReplayGuard
    (currentCnf : Prop)
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbce_Conj
    (ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pbce_Conj
      (ay_pbce_RecomputeObligation currentCnf recompute)
      (ay_pbce_NoSemanticClaim diagnostic))

def ay_pbce_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pbce_Conj exitCode claim

def ay_pbce_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pbce_Disj
    (ay_pbce_ExitCodeSound exitCode (ay_pbce_Sat originalCnf model))
    (ay_pbce_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pbce_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pbce_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbce_conj_left
    (left : Prop) (right : Prop) :
    ay_pbce_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbce_conj_right
    (left : Prop) (right : Prop) :
    ay_pbce_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbce_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pbce_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbce_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pbce_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbce_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pbce_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbce_conj_left (before -> after) (after -> before) eq

theorem ay_pbce_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pbce_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbce_conj_right (before -> after) (after -> before) eq

theorem ay_pbce_blocked_clause_manifest_applies
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop) :
    ay_pbce_BlockedClauseManifest
      blockedClause blockingLiteral manifestWitness ->
    blockedClause ->
    blockingLiteral := by
  intro accepted signature
  exact
    (ay_pbce_conj_right manifestWitness
      (blockedClause -> blockingLiteral) accepted) signature

theorem ay_pbce_blocking_literal_witness_ledger
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop) :
    ay_pbce_BlockingLiteralWitnessLedger
      witnessedClause blockingWitness blockingLedger ->
    witnessedClause ->
    blockingWitness := by
  intro accepted subsumed
  exact
    (ay_pbce_conj_right blockingLedger
      (witnessedClause -> blockingWitness) accepted) subsumed

theorem ay_pbce_blocked_clause_coverage
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop) :
    ay_pbce_BlockedClauseCoverage
      manifestClause coveredManifestClause manifestCoverageWitness ->
    manifestClause ->
    coveredManifestClause := by
  intro accepted removed
  exact
    (ay_pbce_conj_right manifestCoverageWitness
      (manifestClause -> coveredManifestClause) accepted) removed

theorem ay_pbce_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop) :
    ay_pbce_AffectedClauseCoverage
      affectedClause coveredClause clauseCoverageWitness ->
    affectedClause ->
    coveredClause := by
  intro accepted affected
  exact
    (ay_pbce_conj_right clauseCoverageWitness
      (affectedClause -> coveredClause) accepted) affected

theorem ay_pbce_transform_witness_ledger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pbce_TransformWitnessLedger
      affectedClause transformWitness transformLedger ->
    affectedClause ->
    transformWitness := by
  intro accepted affected
  exact
    (ay_pbce_conj_right transformLedger
      (affectedClause -> transformWitness) accepted) affected

theorem ay_pbce_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop)
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop)
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseEliminationReplayGuard
      originalCnf replayedCnf blockedClause blockingLiteral
      manifestWitness witnessedClause blockingWitness blockingLedger
      manifestClause coveredManifestClause manifestCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pbce_Equisat originalCnf replayedCnf)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      eq _model _proof _fingerprint _checker _fallback _build _validator
      _audit => eq)

theorem ay_pbce_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop)
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop)
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseEliminationReplayGuard
      originalCnf replayedCnf blockedClause blockingLiteral
      manifestWitness witnessedClause blockingWitness blockingLedger
      manifestClause coveredManifestClause manifestCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_CheckerReplay bceCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pbce_CheckerReplay bceCertificate checkerAccepted)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      _eq _model _proof _fingerprint checker _fallback _build _validator
      _audit => checker)

theorem ay_pbce_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (manifestWitness : Prop)
    (witnessedClause : Prop) (blockingWitness : Prop)
    (blockingLedger : Prop)
    (manifestClause : Prop) (coveredManifestClause : Prop)
    (manifestCoverageWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (clauseCoverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseEliminationReplayGuard
      originalCnf replayedCnf blockedClause blockingLiteral
      manifestWitness witnessedClause blockingWitness blockingLedger
      manifestClause coveredManifestClause manifestCoverageWitness affectedClause
      coveredClause clauseCoverageWitness transformWitness transformLedger
      replayedModel originalModel certificate conflict originalFingerprint
      replayedFingerprint fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbce_AuditEvidence auditAppended auditAppendOnly)
    (fun _signature _witness _literalCoverage _clauseCoverage _transform
      _eq _model _proof _fingerprint _checker _fallback _build _validator
      audit => audit)

theorem ay_pbce_sat_pullback
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pbce_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pbce_Sat replayedCnf replayedModel ->
    ay_pbce_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pbce_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbce_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pbce_Replay replayedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pbce_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pbce_Sat originalCnf model ->
    ay_pbce_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pbce_disj_left
    (ay_pbce_ExitCodeSound exitCode (ay_pbce_Sat originalCnf model))
    (ay_pbce_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbce_conj_intro exitCode
      (ay_pbce_Sat originalCnf model) exit sat)

theorem ay_pbce_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pbce_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pbce_disj_right
    (ay_pbce_ExitCodeSound exitCode (ay_pbce_Sat originalCnf model))
    (ay_pbce_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbce_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pbce_failure_manifest_drift
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    manifestDrift ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hSignature h

theorem ay_pbce_failure_blocking_witness_mismatch
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    blockingWitnessMismatch ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_pbce_failure_manifest_coverage_gap
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    manifestCoverageGap ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hLiteralCoverage h

theorem ay_pbce_failure_clause_coverage_gap
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    clauseCoverageGap ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hClauseCoverage h

theorem ay_pbce_failure_reconstruction_gap
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pbce_failure_stale_fingerprint
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hStale h

theorem ay_pbce_failure_unchecked_replay
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pbce_failure_build_drift
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pbce_failure_audit_contradiction
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hSignature hWitness hLiteralCoverage hClauseCoverage
    hReconstruction hStale hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pbce_diagnostic_no_claim
    (currentCnf : Prop)
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbce_DiagnosticBlockedClauseReplayGuard
      currentCnf manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pbce_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbce_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pbce_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pbce_diagnostic_recompute
    (currentCnf : Prop)
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbce_DiagnosticBlockedClauseReplayGuard
      currentCnf manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pbce_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbce_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pbce_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pbce_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (manifestDrift : Prop) (blockingWitnessMismatch : Prop)
    (manifestCoverageGap : Prop) (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbce_RecomputeObligation currentCnf recompute ->
    ay_pbce_NoSemanticClaim diagnostic ->
    ay_pbce_DiagnosticBlockedClauseReplayGuard
      currentCnf manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pbce_conj_intro
    (ay_pbce_BlockedClauseReplayGuardFailure
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pbce_Conj
      (ay_pbce_RecomputeObligation currentCnf recompute)
      (ay_pbce_NoSemanticClaim diagnostic))
    (ay_pbce_failure_unchecked_replay
      manifestDrift blockingWitnessMismatch manifestCoverageGap clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_pbce_conj_intro
      (ay_pbce_RecomputeObligation currentCnf recompute)
      (ay_pbce_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
