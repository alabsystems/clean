-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause elimination projection guard soundness.
-- The propositions stand for clause-id manifests, pivot literal coverage, resolvent tautology
-- witnesses, deletion ledgers, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_bceg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bceg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bceg_Equisat (before : Prop) (after : Prop) :=
  ay_bceg_Conj (before -> after) (after -> before)

def ay_bceg_Sat (cnf : Prop) (model : Prop) :=
  ay_bceg_Conj cnf model

def ay_bceg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bceg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_bceg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_bceg_ClauseIdManifest
    (clauseId : Prop) (manifestAccepted : Prop)
    (clauseIdManifest : Prop) :=
  ay_bceg_Conj clauseIdManifest (clauseId -> manifestAccepted)

def ay_bceg_PivotLiteralCoverage
    (pivotLiteral : Prop) (pivotCovered : Prop)
    (pivotCoveredWitness : Prop) :=
  ay_bceg_Conj pivotCoveredWitness (pivotLiteral -> pivotCovered)

def ay_bceg_ResolventTautologyWitness
    (resolvent : Prop) (resolventTautology : Prop)
    (resolventTautologyWitness : Prop) :=
  ay_bceg_Conj resolventTautologyWitness (resolvent -> resolventTautology)

def ay_bceg_DeletionLedger
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop) :=
  ay_bceg_Conj deletionLedger (deletedClause -> deletionRecorded)

def ay_bceg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_bceg_Sat replayedCnf replayedModel ->
    ay_bceg_Sat originalCnf originalModel

def ay_bceg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bceg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bceg_Conj
    (ay_bceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_bceg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_bceg_Conj fingerprintWitness
    (ay_bceg_IdMatch originalFingerprint replayedFingerprint)

def ay_bceg_CheckerReplay
    (bceReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_bceg_Conj bceReplayCertificate checkerAccepted

def ay_bceg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_bceg_Conj baselineSolver baselineAvailable

def ay_bceg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bceg_Conj binaryFingerprint buildReproducible

def ay_bceg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_bceg_Conj validatorAccepted validatorVersion

def ay_bceg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bceg_Conj auditAppended auditAppendOnly

def ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bceg_ClauseIdManifest
       clauseId manifestAccepted clauseIdManifest ->
     ay_bceg_PivotLiteralCoverage
       pivotLiteral pivotCovered pivotCoveredWitness ->
     ay_bceg_ResolventTautologyWitness
       resolvent resolventTautology resolventTautologyWitness ->
     ay_bceg_DeletionLedger
       deletedClause deletionRecorded deletionLedger ->
     ay_bceg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_bceg_Equisat originalCnf replayedCnf ->
     ay_bceg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_bceg_CheckerReplay bceReplayCertificate checkerAccepted ->
     ay_bceg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_bceg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bceg_ValidatorGate validatorAccepted validatorVersion ->
     ay_bceg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bceg_BlockedClauseEliminationProjectionGuardFailure
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleClauseIdManifest -> result) ->
    (pivotCoveredMismatch -> result) ->
    (resolventTautologyMismatch -> result) ->
    (deletionLedgerGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_bceg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bceg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bceg_Conj currentCnf recompute

def ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bceg_Conj
    (ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_bceg_Conj
      (ay_bceg_RecomputeObligation currentCnf recompute)
      (ay_bceg_NoSemanticClaim diagnostic))

def ay_bceg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_bceg_Conj exitCode claim

def ay_bceg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_bceg_Disj
    (ay_bceg_ExitCodeSound exitCode (ay_bceg_Sat originalCnf model))
    (ay_bceg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_bceg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bceg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_bceg_conj_left
    (left : Prop) (right : Prop) :
    ay_bceg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bceg_conj_right
    (left : Prop) (right : Prop) :
    ay_bceg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bceg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bceg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_bceg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bceg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_bceg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bceg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_bceg_conj_left (before -> after) (after -> before) eqsat

theorem ay_bceg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bceg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_bceg_conj_right (before -> after) (after -> before) eqsat

theorem ay_bceg_clause_id_manifest_applies
    (clauseId : Prop) (manifestAccepted : Prop)
    (clauseIdManifest : Prop) :
    ay_bceg_ClauseIdManifest
      clauseId manifestAccepted clauseIdManifest ->
    clauseId -> manifestAccepted := by
  intro digest
  exact ay_bceg_conj_right clauseIdManifest
    (clauseId -> manifestAccepted) digest

theorem ay_bceg_pivot_literal_coverage_applies
    (pivotLiteral : Prop) (pivotCovered : Prop)
    (pivotCoveredWitness : Prop) :
    ay_bceg_PivotLiteralCoverage
      pivotLiteral pivotCovered pivotCoveredWitness ->
    pivotLiteral -> pivotCovered := by
  intro digest
  exact ay_bceg_conj_right pivotCoveredWitness
    (pivotLiteral -> pivotCovered) digest

theorem ay_bceg_resolvent_tautology_witness_applies
    (resolvent : Prop) (resolventTautology : Prop)
    (resolventTautologyWitness : Prop) :
    ay_bceg_ResolventTautologyWitness
      resolvent resolventTautology resolventTautologyWitness ->
    resolvent -> resolventTautology := by
  intro ledger
  exact ay_bceg_conj_right resolventTautologyWitness
    (resolvent -> resolventTautology) ledger

theorem ay_bceg_deletion_ledger_applies
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop) :
    ay_bceg_DeletionLedger
      deletedClause deletionRecorded deletionLedger ->
    deletedClause -> deletionRecorded := by
  intro coverage
  exact ay_bceg_conj_right deletionLedger
    (deletedClause -> deletionRecorded) coverage

theorem ay_bceg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_bceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_bceg_conj_left
    (ay_bceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_bceg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_bceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_bceg_conj_right
    (ay_bceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_bceg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
      originalCnf replayedCnf
      clauseId manifestAccepted clauseIdManifest
      pivotLiteral pivotCovered pivotCoveredWitness
      resolvent resolventTautology resolventTautologyWitness
      deletedClause deletionRecorded deletionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bceReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bceg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_bceg_Equisat originalCnf replayedCnf)
    (fun _manifest _pivot _tautology _deletion _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_bceg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
      originalCnf replayedCnf
      clauseId manifestAccepted clauseIdManifest
      pivotLiteral pivotCovered pivotCoveredWitness
      resolvent resolventTautology resolventTautologyWitness
      deletedClause deletionRecorded deletionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bceReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bceg_CheckerReplay bceReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_bceg_CheckerReplay bceReplayCertificate checkerAccepted)
    (fun _manifest _pivot _tautology _deletion _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_bceg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
      originalCnf replayedCnf
      clauseId manifestAccepted clauseIdManifest
      pivotLiteral pivotCovered pivotCoveredWitness
      resolvent resolventTautology resolventTautologyWitness
      deletedClause deletionRecorded deletionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bceReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bceg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_bceg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _pivot _tautology _deletion _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_bceg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_bceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_bceg_Sat replayedCnf replayedModel ->
    ay_bceg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_bceg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_bceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_bceg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
      originalCnf replayedCnf
      clauseId manifestAccepted clauseIdManifest
      pivotLiteral pivotCovered pivotCoveredWitness
      resolvent resolventTautology resolventTautologyWitness
      deletedClause deletionRecorded deletionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bceReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bceg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_bceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_bceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _pivot _tautology _deletion reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_bceg_disj_left
        (ay_bceg_ExitCodeSound exitCode
          (ay_bceg_Sat originalCnf originalModel))
        (ay_bceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_bceg_conj_intro exitCode
          (ay_bceg_Sat originalCnf originalModel)
          hexit
          ((ay_bceg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_bceg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseId : Prop) (manifestAccepted : Prop) (clauseIdManifest : Prop)
    (pivotLiteral : Prop) (pivotCovered : Prop) (pivotCoveredWitness : Prop)
    (resolvent : Prop) (resolventTautology : Prop) (resolventTautologyWitness : Prop)
    (deletedClause : Prop) (deletionRecorded : Prop)
    (deletionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationProjectionGuard
      originalCnf replayedCnf
      clauseId manifestAccepted clauseIdManifest
      pivotLiteral pivotCovered pivotCoveredWitness
      resolvent resolventTautology resolventTautologyWitness
      deletedClause deletionRecorded deletionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bceReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bceg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_bceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_bceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _pivot _tautology _deletion reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_bceg_disj_right
        (ay_bceg_ExitCodeSound exitCode
          (ay_bceg_Sat originalCnf originalModel))
        (ay_bceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_bceg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_bceg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_bceg_failure_stale_clause_id_manifest
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleClauseIdManifest ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result epoch_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact epoch_case failure

theorem ay_bceg_failure_pivot_literal_coverage
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    pivotCoveredMismatch ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case digest_case _witness_case _deletion_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case failure

theorem ay_bceg_failure_resolvent_tautology_witness
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    resolventTautologyMismatch ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_bceg_failure_deletion_ledger
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    deletionLedgerGap ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_bceg_failure_reconstruction
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_bceg_failure_stale_fingerprint
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_bceg_failure_unchecked_replay
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_bceg_failure_missing_baseline
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_bceg_failure_build
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_bceg_failure_validator
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_bceg_failure_audit
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_bceg_BlockedClauseEliminationProjectionGuardFailure
      staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _pivot_case _witness_case _deletion_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_bceg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bceg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_bceg_conj_right
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_conj_right
      (ay_bceg_BlockedClauseEliminationProjectionGuardFailure
        staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_bceg_Conj
        (ay_bceg_RecomputeObligation currentCnf recompute)
        (ay_bceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_bceg_diagnostic_recompute
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bceg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_bceg_conj_left
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_conj_right
      (ay_bceg_BlockedClauseEliminationProjectionGuardFailure
        staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_bceg_Conj
        (ay_bceg_RecomputeObligation currentCnf recompute)
        (ay_bceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_bceg_unchecked_bce_cannot_bless_public_result
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bceg_Conj
      (ay_bceg_NoSemanticClaim diagnostic)
      (ay_bceg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_bceg_conj_intro
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_diagnostic_no_claim
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_bceg_diagnostic_recompute
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_bceg_unchecked_bce_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bceg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_bceg_diagnostic_no_claim
    currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_bceg_unchecked_bce_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleClauseIdManifest : Prop) (pivotCoveredMismatch : Prop)
    (resolventTautologyMismatch : Prop)
    (deletionLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bceg_DiagnosticBlockedClauseEliminationProjectionGuard
      currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bceg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_bceg_diagnostic_recompute
    currentCnf staleClauseIdManifest pivotCoveredMismatch resolventTautologyMismatch deletionLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
