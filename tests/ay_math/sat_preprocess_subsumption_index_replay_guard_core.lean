-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-index replay guard soundness.
-- The propositions stand for index snapshot digests, subsumption witness ledgers, removed-clause
-- coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_sidx_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sidx_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sidx_Equisat (before : Prop) (after : Prop) :=
  ay_sidx_Conj (before -> after) (after -> before)

def ay_sidx_Sat (cnf : Prop) (model : Prop) :=
  ay_sidx_Conj cnf model

def ay_sidx_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_sidx_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_sidx_Conj (leftId -> rightId) (rightId -> leftId)

def ay_sidx_IndexSnapshotDigest
    (indexSnapshot : Prop) (snapshotDigest : Prop)
    (digestWitness : Prop) :=
  ay_sidx_Conj digestWitness (indexSnapshot -> snapshotDigest)

def ay_sidx_SubsumptionWitnessLedger
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :=
  ay_sidx_Conj subsumptionLedger (subsumingClause -> subsumptionWitness)

def ay_sidx_RemovedClauseCoverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :=
  ay_sidx_Conj removalCoverageWitness (removedClause -> coveredRemovedClause)

def ay_sidx_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_sidx_Sat replayedCnf replayedModel ->
    ay_sidx_Sat originalCnf originalModel

def ay_sidx_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sidx_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_sidx_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sidx_Conj
    (ay_sidx_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sidx_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_sidx_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_sidx_Conj fingerprintWitness
    (ay_sidx_IdMatch originalFingerprint replayedFingerprint)

def ay_sidx_CheckerReplay
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_sidx_Conj subsumptionReplayCertificate checkerAccepted

def ay_sidx_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_sidx_Conj baselineSolver baselineAvailable

def ay_sidx_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_sidx_Conj binaryFingerprint buildReproducible

def ay_sidx_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_sidx_Conj validatorAccepted validatorVersion

def ay_sidx_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_sidx_Conj auditAppended auditAppendOnly

def ay_sidx_AcceptedSubsumptionIndexReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_sidx_IndexSnapshotDigest
       indexSnapshot snapshotDigest digestWitness ->
     ay_sidx_SubsumptionWitnessLedger
       subsumingClause subsumptionWitness subsumptionLedger ->
     ay_sidx_RemovedClauseCoverage
       removedClause coveredRemovedClause removalCoverageWitness ->
     ay_sidx_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_sidx_Equisat originalCnf replayedCnf ->
     ay_sidx_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_sidx_CheckerReplay subsumptionReplayCertificate checkerAccepted ->
     ay_sidx_FallbackBaseline baselineSolver baselineAvailable ->
     ay_sidx_BuildEvidence binaryFingerprint buildReproducible ->
     ay_sidx_ValidatorGate validatorAccepted validatorVersion ->
     ay_sidx_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_sidx_SubsumptionIndexReplayGuardFailure
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (indexDigestMismatch -> result) ->
    (missingSubsumptionWitness -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_sidx_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_sidx_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_sidx_Conj currentCnf recompute

def ay_sidx_DiagnosticSubsumptionIndexReplayGuard
    (currentCnf : Prop)
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_sidx_Conj
    (ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_sidx_Conj
      (ay_sidx_RecomputeObligation currentCnf recompute)
      (ay_sidx_NoSemanticClaim diagnostic))

def ay_sidx_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_sidx_Conj exitCode claim

def ay_sidx_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_sidx_Disj
    (ay_sidx_ExitCodeSound exitCode (ay_sidx_Sat originalCnf model))
    (ay_sidx_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_sidx_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_sidx_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_sidx_conj_left
    (left : Prop) (right : Prop) :
    ay_sidx_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_sidx_conj_right
    (left : Prop) (right : Prop) :
    ay_sidx_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_sidx_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_sidx_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_sidx_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_sidx_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_sidx_equisat_forward
    (before : Prop) (after : Prop) :
    ay_sidx_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_sidx_conj_left (before -> after) (after -> before) eqsat

theorem ay_sidx_equisat_backward
    (before : Prop) (after : Prop) :
    ay_sidx_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_sidx_conj_right (before -> after) (after -> before) eqsat

theorem ay_sidx_index_snapshot_digest_applies
    (indexSnapshot : Prop) (snapshotDigest : Prop)
    (digestWitness : Prop) :
    ay_sidx_IndexSnapshotDigest
      indexSnapshot snapshotDigest digestWitness ->
    indexSnapshot -> snapshotDigest := by
  intro digest
  exact ay_sidx_conj_right digestWitness
    (indexSnapshot -> snapshotDigest) digest

theorem ay_sidx_subsumption_witness_applies
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :
    ay_sidx_SubsumptionWitnessLedger
      subsumingClause subsumptionWitness subsumptionLedger ->
    subsumingClause -> subsumptionWitness := by
  intro ledger
  exact ay_sidx_conj_right subsumptionLedger
    (subsumingClause -> subsumptionWitness) ledger

theorem ay_sidx_removed_clause_coverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :
    ay_sidx_RemovedClauseCoverage
      removedClause coveredRemovedClause removalCoverageWitness ->
    removedClause -> coveredRemovedClause := by
  intro coverage
  exact ay_sidx_conj_right removalCoverageWitness
    (removedClause -> coveredRemovedClause) coverage

theorem ay_sidx_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sidx_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sidx_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_sidx_conj_left
    (ay_sidx_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sidx_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sidx_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sidx_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sidx_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_sidx_conj_right
    (ay_sidx_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sidx_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sidx_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sidx_AcceptedSubsumptionIndexReplayGuard
      originalCnf replayedCnf
      indexSnapshot snapshotDigest digestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      subsumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sidx_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_sidx_Equisat originalCnf replayedCnf)
    (fun _index _subsumption _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_sidx_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sidx_AcceptedSubsumptionIndexReplayGuard
      originalCnf replayedCnf
      indexSnapshot snapshotDigest digestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      subsumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sidx_CheckerReplay subsumptionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_sidx_CheckerReplay subsumptionReplayCertificate checkerAccepted)
    (fun _index _subsumption _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_sidx_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sidx_AcceptedSubsumptionIndexReplayGuard
      originalCnf replayedCnf
      indexSnapshot snapshotDigest digestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      subsumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sidx_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_sidx_AuditTranscript auditAppended auditAppendOnly)
    (fun _index _subsumption _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_sidx_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_sidx_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_sidx_Sat replayedCnf replayedModel ->
    ay_sidx_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_sidx_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sidx_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_sidx_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_sidx_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sidx_AcceptedSubsumptionIndexReplayGuard
      originalCnf replayedCnf
      indexSnapshot snapshotDigest digestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      subsumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sidx_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_sidx_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_sidx_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _index _subsumption _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_sidx_disj_left
        (ay_sidx_ExitCodeSound exitCode
          (ay_sidx_Sat originalCnf originalModel))
        (ay_sidx_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sidx_conj_intro exitCode
          (ay_sidx_Sat originalCnf originalModel)
          hexit
          ((ay_sidx_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_sidx_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (indexSnapshot : Prop) (snapshotDigest : Prop) (digestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sidx_AcceptedSubsumptionIndexReplayGuard
      originalCnf replayedCnf
      indexSnapshot snapshotDigest digestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      subsumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sidx_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_sidx_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_sidx_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _index _subsumption _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_sidx_disj_right
        (ay_sidx_ExitCodeSound exitCode
          (ay_sidx_Sat originalCnf originalModel))
        (ay_sidx_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sidx_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_sidx_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_sidx_failure_index_digest
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    indexDigestMismatch ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact index_case failure

theorem ay_sidx_failure_missing_subsumption_witness
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingSubsumptionWitness ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_sidx_failure_coverage
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_sidx_failure_reconstruction
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_sidx_failure_stale_fingerprint
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_sidx_failure_unchecked_replay
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_sidx_failure_missing_baseline
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_sidx_failure_build
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_sidx_failure_validator
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_sidx_failure_audit
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_sidx_SubsumptionIndexReplayGuardFailure
      indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _index_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_sidx_diagnostic_no_claim
    (currentCnf : Prop)
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sidx_DiagnosticSubsumptionIndexReplayGuard
      currentCnf indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sidx_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_sidx_conj_right
    (ay_sidx_RecomputeObligation currentCnf recompute)
    (ay_sidx_NoSemanticClaim diagnostic)
    (ay_sidx_conj_right
      (ay_sidx_SubsumptionIndexReplayGuardFailure
        indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sidx_Conj
        (ay_sidx_RecomputeObligation currentCnf recompute)
        (ay_sidx_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sidx_diagnostic_recompute
    (currentCnf : Prop)
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sidx_DiagnosticSubsumptionIndexReplayGuard
      currentCnf indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sidx_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_sidx_conj_left
    (ay_sidx_RecomputeObligation currentCnf recompute)
    (ay_sidx_NoSemanticClaim diagnostic)
    (ay_sidx_conj_right
      (ay_sidx_SubsumptionIndexReplayGuardFailure
        indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sidx_Conj
        (ay_sidx_RecomputeObligation currentCnf recompute)
        (ay_sidx_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sidx_unchecked_index_hit_cannot_bless_public_result
    (currentCnf : Prop)
    (indexDigestMismatch : Prop) (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_sidx_DiagnosticSubsumptionIndexReplayGuard
      currentCnf indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sidx_Conj
      (ay_sidx_NoSemanticClaim diagnostic)
      (ay_sidx_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_sidx_conj_intro
    (ay_sidx_NoSemanticClaim diagnostic)
    (ay_sidx_RecomputeObligation currentCnf recompute)
    (ay_sidx_diagnostic_no_claim
      currentCnf indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_sidx_diagnostic_recompute
      currentCnf indexDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
