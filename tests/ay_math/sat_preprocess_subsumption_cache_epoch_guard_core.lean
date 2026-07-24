-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-cache epoch guard soundness.
-- The propositions stand for cache epoch ledgers, cache digests, subsumption witness ledgers, removed-clause
-- coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_sceg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sceg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sceg_Equisat (before : Prop) (after : Prop) :=
  ay_sceg_Conj (before -> after) (after -> before)

def ay_sceg_Sat (cnf : Prop) (model : Prop) :=
  ay_sceg_Conj cnf model

def ay_sceg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_sceg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_sceg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_sceg_CacheEpochLedger
    (cacheEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :=
  ay_sceg_Conj epochLedger (cacheEpoch -> epochAccepted)

def ay_sceg_CacheDigest
    (cacheEntry : Prop) (cacheDigest : Prop)
    (cacheDigestWitness : Prop) :=
  ay_sceg_Conj cacheDigestWitness (cacheEntry -> cacheDigest)

def ay_sceg_SubsumptionWitnessLedger
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :=
  ay_sceg_Conj subsumptionLedger (subsumingClause -> subsumptionWitness)

def ay_sceg_RemovedClauseCoverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :=
  ay_sceg_Conj removalCoverageWitness (removedClause -> coveredRemovedClause)

def ay_sceg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_sceg_Sat replayedCnf replayedModel ->
    ay_sceg_Sat originalCnf originalModel

def ay_sceg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_sceg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sceg_Conj
    (ay_sceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_sceg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_sceg_Conj fingerprintWitness
    (ay_sceg_IdMatch originalFingerprint replayedFingerprint)

def ay_sceg_CheckerReplay
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_sceg_Conj cacheReplayCertificate checkerAccepted

def ay_sceg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_sceg_Conj baselineSolver baselineAvailable

def ay_sceg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_sceg_Conj binaryFingerprint buildReproducible

def ay_sceg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_sceg_Conj validatorAccepted validatorVersion

def ay_sceg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_sceg_Conj auditAppended auditAppendOnly

def ay_sceg_AcceptedSubsumptionCacheEpochGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_sceg_CacheEpochLedger
       cacheEpoch epochAccepted epochLedger ->
     ay_sceg_CacheDigest
       cacheEntry cacheDigest cacheDigestWitness ->
     ay_sceg_SubsumptionWitnessLedger
       subsumingClause subsumptionWitness subsumptionLedger ->
     ay_sceg_RemovedClauseCoverage
       removedClause coveredRemovedClause removalCoverageWitness ->
     ay_sceg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_sceg_Equisat originalCnf replayedCnf ->
     ay_sceg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_sceg_CheckerReplay cacheReplayCertificate checkerAccepted ->
     ay_sceg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_sceg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_sceg_ValidatorGate validatorAccepted validatorVersion ->
     ay_sceg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_sceg_SubsumptionCacheEpochGuardFailure
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleEpoch -> result) ->
    (cacheDigestMismatch -> result) ->
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

def ay_sceg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_sceg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_sceg_Conj currentCnf recompute

def ay_sceg_DiagnosticSubsumptionCacheEpochGuard
    (currentCnf : Prop)
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_sceg_Conj
    (ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_sceg_Conj
      (ay_sceg_RecomputeObligation currentCnf recompute)
      (ay_sceg_NoSemanticClaim diagnostic))

def ay_sceg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_sceg_Conj exitCode claim

def ay_sceg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_sceg_Disj
    (ay_sceg_ExitCodeSound exitCode (ay_sceg_Sat originalCnf model))
    (ay_sceg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_sceg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_sceg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_sceg_conj_left
    (left : Prop) (right : Prop) :
    ay_sceg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_sceg_conj_right
    (left : Prop) (right : Prop) :
    ay_sceg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_sceg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_sceg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_sceg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_sceg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_sceg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_sceg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_sceg_conj_left (before -> after) (after -> before) eqsat

theorem ay_sceg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_sceg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_sceg_conj_right (before -> after) (after -> before) eqsat

theorem ay_sceg_cache_epoch_ledger_applies
    (cacheEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :
    ay_sceg_CacheEpochLedger
      cacheEpoch epochAccepted epochLedger ->
    cacheEpoch -> epochAccepted := by
  intro digest
  exact ay_sceg_conj_right epochLedger
    (cacheEpoch -> epochAccepted) digest

theorem ay_sceg_cache_digest_applies
    (cacheEntry : Prop) (cacheDigest : Prop)
    (cacheDigestWitness : Prop) :
    ay_sceg_CacheDigest
      cacheEntry cacheDigest cacheDigestWitness ->
    cacheEntry -> cacheDigest := by
  intro digest
  exact ay_sceg_conj_right cacheDigestWitness
    (cacheEntry -> cacheDigest) digest

theorem ay_sceg_subsumption_witness_applies
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :
    ay_sceg_SubsumptionWitnessLedger
      subsumingClause subsumptionWitness subsumptionLedger ->
    subsumingClause -> subsumptionWitness := by
  intro ledger
  exact ay_sceg_conj_right subsumptionLedger
    (subsumingClause -> subsumptionWitness) ledger

theorem ay_sceg_removed_clause_coverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :
    ay_sceg_RemovedClauseCoverage
      removedClause coveredRemovedClause removalCoverageWitness ->
    removedClause -> coveredRemovedClause := by
  intro coverage
  exact ay_sceg_conj_right removalCoverageWitness
    (removedClause -> coveredRemovedClause) coverage

theorem ay_sceg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_sceg_conj_left
    (ay_sceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sceg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_sceg_conj_right
    (ay_sceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sceg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sceg_AcceptedSubsumptionCacheEpochGuard
      originalCnf replayedCnf
      cacheEpoch epochAccepted epochLedger
      cacheEntry cacheDigest cacheDigestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cacheReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sceg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_sceg_Equisat originalCnf replayedCnf)
    (fun _epoch _digest _subsumption _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_sceg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sceg_AcceptedSubsumptionCacheEpochGuard
      originalCnf replayedCnf
      cacheEpoch epochAccepted epochLedger
      cacheEntry cacheDigest cacheDigestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cacheReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sceg_CheckerReplay cacheReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_sceg_CheckerReplay cacheReplayCertificate checkerAccepted)
    (fun _epoch _digest _subsumption _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_sceg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sceg_AcceptedSubsumptionCacheEpochGuard
      originalCnf replayedCnf
      cacheEpoch epochAccepted epochLedger
      cacheEntry cacheDigest cacheDigestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cacheReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sceg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_sceg_AuditTranscript auditAppended auditAppendOnly)
    (fun _epoch _digest _subsumption _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_sceg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_sceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_sceg_Sat replayedCnf replayedModel ->
    ay_sceg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_sceg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_sceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_sceg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sceg_AcceptedSubsumptionCacheEpochGuard
      originalCnf replayedCnf
      cacheEpoch epochAccepted epochLedger
      cacheEntry cacheDigest cacheDigestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cacheReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sceg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_sceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_sceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _subsumption _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_sceg_disj_left
        (ay_sceg_ExitCodeSound exitCode
          (ay_sceg_Sat originalCnf originalModel))
        (ay_sceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sceg_conj_intro exitCode
          (ay_sceg_Sat originalCnf originalModel)
          hexit
          ((ay_sceg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_sceg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cacheEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (cacheEntry : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cacheReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sceg_AcceptedSubsumptionCacheEpochGuard
      originalCnf replayedCnf
      cacheEpoch epochAccepted epochLedger
      cacheEntry cacheDigest cacheDigestWitness
      subsumingClause subsumptionWitness subsumptionLedger
      removedClause coveredRemovedClause removalCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cacheReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sceg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_sceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_sceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _subsumption _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_sceg_disj_right
        (ay_sceg_ExitCodeSound exitCode
          (ay_sceg_Sat originalCnf originalModel))
        (ay_sceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sceg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_sceg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_sceg_failure_stale_epoch
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleEpoch ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact epoch_case failure

theorem ay_sceg_failure_cache_digest
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    cacheDigestMismatch ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case digest_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case failure

theorem ay_sceg_failure_missing_subsumption_witness
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingSubsumptionWitness ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_sceg_failure_coverage
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_sceg_failure_reconstruction
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_sceg_failure_stale_fingerprint
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_sceg_failure_unchecked_replay
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_sceg_failure_missing_baseline
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_sceg_failure_build
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_sceg_failure_validator
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_sceg_failure_audit
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_sceg_SubsumptionCacheEpochGuardFailure
      staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_sceg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sceg_DiagnosticSubsumptionCacheEpochGuard
      currentCnf staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sceg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_sceg_conj_right
    (ay_sceg_RecomputeObligation currentCnf recompute)
    (ay_sceg_NoSemanticClaim diagnostic)
    (ay_sceg_conj_right
      (ay_sceg_SubsumptionCacheEpochGuardFailure
        staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sceg_Conj
        (ay_sceg_RecomputeObligation currentCnf recompute)
        (ay_sceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sceg_diagnostic_recompute
    (currentCnf : Prop)
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sceg_DiagnosticSubsumptionCacheEpochGuard
      currentCnf staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sceg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_sceg_conj_left
    (ay_sceg_RecomputeObligation currentCnf recompute)
    (ay_sceg_NoSemanticClaim diagnostic)
    (ay_sceg_conj_right
      (ay_sceg_SubsumptionCacheEpochGuardFailure
        staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sceg_Conj
        (ay_sceg_RecomputeObligation currentCnf recompute)
        (ay_sceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sceg_unchecked_cache_use_cannot_bless_public_result
    (currentCnf : Prop)
    (staleEpoch : Prop) (cacheDigestMismatch : Prop)
    (missingSubsumptionWitness : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_sceg_DiagnosticSubsumptionCacheEpochGuard
      currentCnf staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sceg_Conj
      (ay_sceg_NoSemanticClaim diagnostic)
      (ay_sceg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_sceg_conj_intro
    (ay_sceg_NoSemanticClaim diagnostic)
    (ay_sceg_RecomputeObligation currentCnf recompute)
    (ay_sceg_diagnostic_no_claim
      currentCnf staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_sceg_diagnostic_recompute
      currentCnf staleEpoch cacheDigestMismatch missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
