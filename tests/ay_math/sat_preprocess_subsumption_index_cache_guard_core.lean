-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-index cache guard soundness.
-- The cache is an acceleration structure only. Stale index or cache hits may
-- never delete or strengthen clauses unless exact subsumption, full-scan,
-- reconstruction, replay, validator, archive, and audit evidence agree.

def ay_sicg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sicg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sicg_Equisat (original : Prop) (indexed : Prop) :=
  ay_sicg_Conj (original -> indexed) (indexed -> original)

def ay_sicg_Sat (cnf : Prop) (model : Prop) :=
  ay_sicg_Conj cnf model

def ay_sicg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_sicg_FormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_sicg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_sicg_ClauseDatabaseDigest
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop) :=
  ay_sicg_Conj databaseManifest (databaseDigest -> databaseAccepted)

def ay_sicg_SubsumptionIndexDigest
    (indexDigest : Prop) (indexAccepted : Prop)
    (indexManifest : Prop) :=
  ay_sicg_Conj indexManifest (indexDigest -> indexAccepted)

def ay_sicg_CacheKeyDigest
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop) :=
  ay_sicg_Conj cacheKeyCurrent (cacheKeyDigest -> cacheKeyAccepted)

def ay_sicg_CandidateClauseLedger
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_sicg_Conj candidateCoverage (candidateLedger -> candidateAccepted)

def ay_sicg_SubsumptionWitness
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (exactWitness : Prop) :=
  ay_sicg_Conj exactWitness (subsumptionWitness -> subsumptionAccepted)

def ay_sicg_DeletionStrengtheningLedger
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_sicg_Conj ledgerCoverage
    (deletionStrengtheningLedger -> ledgerAccepted)

def ay_sicg_FallbackFullScanTranscript
    (fullScanTranscript : Prop) (fullScanAccepted : Prop)
    (fullScanCoversCandidates : Prop) :=
  ay_sicg_Conj fullScanCoversCandidates
    (fullScanTranscript -> fullScanAccepted)

def ay_sicg_ModelReconstructionContext
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop) :=
  ay_sicg_Sat indexedCnf indexedModel ->
    ay_sicg_Sat originalCnf originalModel

def ay_sicg_UnsatReplayContext
    (originalCnf : Prop) (indexedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sicg_Replay indexedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_sicg_ReconstructionReplayContext
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sicg_Conj
    (ay_sicg_ModelReconstructionContext
      indexedCnf originalCnf indexedModel originalModel)
    (ay_sicg_UnsatReplayContext originalCnf indexedCnf certificate conflict)

def ay_sicg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_sicg_Conj binaryFingerprint buildReproducible

def ay_sicg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_sicg_Conj checkerAccepted
    (ay_sicg_Conj validatorAccepted validatorVersion)

def ay_sicg_ArchiveManifest
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop) :=
  ay_sicg_Conj archiveAppendOnly
    (ay_sicg_Conj archiveDigest archiveContainsEntry)

def ay_sicg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_sicg_Conj baselineAvailable noClaimPath

def ay_sicg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_sicg_Conj auditAppended auditAppendOnly

def ay_sicg_IndexAccelerationContext
    (candidateCoverage : Prop) (exactWitness : Prop)
    (fullScanCoversCandidates : Prop)
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sicg_Conj candidateCoverage
    (ay_sicg_Conj exactWitness
      (ay_sicg_Conj fullScanCoversCandidates
        (ay_sicg_ReconstructionReplayContext
          indexedCnf originalCnf indexedModel originalModel certificate conflict)))

def ay_sicg_AcceptedSubsumptionIndexCacheGuard
    (originalCnf : Prop) (indexedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (indexDigest : Prop) (indexAccepted : Prop)
    (indexManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (exactWitness : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (fullScanTranscript : Prop) (fullScanAccepted : Prop)
    (fullScanCoversCandidates : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_sicg_FormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_sicg_ClauseDatabaseDigest
       databaseDigest databaseAccepted databaseManifest ->
     ay_sicg_SubsumptionIndexDigest indexDigest indexAccepted indexManifest ->
     ay_sicg_CacheKeyDigest cacheKeyDigest cacheKeyAccepted cacheKeyCurrent ->
     ay_sicg_CandidateClauseLedger
       candidateLedger candidateAccepted candidateCoverage ->
     ay_sicg_SubsumptionWitness
       subsumptionWitness subsumptionAccepted exactWitness ->
     ay_sicg_DeletionStrengtheningLedger
       deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
     ay_sicg_FallbackFullScanTranscript
       fullScanTranscript fullScanAccepted fullScanCoversCandidates ->
     ay_sicg_ReconstructionReplayContext
       indexedCnf originalCnf indexedModel originalModel certificate conflict ->
     ay_sicg_Equisat originalCnf indexedCnf ->
     ay_sicg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_sicg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_sicg_ArchiveManifest
       archiveDigest archiveAppendOnly archiveContainsEntry ->
     ay_sicg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_sicg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_sicg_SubsumptionCacheGuardFailure
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (formulaMismatch -> result) ->
    (dbMismatch -> result) ->
    (indexMismatch -> result) ->
    (cacheMismatch -> result) ->
    (candidateMismatch -> result) ->
    (witnessMismatch -> result) ->
    (deletionMismatch -> result) ->
    (fullScanMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_sicg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_sicg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_sicg_Conj currentCnf recompute

def ay_sicg_DiagnosticSubsumptionCacheGuard
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_sicg_Conj
    (ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch)
    (ay_sicg_Conj
      (ay_sicg_RecomputeObligation currentCnf recompute)
      (ay_sicg_NoSemanticClaim diagnostic))

def ay_sicg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_sicg_Conj exitCode claim

def ay_sicg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_sicg_Disj
    (ay_sicg_ExitCodeSound exitCode (ay_sicg_Sat originalCnf model))
    (ay_sicg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_sicg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_sicg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_sicg_conj_left
    (left : Prop) (right : Prop) :
    ay_sicg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_sicg_conj_right
    (left : Prop) (right : Prop) :
    ay_sicg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_sicg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_sicg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_sicg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_sicg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_sicg_equisat_forward
    (original : Prop) (indexed : Prop) :
    ay_sicg_Equisat original indexed -> original -> indexed := by
  intro equisat
  exact ay_sicg_conj_left (original -> indexed) (indexed -> original)
    equisat

theorem ay_sicg_equisat_backward
    (original : Prop) (indexed : Prop) :
    ay_sicg_Equisat original indexed -> indexed -> original := by
  intro equisat
  exact ay_sicg_conj_right (original -> indexed) (indexed -> original)
    equisat

theorem ay_sicg_index_digest_applies
    (indexDigest : Prop) (indexAccepted : Prop)
    (indexManifest : Prop) :
    ay_sicg_SubsumptionIndexDigest indexDigest indexAccepted indexManifest ->
    indexDigest -> ay_sicg_Conj indexManifest indexAccepted := by
  intro index hindex
  exact ay_sicg_conj_intro indexManifest indexAccepted
    (ay_sicg_conj_left indexManifest (indexDigest -> indexAccepted) index)
    ((ay_sicg_conj_right indexManifest
      (indexDigest -> indexAccepted) index) hindex)

theorem ay_sicg_cache_key_applies
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop) :
    ay_sicg_CacheKeyDigest cacheKeyDigest cacheKeyAccepted cacheKeyCurrent ->
    cacheKeyDigest -> ay_sicg_Conj cacheKeyCurrent cacheKeyAccepted := by
  intro cache hcache
  exact ay_sicg_conj_intro cacheKeyCurrent cacheKeyAccepted
    (ay_sicg_conj_left cacheKeyCurrent
      (cacheKeyDigest -> cacheKeyAccepted) cache)
    ((ay_sicg_conj_right cacheKeyCurrent
      (cacheKeyDigest -> cacheKeyAccepted) cache) hcache)

theorem ay_sicg_candidate_ledger_applies
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_sicg_CandidateClauseLedger
      candidateLedger candidateAccepted candidateCoverage ->
    candidateLedger -> ay_sicg_Conj candidateCoverage candidateAccepted := by
  intro candidate hcandidate
  exact ay_sicg_conj_intro candidateCoverage candidateAccepted
    (ay_sicg_conj_left candidateCoverage
      (candidateLedger -> candidateAccepted) candidate)
    ((ay_sicg_conj_right candidateCoverage
      (candidateLedger -> candidateAccepted) candidate) hcandidate)

theorem ay_sicg_subsumption_witness_applies
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (exactWitness : Prop) :
    ay_sicg_SubsumptionWitness
      subsumptionWitness subsumptionAccepted exactWitness ->
    subsumptionWitness -> ay_sicg_Conj exactWitness subsumptionAccepted := by
  intro witness hwitness
  exact ay_sicg_conj_intro exactWitness subsumptionAccepted
    (ay_sicg_conj_left exactWitness
      (subsumptionWitness -> subsumptionAccepted) witness)
    ((ay_sicg_conj_right exactWitness
      (subsumptionWitness -> subsumptionAccepted) witness) hwitness)

theorem ay_sicg_deletion_ledger_applies
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_sicg_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    deletionStrengtheningLedger ->
    ay_sicg_Conj ledgerCoverage ledgerAccepted := by
  intro ledger hledger
  exact ay_sicg_conj_intro ledgerCoverage ledgerAccepted
    (ay_sicg_conj_left ledgerCoverage
      (deletionStrengtheningLedger -> ledgerAccepted) ledger)
    ((ay_sicg_conj_right ledgerCoverage
      (deletionStrengtheningLedger -> ledgerAccepted) ledger) hledger)

theorem ay_sicg_full_scan_applies
    (fullScanTranscript : Prop) (fullScanAccepted : Prop)
    (fullScanCoversCandidates : Prop) :
    ay_sicg_FallbackFullScanTranscript
      fullScanTranscript fullScanAccepted fullScanCoversCandidates ->
    fullScanTranscript ->
    ay_sicg_Conj fullScanCoversCandidates fullScanAccepted := by
  intro scan hscan
  exact ay_sicg_conj_intro fullScanCoversCandidates fullScanAccepted
    (ay_sicg_conj_left fullScanCoversCandidates
      (fullScanTranscript -> fullScanAccepted) scan)
    ((ay_sicg_conj_right fullScanCoversCandidates
      (fullScanTranscript -> fullScanAccepted) scan) hscan)

theorem ay_sicg_model_context
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_ModelReconstructionContext
      indexedCnf originalCnf indexedModel originalModel := by
  intro reconstruction
  exact ay_sicg_conj_left
    (ay_sicg_ModelReconstructionContext
      indexedCnf originalCnf indexedModel originalModel)
    (ay_sicg_UnsatReplayContext originalCnf indexedCnf certificate conflict)
    reconstruction

theorem ay_sicg_replay_context
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_UnsatReplayContext originalCnf indexedCnf certificate conflict := by
  intro reconstruction
  exact ay_sicg_conj_right
    (ay_sicg_ModelReconstructionContext
      indexedCnf originalCnf indexedModel originalModel)
    (ay_sicg_UnsatReplayContext originalCnf indexedCnf certificate conflict)
    reconstruction

theorem ay_sicg_accepted_equisat
    (originalCnf : Prop) (indexedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (indexDigest : Prop) (indexAccepted : Prop)
    (indexManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (exactWitness : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (fullScanTranscript : Prop) (fullScanAccepted : Prop)
    (fullScanCoversCandidates : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sicg_AcceptedSubsumptionIndexCacheGuard
      originalCnf indexedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest indexDigest indexAccepted
      indexManifest cacheKeyDigest cacheKeyAccepted cacheKeyCurrent
      candidateLedger candidateAccepted candidateCoverage
      subsumptionWitness subsumptionAccepted exactWitness
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      fullScanTranscript fullScanAccepted fullScanCoversCandidates
      indexedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_sicg_Equisat originalCnf indexedCnf := by
  intro accepted
  exact accepted (ay_sicg_Equisat originalCnf indexedCnf)
    (fun _fingerprint _database _index _cache _candidate _witness
      _deletion _scan _reconstruction equisat _build _validator _archive
      _fallback _audit => equisat)

theorem ay_sicg_accepted_reconstruction
    (originalCnf : Prop) (indexedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (indexDigest : Prop) (indexAccepted : Prop)
    (indexManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (exactWitness : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (fullScanTranscript : Prop) (fullScanAccepted : Prop)
    (fullScanCoversCandidates : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sicg_AcceptedSubsumptionIndexCacheGuard
      originalCnf indexedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest indexDigest indexAccepted
      indexManifest cacheKeyDigest cacheKeyAccepted cacheKeyCurrent
      candidateLedger candidateAccepted candidateCoverage
      subsumptionWitness subsumptionAccepted exactWitness
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      fullScanTranscript fullScanAccepted fullScanCoversCandidates
      indexedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict)
    (fun _fingerprint _database _index _cache _candidate _witness
      _deletion _scan reconstruction _equisat _build _validator _archive
      _fallback _audit => reconstruction)

theorem ay_sicg_cache_is_acceleration_only
    (candidateCoverage : Prop) (exactWitness : Prop)
    (fullScanCoversCandidates : Prop)
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sicg_IndexAccelerationContext
      candidateCoverage exactWitness fullScanCoversCandidates
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_Conj candidateCoverage
      (ay_sicg_Conj exactWitness fullScanCoversCandidates) := by
  intro context
  exact ay_sicg_conj_intro candidateCoverage
    (ay_sicg_Conj exactWitness fullScanCoversCandidates)
    (ay_sicg_conj_left candidateCoverage
      (ay_sicg_Conj exactWitness
        (ay_sicg_Conj fullScanCoversCandidates
          (ay_sicg_ReconstructionReplayContext
            indexedCnf originalCnf indexedModel originalModel
            certificate conflict)))
      context)
    (ay_sicg_conj_intro exactWitness fullScanCoversCandidates
      (ay_sicg_conj_left exactWitness
        (ay_sicg_Conj fullScanCoversCandidates
          (ay_sicg_ReconstructionReplayContext
            indexedCnf originalCnf indexedModel originalModel certificate conflict))
        (ay_sicg_conj_right candidateCoverage
          (ay_sicg_Conj exactWitness
            (ay_sicg_Conj fullScanCoversCandidates
              (ay_sicg_ReconstructionReplayContext
                indexedCnf originalCnf indexedModel originalModel
                certificate conflict)))
          context))
      (ay_sicg_conj_left fullScanCoversCandidates
        (ay_sicg_ReconstructionReplayContext
          indexedCnf originalCnf indexedModel originalModel certificate conflict)
        (ay_sicg_conj_right exactWitness
          (ay_sicg_Conj fullScanCoversCandidates
            (ay_sicg_ReconstructionReplayContext
              indexedCnf originalCnf indexedModel originalModel
              certificate conflict))
          (ay_sicg_conj_right candidateCoverage
            (ay_sicg_Conj exactWitness
              (ay_sicg_Conj fullScanCoversCandidates
                (ay_sicg_ReconstructionReplayContext
                  indexedCnf originalCnf indexedModel originalModel
                  certificate conflict)))
            context))))

theorem ay_sicg_sat_pullback
    (originalCnf : Prop) (indexedCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_Sat indexedCnf indexedModel ->
    ay_sicg_Sat originalCnf originalModel := by
  intro reconstruction model
  exact (ay_sicg_model_context indexedCnf originalCnf indexedModel
    originalModel certificate conflict reconstruction) model

theorem ay_sicg_unsat_pushback
    (originalCnf : Prop) (indexedCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_Replay indexedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruction replay
  exact (ay_sicg_replay_context indexedCnf originalCnf indexedModel
    originalModel certificate conflict reconstruction) replay

theorem ay_sicg_public_sat_sound
    (originalCnf : Prop) (indexedCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_ExitCodeSound exitCode (ay_sicg_Sat indexedCnf indexedModel) ->
    ay_sicg_ExitCodeSound exitCode (ay_sicg_Sat originalCnf originalModel) := by
  intro reconstruction publicSat
  exact ay_sicg_conj_intro exitCode
    (ay_sicg_Sat originalCnf originalModel)
    (ay_sicg_conj_left exitCode
      (ay_sicg_Sat indexedCnf indexedModel) publicSat)
    (ay_sicg_sat_pullback originalCnf indexedCnf indexedModel originalModel
      certificate conflict reconstruction
      (ay_sicg_conj_right exitCode
        (ay_sicg_Sat indexedCnf indexedModel) publicSat))

theorem ay_sicg_public_unsat_sound
    (originalCnf : Prop) (indexedCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_sicg_ReconstructionReplayContext
      indexedCnf originalCnf indexedModel originalModel certificate conflict ->
    ay_sicg_Replay indexedCnf certificate conflict ->
    ay_sicg_ExitCodeSound exitCode certificate ->
    ay_sicg_ExitCodeSound exitCode (originalCnf -> conflict) := by
  intro reconstruction replay publicUnsat
  exact ay_sicg_conj_intro exitCode (originalCnf -> conflict)
    (ay_sicg_conj_left exitCode certificate publicUnsat)
    (fun original =>
      ay_sicg_unsat_pushback originalCnf indexedCnf indexedModel
        originalModel certificate conflict reconstruction replay
        (ay_sicg_conj_right exitCode certificate publicUnsat) original)

theorem ay_sicg_failure_formula
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    formulaMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact formula_case mismatch

theorem ay_sicg_failure_db
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    dbMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact db_case mismatch

theorem ay_sicg_failure_index
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    indexMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact index_case mismatch

theorem ay_sicg_failure_cache
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    cacheMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact cache_case mismatch

theorem ay_sicg_failure_candidate
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    candidateMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact candidate_case mismatch

theorem ay_sicg_failure_witness
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    witnessMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact witness_case mismatch

theorem ay_sicg_failure_deletion
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    deletionMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact deletion_case mismatch

theorem ay_sicg_failure_full_scan
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    fullScanMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case scan_case _model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact scan_case mismatch

theorem ay_sicg_failure_model
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    modelMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case model_case
    _replay_case _build_case _validator_case _archive_case _audit_case
  exact model_case mismatch

theorem ay_sicg_failure_replay
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    replayMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    replay_case _build_case _validator_case _archive_case _audit_case
  exact replay_case mismatch

theorem ay_sicg_failure_build
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    buildMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case build_case _validator_case _archive_case _audit_case
  exact build_case mismatch

theorem ay_sicg_failure_validator
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    validatorMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case validator_case _archive_case _audit_case
  exact validator_case mismatch

theorem ay_sicg_failure_archive
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    archiveMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case archive_case _audit_case
  exact archive_case mismatch

theorem ay_sicg_failure_audit
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    auditMismatch ->
    ay_sicg_SubsumptionCacheGuardFailure
      formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
      witnessMismatch deletionMismatch fullScanMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _index_case _cache_case
    _candidate_case _witness_case _deletion_case _scan_case _model_case
    _replay_case _build_case _validator_case _archive_case audit_case
  exact audit_case mismatch

theorem ay_sicg_diagnostic_no_claim
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sicg_DiagnosticSubsumptionCacheGuard
      currentCnf formulaMismatch dbMismatch indexMismatch cacheMismatch
      candidateMismatch witnessMismatch deletionMismatch fullScanMismatch
      modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_sicg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_sicg_conj_right
    (ay_sicg_RecomputeObligation currentCnf recompute)
    (ay_sicg_NoSemanticClaim diagnostic)
    (ay_sicg_conj_right
      (ay_sicg_SubsumptionCacheGuardFailure
        formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
        witnessMismatch deletionMismatch fullScanMismatch modelMismatch
        replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch)
      (ay_sicg_Conj
        (ay_sicg_RecomputeObligation currentCnf recompute)
        (ay_sicg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_sicg_diagnostic_recompute
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sicg_DiagnosticSubsumptionCacheGuard
      currentCnf formulaMismatch dbMismatch indexMismatch cacheMismatch
      candidateMismatch witnessMismatch deletionMismatch fullScanMismatch
      modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_sicg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_sicg_conj_left
    (ay_sicg_RecomputeObligation currentCnf recompute)
    (ay_sicg_NoSemanticClaim diagnostic)
    (ay_sicg_conj_right
      (ay_sicg_SubsumptionCacheGuardFailure
        formulaMismatch dbMismatch indexMismatch cacheMismatch candidateMismatch
        witnessMismatch deletionMismatch fullScanMismatch modelMismatch
        replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch)
      (ay_sicg_Conj
        (ay_sicg_RecomputeObligation currentCnf recompute)
        (ay_sicg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_sicg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sicg_DiagnosticSubsumptionCacheGuard
      currentCnf formulaMismatch dbMismatch indexMismatch cacheMismatch
      candidateMismatch witnessMismatch deletionMismatch fullScanMismatch
      modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_sicg_Disj
      (ay_sicg_NoSemanticClaim diagnostic)
      (ay_sicg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard
  exact ay_sicg_disj_left
    (ay_sicg_NoSemanticClaim diagnostic)
    (ay_sicg_RecomputeObligation currentCnf recompute)
    (ay_sicg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
      indexMismatch cacheMismatch candidateMismatch witnessMismatch
      deletionMismatch fullScanMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch archiveMismatch auditMismatch recompute diagnostic
      diagnosticGuard)

theorem ay_sicg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop) (model : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sicg_DiagnosticSubsumptionCacheGuard
      currentCnf formulaMismatch dbMismatch indexMismatch cacheMismatch
      candidateMismatch witnessMismatch deletionMismatch fullScanMismatch
      modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_sicg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_sicg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
    indexMismatch cacheMismatch candidateMismatch witnessMismatch deletionMismatch
    fullScanMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
    archiveMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_sicg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop) (certificate : Prop) (conflict : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (indexMismatch : Prop) (cacheMismatch : Prop)
    (candidateMismatch : Prop) (witnessMismatch : Prop)
    (deletionMismatch : Prop) (fullScanMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sicg_DiagnosticSubsumptionCacheGuard
      currentCnf formulaMismatch dbMismatch indexMismatch cacheMismatch
      candidateMismatch witnessMismatch deletionMismatch fullScanMismatch
      modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_sicg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_sicg_diagnostic_recompute currentCnf formulaMismatch dbMismatch
    indexMismatch cacheMismatch candidateMismatch witnessMismatch deletionMismatch
    fullScanMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
    archiveMismatch auditMismatch recompute diagnostic diagnosticGuard
