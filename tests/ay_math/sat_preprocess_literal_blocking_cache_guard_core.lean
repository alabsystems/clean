-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Literal-blocking cache guard soundness.
-- Cached blocking decisions are preprocessing acceleration only. They cannot
-- delete clauses or justify public SAT/UNSAT unless exact blocking-literal,
-- complementary-resolvent tautology, full-check, reconstruction, replay,
-- validator, archive, and audit evidence agree.

def ay_lbcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lbcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_lbcg_Equisat (original : Prop) (blocked : Prop) :=
  ay_lbcg_Conj (original -> blocked) (blocked -> original)

def ay_lbcg_Sat (cnf : Prop) (model : Prop) :=
  ay_lbcg_Conj cnf model

def ay_lbcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_lbcg_FormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_lbcg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_lbcg_ClauseDatabaseDigest
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop) :=
  ay_lbcg_Conj databaseManifest (databaseDigest -> databaseAccepted)

def ay_lbcg_BlockingCacheKeyDigest
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop) :=
  ay_lbcg_Conj cacheKeyCurrent (cacheKeyDigest -> cacheKeyAccepted)

def ay_lbcg_BlockingLiteralWitness
    (blockingLiteralWitness : Prop) (literalAccepted : Prop)
    (literalCoversDeletedClause : Prop) :=
  ay_lbcg_Conj literalCoversDeletedClause
    (blockingLiteralWitness -> literalAccepted)

def ay_lbcg_ResolventTautologyTranscript
    (resolventTranscript : Prop) (resolventAccepted : Prop)
    (allComplementaryResolventsChecked : Prop) :=
  ay_lbcg_Conj allComplementaryResolventsChecked
    (resolventTranscript -> resolventAccepted)

def ay_lbcg_DeletedClauseLedger
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_lbcg_Conj deletionCoverage (deletedClauseLedger -> deletionAccepted)

def ay_lbcg_FallbackFullCheckTranscript
    (fullCheckTranscript : Prop) (fullCheckAccepted : Prop)
    (fullCheckCoversClause : Prop) :=
  ay_lbcg_Conj fullCheckCoversClause
    (fullCheckTranscript -> fullCheckAccepted)

def ay_lbcg_ModelReconstructionContext
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop) :=
  ay_lbcg_Sat blockedCnf blockedModel ->
    ay_lbcg_Sat originalCnf originalModel

def ay_lbcg_UnsatReplayContext
    (originalCnf : Prop) (blockedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_lbcg_Replay blockedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_lbcg_ReconstructionReplayContext
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_lbcg_Conj
    (ay_lbcg_ModelReconstructionContext
      blockedCnf originalCnf blockedModel originalModel)
    (ay_lbcg_UnsatReplayContext originalCnf blockedCnf certificate conflict)

def ay_lbcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_lbcg_Conj binaryFingerprint buildReproducible

def ay_lbcg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_lbcg_Conj checkerAccepted
    (ay_lbcg_Conj validatorAccepted validatorVersion)

def ay_lbcg_ArchiveManifest
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop) :=
  ay_lbcg_Conj archiveAppendOnly
    (ay_lbcg_Conj archiveDigest archiveContainsEntry)

def ay_lbcg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_lbcg_Conj baselineAvailable noClaimPath

def ay_lbcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_lbcg_Conj auditAppended auditAppendOnly

def ay_lbcg_BlockingAccelerationContext
    (literalCoversDeletedClause : Prop)
    (allComplementaryResolventsChecked : Prop)
    (fullCheckCoversClause : Prop)
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_lbcg_Conj literalCoversDeletedClause
    (ay_lbcg_Conj allComplementaryResolventsChecked
      (ay_lbcg_Conj fullCheckCoversClause
        (ay_lbcg_ReconstructionReplayContext
          blockedCnf originalCnf blockedModel originalModel certificate conflict)))

def ay_lbcg_AcceptedLiteralBlockingCacheGuard
    (originalCnf : Prop) (blockedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (blockingLiteralWitness : Prop) (literalAccepted : Prop)
    (literalCoversDeletedClause : Prop)
    (resolventTranscript : Prop) (resolventAccepted : Prop)
    (allComplementaryResolventsChecked : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (fullCheckTranscript : Prop) (fullCheckAccepted : Prop)
    (fullCheckCoversClause : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_lbcg_FormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_lbcg_ClauseDatabaseDigest
       databaseDigest databaseAccepted databaseManifest ->
     ay_lbcg_BlockingCacheKeyDigest
       cacheKeyDigest cacheKeyAccepted cacheKeyCurrent ->
     ay_lbcg_BlockingLiteralWitness
       blockingLiteralWitness literalAccepted literalCoversDeletedClause ->
     ay_lbcg_ResolventTautologyTranscript
       resolventTranscript resolventAccepted allComplementaryResolventsChecked ->
     ay_lbcg_DeletedClauseLedger
       deletedClauseLedger deletionAccepted deletionCoverage ->
     ay_lbcg_FallbackFullCheckTranscript
       fullCheckTranscript fullCheckAccepted fullCheckCoversClause ->
     ay_lbcg_ReconstructionReplayContext
       blockedCnf originalCnf blockedModel originalModel certificate conflict ->
     ay_lbcg_Equisat originalCnf blockedCnf ->
     ay_lbcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_lbcg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_lbcg_ArchiveManifest
       archiveDigest archiveAppendOnly archiveContainsEntry ->
     ay_lbcg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_lbcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_lbcg_BlockingCacheGuardFailure
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (formulaMismatch -> result) ->
    (dbMismatch -> result) ->
    (cacheMismatch -> result) ->
    (literalMismatch -> result) ->
    (resolventMismatch -> result) ->
    (deletionMismatch -> result) ->
    (fullCheckMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_lbcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_lbcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_lbcg_Conj currentCnf recompute

def ay_lbcg_DiagnosticBlockingCacheGuard
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :=
  ay_lbcg_Conj
    (ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch)
    (ay_lbcg_Conj
      (ay_lbcg_RecomputeObligation currentCnf recompute)
      (ay_lbcg_NoSemanticClaim diagnostic))

def ay_lbcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_lbcg_Conj exitCode claim

def ay_lbcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_lbcg_Disj
    (ay_lbcg_ExitCodeSound exitCode (ay_lbcg_Sat originalCnf model))
    (ay_lbcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_lbcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_lbcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_lbcg_conj_left
    (left : Prop) (right : Prop) :
    ay_lbcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_lbcg_conj_right
    (left : Prop) (right : Prop) :
    ay_lbcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_lbcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_lbcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_lbcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_lbcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_lbcg_equisat_forward
    (original : Prop) (blocked : Prop) :
    ay_lbcg_Equisat original blocked -> original -> blocked := by
  intro equisat
  exact ay_lbcg_conj_left (original -> blocked) (blocked -> original)
    equisat

theorem ay_lbcg_equisat_backward
    (original : Prop) (blocked : Prop) :
    ay_lbcg_Equisat original blocked -> blocked -> original := by
  intro equisat
  exact ay_lbcg_conj_right (original -> blocked) (blocked -> original)
    equisat

theorem ay_lbcg_cache_key_applies
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop) :
    ay_lbcg_BlockingCacheKeyDigest
      cacheKeyDigest cacheKeyAccepted cacheKeyCurrent ->
    cacheKeyDigest -> ay_lbcg_Conj cacheKeyCurrent cacheKeyAccepted := by
  intro cache hcache
  exact ay_lbcg_conj_intro cacheKeyCurrent cacheKeyAccepted
    (ay_lbcg_conj_left cacheKeyCurrent
      (cacheKeyDigest -> cacheKeyAccepted) cache)
    ((ay_lbcg_conj_right cacheKeyCurrent
      (cacheKeyDigest -> cacheKeyAccepted) cache) hcache)

theorem ay_lbcg_literal_witness_applies
    (blockingLiteralWitness : Prop) (literalAccepted : Prop)
    (literalCoversDeletedClause : Prop) :
    ay_lbcg_BlockingLiteralWitness
      blockingLiteralWitness literalAccepted literalCoversDeletedClause ->
    blockingLiteralWitness ->
    ay_lbcg_Conj literalCoversDeletedClause literalAccepted := by
  intro literal hliteral
  exact ay_lbcg_conj_intro literalCoversDeletedClause literalAccepted
    (ay_lbcg_conj_left literalCoversDeletedClause
      (blockingLiteralWitness -> literalAccepted) literal)
    ((ay_lbcg_conj_right literalCoversDeletedClause
      (blockingLiteralWitness -> literalAccepted) literal) hliteral)

theorem ay_lbcg_resolvent_transcript_applies
    (resolventTranscript : Prop) (resolventAccepted : Prop)
    (allComplementaryResolventsChecked : Prop) :
    ay_lbcg_ResolventTautologyTranscript
      resolventTranscript resolventAccepted allComplementaryResolventsChecked ->
    resolventTranscript ->
    ay_lbcg_Conj allComplementaryResolventsChecked resolventAccepted := by
  intro transcript htranscript
  exact ay_lbcg_conj_intro allComplementaryResolventsChecked resolventAccepted
    (ay_lbcg_conj_left allComplementaryResolventsChecked
      (resolventTranscript -> resolventAccepted) transcript)
    ((ay_lbcg_conj_right allComplementaryResolventsChecked
      (resolventTranscript -> resolventAccepted) transcript) htranscript)

theorem ay_lbcg_deletion_ledger_applies
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_lbcg_DeletedClauseLedger
      deletedClauseLedger deletionAccepted deletionCoverage ->
    deletedClauseLedger -> ay_lbcg_Conj deletionCoverage deletionAccepted := by
  intro deletion hdeletion
  exact ay_lbcg_conj_intro deletionCoverage deletionAccepted
    (ay_lbcg_conj_left deletionCoverage
      (deletedClauseLedger -> deletionAccepted) deletion)
    ((ay_lbcg_conj_right deletionCoverage
      (deletedClauseLedger -> deletionAccepted) deletion) hdeletion)

theorem ay_lbcg_full_check_applies
    (fullCheckTranscript : Prop) (fullCheckAccepted : Prop)
    (fullCheckCoversClause : Prop) :
    ay_lbcg_FallbackFullCheckTranscript
      fullCheckTranscript fullCheckAccepted fullCheckCoversClause ->
    fullCheckTranscript ->
    ay_lbcg_Conj fullCheckCoversClause fullCheckAccepted := by
  intro fullCheck hfullCheck
  exact ay_lbcg_conj_intro fullCheckCoversClause fullCheckAccepted
    (ay_lbcg_conj_left fullCheckCoversClause
      (fullCheckTranscript -> fullCheckAccepted) fullCheck)
    ((ay_lbcg_conj_right fullCheckCoversClause
      (fullCheckTranscript -> fullCheckAccepted) fullCheck) hfullCheck)

theorem ay_lbcg_model_context
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_ModelReconstructionContext
      blockedCnf originalCnf blockedModel originalModel := by
  intro reconstruction
  exact ay_lbcg_conj_left
    (ay_lbcg_ModelReconstructionContext
      blockedCnf originalCnf blockedModel originalModel)
    (ay_lbcg_UnsatReplayContext originalCnf blockedCnf certificate conflict)
    reconstruction

theorem ay_lbcg_replay_context
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_UnsatReplayContext originalCnf blockedCnf certificate conflict := by
  intro reconstruction
  exact ay_lbcg_conj_right
    (ay_lbcg_ModelReconstructionContext
      blockedCnf originalCnf blockedModel originalModel)
    (ay_lbcg_UnsatReplayContext originalCnf blockedCnf certificate conflict)
    reconstruction

theorem ay_lbcg_accepted_equisat
    (originalCnf : Prop) (blockedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (blockingLiteralWitness : Prop) (literalAccepted : Prop)
    (literalCoversDeletedClause : Prop)
    (resolventTranscript : Prop) (resolventAccepted : Prop)
    (allComplementaryResolventsChecked : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (fullCheckTranscript : Prop) (fullCheckAccepted : Prop)
    (fullCheckCoversClause : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_lbcg_AcceptedLiteralBlockingCacheGuard
      originalCnf blockedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest
      cacheKeyDigest cacheKeyAccepted cacheKeyCurrent
      blockingLiteralWitness literalAccepted literalCoversDeletedClause
      resolventTranscript resolventAccepted allComplementaryResolventsChecked
      deletedClauseLedger deletionAccepted deletionCoverage
      fullCheckTranscript fullCheckAccepted fullCheckCoversClause
      blockedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_lbcg_Equisat originalCnf blockedCnf := by
  intro accepted
  exact accepted (ay_lbcg_Equisat originalCnf blockedCnf)
    (fun _fingerprint _database _cache _literal _resolvent _deletion
      _fullCheck _reconstruction equisat _build _validator _archive
      _fallback _audit => equisat)

theorem ay_lbcg_accepted_reconstruction
    (originalCnf : Prop) (blockedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (cacheKeyDigest : Prop) (cacheKeyAccepted : Prop)
    (cacheKeyCurrent : Prop)
    (blockingLiteralWitness : Prop) (literalAccepted : Prop)
    (literalCoversDeletedClause : Prop)
    (resolventTranscript : Prop) (resolventAccepted : Prop)
    (allComplementaryResolventsChecked : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (fullCheckTranscript : Prop) (fullCheckAccepted : Prop)
    (fullCheckCoversClause : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_lbcg_AcceptedLiteralBlockingCacheGuard
      originalCnf blockedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest
      cacheKeyDigest cacheKeyAccepted cacheKeyCurrent
      blockingLiteralWitness literalAccepted literalCoversDeletedClause
      resolventTranscript resolventAccepted allComplementaryResolventsChecked
      deletedClauseLedger deletionAccepted deletionCoverage
      fullCheckTranscript fullCheckAccepted fullCheckCoversClause
      blockedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict)
    (fun _fingerprint _database _cache _literal _resolvent _deletion
      _fullCheck reconstruction _equisat _build _validator _archive
      _fallback _audit => reconstruction)

theorem ay_lbcg_cache_is_acceleration_only
    (literalCoversDeletedClause : Prop)
    (allComplementaryResolventsChecked : Prop)
    (fullCheckCoversClause : Prop)
    (blockedCnf : Prop) (originalCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_lbcg_BlockingAccelerationContext
      literalCoversDeletedClause allComplementaryResolventsChecked
      fullCheckCoversClause blockedCnf originalCnf blockedModel originalModel
      certificate conflict ->
    ay_lbcg_Conj literalCoversDeletedClause
      (ay_lbcg_Conj allComplementaryResolventsChecked fullCheckCoversClause) := by
  intro context
  exact ay_lbcg_conj_intro literalCoversDeletedClause
    (ay_lbcg_Conj allComplementaryResolventsChecked fullCheckCoversClause)
    (ay_lbcg_conj_left literalCoversDeletedClause
      (ay_lbcg_Conj allComplementaryResolventsChecked
        (ay_lbcg_Conj fullCheckCoversClause
          (ay_lbcg_ReconstructionReplayContext
            blockedCnf originalCnf blockedModel originalModel certificate conflict)))
      context)
    (ay_lbcg_conj_intro allComplementaryResolventsChecked fullCheckCoversClause
      (ay_lbcg_conj_left allComplementaryResolventsChecked
        (ay_lbcg_Conj fullCheckCoversClause
          (ay_lbcg_ReconstructionReplayContext
            blockedCnf originalCnf blockedModel originalModel certificate conflict))
        (ay_lbcg_conj_right literalCoversDeletedClause
          (ay_lbcg_Conj allComplementaryResolventsChecked
            (ay_lbcg_Conj fullCheckCoversClause
              (ay_lbcg_ReconstructionReplayContext
                blockedCnf originalCnf blockedModel originalModel
                certificate conflict)))
          context))
      (ay_lbcg_conj_left fullCheckCoversClause
        (ay_lbcg_ReconstructionReplayContext
          blockedCnf originalCnf blockedModel originalModel certificate conflict)
        (ay_lbcg_conj_right allComplementaryResolventsChecked
          (ay_lbcg_Conj fullCheckCoversClause
            (ay_lbcg_ReconstructionReplayContext
              blockedCnf originalCnf blockedModel originalModel certificate conflict))
          (ay_lbcg_conj_right literalCoversDeletedClause
            (ay_lbcg_Conj allComplementaryResolventsChecked
              (ay_lbcg_Conj fullCheckCoversClause
                (ay_lbcg_ReconstructionReplayContext
                  blockedCnf originalCnf blockedModel originalModel
                  certificate conflict)))
            context))))

theorem ay_lbcg_sat_pullback
    (originalCnf : Prop) (blockedCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_Sat blockedCnf blockedModel ->
    ay_lbcg_Sat originalCnf originalModel := by
  intro reconstruction model
  exact (ay_lbcg_model_context blockedCnf originalCnf blockedModel
    originalModel certificate conflict reconstruction) model

theorem ay_lbcg_unsat_pushback
    (originalCnf : Prop) (blockedCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_Replay blockedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruction replay
  exact (ay_lbcg_replay_context blockedCnf originalCnf blockedModel
    originalModel certificate conflict reconstruction) replay

theorem ay_lbcg_public_sat_sound
    (originalCnf : Prop) (blockedCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_ExitCodeSound exitCode (ay_lbcg_Sat blockedCnf blockedModel) ->
    ay_lbcg_ExitCodeSound exitCode (ay_lbcg_Sat originalCnf originalModel) := by
  intro reconstruction publicSat
  exact ay_lbcg_conj_intro exitCode
    (ay_lbcg_Sat originalCnf originalModel)
    (ay_lbcg_conj_left exitCode
      (ay_lbcg_Sat blockedCnf blockedModel) publicSat)
    (ay_lbcg_sat_pullback originalCnf blockedCnf blockedModel originalModel
      certificate conflict reconstruction
      (ay_lbcg_conj_right exitCode
        (ay_lbcg_Sat blockedCnf blockedModel) publicSat))

theorem ay_lbcg_public_unsat_sound
    (originalCnf : Prop) (blockedCnf : Prop)
    (blockedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_lbcg_ReconstructionReplayContext
      blockedCnf originalCnf blockedModel originalModel certificate conflict ->
    ay_lbcg_Replay blockedCnf certificate conflict ->
    ay_lbcg_ExitCodeSound exitCode certificate ->
    ay_lbcg_ExitCodeSound exitCode (originalCnf -> conflict) := by
  intro reconstruction replay publicUnsat
  exact ay_lbcg_conj_intro exitCode (originalCnf -> conflict)
    (ay_lbcg_conj_left exitCode certificate publicUnsat)
    (fun original =>
      ay_lbcg_unsat_pushback originalCnf blockedCnf blockedModel
        originalModel certificate conflict reconstruction replay
        (ay_lbcg_conj_right exitCode certificate publicUnsat) original)

theorem ay_lbcg_failure_formula
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    formulaMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact formula_case mismatch

theorem ay_lbcg_failure_db
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    dbMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact db_case mismatch

theorem ay_lbcg_failure_cache
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    cacheMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact cache_case mismatch

theorem ay_lbcg_failure_literal
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    literalMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact literal_case mismatch

theorem ay_lbcg_failure_resolvent
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    resolventMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact resolvent_case mismatch

theorem ay_lbcg_failure_deletion
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    deletionMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact deletion_case mismatch

theorem ay_lbcg_failure_full_check
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    fullCheckMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case full_case _model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact full_case mismatch

theorem ay_lbcg_failure_model
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    modelMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case model_case _replay_case
    _build_case _validator_case _archive_case _audit_case
  exact model_case mismatch

theorem ay_lbcg_failure_replay
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    replayMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case replay_case
    _build_case _validator_case _archive_case _audit_case
  exact replay_case mismatch

theorem ay_lbcg_failure_build
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    build_case _validator_case _archive_case _audit_case
  exact build_case mismatch

theorem ay_lbcg_failure_validator
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case validator_case _archive_case _audit_case
  exact validator_case mismatch

theorem ay_lbcg_failure_archive
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    archiveMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case archive_case _audit_case
  exact archive_case mismatch

theorem ay_lbcg_failure_audit
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_lbcg_BlockingCacheGuardFailure
      formulaMismatch dbMismatch cacheMismatch literalMismatch resolventMismatch
      deletionMismatch fullCheckMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _cache_case _literal_case
    _resolvent_case _deletion_case _full_case _model_case _replay_case
    _build_case _validator_case _archive_case audit_case
  exact audit_case mismatch

theorem ay_lbcg_diagnostic_no_claim
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_lbcg_DiagnosticBlockingCacheGuard
      currentCnf formulaMismatch dbMismatch cacheMismatch literalMismatch
      resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic ->
    ay_lbcg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_lbcg_conj_right
    (ay_lbcg_RecomputeObligation currentCnf recompute)
    (ay_lbcg_NoSemanticClaim diagnostic)
    (ay_lbcg_conj_right
      (ay_lbcg_BlockingCacheGuardFailure
        formulaMismatch dbMismatch cacheMismatch literalMismatch
        resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
        replayMismatch buildMismatch validatorMismatch archiveMismatch
        auditMismatch)
      (ay_lbcg_Conj
        (ay_lbcg_RecomputeObligation currentCnf recompute)
        (ay_lbcg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_lbcg_diagnostic_recompute
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_lbcg_DiagnosticBlockingCacheGuard
      currentCnf formulaMismatch dbMismatch cacheMismatch literalMismatch
      resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic ->
    ay_lbcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_lbcg_conj_left
    (ay_lbcg_RecomputeObligation currentCnf recompute)
    (ay_lbcg_NoSemanticClaim diagnostic)
    (ay_lbcg_conj_right
      (ay_lbcg_BlockingCacheGuardFailure
        formulaMismatch dbMismatch cacheMismatch literalMismatch
        resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
        replayMismatch buildMismatch validatorMismatch archiveMismatch
        auditMismatch)
      (ay_lbcg_Conj
        (ay_lbcg_RecomputeObligation currentCnf recompute)
        (ay_lbcg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_lbcg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_lbcg_DiagnosticBlockingCacheGuard
      currentCnf formulaMismatch dbMismatch cacheMismatch literalMismatch
      resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic ->
    ay_lbcg_Disj
      (ay_lbcg_NoSemanticClaim diagnostic)
      (ay_lbcg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard
  exact ay_lbcg_disj_left
    (ay_lbcg_NoSemanticClaim diagnostic)
    (ay_lbcg_RecomputeObligation currentCnf recompute)
    (ay_lbcg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
      cacheMismatch literalMismatch resolventMismatch deletionMismatch
      fullCheckMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch archiveMismatch auditMismatch recompute diagnostic
      diagnosticGuard)

theorem ay_lbcg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop) (model : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_lbcg_DiagnosticBlockingCacheGuard
      currentCnf formulaMismatch dbMismatch cacheMismatch literalMismatch
      resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic ->
    ay_lbcg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_lbcg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
    cacheMismatch literalMismatch resolventMismatch deletionMismatch
    fullCheckMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
    archiveMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_lbcg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop) (certificate : Prop) (conflict : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (cacheMismatch : Prop) (literalMismatch : Prop)
    (resolventMismatch : Prop) (deletionMismatch : Prop)
    (fullCheckMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_lbcg_DiagnosticBlockingCacheGuard
      currentCnf formulaMismatch dbMismatch cacheMismatch literalMismatch
      resolventMismatch deletionMismatch fullCheckMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic ->
    ay_lbcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_lbcg_diagnostic_recompute currentCnf formulaMismatch dbMismatch
    cacheMismatch literalMismatch resolventMismatch deletionMismatch
    fullCheckMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
    archiveMismatch auditMismatch recompute diagnostic diagnosticGuard
