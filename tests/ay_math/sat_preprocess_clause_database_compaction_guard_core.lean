-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-database compaction guard soundness.
-- Compaction is data-structure maintenance: it may preserve live clauses,
-- watch references, model reconstruction context, and UNSAT replay context,
-- but it cannot independently justify a public SAT or UNSAT answer.

def ay_cdcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cdcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cdcg_Equisat (original : Prop) (compacted : Prop) :=
  ay_cdcg_Conj (original -> compacted) (compacted -> original)

def ay_cdcg_Sat (cnf : Prop) (model : Prop) :=
  ay_cdcg_Conj cnf model

def ay_cdcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cdcg_FormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_cdcg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_cdcg_DatabaseDigest
    (beforeDigest : Prop) (afterDigest : Prop)
    (digestAccepted : Prop) :=
  ay_cdcg_Conj (beforeDigest -> digestAccepted)
    (afterDigest -> digestAccepted)

def ay_cdcg_DeletionLedger
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_cdcg_Conj deletionCoverage (deletionLedger -> deletionAccepted)

def ay_cdcg_RelocationMapDigest
    (relocationDigest : Prop) (relocationAccepted : Prop)
    (relocationTotal : Prop) :=
  ay_cdcg_Conj relocationTotal (relocationDigest -> relocationAccepted)

def ay_cdcg_LiveClausePreservation
    (liveBefore : Prop) (liveAfter : Prop)
    (livePreserved : Prop) :=
  ay_cdcg_Conj livePreserved (liveBefore -> liveAfter)

def ay_cdcg_WatchlistRewrite
    (watchDigest : Prop) (watchAccepted : Prop)
    (watchReferencesPreserved : Prop) :=
  ay_cdcg_Conj watchReferencesPreserved (watchDigest -> watchAccepted)

def ay_cdcg_ModelReconstructionContext
    (compactedCnf : Prop) (originalCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop) :=
  ay_cdcg_Sat compactedCnf compactedModel ->
    ay_cdcg_Sat originalCnf originalModel

def ay_cdcg_UnsatReplayContext
    (originalCnf : Prop) (compactedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cdcg_Replay compactedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cdcg_ReconstructionContext
    (compactedCnf : Prop) (originalCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cdcg_Conj
    (ay_cdcg_ModelReconstructionContext
      compactedCnf originalCnf compactedModel originalModel)
    (ay_cdcg_UnsatReplayContext originalCnf compactedCnf certificate conflict)

def ay_cdcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cdcg_Conj binaryFingerprint buildReproducible

def ay_cdcg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_cdcg_Conj checkerAccepted
    (ay_cdcg_Conj validatorAccepted validatorVersion)

def ay_cdcg_ArchiveManifest
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop) :=
  ay_cdcg_Conj archiveAppendOnly
    (ay_cdcg_Conj archiveDigest archiveContainsEntry)

def ay_cdcg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_cdcg_Conj baselineAvailable noClaimPath

def ay_cdcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cdcg_Conj auditAppended auditAppendOnly

def ay_cdcg_CompactionMaintenanceContext
    (liveBefore : Prop) (liveAfter : Prop)
    (watchReferencesPreserved : Prop)
    (compactedCnf : Prop) (originalCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cdcg_Conj
    (ay_cdcg_LiveClausePreservation liveBefore liveAfter liveAfter)
    (ay_cdcg_Conj watchReferencesPreserved
      (ay_cdcg_ReconstructionContext
        compactedCnf originalCnf compactedModel originalModel certificate conflict))

def ay_cdcg_AcceptedClauseDatabaseCompactionGuard
    (originalCnf : Prop) (compactedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop) (digestAccepted : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (relocationDigest : Prop) (relocationAccepted : Prop)
    (relocationTotal : Prop)
    (liveBefore : Prop) (liveAfter : Prop) (livePreserved : Prop)
    (watchDigest : Prop) (watchAccepted : Prop)
    (watchReferencesPreserved : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cdcg_FormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_cdcg_DatabaseDigest beforeDigest afterDigest digestAccepted ->
     ay_cdcg_DeletionLedger deletionLedger deletionAccepted deletionCoverage ->
     ay_cdcg_RelocationMapDigest
       relocationDigest relocationAccepted relocationTotal ->
     ay_cdcg_LiveClausePreservation liveBefore liveAfter livePreserved ->
     ay_cdcg_WatchlistRewrite
       watchDigest watchAccepted watchReferencesPreserved ->
     ay_cdcg_ReconstructionContext
       compactedCnf originalCnf compactedModel originalModel certificate conflict ->
     ay_cdcg_Equisat originalCnf compactedCnf ->
     ay_cdcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cdcg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_cdcg_ArchiveManifest
       archiveDigest archiveAppendOnly archiveContainsEntry ->
     ay_cdcg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_cdcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cdcg_CompactionGuardFailure
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (dbMismatch -> result) ->
    (deletionMismatch -> result) ->
    (relocationMismatch -> result) ->
    (liveClauseMismatch -> result) ->
    (watchMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cdcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cdcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cdcg_Conj currentCnf recompute

def ay_cdcg_DiagnosticCompactionGuard
    (currentCnf : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :=
  ay_cdcg_Conj
    (ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch)
    (ay_cdcg_Conj
      (ay_cdcg_RecomputeObligation currentCnf recompute)
      (ay_cdcg_NoSemanticClaim diagnostic))

def ay_cdcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cdcg_Conj exitCode claim

def ay_cdcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cdcg_Disj
    (ay_cdcg_ExitCodeSound exitCode (ay_cdcg_Sat originalCnf model))
    (ay_cdcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cdcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cdcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cdcg_conj_left
    (left : Prop) (right : Prop) :
    ay_cdcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cdcg_conj_right
    (left : Prop) (right : Prop) :
    ay_cdcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cdcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cdcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cdcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cdcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cdcg_equisat_forward
    (original : Prop) (compacted : Prop) :
    ay_cdcg_Equisat original compacted -> original -> compacted := by
  intro equisat
  exact ay_cdcg_conj_left (original -> compacted) (compacted -> original)
    equisat

theorem ay_cdcg_equisat_backward
    (original : Prop) (compacted : Prop) :
    ay_cdcg_Equisat original compacted -> compacted -> original := by
  intro equisat
  exact ay_cdcg_conj_right (original -> compacted) (compacted -> original)
    equisat

theorem ay_cdcg_database_digest_applies
    (beforeDigest : Prop) (afterDigest : Prop) (digestAccepted : Prop) :
    ay_cdcg_DatabaseDigest beforeDigest afterDigest digestAccepted ->
    beforeDigest -> afterDigest -> ay_cdcg_Conj digestAccepted digestAccepted := by
  intro digest hbefore hafter
  exact ay_cdcg_conj_intro digestAccepted digestAccepted
    ((ay_cdcg_conj_left (beforeDigest -> digestAccepted)
      (afterDigest -> digestAccepted) digest) hbefore)
    ((ay_cdcg_conj_right (beforeDigest -> digestAccepted)
      (afterDigest -> digestAccepted) digest) hafter)

theorem ay_cdcg_deletion_ledger_applies
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_cdcg_DeletionLedger deletionLedger deletionAccepted deletionCoverage ->
    deletionLedger -> deletionCoverage := by
  intro ledger _hdeletion
  exact ay_cdcg_conj_left deletionCoverage
    (deletionLedger -> deletionAccepted) ledger

theorem ay_cdcg_relocation_map_applies
    (relocationDigest : Prop) (relocationAccepted : Prop)
    (relocationTotal : Prop) :
    ay_cdcg_RelocationMapDigest
      relocationDigest relocationAccepted relocationTotal ->
    relocationDigest -> ay_cdcg_Conj relocationTotal relocationAccepted := by
  intro relocation hrelocation
  exact ay_cdcg_conj_intro relocationTotal relocationAccepted
    (ay_cdcg_conj_left relocationTotal
      (relocationDigest -> relocationAccepted) relocation)
    ((ay_cdcg_conj_right relocationTotal
      (relocationDigest -> relocationAccepted) relocation) hrelocation)

theorem ay_cdcg_live_clause_preserved
    (liveBefore : Prop) (liveAfter : Prop) (livePreserved : Prop) :
    ay_cdcg_LiveClausePreservation liveBefore liveAfter livePreserved ->
    liveBefore -> liveAfter := by
  intro live hbefore
  exact (ay_cdcg_conj_right livePreserved (liveBefore -> liveAfter) live)
    hbefore

theorem ay_cdcg_watchlist_rewrite_applies
    (watchDigest : Prop) (watchAccepted : Prop)
    (watchReferencesPreserved : Prop) :
    ay_cdcg_WatchlistRewrite
      watchDigest watchAccepted watchReferencesPreserved ->
    watchDigest -> ay_cdcg_Conj watchReferencesPreserved watchAccepted := by
  intro watch hwatch
  exact ay_cdcg_conj_intro watchReferencesPreserved watchAccepted
    (ay_cdcg_conj_left watchReferencesPreserved
      (watchDigest -> watchAccepted) watch)
    ((ay_cdcg_conj_right watchReferencesPreserved
      (watchDigest -> watchAccepted) watch) hwatch)

theorem ay_cdcg_model_context
    (compactedCnf : Prop) (originalCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_ModelReconstructionContext
      compactedCnf originalCnf compactedModel originalModel := by
  intro reconstruction
  exact ay_cdcg_conj_left
    (ay_cdcg_ModelReconstructionContext
      compactedCnf originalCnf compactedModel originalModel)
    (ay_cdcg_UnsatReplayContext originalCnf compactedCnf certificate conflict)
    reconstruction

theorem ay_cdcg_replay_context
    (compactedCnf : Prop) (originalCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_UnsatReplayContext originalCnf compactedCnf certificate conflict := by
  intro reconstruction
  exact ay_cdcg_conj_right
    (ay_cdcg_ModelReconstructionContext
      compactedCnf originalCnf compactedModel originalModel)
    (ay_cdcg_UnsatReplayContext originalCnf compactedCnf certificate conflict)
    reconstruction

theorem ay_cdcg_accepted_equisat
    (originalCnf : Prop) (compactedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop) (digestAccepted : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (relocationDigest : Prop) (relocationAccepted : Prop)
    (relocationTotal : Prop)
    (liveBefore : Prop) (liveAfter : Prop) (livePreserved : Prop)
    (watchDigest : Prop) (watchAccepted : Prop)
    (watchReferencesPreserved : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cdcg_AcceptedClauseDatabaseCompactionGuard
      originalCnf compactedCnf fingerprint fingerprintAccepted fingerprintManifest
      beforeDigest afterDigest digestAccepted
      deletionLedger deletionAccepted deletionCoverage
      relocationDigest relocationAccepted relocationTotal
      liveBefore liveAfter livePreserved
      watchDigest watchAccepted watchReferencesPreserved
      compactedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_cdcg_Equisat originalCnf compactedCnf := by
  intro accepted
  exact accepted (ay_cdcg_Equisat originalCnf compactedCnf)
    (fun _fingerprint _db _deletion _relocation _live _watch
      _reconstruction equisat _build _validator _archive _fallback _audit =>
      equisat)

theorem ay_cdcg_accepted_reconstruction
    (originalCnf : Prop) (compactedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop) (digestAccepted : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (relocationDigest : Prop) (relocationAccepted : Prop)
    (relocationTotal : Prop)
    (liveBefore : Prop) (liveAfter : Prop) (livePreserved : Prop)
    (watchDigest : Prop) (watchAccepted : Prop)
    (watchReferencesPreserved : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cdcg_AcceptedClauseDatabaseCompactionGuard
      originalCnf compactedCnf fingerprint fingerprintAccepted fingerprintManifest
      beforeDigest afterDigest digestAccepted
      deletionLedger deletionAccepted deletionCoverage
      relocationDigest relocationAccepted relocationTotal
      liveBefore liveAfter livePreserved
      watchDigest watchAccepted watchReferencesPreserved
      compactedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict)
    (fun _fingerprint _db _deletion _relocation _live _watch
      reconstruction _equisat _build _validator _archive _fallback _audit =>
      reconstruction)

theorem ay_cdcg_compaction_is_maintenance_only
    (originalCnf : Prop) (compactedCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_Equisat originalCnf compactedCnf ->
    ay_cdcg_Conj
      (ay_cdcg_ModelReconstructionContext
        compactedCnf originalCnf compactedModel originalModel)
      (ay_cdcg_UnsatReplayContext
        originalCnf compactedCnf certificate conflict) := by
  intro reconstruction _equisat
  exact reconstruction

theorem ay_cdcg_sat_pullback
    (originalCnf : Prop) (compactedCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_Sat compactedCnf compactedModel ->
    ay_cdcg_Sat originalCnf originalModel := by
  intro reconstruction model
  exact (ay_cdcg_model_context compactedCnf originalCnf compactedModel
    originalModel certificate conflict reconstruction) model

theorem ay_cdcg_unsat_pushback
    (originalCnf : Prop) (compactedCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_Replay compactedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruction replay
  exact (ay_cdcg_replay_context compactedCnf originalCnf compactedModel
    originalModel certificate conflict reconstruction) replay

theorem ay_cdcg_public_sat_sound
    (originalCnf : Prop) (compactedCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_ExitCodeSound exitCode
      (ay_cdcg_Sat compactedCnf compactedModel) ->
    ay_cdcg_ExitCodeSound exitCode
      (ay_cdcg_Sat originalCnf originalModel) := by
  intro reconstruction publicSat
  exact ay_cdcg_conj_intro exitCode
    (ay_cdcg_Sat originalCnf originalModel)
    (ay_cdcg_conj_left exitCode
      (ay_cdcg_Sat compactedCnf compactedModel) publicSat)
    (ay_cdcg_sat_pullback originalCnf compactedCnf compactedModel
      originalModel certificate conflict reconstruction
      (ay_cdcg_conj_right exitCode
        (ay_cdcg_Sat compactedCnf compactedModel) publicSat))

theorem ay_cdcg_public_unsat_sound
    (originalCnf : Prop) (compactedCnf : Prop)
    (compactedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cdcg_ReconstructionContext
      compactedCnf originalCnf compactedModel originalModel certificate conflict ->
    ay_cdcg_Replay compactedCnf certificate conflict ->
    ay_cdcg_ExitCodeSound exitCode certificate ->
    ay_cdcg_ExitCodeSound exitCode
      (originalCnf -> conflict) := by
  intro reconstruction replay publicUnsat
  exact ay_cdcg_conj_intro exitCode (originalCnf -> conflict)
    (ay_cdcg_conj_left exitCode certificate publicUnsat)
    (fun original =>
      ay_cdcg_unsat_pushback originalCnf compactedCnf compactedModel
        originalModel certificate conflict reconstruction replay
        (ay_cdcg_conj_right exitCode certificate publicUnsat) original)

theorem ay_cdcg_failure_db
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    dbMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact db_case mismatch

theorem ay_cdcg_failure_deletion
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    deletionMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact deletion_case mismatch

theorem ay_cdcg_failure_relocation
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    relocationMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case relocation_case _live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact relocation_case mismatch

theorem ay_cdcg_failure_live_clause
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    liveClauseMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact live_case mismatch

theorem ay_cdcg_failure_watch
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    watchMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    watch_case _model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact watch_case mismatch

theorem ay_cdcg_failure_model
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    modelMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case model_case _replay_case _build_case _validator_case
    _archive_case _audit_case
  exact model_case mismatch

theorem ay_cdcg_failure_replay
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    replayMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case replay_case _build_case _validator_case
    _archive_case _audit_case
  exact replay_case mismatch

theorem ay_cdcg_failure_build
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case build_case _validator_case
    _archive_case _audit_case
  exact build_case mismatch

theorem ay_cdcg_failure_validator
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case _build_case validator_case
    _archive_case _audit_case
  exact validator_case mismatch

theorem ay_cdcg_failure_archive
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    archiveMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    archive_case _audit_case
  exact archive_case mismatch

theorem ay_cdcg_failure_audit
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_cdcg_CompactionGuardFailure
      dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch := by
  intro mismatch result _db_case _deletion_case _relocation_case _live_case
    _watch_case _model_case _replay_case _build_case _validator_case
    _archive_case audit_case
  exact audit_case mismatch

theorem ay_cdcg_diagnostic_no_claim
    (currentCnf : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticCompactionGuard
      currentCnf dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_cdcg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_cdcg_conj_right
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_conj_right
      (ay_cdcg_CompactionGuardFailure
        dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
        watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
        archiveMismatch auditMismatch)
      (ay_cdcg_Conj
        (ay_cdcg_RecomputeObligation currentCnf recompute)
        (ay_cdcg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cdcg_diagnostic_recompute
    (currentCnf : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticCompactionGuard
      currentCnf dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_cdcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_cdcg_conj_left
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_conj_right
      (ay_cdcg_CompactionGuardFailure
        dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
        watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
        archiveMismatch auditMismatch)
      (ay_cdcg_Conj
        (ay_cdcg_RecomputeObligation currentCnf recompute)
        (ay_cdcg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cdcg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticCompactionGuard
      currentCnf dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_cdcg_Disj
      (ay_cdcg_NoSemanticClaim diagnostic)
      (ay_cdcg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard
  exact ay_cdcg_disj_left
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_diagnostic_no_claim currentCnf dbMismatch deletionMismatch
      relocationMismatch liveClauseMismatch watchMismatch modelMismatch
      replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic diagnosticGuard)

theorem ay_cdcg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop) (model : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticCompactionGuard
      currentCnf dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_cdcg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_cdcg_diagnostic_no_claim currentCnf dbMismatch deletionMismatch
    relocationMismatch liveClauseMismatch watchMismatch modelMismatch
    replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch
    recompute diagnostic diagnosticGuard

theorem ay_cdcg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop) (certificate : Prop) (conflict : Prop)
    (dbMismatch : Prop) (deletionMismatch : Prop)
    (relocationMismatch : Prop) (liveClauseMismatch : Prop)
    (watchMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticCompactionGuard
      currentCnf dbMismatch deletionMismatch relocationMismatch liveClauseMismatch
      watchMismatch modelMismatch replayMismatch buildMismatch validatorMismatch
      archiveMismatch auditMismatch recompute diagnostic ->
    ay_cdcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_cdcg_diagnostic_recompute currentCnf dbMismatch deletionMismatch
    relocationMismatch liveClauseMismatch watchMismatch modelMismatch
    replayMismatch buildMismatch validatorMismatch archiveMismatch auditMismatch
    recompute diagnostic diagnosticGuard
