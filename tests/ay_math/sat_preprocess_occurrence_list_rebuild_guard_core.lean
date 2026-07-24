-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Occurrence-list rebuild guard soundness.
-- Rebuilding occurrence lists is indexing/data-structure maintenance only. It
-- can preserve exact formula, clause membership, live-clause, and fallback
-- scan context for later preprocessing, but cannot independently justify SAT
-- or UNSAT publication.

def ay_olrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_olrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_olrg_Equisat (original : Prop) (maintained : Prop) :=
  ay_olrg_Conj (original -> maintained) (maintained -> original)

def ay_olrg_Sat (cnf : Prop) (model : Prop) :=
  ay_olrg_Conj cnf model

def ay_olrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_olrg_FormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_olrg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_olrg_ClauseDatabaseDigest
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop) :=
  ay_olrg_Conj databaseManifest (databaseDigest -> databaseAccepted)

def ay_olrg_OccurrenceListDigests
    (beforeDigest : Prop) (afterDigest : Prop)
    (occurrenceAccepted : Prop) :=
  ay_olrg_Conj (beforeDigest -> occurrenceAccepted)
    (afterDigest -> occurrenceAccepted)

def ay_olrg_RebuildPolicyManifest
    (policyManifest : Prop) (policyAccepted : Prop)
    (policyDeterministic : Prop) :=
  ay_olrg_Conj policyDeterministic (policyManifest -> policyAccepted)

def ay_olrg_LiteralClauseMembershipWitness
    (membershipWitness : Prop) (membershipAccepted : Prop)
    (membershipCoverage : Prop) :=
  ay_olrg_Conj membershipCoverage (membershipWitness -> membershipAccepted)

def ay_olrg_DeletedLiveClauseLedger
    (liveLedger : Prop) (liveLedgerAccepted : Prop)
    (liveLedgerCoverage : Prop) :=
  ay_olrg_Conj liveLedgerCoverage (liveLedger -> liveLedgerAccepted)

def ay_olrg_SimplificationPhaseDigest
    (phaseDigest : Prop) (phaseAccepted : Prop)
    (phaseManifest : Prop) :=
  ay_olrg_Conj phaseManifest (phaseDigest -> phaseAccepted)

def ay_olrg_FallbackScanTranscript
    (scanTranscript : Prop) (scanAccepted : Prop)
    (scanCoversFormula : Prop) :=
  ay_olrg_Conj scanCoversFormula (scanTranscript -> scanAccepted)

def ay_olrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_olrg_Conj binaryFingerprint buildReproducible

def ay_olrg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_olrg_Conj checkerAccepted
    (ay_olrg_Conj validatorAccepted validatorVersion)

def ay_olrg_ArchiveManifest
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop) :=
  ay_olrg_Conj archiveAppendOnly
    (ay_olrg_Conj archiveDigest archiveContainsEntry)

def ay_olrg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_olrg_Conj baselineAvailable noClaimPath

def ay_olrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_olrg_Conj auditAppended auditAppendOnly

def ay_olrg_ModelContext
    (maintainedCnf : Prop) (originalCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop) :=
  ay_olrg_Sat maintainedCnf maintainedModel ->
    ay_olrg_Sat originalCnf originalModel

def ay_olrg_UnsatReplayContext
    (originalCnf : Prop) (maintainedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_olrg_Replay maintainedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_olrg_ReconstructionContext
    (maintainedCnf : Prop) (originalCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_olrg_Conj
    (ay_olrg_ModelContext
      maintainedCnf originalCnf maintainedModel originalModel)
    (ay_olrg_UnsatReplayContext originalCnf maintainedCnf certificate conflict)

def ay_olrg_IndexMaintenanceContext
    (membershipCoverage : Prop) (liveLedgerCoverage : Prop)
    (scanCoversFormula : Prop)
    (maintainedCnf : Prop) (originalCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_olrg_Conj membershipCoverage
    (ay_olrg_Conj liveLedgerCoverage
      (ay_olrg_Conj scanCoversFormula
        (ay_olrg_ReconstructionContext
          maintainedCnf originalCnf maintainedModel originalModel
          certificate conflict)))

def ay_olrg_AcceptedOccurrenceListRebuildGuard
    (originalCnf : Prop) (maintainedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop)
    (occurrenceAccepted : Prop)
    (policyManifest : Prop) (policyAccepted : Prop)
    (policyDeterministic : Prop)
    (membershipWitness : Prop) (membershipAccepted : Prop)
    (membershipCoverage : Prop)
    (liveLedger : Prop) (liveLedgerAccepted : Prop)
    (liveLedgerCoverage : Prop)
    (phaseDigest : Prop) (phaseAccepted : Prop)
    (phaseManifest : Prop)
    (scanTranscript : Prop) (scanAccepted : Prop)
    (scanCoversFormula : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_olrg_FormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_olrg_ClauseDatabaseDigest
       databaseDigest databaseAccepted databaseManifest ->
     ay_olrg_OccurrenceListDigests
       beforeDigest afterDigest occurrenceAccepted ->
     ay_olrg_RebuildPolicyManifest
       policyManifest policyAccepted policyDeterministic ->
     ay_olrg_LiteralClauseMembershipWitness
       membershipWitness membershipAccepted membershipCoverage ->
     ay_olrg_DeletedLiveClauseLedger
       liveLedger liveLedgerAccepted liveLedgerCoverage ->
     ay_olrg_SimplificationPhaseDigest
       phaseDigest phaseAccepted phaseManifest ->
     ay_olrg_FallbackScanTranscript
       scanTranscript scanAccepted scanCoversFormula ->
     ay_olrg_ReconstructionContext
       maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
     ay_olrg_Equisat originalCnf maintainedCnf ->
     ay_olrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_olrg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_olrg_ArchiveManifest
       archiveDigest archiveAppendOnly archiveContainsEntry ->
     ay_olrg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_olrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_olrg_OccurrenceListGuardFailure
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (formulaMismatch -> result) ->
    (dbMismatch -> result) ->
    (occurrenceMismatch -> result) ->
    (policyMismatch -> result) ->
    (membershipMismatch -> result) ->
    (liveLedgerMismatch -> result) ->
    (phaseMismatch -> result) ->
    (scanMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_olrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_olrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_olrg_Conj currentCnf recompute

def ay_olrg_DiagnosticOccurrenceListGuard
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_olrg_Conj
    (ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch)
    (ay_olrg_Conj
      (ay_olrg_RecomputeObligation currentCnf recompute)
      (ay_olrg_NoSemanticClaim diagnostic))

def ay_olrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_olrg_Conj exitCode claim

def ay_olrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_olrg_Disj
    (ay_olrg_ExitCodeSound exitCode (ay_olrg_Sat originalCnf model))
    (ay_olrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_olrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_olrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_olrg_conj_left
    (left : Prop) (right : Prop) :
    ay_olrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_olrg_conj_right
    (left : Prop) (right : Prop) :
    ay_olrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_olrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_olrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_olrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_olrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_olrg_equisat_forward
    (original : Prop) (maintained : Prop) :
    ay_olrg_Equisat original maintained -> original -> maintained := by
  intro equisat
  exact ay_olrg_conj_left (original -> maintained) (maintained -> original)
    equisat

theorem ay_olrg_equisat_backward
    (original : Prop) (maintained : Prop) :
    ay_olrg_Equisat original maintained -> maintained -> original := by
  intro equisat
  exact ay_olrg_conj_right (original -> maintained) (maintained -> original)
    equisat

theorem ay_olrg_occurrence_digests_apply
    (beforeDigest : Prop) (afterDigest : Prop)
    (occurrenceAccepted : Prop) :
    ay_olrg_OccurrenceListDigests
      beforeDigest afterDigest occurrenceAccepted ->
    beforeDigest -> afterDigest ->
    ay_olrg_Conj occurrenceAccepted occurrenceAccepted := by
  intro digests hbefore hafter
  exact ay_olrg_conj_intro occurrenceAccepted occurrenceAccepted
    ((ay_olrg_conj_left (beforeDigest -> occurrenceAccepted)
      (afterDigest -> occurrenceAccepted) digests) hbefore)
    ((ay_olrg_conj_right (beforeDigest -> occurrenceAccepted)
      (afterDigest -> occurrenceAccepted) digests) hafter)

theorem ay_olrg_policy_manifest_applies
    (policyManifest : Prop) (policyAccepted : Prop)
    (policyDeterministic : Prop) :
    ay_olrg_RebuildPolicyManifest
      policyManifest policyAccepted policyDeterministic ->
    policyManifest -> ay_olrg_Conj policyDeterministic policyAccepted := by
  intro policy hpolicy
  exact ay_olrg_conj_intro policyDeterministic policyAccepted
    (ay_olrg_conj_left policyDeterministic
      (policyManifest -> policyAccepted) policy)
    ((ay_olrg_conj_right policyDeterministic
      (policyManifest -> policyAccepted) policy) hpolicy)

theorem ay_olrg_membership_witness_applies
    (membershipWitness : Prop) (membershipAccepted : Prop)
    (membershipCoverage : Prop) :
    ay_olrg_LiteralClauseMembershipWitness
      membershipWitness membershipAccepted membershipCoverage ->
    membershipWitness -> ay_olrg_Conj membershipCoverage membershipAccepted := by
  intro membership hmembership
  exact ay_olrg_conj_intro membershipCoverage membershipAccepted
    (ay_olrg_conj_left membershipCoverage
      (membershipWitness -> membershipAccepted) membership)
    ((ay_olrg_conj_right membershipCoverage
      (membershipWitness -> membershipAccepted) membership) hmembership)

theorem ay_olrg_live_ledger_applies
    (liveLedger : Prop) (liveLedgerAccepted : Prop)
    (liveLedgerCoverage : Prop) :
    ay_olrg_DeletedLiveClauseLedger
      liveLedger liveLedgerAccepted liveLedgerCoverage ->
    liveLedger -> ay_olrg_Conj liveLedgerCoverage liveLedgerAccepted := by
  intro ledger hledger
  exact ay_olrg_conj_intro liveLedgerCoverage liveLedgerAccepted
    (ay_olrg_conj_left liveLedgerCoverage
      (liveLedger -> liveLedgerAccepted) ledger)
    ((ay_olrg_conj_right liveLedgerCoverage
      (liveLedger -> liveLedgerAccepted) ledger) hledger)

theorem ay_olrg_phase_digest_applies
    (phaseDigest : Prop) (phaseAccepted : Prop)
    (phaseManifest : Prop) :
    ay_olrg_SimplificationPhaseDigest
      phaseDigest phaseAccepted phaseManifest ->
    phaseDigest -> ay_olrg_Conj phaseManifest phaseAccepted := by
  intro phase hphase
  exact ay_olrg_conj_intro phaseManifest phaseAccepted
    (ay_olrg_conj_left phaseManifest
      (phaseDigest -> phaseAccepted) phase)
    ((ay_olrg_conj_right phaseManifest
      (phaseDigest -> phaseAccepted) phase) hphase)

theorem ay_olrg_fallback_scan_applies
    (scanTranscript : Prop) (scanAccepted : Prop)
    (scanCoversFormula : Prop) :
    ay_olrg_FallbackScanTranscript
      scanTranscript scanAccepted scanCoversFormula ->
    scanTranscript -> ay_olrg_Conj scanCoversFormula scanAccepted := by
  intro scan hscan
  exact ay_olrg_conj_intro scanCoversFormula scanAccepted
    (ay_olrg_conj_left scanCoversFormula
      (scanTranscript -> scanAccepted) scan)
    ((ay_olrg_conj_right scanCoversFormula
      (scanTranscript -> scanAccepted) scan) hscan)

theorem ay_olrg_model_context
    (maintainedCnf : Prop) (originalCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_ModelContext
      maintainedCnf originalCnf maintainedModel originalModel := by
  intro reconstruction
  exact ay_olrg_conj_left
    (ay_olrg_ModelContext
      maintainedCnf originalCnf maintainedModel originalModel)
    (ay_olrg_UnsatReplayContext originalCnf maintainedCnf certificate conflict)
    reconstruction

theorem ay_olrg_replay_context
    (maintainedCnf : Prop) (originalCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_UnsatReplayContext originalCnf maintainedCnf certificate conflict := by
  intro reconstruction
  exact ay_olrg_conj_right
    (ay_olrg_ModelContext
      maintainedCnf originalCnf maintainedModel originalModel)
    (ay_olrg_UnsatReplayContext originalCnf maintainedCnf certificate conflict)
    reconstruction

theorem ay_olrg_accepted_equisat
    (originalCnf : Prop) (maintainedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop)
    (occurrenceAccepted : Prop)
    (policyManifest : Prop) (policyAccepted : Prop)
    (policyDeterministic : Prop)
    (membershipWitness : Prop) (membershipAccepted : Prop)
    (membershipCoverage : Prop)
    (liveLedger : Prop) (liveLedgerAccepted : Prop)
    (liveLedgerCoverage : Prop)
    (phaseDigest : Prop) (phaseAccepted : Prop)
    (phaseManifest : Prop)
    (scanTranscript : Prop) (scanAccepted : Prop)
    (scanCoversFormula : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_olrg_AcceptedOccurrenceListRebuildGuard
      originalCnf maintainedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest
      beforeDigest afterDigest occurrenceAccepted
      policyManifest policyAccepted policyDeterministic
      membershipWitness membershipAccepted membershipCoverage
      liveLedger liveLedgerAccepted liveLedgerCoverage
      phaseDigest phaseAccepted phaseManifest
      scanTranscript scanAccepted scanCoversFormula
      maintainedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_olrg_Equisat originalCnf maintainedCnf := by
  intro accepted
  exact accepted (ay_olrg_Equisat originalCnf maintainedCnf)
    (fun _fingerprint _database _occurrence _policy _membership _live
      _phase _scan _reconstruction equisat _build _validator _archive
      _fallback _audit => equisat)

theorem ay_olrg_accepted_reconstruction
    (originalCnf : Prop) (maintainedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (databaseDigest : Prop) (databaseAccepted : Prop)
    (databaseManifest : Prop)
    (beforeDigest : Prop) (afterDigest : Prop)
    (occurrenceAccepted : Prop)
    (policyManifest : Prop) (policyAccepted : Prop)
    (policyDeterministic : Prop)
    (membershipWitness : Prop) (membershipAccepted : Prop)
    (membershipCoverage : Prop)
    (liveLedger : Prop) (liveLedgerAccepted : Prop)
    (liveLedgerCoverage : Prop)
    (phaseDigest : Prop) (phaseAccepted : Prop)
    (phaseManifest : Prop)
    (scanTranscript : Prop) (scanAccepted : Prop)
    (scanCoversFormula : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (archiveDigest : Prop) (archiveAppendOnly : Prop)
    (archiveContainsEntry : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_olrg_AcceptedOccurrenceListRebuildGuard
      originalCnf maintainedCnf fingerprint fingerprintAccepted fingerprintManifest
      databaseDigest databaseAccepted databaseManifest
      beforeDigest afterDigest occurrenceAccepted
      policyManifest policyAccepted policyDeterministic
      membershipWitness membershipAccepted membershipCoverage
      liveLedger liveLedgerAccepted liveLedgerCoverage
      phaseDigest phaseAccepted phaseManifest
      scanTranscript scanAccepted scanCoversFormula
      maintainedModel originalModel certificate conflict
      binaryFingerprint buildReproducible checkerAccepted validatorAccepted
      validatorVersion archiveDigest archiveAppendOnly archiveContainsEntry
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict)
    (fun _fingerprint _database _occurrence _policy _membership _live
      _phase _scan reconstruction _equisat _build _validator _archive
      _fallback _audit => reconstruction)

theorem ay_olrg_rebuild_is_maintenance_only
    (originalCnf : Prop) (maintainedCnf : Prop)
    (membershipCoverage : Prop) (liveLedgerCoverage : Prop)
    (scanCoversFormula : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_olrg_IndexMaintenanceContext
      membershipCoverage liveLedgerCoverage scanCoversFormula
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_Conj membershipCoverage
      (ay_olrg_Conj liveLedgerCoverage scanCoversFormula) := by
  intro maintenance
  exact ay_olrg_conj_intro membershipCoverage
    (ay_olrg_Conj liveLedgerCoverage scanCoversFormula)
    (ay_olrg_conj_left membershipCoverage
      (ay_olrg_Conj liveLedgerCoverage
        (ay_olrg_Conj scanCoversFormula
          (ay_olrg_ReconstructionContext
            maintainedCnf originalCnf maintainedModel originalModel
            certificate conflict)))
      maintenance)
    (ay_olrg_conj_intro liveLedgerCoverage scanCoversFormula
      (ay_olrg_conj_left liveLedgerCoverage
        (ay_olrg_Conj scanCoversFormula
          (ay_olrg_ReconstructionContext
            maintainedCnf originalCnf maintainedModel originalModel
            certificate conflict))
        (ay_olrg_conj_right membershipCoverage
          (ay_olrg_Conj liveLedgerCoverage
            (ay_olrg_Conj scanCoversFormula
              (ay_olrg_ReconstructionContext
                maintainedCnf originalCnf maintainedModel originalModel
                certificate conflict)))
          maintenance))
      (ay_olrg_conj_left scanCoversFormula
        (ay_olrg_ReconstructionContext
          maintainedCnf originalCnf maintainedModel originalModel certificate conflict)
        (ay_olrg_conj_right liveLedgerCoverage
          (ay_olrg_Conj scanCoversFormula
            (ay_olrg_ReconstructionContext
              maintainedCnf originalCnf maintainedModel originalModel
              certificate conflict))
          (ay_olrg_conj_right membershipCoverage
            (ay_olrg_Conj liveLedgerCoverage
              (ay_olrg_Conj scanCoversFormula
                (ay_olrg_ReconstructionContext
                  maintainedCnf originalCnf maintainedModel originalModel
                  certificate conflict)))
            maintenance))))

theorem ay_olrg_sat_pullback
    (originalCnf : Prop) (maintainedCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_Sat maintainedCnf maintainedModel ->
    ay_olrg_Sat originalCnf originalModel := by
  intro reconstruction model
  exact (ay_olrg_model_context maintainedCnf originalCnf maintainedModel
    originalModel certificate conflict reconstruction) model

theorem ay_olrg_unsat_pushback
    (originalCnf : Prop) (maintainedCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_Replay maintainedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruction replay
  exact (ay_olrg_replay_context maintainedCnf originalCnf maintainedModel
    originalModel certificate conflict reconstruction) replay

theorem ay_olrg_public_sat_sound
    (originalCnf : Prop) (maintainedCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_ExitCodeSound exitCode
      (ay_olrg_Sat maintainedCnf maintainedModel) ->
    ay_olrg_ExitCodeSound exitCode
      (ay_olrg_Sat originalCnf originalModel) := by
  intro reconstruction publicSat
  exact ay_olrg_conj_intro exitCode
    (ay_olrg_Sat originalCnf originalModel)
    (ay_olrg_conj_left exitCode
      (ay_olrg_Sat maintainedCnf maintainedModel) publicSat)
    (ay_olrg_sat_pullback originalCnf maintainedCnf maintainedModel
      originalModel certificate conflict reconstruction
      (ay_olrg_conj_right exitCode
        (ay_olrg_Sat maintainedCnf maintainedModel) publicSat))

theorem ay_olrg_public_unsat_sound
    (originalCnf : Prop) (maintainedCnf : Prop)
    (maintainedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_olrg_ReconstructionContext
      maintainedCnf originalCnf maintainedModel originalModel certificate conflict ->
    ay_olrg_Replay maintainedCnf certificate conflict ->
    ay_olrg_ExitCodeSound exitCode certificate ->
    ay_olrg_ExitCodeSound exitCode
      (originalCnf -> conflict) := by
  intro reconstruction replay publicUnsat
  exact ay_olrg_conj_intro exitCode (originalCnf -> conflict)
    (ay_olrg_conj_left exitCode certificate publicUnsat)
    (fun original =>
      ay_olrg_unsat_pushback originalCnf maintainedCnf maintainedModel
        originalModel certificate conflict reconstruction replay
        (ay_olrg_conj_right exitCode certificate publicUnsat) original)

theorem ay_olrg_failure_formula
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    formulaMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact formula_case mismatch

theorem ay_olrg_failure_db
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    dbMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact db_case mismatch

theorem ay_olrg_failure_occurrence
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    occurrenceMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact occurrence_case mismatch

theorem ay_olrg_failure_policy
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    policyMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact policy_case mismatch

theorem ay_olrg_failure_membership
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    membershipMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact membership_case mismatch

theorem ay_olrg_failure_live_ledger
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    liveLedgerMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case live_case _phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact live_case mismatch

theorem ay_olrg_failure_phase
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    phaseMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case phase_case _scan_case _build_case
    _validator_case _archive_case _audit_case
  exact phase_case mismatch

theorem ay_olrg_failure_scan
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    scanMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case scan_case _build_case
    _validator_case _archive_case _audit_case
  exact scan_case mismatch

theorem ay_olrg_failure_build
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    buildMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case build_case
    _validator_case _archive_case _audit_case
  exact build_case mismatch

theorem ay_olrg_failure_validator
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    validatorMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    validator_case _archive_case _audit_case
  exact validator_case mismatch

theorem ay_olrg_failure_archive
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    archiveMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case archive_case _audit_case
  exact archive_case mismatch

theorem ay_olrg_failure_audit
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :
    auditMismatch ->
    ay_olrg_OccurrenceListGuardFailure
      formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch := by
  intro mismatch result _formula_case _db_case _occurrence_case _policy_case
    _membership_case _live_case _phase_case _scan_case _build_case
    _validator_case _archive_case audit_case
  exact audit_case mismatch

theorem ay_olrg_diagnostic_no_claim
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_olrg_DiagnosticOccurrenceListGuard
      currentCnf formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic ->
    ay_olrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_olrg_conj_right
    (ay_olrg_RecomputeObligation currentCnf recompute)
    (ay_olrg_NoSemanticClaim diagnostic)
    (ay_olrg_conj_right
      (ay_olrg_OccurrenceListGuardFailure
        formulaMismatch dbMismatch occurrenceMismatch policyMismatch
        membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
        buildMismatch validatorMismatch archiveMismatch auditMismatch)
      (ay_olrg_Conj
        (ay_olrg_RecomputeObligation currentCnf recompute)
        (ay_olrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_olrg_diagnostic_recompute
    (currentCnf : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_olrg_DiagnosticOccurrenceListGuard
      currentCnf formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic ->
    ay_olrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_olrg_conj_left
    (ay_olrg_RecomputeObligation currentCnf recompute)
    (ay_olrg_NoSemanticClaim diagnostic)
    (ay_olrg_conj_right
      (ay_olrg_OccurrenceListGuardFailure
        formulaMismatch dbMismatch occurrenceMismatch policyMismatch
        membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
        buildMismatch validatorMismatch archiveMismatch auditMismatch)
      (ay_olrg_Conj
        (ay_olrg_RecomputeObligation currentCnf recompute)
        (ay_olrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_olrg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_olrg_DiagnosticOccurrenceListGuard
      currentCnf formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic ->
    ay_olrg_Disj
      (ay_olrg_NoSemanticClaim diagnostic)
      (ay_olrg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard
  exact ay_olrg_disj_left
    (ay_olrg_NoSemanticClaim diagnostic)
    (ay_olrg_RecomputeObligation currentCnf recompute)
    (ay_olrg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
      occurrenceMismatch policyMismatch membershipMismatch liveLedgerMismatch
      phaseMismatch scanMismatch buildMismatch validatorMismatch archiveMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_olrg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop) (model : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_olrg_DiagnosticOccurrenceListGuard
      currentCnf formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic ->
    ay_olrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_olrg_diagnostic_no_claim currentCnf formulaMismatch dbMismatch
    occurrenceMismatch policyMismatch membershipMismatch liveLedgerMismatch
    phaseMismatch scanMismatch buildMismatch validatorMismatch archiveMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_olrg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop) (certificate : Prop) (conflict : Prop)
    (formulaMismatch : Prop) (dbMismatch : Prop)
    (occurrenceMismatch : Prop) (policyMismatch : Prop)
    (membershipMismatch : Prop) (liveLedgerMismatch : Prop)
    (phaseMismatch : Prop) (scanMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_olrg_DiagnosticOccurrenceListGuard
      currentCnf formulaMismatch dbMismatch occurrenceMismatch policyMismatch
      membershipMismatch liveLedgerMismatch phaseMismatch scanMismatch
      buildMismatch validatorMismatch archiveMismatch auditMismatch
      recompute diagnostic ->
    ay_olrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_olrg_diagnostic_recompute currentCnf formulaMismatch dbMismatch
    occurrenceMismatch policyMismatch membershipMismatch liveLedgerMismatch
    phaseMismatch scanMismatch buildMismatch validatorMismatch archiveMismatch
    auditMismatch recompute diagnostic diagnosticGuard
