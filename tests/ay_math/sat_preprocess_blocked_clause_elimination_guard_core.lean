-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause-elimination preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, blocked-clause
-- ledgers, blocking literal witnesses, complementary resolvent tautology
-- witnesses, deletion certificate digests, preserved-clause maps, SAT model
-- extension, UNSAT replay/equisat evidence, build/checker/validator gates,
-- fallback no-claim paths, audit transcripts, and public SAT/UNSAT reports.

def ay_bceg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bceg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bceg_Equisat (original : Prop) (reduced : Prop) :=
  ay_bceg_Conj (original -> reduced) (reduced -> original)

def ay_bceg_Sat (cnf : Prop) (model : Prop) :=
  ay_bceg_Conj cnf model

def ay_bceg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bceg_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_bceg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_bceg_BlockedClauseLedger
    (blockedClauseLedger : Prop) (blockedLedgerAccepted : Prop)
    (blockedLedgerCoverage : Prop) :=
  ay_bceg_Conj blockedLedgerCoverage
    (blockedClauseLedger -> blockedLedgerAccepted)

def ay_bceg_BlockedLiteralWitness
    (blockedLiteralWitness : Prop) (blockedLiteralAccepted : Prop)
    (blockedLiteralCoverage : Prop) :=
  ay_bceg_Conj blockedLiteralCoverage
    (blockedLiteralWitness -> blockedLiteralAccepted)

def ay_bceg_ComplementaryResolventTautologyWitness
    (resolventTautologyWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :=
  ay_bceg_Conj resolventCoverage
    (resolventTautologyWitness -> resolventAccepted)

def ay_bceg_DeletionCertificateDigest
    (deletionCertificateDigest : Prop) (deletionDigestAccepted : Prop)
    (deletionDigestManifest : Prop) :=
  ay_bceg_Conj deletionDigestManifest
    (deletionCertificateDigest -> deletionDigestAccepted)

def ay_bceg_PreservedClauseMap
    (preservedClauseMap : Prop) (preservedMapAccepted : Prop)
    (preservedMapCoverage : Prop) :=
  ay_bceg_Conj preservedMapCoverage
    (preservedClauseMap -> preservedMapAccepted)

def ay_bceg_CheckerValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_bceg_Conj checkerAccepted
    (ay_bceg_Conj validatorAccepted validatorVersion)

def ay_bceg_ModelExtensionMap
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_bceg_Sat reducedCnf reducedModel ->
    ay_bceg_Sat originalCnf originalModel

def ay_bceg_UnsatReplayEvidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bceg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bceg_ReconstructionEvidence
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bceg_Conj
    (ay_bceg_ModelExtensionMap
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bceg_UnsatReplayEvidence
      originalCnf reducedCnf certificate conflict)

def ay_bceg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bceg_Conj binaryFingerprint buildReproducible

def ay_bceg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_bceg_Conj baselineAvailable noClaimPath

def ay_bceg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bceg_Conj auditAppended auditAppendOnly

def ay_bceg_AcceptedBlockedClauseEliminationGuard
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (blockedClauseLedger : Prop) (blockedLedgerAccepted : Prop)
    (blockedLedgerCoverage : Prop)
    (blockedLiteralWitness : Prop) (blockedLiteralAccepted : Prop)
    (blockedLiteralCoverage : Prop)
    (resolventTautologyWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (deletionCertificateDigest : Prop) (deletionDigestAccepted : Prop)
    (deletionDigestManifest : Prop)
    (preservedClauseMap : Prop) (preservedMapAccepted : Prop)
    (preservedMapCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bceg_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_bceg_BlockedClauseLedger
       blockedClauseLedger blockedLedgerAccepted blockedLedgerCoverage ->
     ay_bceg_BlockedLiteralWitness
       blockedLiteralWitness blockedLiteralAccepted blockedLiteralCoverage ->
     ay_bceg_ComplementaryResolventTautologyWitness
       resolventTautologyWitness resolventAccepted resolventCoverage ->
     ay_bceg_DeletionCertificateDigest
       deletionCertificateDigest deletionDigestAccepted deletionDigestManifest ->
     ay_bceg_PreservedClauseMap
       preservedClauseMap preservedMapAccepted preservedMapCoverage ->
     ay_bceg_ReconstructionEvidence
       reducedCnf originalCnf reducedModel originalModel certificate conflict ->
     ay_bceg_Equisat originalCnf reducedCnf ->
     ay_bceg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bceg_CheckerValidatorGate
       checkerAccepted validatorAccepted validatorVersion ->
     ay_bceg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_bceg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bceg_BceGuardFailure
    (ledgerMismatch : Prop) (witnessMismatch : Prop)
    (resolventMismatch : Prop) (modelExtensionMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (checkerMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (ledgerMismatch -> result) ->
    (witnessMismatch -> result) ->
    (resolventMismatch -> result) ->
    (modelExtensionMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (checkerMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_bceg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bceg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bceg_Conj currentCnf recompute

def ay_bceg_DiagnosticBceGuard
    (currentCnf : Prop)
    (ledgerMismatch : Prop) (witnessMismatch : Prop)
    (resolventMismatch : Prop) (modelExtensionMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (checkerMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bceg_Conj
    (ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch)
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
    (original : Prop) (reduced : Prop) :
    ay_bceg_Equisat original reduced -> original -> reduced := by
  intro eqsat
  exact ay_bceg_conj_left (original -> reduced) (reduced -> original) eqsat

theorem ay_bceg_equisat_backward
    (original : Prop) (reduced : Prop) :
    ay_bceg_Equisat original reduced -> reduced -> original := by
  intro eqsat
  exact ay_bceg_conj_right (original -> reduced) (reduced -> original) eqsat

theorem ay_bceg_fingerprint_applies
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :
    ay_bceg_OriginalFormulaFingerprint
      fingerprint fingerprintAccepted fingerprintManifest ->
    fingerprint -> fingerprintAccepted := by
  intro fp
  exact ay_bceg_conj_right
    fingerprintManifest (fingerprint -> fingerprintAccepted) fp

theorem ay_bceg_blocked_clause_ledger_applies
    (blockedClauseLedger : Prop) (blockedLedgerAccepted : Prop)
    (blockedLedgerCoverage : Prop) :
    ay_bceg_BlockedClauseLedger
      blockedClauseLedger blockedLedgerAccepted blockedLedgerCoverage ->
    blockedClauseLedger -> blockedLedgerAccepted := by
  intro ledger
  exact ay_bceg_conj_right
    blockedLedgerCoverage (blockedClauseLedger -> blockedLedgerAccepted) ledger

theorem ay_bceg_blocked_literal_witness_applies
    (blockedLiteralWitness : Prop) (blockedLiteralAccepted : Prop)
    (blockedLiteralCoverage : Prop) :
    ay_bceg_BlockedLiteralWitness
      blockedLiteralWitness blockedLiteralAccepted blockedLiteralCoverage ->
    blockedLiteralWitness -> blockedLiteralAccepted := by
  intro witness
  exact ay_bceg_conj_right
    blockedLiteralCoverage (blockedLiteralWitness -> blockedLiteralAccepted)
    witness

theorem ay_bceg_resolvent_tautology_witness_applies
    (resolventTautologyWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :
    ay_bceg_ComplementaryResolventTautologyWitness
      resolventTautologyWitness resolventAccepted resolventCoverage ->
    resolventTautologyWitness -> resolventAccepted := by
  intro witness
  exact ay_bceg_conj_right
    resolventCoverage (resolventTautologyWitness -> resolventAccepted)
    witness

theorem ay_bceg_deletion_certificate_digest_applies
    (deletionCertificateDigest : Prop) (deletionDigestAccepted : Prop)
    (deletionDigestManifest : Prop) :
    ay_bceg_DeletionCertificateDigest
      deletionCertificateDigest deletionDigestAccepted deletionDigestManifest ->
    deletionCertificateDigest -> deletionDigestAccepted := by
  intro digest
  exact ay_bceg_conj_right
    deletionDigestManifest (deletionCertificateDigest -> deletionDigestAccepted)
    digest

theorem ay_bceg_preserved_clause_map_applies
    (preservedClauseMap : Prop) (preservedMapAccepted : Prop)
    (preservedMapCoverage : Prop) :
    ay_bceg_PreservedClauseMap
      preservedClauseMap preservedMapAccepted preservedMapCoverage ->
    preservedClauseMap -> preservedMapAccepted := by
  intro mapOk
  exact ay_bceg_conj_right
    preservedMapCoverage (preservedClauseMap -> preservedMapAccepted) mapOk

theorem ay_bceg_model_extension
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bceg_Sat reducedCnf reducedModel ->
    ay_bceg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_bceg_conj_left
    (ay_bceg_ModelExtensionMap
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bceg_UnsatReplayEvidence
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bceg_unsat_replay
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bceg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_bceg_conj_right
    (ay_bceg_ModelExtensionMap
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bceg_UnsatReplayEvidence
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bceg_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (blockedClauseLedger : Prop) (blockedLedgerAccepted : Prop)
    (blockedLedgerCoverage : Prop)
    (blockedLiteralWitness : Prop) (blockedLiteralAccepted : Prop)
    (blockedLiteralCoverage : Prop)
    (resolventTautologyWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (deletionCertificateDigest : Prop) (deletionDigestAccepted : Prop)
    (deletionDigestManifest : Prop)
    (preservedClauseMap : Prop) (preservedMapAccepted : Prop)
    (preservedMapCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationGuard
      originalCnf reducedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      blockedClauseLedger blockedLedgerAccepted blockedLedgerCoverage
      blockedLiteralWitness blockedLiteralAccepted blockedLiteralCoverage
      resolventTautologyWitness resolventAccepted resolventCoverage
      deletionCertificateDigest deletionDigestAccepted deletionDigestManifest
      preservedClauseMap preservedMapAccepted preservedMapCoverage
      checkerAccepted validatorAccepted validatorVersion
      reducedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_bceg_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_bceg_Equisat originalCnf reducedCnf)
    (fun _fingerprint _ledger _literal _resolvent _deletion _preserved
      _reconstruct eqsat _build _checker _fallback _audit => eqsat)

theorem ay_bceg_accepted_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (blockedClauseLedger : Prop) (blockedLedgerAccepted : Prop)
    (blockedLedgerCoverage : Prop)
    (blockedLiteralWitness : Prop) (blockedLiteralAccepted : Prop)
    (blockedLiteralCoverage : Prop)
    (resolventTautologyWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (deletionCertificateDigest : Prop) (deletionDigestAccepted : Prop)
    (deletionDigestManifest : Prop)
    (preservedClauseMap : Prop) (preservedMapAccepted : Prop)
    (preservedMapCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bceg_AcceptedBlockedClauseEliminationGuard
      originalCnf reducedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      blockedClauseLedger blockedLedgerAccepted blockedLedgerCoverage
      blockedLiteralWitness blockedLiteralAccepted blockedLiteralCoverage
      resolventTautologyWitness resolventAccepted resolventCoverage
      deletionCertificateDigest deletionDigestAccepted deletionDigestManifest
      preservedClauseMap preservedMapAccepted preservedMapCoverage
      checkerAccepted validatorAccepted validatorVersion
      reducedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict)
    (fun _fingerprint _ledger _literal _resolvent _deletion _preserved
      reconstruct _eqsat _build _checker _fallback _audit => reconstruct)

theorem ay_bceg_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bceg_Sat reducedCnf reducedModel ->
    ay_bceg_Sat originalCnf originalModel := by
  intro witnesses satReduced
  exact ay_bceg_model_extension
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses satReduced

theorem ay_bceg_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bceg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bceg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_bceg_unsat_replay
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses replay

theorem ay_bceg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bceg_ExitCodeSound exitCode (ay_bceg_Sat originalCnf originalModel) ->
    ay_bceg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_bceg_disj_left
    (ay_bceg_ExitCodeSound exitCode (ay_bceg_Sat originalCnf originalModel))
    (ay_bceg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_bceg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bceg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bceg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_bceg_disj_right
    (ay_bceg_ExitCodeSound exitCode (ay_bceg_Sat originalCnf originalModel))
    (ay_bceg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_bceg_failure_ledger
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    ledgerMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result ledger_case _witness_case _resolvent_case _model_case
    _replay_case _build_case _checker_case _audit_case
  exact ledger_case h

theorem ay_bceg_failure_witness
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    witnessMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case witness_case _resolvent_case _model_case
    _replay_case _build_case _checker_case _audit_case
  exact witness_case h

theorem ay_bceg_failure_resolvent
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    resolventMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case resolvent_case _model_case
    _replay_case _build_case _checker_case _audit_case
  exact resolvent_case h

theorem ay_bceg_failure_model_extension
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    modelExtensionMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case _resolvent_case model_case
    _replay_case _build_case _checker_case _audit_case
  exact model_case h

theorem ay_bceg_failure_replay
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case _resolvent_case _model_case
    replay_case _build_case _checker_case _audit_case
  exact replay_case h

theorem ay_bceg_failure_build
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case _resolvent_case _model_case
    _replay_case build_case _checker_case _audit_case
  exact build_case h

theorem ay_bceg_failure_checker
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case _resolvent_case _model_case
    _replay_case _build_case checker_case _audit_case
  exact checker_case h

theorem ay_bceg_failure_audit
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_bceg_BceGuardFailure
      ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
      replayMismatch buildMismatch checkerMismatch auditMismatch := by
  intro h result _ledger_case _witness_case _resolvent_case _model_case
    _replay_case _build_case _checker_case audit_case
  exact audit_case h

theorem ay_bceg_diagnostic_no_claim
    (currentCnf : Prop)
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bceg_DiagnosticBceGuard
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic ->
    ay_bceg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_bceg_conj_right
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_conj_right
      (ay_bceg_BceGuardFailure
        ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
        replayMismatch buildMismatch checkerMismatch auditMismatch)
      (ay_bceg_Conj
        (ay_bceg_RecomputeObligation currentCnf recompute)
        (ay_bceg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bceg_diagnostic_recompute
    (currentCnf : Prop)
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bceg_DiagnosticBceGuard
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic ->
    ay_bceg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_bceg_conj_left
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_conj_right
      (ay_bceg_BceGuardFailure
        ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch
        replayMismatch buildMismatch checkerMismatch auditMismatch)
      (ay_bceg_Conj
        (ay_bceg_RecomputeObligation currentCnf recompute)
        (ay_bceg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bceg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bceg_DiagnosticBceGuard
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic ->
    ay_bceg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_bceg_Conj
      (ay_bceg_NoSemanticClaim diagnostic)
      (ay_bceg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_bceg_conj_intro
    (ay_bceg_NoSemanticClaim diagnostic)
    (ay_bceg_RecomputeObligation currentCnf recompute)
    (ay_bceg_diagnostic_no_claim
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic diagnosticGuard)
    (ay_bceg_diagnostic_recompute
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_bceg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_bceg_DiagnosticBceGuard
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic ->
    ay_bceg_ExitCodeSound exitCode (ay_bceg_Sat originalCnf model) ->
    ay_bceg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_bceg_diagnostic_no_claim
    currentCnf ledgerMismatch witnessMismatch resolventMismatch
    modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_bceg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (ledgerMismatch witnessMismatch resolventMismatch modelExtensionMismatch : Prop)
    (replayMismatch buildMismatch checkerMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_bceg_DiagnosticBceGuard
      currentCnf ledgerMismatch witnessMismatch resolventMismatch
      modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
      auditMismatch recompute diagnostic ->
    ay_bceg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bceg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_bceg_diagnostic_no_claim
    currentCnf ledgerMismatch witnessMismatch resolventMismatch
    modelExtensionMismatch replayMismatch buildMismatch checkerMismatch
    auditMismatch recompute diagnostic diagnosticGuard
