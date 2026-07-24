-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause elimination replay soundness for preprocessing. The
-- propositions stand for blocked clause detection/deletion ledgers, blocking
-- literal witnesses, clause coverage, model/proof reconstruction, checker
-- replay, formula fingerprints, fallback baseline, build evidence, validator
-- gate, audit evidence, diagnostics, and public SAT/UNSAT reports.

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

def ay_pbce_BlockingWitness
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop) :=
  ay_pbce_Conj blockingWitness
    (ay_pbce_Conj blockedClause blockingLiteral)

def ay_pbce_DeletionLedger
    (deletionLedger : Prop) (blockedClause : Prop)
    (ledgerWitness : Prop) :=
  ay_pbce_Conj ledgerWitness (blockedClause -> deletionLedger)

def ay_pbce_ClauseCoverage
    (blockedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pbce_Conj coverageWitness (blockedClause -> coveredClause)

def ay_pbce_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pbce_Sat reducedCnf reducedModel ->
    ay_pbce_Sat originalCnf originalModel

def ay_pbce_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbce_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbce_CheckerReplay
    (bceCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbce_Conj bceCertificate checkerAccepted

def ay_pbce_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbce_Conj fingerprintWitness
    (ay_pbce_IdMatch originalFingerprint reducedFingerprint)

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

def ay_pbce_AcceptedBlockedClauseReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop)
    (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbce_BlockingWitness
       blockedClause blockingLiteral blockingWitness ->
     ay_pbce_DeletionLedger
       deletionLedger blockedClause ledgerWitness ->
     ay_pbce_ClauseCoverage
       blockedClause coveredClause coverageWitness ->
     ay_pbce_Equisat originalCnf reducedCnf ->
     ay_pbce_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pbce_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pbce_CheckerReplay bceCertificate checkerAccepted ->
     ay_pbce_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pbce_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbce_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbce_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbce_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pbce_BceFailure
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :=
  ay_pbce_Disj blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))

def ay_pbce_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbce_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbce_Conj currentCnf recompute

def ay_pbce_DiagnosticBceReplay
    (currentCnf : Prop)
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbce_Conj
    (ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay)
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

theorem ay_pbce_blocking_literal_present
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop) :
    ay_pbce_BlockingWitness
      blockedClause blockingLiteral blockingWitness ->
    blockingLiteral := by
  intro accepted
  exact accepted blockingLiteral
    (fun _witness pair =>
      pair blockingLiteral
        (fun _clause literal => literal))

theorem ay_pbce_deletion_ledger_records_clause
    (deletionLedger : Prop) (blockedClause : Prop)
    (ledgerWitness : Prop) :
    ay_pbce_DeletionLedger
      deletionLedger blockedClause ledgerWitness ->
    blockedClause ->
    deletionLedger := by
  intro accepted blocked
  exact
    (ay_pbce_conj_right ledgerWitness
      (blockedClause -> deletionLedger) accepted) blocked

theorem ay_pbce_clause_coverage
    (blockedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pbce_ClauseCoverage
      blockedClause coveredClause coverageWitness ->
    blockedClause ->
    coveredClause := by
  intro accepted blocked
  exact
    (ay_pbce_conj_right coverageWitness
      (blockedClause -> coveredClause) accepted) blocked

theorem ay_pbce_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop)
    (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseReplay
      originalCnf reducedCnf blockedClause blockingLiteral blockingWitness
      deletionLedger ledgerWitness coveredClause coverageWitness reducedModel
      originalModel certificate conflict bceCertificate checkerAccepted
      originalFingerprint reducedFingerprint fingerprintWitness baselineSolver
      baselineAvailable binaryFingerprint buildReproducible validatorAccepted
      validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pbce_Equisat originalCnf reducedCnf)
    (fun _blocking _ledger _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pbce_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop)
    (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseReplay
      originalCnf reducedCnf blockedClause blockingLiteral blockingWitness
      deletionLedger ledgerWitness coveredClause coverageWitness reducedModel
      originalModel certificate conflict bceCertificate checkerAccepted
      originalFingerprint reducedFingerprint fingerprintWitness baselineSolver
      baselineAvailable binaryFingerprint buildReproducible validatorAccepted
      validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_CheckerReplay bceCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pbce_CheckerReplay bceCertificate checkerAccepted)
    (fun _blocking _ledger _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pbce_accepted_audit_gate
    (originalCnf : Prop) (reducedCnf : Prop)
    (blockedClause : Prop) (blockingLiteral : Prop)
    (blockingWitness : Prop)
    (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbce_AcceptedBlockedClauseReplay
      originalCnf reducedCnf blockedClause blockingLiteral blockingWitness
      deletionLedger ledgerWitness coveredClause coverageWitness reducedModel
      originalModel certificate conflict bceCertificate checkerAccepted
      originalFingerprint reducedFingerprint fingerprintWitness baselineSolver
      baselineAvailable binaryFingerprint buildReproducible validatorAccepted
      validatorVersion auditAppended auditAppendOnly ->
    ay_pbce_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbce_AuditEvidence auditAppended auditAppendOnly)
    (fun _blocking _ledger _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pbce_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pbce_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pbce_Sat reducedCnf reducedModel ->
    ay_pbce_Sat originalCnf originalModel := by
  intro reconstruct reducedSat
  exact reconstruct reducedSat

theorem ay_pbce_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbce_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pbce_Replay reducedCnf certificate conflict ->
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

theorem ay_pbce_failure_blockedness_drift
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    blockednessDrift ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pbce_disj_left blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    drift

theorem ay_pbce_failure_deletion_mismatch
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    deletionMismatch ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pbce_disj_right blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    (ay_pbce_disj_left deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)))
      mismatch)

theorem ay_pbce_failure_missing_witness
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    missingWitness ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pbce_disj_right blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    (ay_pbce_disj_right deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)))
      (ay_pbce_disj_left missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))
        missing))

theorem ay_pbce_failure_missing_coverage
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pbce_disj_right blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    (ay_pbce_disj_right deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)))
      (ay_pbce_disj_right missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))
        (ay_pbce_disj_left missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)
          missing)))

theorem ay_pbce_failure_stale_fingerprint
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pbce_disj_right blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    (ay_pbce_disj_right deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)))
      (ay_pbce_disj_right missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))
        (ay_pbce_disj_right missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)
          (ay_pbce_disj_left staleFingerprint uncheckedReplay stale))))

theorem ay_pbce_failure_unchecked_replay
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pbce_disj_right blockednessDrift
    (ay_pbce_Disj deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))))
    (ay_pbce_disj_right deletionMismatch
      (ay_pbce_Disj missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)))
      (ay_pbce_disj_right missingWitness
        (ay_pbce_Disj missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay))
        (ay_pbce_disj_right missingCoverage
          (ay_pbce_Disj staleFingerprint uncheckedReplay)
          (ay_pbce_disj_right staleFingerprint uncheckedReplay unchecked))))

theorem ay_pbce_diagnostic_no_claim
    (currentCnf : Prop)
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbce_DiagnosticBceReplay
      currentCnf blockednessDrift deletionMismatch missingWitness
      missingCoverage staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pbce_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbce_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pbce_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pbce_diagnostic_recompute
    (currentCnf : Prop)
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbce_DiagnosticBceReplay
      currentCnf blockednessDrift deletionMismatch missingWitness
      missingCoverage staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pbce_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbce_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pbce_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pbce_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (blockednessDrift : Prop) (deletionMismatch : Prop)
    (missingWitness : Prop) (missingCoverage : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbce_RecomputeObligation currentCnf recompute ->
    ay_pbce_NoSemanticClaim diagnostic ->
    ay_pbce_DiagnosticBceReplay
      currentCnf blockednessDrift deletionMismatch missingWitness
      missingCoverage staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pbce_conj_intro
    (ay_pbce_BceFailure
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pbce_Conj
      (ay_pbce_RecomputeObligation currentCnf recompute)
      (ay_pbce_NoSemanticClaim diagnostic))
    (ay_pbce_failure_unchecked_replay
      blockednessDrift deletionMismatch missingWitness missingCoverage
      staleFingerprint uncheckedReplay unchecked)
    (ay_pbce_conj_intro
      (ay_pbce_RecomputeObligation currentCnf recompute)
      (ay_pbce_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
