-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Tautology-elimination replay soundness for preprocessing. The propositions
-- stand for tautological-clause detection/deletion ledgers, clause coverage,
-- formula fingerprints, model/proof reconstruction, checker replay, fallback
-- baselines, build evidence, validator/audit gates, diagnostics, and public
-- SAT/UNSAT reports.

def ay_pter_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pter_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pter_Equisat (before : Prop) (after : Prop) :=
  ay_pter_Conj (before -> after) (after -> before)

def ay_pter_Sat (cnf : Prop) (model : Prop) :=
  ay_pter_Conj cnf model

def ay_pter_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pter_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pter_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pter_TautologyDetection
    (tautologicalClause : Prop) (detectionWitness : Prop)
    (deletedClause : Prop) :=
  ay_pter_Conj detectionWitness (tautologicalClause -> deletedClause)

def ay_pter_DeletionLedger
    (deletionLedger : Prop) (deletedClause : Prop)
    (ledgerWitness : Prop) :=
  ay_pter_Conj ledgerWitness (deletedClause -> deletionLedger)

def ay_pter_ClauseCoverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pter_Conj coverageWitness (deletedClause -> coveredClause)

def ay_pter_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pter_Conj fingerprintWitness
    (ay_pter_IdMatch originalFingerprint reducedFingerprint)

def ay_pter_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pter_Sat reducedCnf reducedModel ->
    ay_pter_Sat originalCnf originalModel

def ay_pter_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pter_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pter_CheckerReplay
    (tautologyCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pter_Conj tautologyCertificate checkerAccepted

def ay_pter_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pter_Conj baselineSolver baselineAvailable

def ay_pter_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pter_Conj binaryFingerprint buildReproducible

def ay_pter_ValidatorAuditGate
    (validatorAccepted : Prop) (auditAppended : Prop) :=
  ay_pter_Conj validatorAccepted auditAppended

def ay_pter_AcceptedTautologyReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (tautologicalClause : Prop) (detectionWitness : Prop)
    (deletedClause : Prop) (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (tautologyCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (auditAppended : Prop) :=
  ay_pter_Conj
    (ay_pter_TautologyDetection
      tautologicalClause detectionWitness deletedClause)
    (ay_pter_Conj
      (ay_pter_DeletionLedger
        deletionLedger deletedClause ledgerWitness)
      (ay_pter_Conj
        (ay_pter_ClauseCoverage
          deletedClause coveredClause coverageWitness)
        (ay_pter_Conj
          (ay_pter_FingerprintAgreement
            originalFingerprint reducedFingerprint fingerprintWitness)
          (ay_pter_Conj
            (ay_pter_Equisat originalCnf reducedCnf)
            (ay_pter_Conj
              (ay_pter_ModelReconstruction
                reducedCnf originalCnf reducedModel originalModel)
              (ay_pter_Conj
                (ay_pter_ProofReconstruction
                  originalCnf reducedCnf certificate conflict)
                (ay_pter_Conj
                  (ay_pter_CheckerReplay
                    tautologyCertificate checkerAccepted)
                  (ay_pter_Conj
                    (ay_pter_FallbackBaseline
                      baselineSolver baselineAvailable)
                    (ay_pter_Conj
                      (ay_pter_BuildEvidence
                        binaryFingerprint buildReproducible)
                      (ay_pter_ValidatorAuditGate
                        validatorAccepted auditAppended))))))))))

def ay_pter_TautologyFailure
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pter_Disj hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))

def ay_pter_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pter_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pter_Conj currentCnf recompute

def ay_pter_DiagnosticTautologyReplay
    (currentCnf : Prop)
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pter_Conj
    (ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay)
    (ay_pter_Conj
      (ay_pter_RecomputeObligation currentCnf recompute)
      (ay_pter_NoSemanticClaim diagnostic))

def ay_pter_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pter_Conj exitCode claim

def ay_pter_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pter_Disj
    (ay_pter_ExitCodeSound exitCode (ay_pter_Sat originalCnf model))
    (ay_pter_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pter_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pter_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pter_conj_left
    (left : Prop) (right : Prop) :
    ay_pter_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pter_conj_right
    (left : Prop) (right : Prop) :
    ay_pter_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pter_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pter_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pter_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pter_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pter_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pter_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pter_conj_left (before -> after) (after -> before) eq

theorem ay_pter_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pter_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pter_conj_right (before -> after) (after -> before) eq

theorem ay_pter_tautological_clause_detection
    (tautologicalClause : Prop) (detectionWitness : Prop)
    (deletedClause : Prop) :
    ay_pter_TautologyDetection
      tautologicalClause detectionWitness deletedClause ->
    tautologicalClause ->
    deletedClause := by
  intro accepted tautological
  exact
    (ay_pter_conj_right detectionWitness
      (tautologicalClause -> deletedClause) accepted) tautological

theorem ay_pter_deletion_ledger_records_clause
    (deletionLedger : Prop) (deletedClause : Prop)
    (ledgerWitness : Prop) :
    ay_pter_DeletionLedger
      deletionLedger deletedClause ledgerWitness ->
    deletedClause ->
    deletionLedger := by
  intro accepted deleted
  exact
    (ay_pter_conj_right ledgerWitness
      (deletedClause -> deletionLedger) accepted) deleted

theorem ay_pter_clause_coverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pter_ClauseCoverage
      deletedClause coveredClause coverageWitness ->
    deletedClause ->
    coveredClause := by
  intro accepted deleted
  exact
    (ay_pter_conj_right coverageWitness
      (deletedClause -> coveredClause) accepted) deleted

theorem ay_pter_tautology_elimination_equisat
    (originalCnf : Prop) (reducedCnf : Prop) :
    ay_pter_Equisat originalCnf reducedCnf ->
    ay_pter_Equisat reducedCnf originalCnf := by
  intro eq
  exact
    ay_pter_conj_intro (reducedCnf -> originalCnf)
      (originalCnf -> reducedCnf)
      (ay_pter_equisat_backward originalCnf reducedCnf eq)
      (ay_pter_equisat_forward originalCnf reducedCnf eq)

theorem ay_pter_accepted_tautology_detection
    (originalCnf : Prop) (reducedCnf : Prop)
    (tautologicalClause : Prop) (detectionWitness : Prop)
    (deletedClause : Prop) (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (tautologyCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (auditAppended : Prop) :
    ay_pter_AcceptedTautologyReplay
      originalCnf reducedCnf tautologicalClause detectionWitness
      deletedClause deletionLedger ledgerWitness coveredClause coverageWitness
      originalFingerprint reducedFingerprint fingerprintWitness
      reducedModel originalModel certificate conflict tautologyCertificate
      checkerAccepted baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted auditAppended ->
    ay_pter_TautologyDetection
      tautologicalClause detectionWitness deletedClause := by
  intro accepted
  exact ay_pter_conj_left
    (ay_pter_TautologyDetection
      tautologicalClause detectionWitness deletedClause)
    (ay_pter_Conj
      (ay_pter_DeletionLedger deletionLedger deletedClause ledgerWitness)
      (ay_pter_Conj
        (ay_pter_ClauseCoverage deletedClause coveredClause coverageWitness)
        (ay_pter_Conj
          (ay_pter_FingerprintAgreement
            originalFingerprint reducedFingerprint fingerprintWitness)
          (ay_pter_Conj
            (ay_pter_Equisat originalCnf reducedCnf)
            (ay_pter_Conj
              (ay_pter_ModelReconstruction
                reducedCnf originalCnf reducedModel originalModel)
              (ay_pter_Conj
                (ay_pter_ProofReconstruction
                  originalCnf reducedCnf certificate conflict)
                (ay_pter_Conj
                  (ay_pter_CheckerReplay
                    tautologyCertificate checkerAccepted)
                  (ay_pter_Conj
                    (ay_pter_FallbackBaseline
                      baselineSolver baselineAvailable)
                    (ay_pter_Conj
                      (ay_pter_BuildEvidence
                        binaryFingerprint buildReproducible)
                      (ay_pter_ValidatorAuditGate
                        validatorAccepted auditAppended))))))))))
    accepted

theorem ay_pter_accepted_tautology_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (tautologicalClause : Prop) (detectionWitness : Prop)
    (deletedClause : Prop) (deletionLedger : Prop) (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (tautologyCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (auditAppended : Prop) :
    ay_pter_AcceptedTautologyReplay
      originalCnf reducedCnf tautologicalClause detectionWitness
      deletedClause deletionLedger ledgerWitness coveredClause coverageWitness
      originalFingerprint reducedFingerprint fingerprintWitness
      reducedModel originalModel certificate conflict tautologyCertificate
      checkerAccepted baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted auditAppended ->
    ay_pter_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pter_Equisat originalCnf reducedCnf)
    (fun _detection rest1 =>
      rest1 (ay_pter_Equisat originalCnf reducedCnf)
        (fun _ledger rest2 =>
          rest2 (ay_pter_Equisat originalCnf reducedCnf)
            (fun _coverage rest3 =>
              rest3 (ay_pter_Equisat originalCnf reducedCnf)
                (fun _fingerprint rest4 =>
                  rest4 (ay_pter_Equisat originalCnf reducedCnf)
                    (fun eq _tail => eq)))))

theorem ay_pter_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pter_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pter_Sat reducedCnf reducedModel ->
    ay_pter_Sat originalCnf originalModel := by
  intro reconstruct reducedSat
  exact reconstruct reducedSat

theorem ay_pter_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pter_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pter_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pter_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pter_Sat originalCnf model ->
    ay_pter_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pter_disj_left
    (ay_pter_ExitCodeSound exitCode (ay_pter_Sat originalCnf model))
    (ay_pter_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pter_conj_intro exitCode
      (ay_pter_Sat originalCnf model) exit sat)

theorem ay_pter_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pter_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pter_disj_right
    (ay_pter_ExitCodeSound exitCode (ay_pter_Sat originalCnf model))
    (ay_pter_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pter_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pter_failure_hash_drift
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    hashDrift ->
    ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay := by
  intro drift
  exact ay_pter_disj_left hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pter_failure_deletion_mismatch
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    deletionMismatch ->
    ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay := by
  intro mismatch
  exact ay_pter_disj_right hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))
    (ay_pter_disj_left deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pter_failure_missing_coverage
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay := by
  intro missing
  exact ay_pter_disj_right hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))
    (ay_pter_disj_right deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay))
      (ay_pter_disj_left missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pter_failure_stale_fingerprint
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay := by
  intro stale
  exact ay_pter_disj_right hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))
    (ay_pter_disj_right deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay))
      (ay_pter_disj_right missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)
        (ay_pter_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pter_failure_unchecked_replay
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay := by
  intro unchecked
  exact ay_pter_disj_right hashDrift
    (ay_pter_Disj deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)))
    (ay_pter_disj_right deletionMismatch
      (ay_pter_Disj missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay))
      (ay_pter_disj_right missingCoverage
        (ay_pter_Disj staleFingerprint uncheckedReplay)
        (ay_pter_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pter_diagnostic_no_claim
    (currentCnf : Prop)
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pter_DiagnosticTautologyReplay
      currentCnf hashDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pter_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pter_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pter_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pter_diagnostic_recompute
    (currentCnf : Prop)
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pter_DiagnosticTautologyReplay
      currentCnf hashDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pter_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pter_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pter_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pter_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (hashDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pter_RecomputeObligation currentCnf recompute ->
    ay_pter_NoSemanticClaim diagnostic ->
    ay_pter_DiagnosticTautologyReplay
      currentCnf hashDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pter_conj_intro
    (ay_pter_TautologyFailure
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay)
    (ay_pter_Conj
      (ay_pter_RecomputeObligation currentCnf recompute)
      (ay_pter_NoSemanticClaim diagnostic))
    (ay_pter_failure_unchecked_replay
      hashDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pter_conj_intro
      (ay_pter_RecomputeObligation currentCnf recompute)
      (ay_pter_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
