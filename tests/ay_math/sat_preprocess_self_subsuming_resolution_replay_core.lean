-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-subsuming-resolution replay soundness for preprocessing. The
-- propositions stand for strengthening witnesses, deletion/strengthening
-- ledgers, clause coverage, reconstruction hooks, checker replay, formula
-- fingerprints, fallback baseline, build evidence, validator/audit gates,
-- diagnostics, and public SAT/UNSAT reports.

def ay_pssr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pssr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pssr_Equisat (before : Prop) (after : Prop) :=
  ay_pssr_Conj (before -> after) (after -> before)

def ay_pssr_Sat (cnf : Prop) (model : Prop) :=
  ay_pssr_Conj cnf model

def ay_pssr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pssr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pssr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pssr_StrengtheningWitness
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop) :=
  ay_pssr_Conj strengtheningWitness (sourceClause -> strengthenedClause)

def ay_pssr_StrengtheningLedger
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop) :=
  ay_pssr_Conj ledgerWitness
    (ay_pssr_IdMatch deletionLedger strengtheningLedger)

def ay_pssr_ClauseCoverage
    (strengthenedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pssr_Conj coverageWitness (strengthenedClause -> coveredClause)

def ay_pssr_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pssr_Sat reducedCnf reducedModel ->
    ay_pssr_Sat originalCnf originalModel

def ay_pssr_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pssr_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pssr_CheckerReplay
    (ssrCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pssr_Conj ssrCertificate checkerAccepted

def ay_pssr_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pssr_Conj fingerprintWitness
    (ay_pssr_IdMatch originalFingerprint reducedFingerprint)

def ay_pssr_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pssr_Conj baselineSolver baselineAvailable

def ay_pssr_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pssr_Conj binaryFingerprint buildReproducible

def ay_pssr_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pssr_Conj validatorAccepted validatorVersion

def ay_pssr_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pssr_Conj auditAppended auditAppendOnly

def ay_pssr_AcceptedSelfSubsumingResolutionReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop)
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pssr_StrengtheningWitness
       sourceClause strengthenedClause strengtheningWitness ->
     ay_pssr_StrengtheningLedger
       deletionLedger strengtheningLedger ledgerWitness ->
     ay_pssr_ClauseCoverage
       strengthenedClause coveredClause coverageWitness ->
     ay_pssr_Equisat originalCnf reducedCnf ->
     ay_pssr_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pssr_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pssr_CheckerReplay ssrCertificate checkerAccepted ->
     ay_pssr_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pssr_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pssr_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pssr_ValidatorGate validatorAccepted validatorVersion ->
     ay_pssr_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pssr_SsrFailure
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pssr_Disj witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))

def ay_pssr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pssr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pssr_Conj currentCnf recompute

def ay_pssr_DiagnosticSelfSubsumingResolutionReplay
    (currentCnf : Prop)
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pssr_Conj
    (ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pssr_Conj
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic))

def ay_pssr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pssr_Conj exitCode claim

def ay_pssr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pssr_Disj
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pssr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pssr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pssr_conj_left
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pssr_conj_right
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pssr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pssr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pssr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pssr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pssr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pssr_conj_left (before -> after) (after -> before) eq

theorem ay_pssr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pssr_conj_right (before -> after) (after -> before) eq

theorem ay_pssr_strengthening_witness_applies
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop) :
    ay_pssr_StrengtheningWitness
      sourceClause strengthenedClause strengtheningWitness ->
    sourceClause ->
    strengthenedClause := by
  intro accepted source
  exact
    (ay_pssr_conj_right strengtheningWitness
      (sourceClause -> strengthenedClause) accepted) source

theorem ay_pssr_strengthening_ledger_forward
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop) :
    ay_pssr_StrengtheningLedger
      deletionLedger strengtheningLedger ledgerWitness ->
    deletionLedger ->
    strengtheningLedger := by
  intro accepted deletion
  exact accepted strengtheningLedger
    (fun _witness ids =>
      ids strengtheningLedger
        (fun forward _backward => forward deletion))

theorem ay_pssr_clause_coverage
    (strengthenedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pssr_ClauseCoverage
      strengthenedClause coveredClause coverageWitness ->
    strengthenedClause ->
    coveredClause := by
  intro accepted strengthened
  exact
    (ay_pssr_conj_right coverageWitness
      (strengthenedClause -> coveredClause) accepted) strengthened

theorem ay_pssr_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop)
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSelfSubsumingResolutionReplay
      originalCnf reducedCnf sourceClause strengthenedClause
      strengtheningWitness deletionLedger strengtheningLedger ledgerWitness
      coveredClause coverageWitness reducedModel originalModel certificate
      conflict ssrCertificate checkerAccepted originalFingerprint
      reducedFingerprint fingerprintWitness baselineSolver baselineAvailable
      binaryFingerprint buildReproducible validatorAccepted validatorVersion
      auditAppended auditAppendOnly ->
    ay_pssr_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pssr_Equisat originalCnf reducedCnf)
    (fun _witness _ledger _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pssr_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop)
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSelfSubsumingResolutionReplay
      originalCnf reducedCnf sourceClause strengthenedClause
      strengtheningWitness deletionLedger strengtheningLedger ledgerWitness
      coveredClause coverageWitness reducedModel originalModel certificate
      conflict ssrCertificate checkerAccepted originalFingerprint
      reducedFingerprint fingerprintWitness baselineSolver baselineAvailable
      binaryFingerprint buildReproducible validatorAccepted validatorVersion
      auditAppended auditAppendOnly ->
    ay_pssr_CheckerReplay ssrCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
    (fun _witness _ledger _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pssr_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop)
    (strengtheningWitness : Prop)
    (deletionLedger : Prop) (strengtheningLedger : Prop)
    (ledgerWitness : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pssr_AcceptedSelfSubsumingResolutionReplay
      originalCnf reducedCnf sourceClause strengthenedClause
      strengtheningWitness deletionLedger strengtheningLedger ledgerWitness
      coveredClause coverageWitness reducedModel originalModel certificate
      conflict ssrCertificate checkerAccepted originalFingerprint
      reducedFingerprint fingerprintWitness baselineSolver baselineAvailable
      binaryFingerprint buildReproducible validatorAccepted validatorVersion
      auditAppended auditAppendOnly ->
    ay_pssr_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pssr_AuditEvidence auditAppended auditAppendOnly)
    (fun _witness _ledger _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pssr_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pssr_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pssr_Sat reducedCnf reducedModel ->
    ay_pssr_Sat originalCnf originalModel := by
  intro reconstruct reducedSat
  exact reconstruct reducedSat

theorem ay_pssr_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pssr_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pssr_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pssr_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pssr_Sat originalCnf model ->
    ay_pssr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pssr_disj_left
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (ay_pssr_Sat originalCnf model) exit sat)

theorem ay_pssr_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pssr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pssr_disj_right
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat originalCnf model))
    (ay_pssr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pssr_failure_witness_drift
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    witnessDrift ->
    ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pssr_disj_left witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pssr_failure_strengthening_mismatch
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    strengtheningMismatch ->
    ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pssr_disj_right witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))
    (ay_pssr_disj_left strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pssr_failure_missing_coverage
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pssr_disj_right witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))
    (ay_pssr_disj_right strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay))
      (ay_pssr_disj_left missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pssr_failure_stale_fingerprint
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pssr_disj_right witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))
    (ay_pssr_disj_right strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay))
      (ay_pssr_disj_right missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)
        (ay_pssr_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pssr_failure_unchecked_replay
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pssr_disj_right witnessDrift
    (ay_pssr_Disj strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)))
    (ay_pssr_disj_right strengtheningMismatch
      (ay_pssr_Disj missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay))
      (ay_pssr_disj_right missingCoverage
        (ay_pssr_Disj staleFingerprint uncheckedReplay)
        (ay_pssr_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pssr_diagnostic_no_claim
    (currentCnf : Prop)
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticSelfSubsumingResolutionReplay
      currentCnf witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pssr_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pssr_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pssr_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pssr_diagnostic_recompute
    (currentCnf : Prop)
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticSelfSubsumingResolutionReplay
      currentCnf witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pssr_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pssr_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pssr_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pssr_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (witnessDrift : Prop) (strengtheningMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pssr_RecomputeObligation currentCnf recompute ->
    ay_pssr_NoSemanticClaim diagnostic ->
    ay_pssr_DiagnosticSelfSubsumingResolutionReplay
      currentCnf witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pssr_conj_intro
    (ay_pssr_SsrFailure
      witnessDrift strengtheningMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pssr_Conj
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic))
    (ay_pssr_failure_unchecked_replay
      witnessDrift strengtheningMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pssr_conj_intro
      (ay_pssr_RecomputeObligation currentCnf recompute)
      (ay_pssr_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
