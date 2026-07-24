-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption replay soundness for preprocessing. The
-- propositions stand for subsumption witnesses, deletion ledgers,
-- clause coverage, reconstruction hooks, checker replay, formula fingerprints,
-- fallback baseline, build evidence, validator/audit gates, diagnostics, and
-- public SAT/UNSAT reports.

def ay_psub_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psub_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_psub_Equisat (before : Prop) (after : Prop) :=
  ay_psub_Conj (before -> after) (after -> before)

def ay_psub_Sat (cnf : Prop) (model : Prop) :=
  ay_psub_Conj cnf model

def ay_psub_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_psub_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_psub_Conj (leftId -> rightId) (rightId -> leftId)

def ay_psub_SubsumptionWitness
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :=
  ay_psub_Conj witnessLedger (subsumedClause -> subsumptionWitness)

def ay_psub_DeletionLedger
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop) :=
  ay_psub_Conj deletionWitness
    (ay_psub_IdMatch deletionLedger deletedClause)

def ay_psub_ClauseCoverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_psub_Conj coverageWitness (deletedClause -> coveredClause)

def ay_psub_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_psub_Sat reducedCnf reducedModel ->
    ay_psub_Sat originalCnf originalModel

def ay_psub_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_psub_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_psub_CheckerReplay
    (subsumptionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_psub_Conj subsumptionCertificate checkerAccepted

def ay_psub_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psub_Conj fingerprintWitness
    (ay_psub_IdMatch originalFingerprint reducedFingerprint)

def ay_psub_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_psub_Conj baselineSolver baselineAvailable

def ay_psub_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_psub_Conj binaryFingerprint buildReproducible

def ay_psub_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_psub_Conj validatorAccepted validatorVersion

def ay_psub_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_psub_Conj auditAppended auditAppendOnly

def ay_psub_AcceptedSubsumptionReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_psub_SubsumptionWitness
       subsumedClause subsumptionWitness witnessLedger ->
     ay_psub_DeletionLedger
       deletionLedger deletedClause deletionWitness ->
     ay_psub_ClauseCoverage
       deletedClause coveredClause coverageWitness ->
     ay_psub_Equisat originalCnf reducedCnf ->
     ay_psub_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_psub_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_psub_CheckerReplay subsumptionCertificate checkerAccepted ->
     ay_psub_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_psub_FallbackBaseline baselineSolver baselineAvailable ->
     ay_psub_BuildEvidence binaryFingerprint buildReproducible ->
     ay_psub_ValidatorGate validatorAccepted validatorVersion ->
     ay_psub_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_psub_SubsumptionFailure
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_psub_Disj witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))

def ay_psub_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_psub_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_psub_Conj currentCnf recompute

def ay_psub_DiagnosticSubsumptionReplay
    (currentCnf : Prop)
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_psub_Conj
    (ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_psub_Conj
      (ay_psub_RecomputeObligation currentCnf recompute)
      (ay_psub_NoSemanticClaim diagnostic))

def ay_psub_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_psub_Conj exitCode claim

def ay_psub_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_psub_Disj
    (ay_psub_ExitCodeSound exitCode (ay_psub_Sat originalCnf model))
    (ay_psub_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_psub_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_psub_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_psub_conj_left
    (left : Prop) (right : Prop) :
    ay_psub_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_psub_conj_right
    (left : Prop) (right : Prop) :
    ay_psub_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_psub_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_psub_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_psub_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_psub_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_psub_equisat_forward
    (before : Prop) (after : Prop) :
    ay_psub_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_psub_conj_left (before -> after) (after -> before) eq

theorem ay_psub_equisat_backward
    (before : Prop) (after : Prop) :
    ay_psub_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_psub_conj_right (before -> after) (after -> before) eq

theorem ay_psub_subsumption_witness_records
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :
    ay_psub_SubsumptionWitness
      subsumedClause subsumptionWitness witnessLedger ->
    subsumedClause ->
    subsumptionWitness := by
  intro accepted equivalent
  exact
    (ay_psub_conj_right witnessLedger
      (subsumedClause -> subsumptionWitness) accepted) equivalent

theorem ay_psub_deletion_ledger_records
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop) :
    ay_psub_DeletionLedger
      deletionLedger deletedClause deletionWitness ->
    deletionLedger ->
    deletedClause := by
  intro accepted source
  exact accepted deletedClause
    (fun _witness ids =>
      ids deletedClause
        (fun forward _backward => forward source))

theorem ay_psub_clause_coverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_psub_ClauseCoverage
      deletedClause coveredClause coverageWitness ->
    deletedClause ->
    coveredClause := by
  intro accepted substituted
  exact
    (ay_psub_conj_right coverageWitness
      (deletedClause -> coveredClause) accepted) substituted

theorem ay_psub_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psub_AcceptedSubsumptionReplay
      originalCnf reducedCnf subsumedClause subsumptionWitness
      witnessLedger deletionLedger deletedClause deletionWitness
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict subsumptionCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_psub_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_psub_Equisat originalCnf reducedCnf)
    (fun _ledger _representative _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_psub_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psub_AcceptedSubsumptionReplay
      originalCnf reducedCnf subsumedClause subsumptionWitness
      witnessLedger deletionLedger deletedClause deletionWitness
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict subsumptionCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_psub_CheckerReplay subsumptionCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_psub_CheckerReplay subsumptionCertificate checkerAccepted)
    (fun _ledger _representative _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_psub_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (deletionLedger : Prop) (deletedClause : Prop)
    (deletionWitness : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psub_AcceptedSubsumptionReplay
      originalCnf reducedCnf subsumedClause subsumptionWitness
      witnessLedger deletionLedger deletedClause deletionWitness
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict subsumptionCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_psub_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_psub_AuditEvidence auditAppended auditAppendOnly)
    (fun _ledger _representative _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_psub_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_psub_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_psub_Sat reducedCnf reducedModel ->
    ay_psub_Sat originalCnf originalModel := by
  intro reconstruct substitutedSat
  exact reconstruct substitutedSat

theorem ay_psub_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_psub_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_psub_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_psub_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_psub_Sat originalCnf model ->
    ay_psub_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_psub_disj_left
    (ay_psub_ExitCodeSound exitCode (ay_psub_Sat originalCnf model))
    (ay_psub_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_psub_conj_intro exitCode
      (ay_psub_Sat originalCnf model) exit sat)

theorem ay_psub_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_psub_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_psub_disj_right
    (ay_psub_ExitCodeSound exitCode (ay_psub_Sat originalCnf model))
    (ay_psub_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_psub_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_psub_failure_witness_drift
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    witnessDrift ->
    ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_psub_disj_left witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_psub_failure_deletion_mismatch
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    deletionMismatch ->
    ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_psub_disj_right witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))
    (ay_psub_disj_left deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_psub_failure_missing_coverage
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_psub_disj_right witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))
    (ay_psub_disj_right deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay))
      (ay_psub_disj_left missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_psub_failure_stale_fingerprint
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_psub_disj_right witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))
    (ay_psub_disj_right deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay))
      (ay_psub_disj_right missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)
        (ay_psub_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_psub_failure_unchecked_replay
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_psub_disj_right witnessDrift
    (ay_psub_Disj deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)))
    (ay_psub_disj_right deletionMismatch
      (ay_psub_Disj missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay))
      (ay_psub_disj_right missingCoverage
        (ay_psub_Disj staleFingerprint uncheckedReplay)
        (ay_psub_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_psub_diagnostic_no_claim
    (currentCnf : Prop)
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psub_DiagnosticSubsumptionReplay
      currentCnf witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_psub_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_psub_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_psub_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_psub_diagnostic_recompute
    (currentCnf : Prop)
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psub_DiagnosticSubsumptionReplay
      currentCnf witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_psub_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_psub_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_psub_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_psub_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (witnessDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_psub_RecomputeObligation currentCnf recompute ->
    ay_psub_NoSemanticClaim diagnostic ->
    ay_psub_DiagnosticSubsumptionReplay
      currentCnf witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_psub_conj_intro
    (ay_psub_SubsumptionFailure
      witnessDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_psub_Conj
      (ay_psub_RecomputeObligation currentCnf recompute)
      (ay_psub_NoSemanticClaim diagnostic))
    (ay_psub_failure_unchecked_replay
      witnessDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_psub_conj_intro
      (ay_psub_RecomputeObligation currentCnf recompute)
      (ay_psub_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
