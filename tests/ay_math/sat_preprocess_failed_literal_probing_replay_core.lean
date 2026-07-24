-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Failed-literal probing replay soundness for preprocessing. The
-- propositions stand for probing ledgers, contradiction witnesses, unit propagation replay,
-- clause coverage, reconstruction hooks, checker replay, formula fingerprints,
-- fallback baseline, build evidence, validator/audit gates, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pflp_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pflp_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pflp_Equisat (before : Prop) (after : Prop) :=
  ay_pflp_Conj (before -> after) (after -> before)

def ay_pflp_Sat (cnf : Prop) (model : Prop) :=
  ay_pflp_Conj cnf model

def ay_pflp_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pflp_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pflp_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pflp_ProbingLedger
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop) :=
  ay_pflp_Conj probingWitness (probingTrail -> probingLedger)

def ay_pflp_ContradictionWitness
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop) :=
  ay_pflp_Conj contradictionProof
    (ay_pflp_IdMatch failedLiteral contradictionWitness)

def ay_pflp_UnitPropagationReplay
    (failedLiteral : Prop) (impliedUnitClause : Prop)
    (unitReplay : Prop) :=
  ay_pflp_Conj unitReplay (failedLiteral -> impliedUnitClause)

def ay_pflp_ClauseCoverage
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pflp_Conj coverageWitness (impliedUnitClause -> coveredClause)

def ay_pflp_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pflp_Sat reducedCnf reducedModel ->
    ay_pflp_Sat originalCnf originalModel

def ay_pflp_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pflp_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pflp_CheckerReplay
    (probingCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pflp_Conj probingCertificate checkerAccepted

def ay_pflp_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pflp_Conj fingerprintWitness
    (ay_pflp_IdMatch originalFingerprint reducedFingerprint)

def ay_pflp_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pflp_Conj baselineSolver baselineAvailable

def ay_pflp_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pflp_Conj binaryFingerprint buildReproducible

def ay_pflp_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pflp_Conj validatorAccepted validatorVersion

def ay_pflp_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pflp_Conj auditAppended auditAppendOnly

def ay_pflp_AcceptedFailedLiteralProbingReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop)
    (unitReplay : Prop)
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pflp_ProbingLedger
       probingTrail probingLedger probingWitness ->
     ay_pflp_ContradictionWitness
       failedLiteral contradictionWitness contradictionProof ->
     ay_pflp_UnitPropagationReplay
       failedLiteral impliedUnitClause unitReplay ->
     ay_pflp_ClauseCoverage
       impliedUnitClause coveredClause coverageWitness ->
     ay_pflp_Equisat originalCnf reducedCnf ->
     ay_pflp_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pflp_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pflp_CheckerReplay probingCertificate checkerAccepted ->
     ay_pflp_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pflp_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pflp_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pflp_ValidatorGate validatorAccepted validatorVersion ->
     ay_pflp_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pflp_FailedLiteralProbingFailure
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pflp_Disj contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))

def ay_pflp_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pflp_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pflp_Conj currentCnf recompute

def ay_pflp_DiagnosticFailedLiteralProbingReplay
    (currentCnf : Prop)
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pflp_Conj
    (ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pflp_Conj
      (ay_pflp_RecomputeObligation currentCnf recompute)
      (ay_pflp_NoSemanticClaim diagnostic))

def ay_pflp_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pflp_Conj exitCode claim

def ay_pflp_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pflp_Disj
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf model))
    (ay_pflp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pflp_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pflp_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pflp_conj_left
    (left : Prop) (right : Prop) :
    ay_pflp_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pflp_conj_right
    (left : Prop) (right : Prop) :
    ay_pflp_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pflp_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pflp_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pflp_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pflp_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pflp_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pflp_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pflp_conj_left (before -> after) (after -> before) eq

theorem ay_pflp_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pflp_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pflp_conj_right (before -> after) (after -> before) eq

theorem ay_pflp_probing_ledger_records
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop) :
    ay_pflp_ProbingLedger
      probingTrail probingLedger probingWitness ->
    probingTrail ->
    probingLedger := by
  intro accepted equivalent
  exact
    (ay_pflp_conj_right probingWitness
      (probingTrail -> probingLedger) accepted) equivalent

theorem ay_pflp_contradiction_witness
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop) :
    ay_pflp_ContradictionWitness
      failedLiteral contradictionWitness contradictionProof ->
    failedLiteral ->
    contradictionWitness := by
  intro accepted source
  exact accepted contradictionWitness
    (fun _witness ids =>
      ids contradictionWitness
        (fun forward _backward => forward source))

theorem ay_pflp_unit_propagation_replay
    (failedLiteral : Prop) (impliedUnitClause : Prop)
    (unitReplay : Prop) :
    ay_pflp_UnitPropagationReplay
      failedLiteral impliedUnitClause unitReplay ->
    failedLiteral ->
    impliedUnitClause := by
  intro accepted failed
  exact
    (ay_pflp_conj_right unitReplay
      (failedLiteral -> impliedUnitClause) accepted) failed

theorem ay_pflp_clause_coverage
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pflp_ClauseCoverage
      impliedUnitClause coveredClause coverageWitness ->
    impliedUnitClause ->
    coveredClause := by
  intro accepted substituted
  exact
    (ay_pflp_conj_right coverageWitness
      (impliedUnitClause -> coveredClause) accepted) substituted

theorem ay_pflp_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop)
    (unitReplay : Prop)
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pflp_AcceptedFailedLiteralProbingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness failedLiteral contradictionWitness contradictionProof
      unitReplay impliedUnitClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict probingCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pflp_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pflp_Equisat originalCnf reducedCnf)
    (fun _ledger _contradiction _unit _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pflp_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop)
    (unitReplay : Prop)
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pflp_AcceptedFailedLiteralProbingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness failedLiteral contradictionWitness contradictionProof
      unitReplay impliedUnitClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict probingCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pflp_CheckerReplay probingCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pflp_CheckerReplay probingCertificate checkerAccepted)
    (fun _ledger _contradiction _unit _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pflp_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (failedLiteral : Prop) (contradictionWitness : Prop)
    (contradictionProof : Prop)
    (unitReplay : Prop)
    (impliedUnitClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pflp_AcceptedFailedLiteralProbingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness failedLiteral contradictionWitness contradictionProof
      unitReplay impliedUnitClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict probingCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pflp_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pflp_AuditEvidence auditAppended auditAppendOnly)
    (fun _ledger _contradiction _unit _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pflp_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pflp_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pflp_Sat reducedCnf reducedModel ->
    ay_pflp_Sat originalCnf originalModel := by
  intro reconstruct substitutedSat
  exact reconstruct substitutedSat

theorem ay_pflp_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pflp_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pflp_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pflp_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pflp_Sat originalCnf model ->
    ay_pflp_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pflp_disj_left
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf model))
    (ay_pflp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pflp_conj_intro exitCode
      (ay_pflp_Sat originalCnf model) exit sat)

theorem ay_pflp_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pflp_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pflp_disj_right
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf model))
    (ay_pflp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pflp_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pflp_failure_contradiction_drift
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    contradictionDrift ->
    ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pflp_disj_left contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pflp_failure_unit_mismatch
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    unitMismatch ->
    ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pflp_disj_right contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))
    (ay_pflp_disj_left unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pflp_failure_missing_coverage
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pflp_disj_right contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))
    (ay_pflp_disj_right unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay))
      (ay_pflp_disj_left missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pflp_failure_stale_fingerprint
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pflp_disj_right contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))
    (ay_pflp_disj_right unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay))
      (ay_pflp_disj_right missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)
        (ay_pflp_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pflp_failure_unchecked_replay
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pflp_disj_right contradictionDrift
    (ay_pflp_Disj unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)))
    (ay_pflp_disj_right unitMismatch
      (ay_pflp_Disj missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay))
      (ay_pflp_disj_right missingCoverage
        (ay_pflp_Disj staleFingerprint uncheckedReplay)
        (ay_pflp_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pflp_diagnostic_no_claim
    (currentCnf : Prop)
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pflp_DiagnosticFailedLiteralProbingReplay
      currentCnf contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pflp_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pflp_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pflp_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pflp_diagnostic_recompute
    (currentCnf : Prop)
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pflp_DiagnosticFailedLiteralProbingReplay
      currentCnf contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pflp_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pflp_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pflp_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pflp_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (contradictionDrift : Prop) (unitMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pflp_RecomputeObligation currentCnf recompute ->
    ay_pflp_NoSemanticClaim diagnostic ->
    ay_pflp_DiagnosticFailedLiteralProbingReplay
      currentCnf contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pflp_conj_intro
    (ay_pflp_FailedLiteralProbingFailure
      contradictionDrift unitMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pflp_Conj
      (ay_pflp_RecomputeObligation currentCnf recompute)
      (ay_pflp_NoSemanticClaim diagnostic))
    (ay_pflp_failure_unchecked_replay
      contradictionDrift unitMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pflp_conj_intro
      (ay_pflp_RecomputeObligation currentCnf recompute)
      (ay_pflp_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
