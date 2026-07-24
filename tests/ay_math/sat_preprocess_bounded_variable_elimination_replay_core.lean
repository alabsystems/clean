-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded variable elimination replay soundness for preprocessing. The
-- propositions stand for resolvent-budget ledgers, resolvent coverage,
-- clause coverage, reconstruction hooks, checker replay, formula fingerprints,
-- fallback baseline, build evidence, validator/audit gates, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pbve_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pbve_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pbve_Equisat (before : Prop) (after : Prop) :=
  ay_pbve_Conj (before -> after) (after -> before)

def ay_pbve_Sat (cnf : Prop) (model : Prop) :=
  ay_pbve_Conj cnf model

def ay_pbve_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pbve_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pbve_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pbve_EliminationLedger
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop) :=
  ay_pbve_Conj budgetWitness (resolventBudget -> eliminationLedger)

def ay_pbve_ResolventCoverage
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop) :=
  ay_pbve_Conj resolventWitness
    (ay_pbve_IdMatch eliminatedVariable resolventSet)

def ay_pbve_ClauseCoverage
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pbve_Conj coverageWitness (sourceClause -> coveredClause)

def ay_pbve_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pbve_Sat reducedCnf reducedModel ->
    ay_pbve_Sat originalCnf originalModel

def ay_pbve_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbve_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbve_CheckerReplay
    (bveCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbve_Conj bveCertificate checkerAccepted

def ay_pbve_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbve_Conj fingerprintWitness
    (ay_pbve_IdMatch originalFingerprint reducedFingerprint)

def ay_pbve_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pbve_Conj baselineSolver baselineAvailable

def ay_pbve_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pbve_Conj binaryFingerprint buildReproducible

def ay_pbve_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pbve_Conj validatorAccepted validatorVersion

def ay_pbve_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pbve_Conj auditAppended auditAppendOnly

def ay_pbve_AcceptedBoundedVariableEliminationReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop)
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop)
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bveCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbve_EliminationLedger
       resolventBudget eliminationLedger budgetWitness ->
     ay_pbve_ResolventCoverage
       eliminatedVariable resolventSet resolventWitness ->
     ay_pbve_ClauseCoverage
       sourceClause coveredClause coverageWitness ->
     ay_pbve_Equisat originalCnf reducedCnf ->
     ay_pbve_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pbve_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pbve_CheckerReplay bveCertificate checkerAccepted ->
     ay_pbve_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pbve_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbve_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbve_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbve_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pbve_BveFailure
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pbve_Disj budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))

def ay_pbve_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbve_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbve_Conj currentCnf recompute

def ay_pbve_DiagnosticBoundedVariableEliminationReplay
    (currentCnf : Prop)
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbve_Conj
    (ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pbve_Conj
      (ay_pbve_RecomputeObligation currentCnf recompute)
      (ay_pbve_NoSemanticClaim diagnostic))

def ay_pbve_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pbve_Conj exitCode claim

def ay_pbve_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pbve_Disj
    (ay_pbve_ExitCodeSound exitCode (ay_pbve_Sat originalCnf model))
    (ay_pbve_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pbve_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pbve_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbve_conj_left
    (left : Prop) (right : Prop) :
    ay_pbve_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbve_conj_right
    (left : Prop) (right : Prop) :
    ay_pbve_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbve_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pbve_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbve_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pbve_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbve_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pbve_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbve_conj_left (before -> after) (after -> before) eq

theorem ay_pbve_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pbve_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbve_conj_right (before -> after) (after -> before) eq

theorem ay_pbve_elimination_ledger_records
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop) :
    ay_pbve_EliminationLedger
      resolventBudget eliminationLedger budgetWitness ->
    resolventBudget ->
    eliminationLedger := by
  intro accepted equivalent
  exact
    (ay_pbve_conj_right budgetWitness
      (resolventBudget -> eliminationLedger) accepted) equivalent

theorem ay_pbve_resolvent_coverage
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop) :
    ay_pbve_ResolventCoverage
      eliminatedVariable resolventSet resolventWitness ->
    eliminatedVariable ->
    resolventSet := by
  intro accepted source
  exact accepted resolventSet
    (fun _witness ids =>
      ids resolventSet
        (fun forward _backward => forward source))

theorem ay_pbve_clause_coverage
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pbve_ClauseCoverage
      sourceClause coveredClause coverageWitness ->
    sourceClause ->
    coveredClause := by
  intro accepted substituted
  exact
    (ay_pbve_conj_right coverageWitness
      (sourceClause -> coveredClause) accepted) substituted

theorem ay_pbve_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop)
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop)
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bveCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbve_AcceptedBoundedVariableEliminationReplay
      originalCnf reducedCnf resolventBudget eliminationLedger
      budgetWitness eliminatedVariable resolventSet resolventWitness
      sourceClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict bveCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pbve_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pbve_Equisat originalCnf reducedCnf)
    (fun _ledger _representative _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pbve_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop)
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop)
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bveCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbve_AcceptedBoundedVariableEliminationReplay
      originalCnf reducedCnf resolventBudget eliminationLedger
      budgetWitness eliminatedVariable resolventSet resolventWitness
      sourceClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict bveCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pbve_CheckerReplay bveCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pbve_CheckerReplay bveCertificate checkerAccepted)
    (fun _ledger _representative _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pbve_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolventBudget : Prop) (eliminationLedger : Prop)
    (budgetWitness : Prop)
    (eliminatedVariable : Prop) (resolventSet : Prop)
    (resolventWitness : Prop)
    (sourceClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (bveCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbve_AcceptedBoundedVariableEliminationReplay
      originalCnf reducedCnf resolventBudget eliminationLedger
      budgetWitness eliminatedVariable resolventSet resolventWitness
      sourceClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict bveCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pbve_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbve_AuditEvidence auditAppended auditAppendOnly)
    (fun _ledger _representative _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pbve_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pbve_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pbve_Sat reducedCnf reducedModel ->
    ay_pbve_Sat originalCnf originalModel := by
  intro reconstruct substitutedSat
  exact reconstruct substitutedSat

theorem ay_pbve_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbve_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pbve_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pbve_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pbve_Sat originalCnf model ->
    ay_pbve_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pbve_disj_left
    (ay_pbve_ExitCodeSound exitCode (ay_pbve_Sat originalCnf model))
    (ay_pbve_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbve_conj_intro exitCode
      (ay_pbve_Sat originalCnf model) exit sat)

theorem ay_pbve_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pbve_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pbve_disj_right
    (ay_pbve_ExitCodeSound exitCode (ay_pbve_Sat originalCnf model))
    (ay_pbve_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbve_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pbve_failure_budget_drift
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    budgetDrift ->
    ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pbve_disj_left budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pbve_failure_resolvent_mismatch
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    resolventMismatch ->
    ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pbve_disj_right budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))
    (ay_pbve_disj_left resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pbve_failure_missing_coverage
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pbve_disj_right budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))
    (ay_pbve_disj_right resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay))
      (ay_pbve_disj_left missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pbve_failure_stale_fingerprint
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pbve_disj_right budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))
    (ay_pbve_disj_right resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay))
      (ay_pbve_disj_right missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)
        (ay_pbve_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pbve_failure_unchecked_replay
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pbve_disj_right budgetDrift
    (ay_pbve_Disj resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)))
    (ay_pbve_disj_right resolventMismatch
      (ay_pbve_Disj missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay))
      (ay_pbve_disj_right missingCoverage
        (ay_pbve_Disj staleFingerprint uncheckedReplay)
        (ay_pbve_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pbve_diagnostic_no_claim
    (currentCnf : Prop)
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbve_DiagnosticBoundedVariableEliminationReplay
      currentCnf budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pbve_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbve_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pbve_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pbve_diagnostic_recompute
    (currentCnf : Prop)
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbve_DiagnosticBoundedVariableEliminationReplay
      currentCnf budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pbve_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbve_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pbve_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pbve_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (budgetDrift : Prop) (resolventMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbve_RecomputeObligation currentCnf recompute ->
    ay_pbve_NoSemanticClaim diagnostic ->
    ay_pbve_DiagnosticBoundedVariableEliminationReplay
      currentCnf budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pbve_conj_intro
    (ay_pbve_BveFailure
      budgetDrift resolventMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pbve_Conj
      (ay_pbve_RecomputeObligation currentCnf recompute)
      (ay_pbve_NoSemanticClaim diagnostic))
    (ay_pbve_failure_unchecked_replay
      budgetDrift resolventMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pbve_conj_intro
      (ay_pbve_RecomputeObligation currentCnf recompute)
      (ay_pbve_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
