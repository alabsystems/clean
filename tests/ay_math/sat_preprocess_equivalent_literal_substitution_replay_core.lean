-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalent-literal substitution replay soundness for preprocessing. The
-- propositions stand for equivalence ledgers, representative literal maps,
-- clause coverage, reconstruction hooks, checker replay, formula fingerprints,
-- fallback baseline, build evidence, validator/audit gates, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pels_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pels_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pels_Equisat (before : Prop) (after : Prop) :=
  ay_pels_Conj (before -> after) (after -> before)

def ay_pels_Sat (cnf : Prop) (model : Prop) :=
  ay_pels_Conj cnf model

def ay_pels_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pels_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pels_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pels_EquivalenceLedger
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop) :=
  ay_pels_Conj ledgerWitness (literalEquivalence -> equivalenceLedger)

def ay_pels_RepresentativeMap
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :=
  ay_pels_Conj representativeWitness
    (ay_pels_IdMatch sourceLiteral representativeLiteral)

def ay_pels_ClauseCoverage
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pels_Conj coverageWitness (substitutedClause -> coveredClause)

def ay_pels_ModelReconstruction
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop) :=
  ay_pels_Sat substitutedCnf substitutedModel ->
    ay_pels_Sat originalCnf originalModel

def ay_pels_ProofReconstruction
    (originalCnf : Prop) (substitutedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pels_Replay substitutedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pels_CheckerReplay
    (substitutionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pels_Conj substitutionCertificate checkerAccepted

def ay_pels_FingerprintAgreement
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pels_Conj fingerprintWitness
    (ay_pels_IdMatch originalFingerprint substitutedFingerprint)

def ay_pels_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pels_Conj baselineSolver baselineAvailable

def ay_pels_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pels_Conj binaryFingerprint buildReproducible

def ay_pels_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pels_Conj validatorAccepted validatorVersion

def ay_pels_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pels_Conj auditAppended auditAppendOnly

def ay_pels_AcceptedEquivalentLiteralReplay
    (originalCnf : Prop) (substitutedCnf : Prop)
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop)
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pels_EquivalenceLedger
       literalEquivalence equivalenceLedger ledgerWitness ->
     ay_pels_RepresentativeMap
       sourceLiteral representativeLiteral representativeWitness ->
     ay_pels_ClauseCoverage
       substitutedClause coveredClause coverageWitness ->
     ay_pels_Equisat originalCnf substitutedCnf ->
     ay_pels_ModelReconstruction
       substitutedCnf originalCnf substitutedModel originalModel ->
     ay_pels_ProofReconstruction
       originalCnf substitutedCnf certificate conflict ->
     ay_pels_CheckerReplay substitutionCertificate checkerAccepted ->
     ay_pels_FingerprintAgreement
       originalFingerprint substitutedFingerprint fingerprintWitness ->
     ay_pels_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pels_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pels_ValidatorGate validatorAccepted validatorVersion ->
     ay_pels_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pels_SubstitutionFailure
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pels_Disj representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))

def ay_pels_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pels_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pels_Conj currentCnf recompute

def ay_pels_DiagnosticEquivalentLiteralReplay
    (currentCnf : Prop)
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pels_Conj
    (ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pels_Conj
      (ay_pels_RecomputeObligation currentCnf recompute)
      (ay_pels_NoSemanticClaim diagnostic))

def ay_pels_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pels_Conj exitCode claim

def ay_pels_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pels_Disj
    (ay_pels_ExitCodeSound exitCode (ay_pels_Sat originalCnf model))
    (ay_pels_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pels_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pels_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pels_conj_left
    (left : Prop) (right : Prop) :
    ay_pels_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pels_conj_right
    (left : Prop) (right : Prop) :
    ay_pels_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pels_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pels_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pels_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pels_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pels_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pels_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pels_conj_left (before -> after) (after -> before) eq

theorem ay_pels_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pels_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pels_conj_right (before -> after) (after -> before) eq

theorem ay_pels_equivalence_ledger_records
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop) :
    ay_pels_EquivalenceLedger
      literalEquivalence equivalenceLedger ledgerWitness ->
    literalEquivalence ->
    equivalenceLedger := by
  intro accepted equivalent
  exact
    (ay_pels_conj_right ledgerWitness
      (literalEquivalence -> equivalenceLedger) accepted) equivalent

theorem ay_pels_representative_forward
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :
    ay_pels_RepresentativeMap
      sourceLiteral representativeLiteral representativeWitness ->
    sourceLiteral ->
    representativeLiteral := by
  intro accepted source
  exact accepted representativeLiteral
    (fun _witness ids =>
      ids representativeLiteral
        (fun forward _backward => forward source))

theorem ay_pels_clause_coverage
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pels_ClauseCoverage
      substitutedClause coveredClause coverageWitness ->
    substitutedClause ->
    coveredClause := by
  intro accepted substituted
  exact
    (ay_pels_conj_right coverageWitness
      (substitutedClause -> coveredClause) accepted) substituted

theorem ay_pels_accepted_equisat
    (originalCnf : Prop) (substitutedCnf : Prop)
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop)
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pels_AcceptedEquivalentLiteralReplay
      originalCnf substitutedCnf literalEquivalence equivalenceLedger
      ledgerWitness sourceLiteral representativeLiteral representativeWitness
      substitutedClause coveredClause coverageWitness substitutedModel
      originalModel certificate conflict substitutionCertificate
      checkerAccepted originalFingerprint substitutedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pels_Equisat originalCnf substitutedCnf := by
  intro accepted
  exact accepted (ay_pels_Equisat originalCnf substitutedCnf)
    (fun _ledger _representative _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pels_accepted_checker_replay
    (originalCnf : Prop) (substitutedCnf : Prop)
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop)
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pels_AcceptedEquivalentLiteralReplay
      originalCnf substitutedCnf literalEquivalence equivalenceLedger
      ledgerWitness sourceLiteral representativeLiteral representativeWitness
      substitutedClause coveredClause coverageWitness substitutedModel
      originalModel certificate conflict substitutionCertificate
      checkerAccepted originalFingerprint substitutedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pels_CheckerReplay substitutionCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pels_CheckerReplay substitutionCertificate checkerAccepted)
    (fun _ledger _representative _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pels_accepted_audit_evidence
    (originalCnf : Prop) (substitutedCnf : Prop)
    (literalEquivalence : Prop) (equivalenceLedger : Prop)
    (ledgerWitness : Prop)
    (sourceLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (substitutedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pels_AcceptedEquivalentLiteralReplay
      originalCnf substitutedCnf literalEquivalence equivalenceLedger
      ledgerWitness sourceLiteral representativeLiteral representativeWitness
      substitutedClause coveredClause coverageWitness substitutedModel
      originalModel certificate conflict substitutionCertificate
      checkerAccepted originalFingerprint substitutedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pels_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pels_AuditEvidence auditAppended auditAppendOnly)
    (fun _ledger _representative _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pels_sat_pullback
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop) :
    ay_pels_ModelReconstruction
      substitutedCnf originalCnf substitutedModel originalModel ->
    ay_pels_Sat substitutedCnf substitutedModel ->
    ay_pels_Sat originalCnf originalModel := by
  intro reconstruct substitutedSat
  exact reconstruct substitutedSat

theorem ay_pels_unsat_pushback
    (originalCnf : Prop) (substitutedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pels_ProofReconstruction
      originalCnf substitutedCnf certificate conflict ->
    ay_pels_Replay substitutedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pels_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pels_Sat originalCnf model ->
    ay_pels_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pels_disj_left
    (ay_pels_ExitCodeSound exitCode (ay_pels_Sat originalCnf model))
    (ay_pels_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pels_conj_intro exitCode
      (ay_pels_Sat originalCnf model) exit sat)

theorem ay_pels_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pels_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pels_disj_right
    (ay_pels_ExitCodeSound exitCode (ay_pels_Sat originalCnf model))
    (ay_pels_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pels_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pels_failure_representative_drift
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    representativeDrift ->
    ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pels_disj_left representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pels_failure_substitution_mismatch
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    substitutionMismatch ->
    ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pels_disj_right representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))
    (ay_pels_disj_left substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pels_failure_missing_coverage
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pels_disj_right representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))
    (ay_pels_disj_right substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay))
      (ay_pels_disj_left missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pels_failure_stale_fingerprint
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pels_disj_right representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))
    (ay_pels_disj_right substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay))
      (ay_pels_disj_right missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)
        (ay_pels_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pels_failure_unchecked_replay
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pels_disj_right representativeDrift
    (ay_pels_Disj substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)))
    (ay_pels_disj_right substitutionMismatch
      (ay_pels_Disj missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay))
      (ay_pels_disj_right missingCoverage
        (ay_pels_Disj staleFingerprint uncheckedReplay)
        (ay_pels_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pels_diagnostic_no_claim
    (currentCnf : Prop)
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pels_DiagnosticEquivalentLiteralReplay
      currentCnf representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pels_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pels_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pels_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pels_diagnostic_recompute
    (currentCnf : Prop)
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pels_DiagnosticEquivalentLiteralReplay
      currentCnf representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pels_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pels_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pels_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pels_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (representativeDrift : Prop) (substitutionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pels_RecomputeObligation currentCnf recompute ->
    ay_pels_NoSemanticClaim diagnostic ->
    ay_pels_DiagnosticEquivalentLiteralReplay
      currentCnf representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pels_conj_intro
    (ay_pels_SubstitutionFailure
      representativeDrift substitutionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pels_Conj
      (ay_pels_RecomputeObligation currentCnf recompute)
      (ay_pels_NoSemanticClaim diagnostic))
    (ay_pels_failure_unchecked_replay
      representativeDrift substitutionMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pels_conj_intro
      (ay_pels_RecomputeObligation currentCnf recompute)
      (ay_pels_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
