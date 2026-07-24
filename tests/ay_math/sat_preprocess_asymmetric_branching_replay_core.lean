-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Asymmetric branching replay soundness for preprocessing. The
-- propositions stand for probing ledgers, implication witnesses,
-- clause coverage, reconstruction hooks, checker replay, formula fingerprints,
-- fallback baseline, build evidence, validator/audit gates, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pabr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pabr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pabr_Equisat (before : Prop) (after : Prop) :=
  ay_pabr_Conj (before -> after) (after -> before)

def ay_pabr_Sat (cnf : Prop) (model : Prop) :=
  ay_pabr_Conj cnf model

def ay_pabr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pabr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pabr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pabr_ProbingLedger
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop) :=
  ay_pabr_Conj probingWitness (probingTrail -> probingLedger)

def ay_pabr_ImplicationWitness
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop) :=
  ay_pabr_Conj implicationProof
    (ay_pabr_IdMatch impliedLiteral implicationWitness)

def ay_pabr_ClauseCoverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pabr_Conj coverageWitness (deletedClause -> coveredClause)

def ay_pabr_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pabr_Sat reducedCnf reducedModel ->
    ay_pabr_Sat originalCnf originalModel

def ay_pabr_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pabr_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pabr_CheckerReplay
    (asymmetricCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pabr_Conj asymmetricCertificate checkerAccepted

def ay_pabr_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pabr_Conj fingerprintWitness
    (ay_pabr_IdMatch originalFingerprint reducedFingerprint)

def ay_pabr_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pabr_Conj baselineSolver baselineAvailable

def ay_pabr_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pabr_Conj binaryFingerprint buildReproducible

def ay_pabr_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pabr_Conj validatorAccepted validatorVersion

def ay_pabr_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pabr_Conj auditAppended auditAppendOnly

def ay_pabr_AcceptedAsymmetricBranchingReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (asymmetricCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pabr_ProbingLedger
       probingTrail probingLedger probingWitness ->
     ay_pabr_ImplicationWitness
       impliedLiteral implicationWitness implicationProof ->
     ay_pabr_ClauseCoverage
       deletedClause coveredClause coverageWitness ->
     ay_pabr_Equisat originalCnf reducedCnf ->
     ay_pabr_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pabr_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pabr_CheckerReplay asymmetricCertificate checkerAccepted ->
     ay_pabr_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pabr_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pabr_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pabr_ValidatorGate validatorAccepted validatorVersion ->
     ay_pabr_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pabr_AsymmetricBranchingFailure
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :=
  ay_pabr_Disj implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))

def ay_pabr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pabr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pabr_Conj currentCnf recompute

def ay_pabr_DiagnosticAsymmetricBranchingReplay
    (currentCnf : Prop)
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pabr_Conj
    (ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pabr_Conj
      (ay_pabr_RecomputeObligation currentCnf recompute)
      (ay_pabr_NoSemanticClaim diagnostic))

def ay_pabr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pabr_Conj exitCode claim

def ay_pabr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pabr_Disj
    (ay_pabr_ExitCodeSound exitCode (ay_pabr_Sat originalCnf model))
    (ay_pabr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pabr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pabr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pabr_conj_left
    (left : Prop) (right : Prop) :
    ay_pabr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pabr_conj_right
    (left : Prop) (right : Prop) :
    ay_pabr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pabr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pabr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pabr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pabr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pabr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pabr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pabr_conj_left (before -> after) (after -> before) eq

theorem ay_pabr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pabr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pabr_conj_right (before -> after) (after -> before) eq

theorem ay_pabr_probing_ledger_records
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop) :
    ay_pabr_ProbingLedger
      probingTrail probingLedger probingWitness ->
    probingTrail ->
    probingLedger := by
  intro accepted equivalent
  exact
    (ay_pabr_conj_right probingWitness
      (probingTrail -> probingLedger) accepted) equivalent

theorem ay_pabr_implication_witness
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop) :
    ay_pabr_ImplicationWitness
      impliedLiteral implicationWitness implicationProof ->
    impliedLiteral ->
    implicationWitness := by
  intro accepted source
  exact accepted implicationWitness
    (fun _witness ids =>
      ids implicationWitness
        (fun forward _backward => forward source))

theorem ay_pabr_clause_coverage
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pabr_ClauseCoverage
      deletedClause coveredClause coverageWitness ->
    deletedClause ->
    coveredClause := by
  intro accepted substituted
  exact
    (ay_pabr_conj_right coverageWitness
      (deletedClause -> coveredClause) accepted) substituted

theorem ay_pabr_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (asymmetricCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pabr_AcceptedAsymmetricBranchingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness impliedLiteral implicationWitness implicationProof
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict asymmetricCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pabr_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pabr_Equisat originalCnf reducedCnf)
    (fun _ledger _representative _coverage eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pabr_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (asymmetricCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pabr_AcceptedAsymmetricBranchingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness impliedLiteral implicationWitness implicationProof
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict asymmetricCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pabr_CheckerReplay asymmetricCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pabr_CheckerReplay asymmetricCertificate checkerAccepted)
    (fun _ledger _representative _coverage _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pabr_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (probingTrail : Prop) (probingLedger : Prop)
    (probingWitness : Prop)
    (impliedLiteral : Prop) (implicationWitness : Prop)
    (implicationProof : Prop)
    (deletedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (asymmetricCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pabr_AcceptedAsymmetricBranchingReplay
      originalCnf reducedCnf probingTrail probingLedger
      probingWitness impliedLiteral implicationWitness implicationProof
      deletedClause coveredClause coverageWitness reducedModel
      originalModel certificate conflict asymmetricCertificate
      checkerAccepted originalFingerprint reducedFingerprint
      fingerprintWitness baselineSolver baselineAvailable binaryFingerprint
      buildReproducible validatorAccepted validatorVersion auditAppended
      auditAppendOnly ->
    ay_pabr_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pabr_AuditEvidence auditAppended auditAppendOnly)
    (fun _ledger _representative _coverage _eq _model _proof _checker
      _fingerprint _fallback _build _validator audit => audit)

theorem ay_pabr_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pabr_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pabr_Sat reducedCnf reducedModel ->
    ay_pabr_Sat originalCnf originalModel := by
  intro reconstruct substitutedSat
  exact reconstruct substitutedSat

theorem ay_pabr_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pabr_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pabr_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pabr_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pabr_Sat originalCnf model ->
    ay_pabr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pabr_disj_left
    (ay_pabr_ExitCodeSound exitCode (ay_pabr_Sat originalCnf model))
    (ay_pabr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pabr_conj_intro exitCode
      (ay_pabr_Sat originalCnf model) exit sat)

theorem ay_pabr_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pabr_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pabr_disj_right
    (ay_pabr_ExitCodeSound exitCode (ay_pabr_Sat originalCnf model))
    (ay_pabr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pabr_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pabr_failure_implication_drift
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    implicationDrift ->
    ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro drift
  exact ay_pabr_disj_left implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))
    drift

theorem ay_pabr_failure_deletion_mismatch
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    deletionMismatch ->
    ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro mismatch
  exact ay_pabr_disj_right implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))
    (ay_pabr_disj_left deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay))
      mismatch)

theorem ay_pabr_failure_missing_coverage
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro missing
  exact ay_pabr_disj_right implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))
    (ay_pabr_disj_right deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay))
      (ay_pabr_disj_left missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)
        missing))

theorem ay_pabr_failure_stale_fingerprint
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    staleFingerprint ->
    ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro stale
  exact ay_pabr_disj_right implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))
    (ay_pabr_disj_right deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay))
      (ay_pabr_disj_right missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)
        (ay_pabr_disj_left staleFingerprint uncheckedReplay stale)))

theorem ay_pabr_failure_unchecked_replay
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay := by
  intro unchecked
  exact ay_pabr_disj_right implicationDrift
    (ay_pabr_Disj deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)))
    (ay_pabr_disj_right deletionMismatch
      (ay_pabr_Disj missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay))
      (ay_pabr_disj_right missingCoverage
        (ay_pabr_Disj staleFingerprint uncheckedReplay)
        (ay_pabr_disj_right staleFingerprint uncheckedReplay unchecked)))

theorem ay_pabr_diagnostic_no_claim
    (currentCnf : Prop)
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pabr_DiagnosticAsymmetricBranchingReplay
      currentCnf implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pabr_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pabr_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pabr_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pabr_diagnostic_recompute
    (currentCnf : Prop)
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pabr_DiagnosticAsymmetricBranchingReplay
      currentCnf implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic ->
    ay_pabr_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pabr_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pabr_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pabr_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (implicationDrift : Prop) (deletionMismatch : Prop)
    (missingCoverage : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pabr_RecomputeObligation currentCnf recompute ->
    ay_pabr_NoSemanticClaim diagnostic ->
    ay_pabr_DiagnosticAsymmetricBranchingReplay
      currentCnf implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pabr_conj_intro
    (ay_pabr_AsymmetricBranchingFailure
      implicationDrift deletionMismatch missingCoverage
      staleFingerprint uncheckedReplay)
    (ay_pabr_Conj
      (ay_pabr_RecomputeObligation currentCnf recompute)
      (ay_pabr_NoSemanticClaim diagnostic))
    (ay_pabr_failure_unchecked_replay
      implicationDrift deletionMismatch missingCoverage staleFingerprint
      uncheckedReplay unchecked)
    (ay_pabr_conj_intro
      (ay_pabr_RecomputeObligation currentCnf recompute)
      (ay_pabr_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
