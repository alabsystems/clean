-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Binary-implication-graph epoch replay soundness for preprocessing. The
-- propositions stand for graph epoch ledgers, binary-clause coverage,
-- implication witness ledgers, affected-clause reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pbig_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pbig_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pbig_Equisat (before : Prop) (after : Prop) :=
  ay_pbig_Conj (before -> after) (after -> before)

def ay_pbig_Sat (cnf : Prop) (model : Prop) :=
  ay_pbig_Conj cnf model

def ay_pbig_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pbig_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pbig_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pbig_GraphEpochLedger
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop) :=
  ay_pbig_Conj epochWitness
    (graphEpoch -> graphLedger)

def ay_pbig_BinaryClauseCoverage
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop) :=
  ay_pbig_Conj binaryCoverageWitness
    (ay_pbig_Conj binaryClause coveredBinaryClause)

def ay_pbig_ImplicationWitnessLedger
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop) :=
  ay_pbig_Conj implicationLedger (affectedClause -> implicationWitness)

def ay_pbig_AffectedClauseReconstruction
    (reconstructionLedger : Prop) (graphLedger : Prop)
    (reconstructionWitness : Prop) :=
  ay_pbig_Conj reconstructionWitness
    (graphLedger -> reconstructionLedger)

def ay_pbig_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pbig_Sat reducedCnf reducedModel ->
    ay_pbig_Sat originalCnf originalModel

def ay_pbig_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbig_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbig_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbig_Conj fingerprintWitness
    (ay_pbig_IdMatch originalFingerprint reducedFingerprint)

def ay_pbig_CheckerReplay
    (bigCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbig_Conj bigCertificate checkerAccepted

def ay_pbig_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pbig_Conj baselineSolver baselineAvailable

def ay_pbig_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pbig_Conj binaryFingerprint buildReproducible

def ay_pbig_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pbig_Conj validatorAccepted validatorVersion

def ay_pbig_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pbig_Conj auditAppended auditAppendOnly

def ay_pbig_AcceptedBinaryImplicationGraphEpochReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop)
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop)
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bigCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbig_GraphEpochLedger
       graphEpoch graphLedger epochWitness ->
     ay_pbig_BinaryClauseCoverage
       binaryClause coveredBinaryClause binaryCoverageWitness ->
     ay_pbig_ImplicationWitnessLedger
       affectedClause implicationWitness implicationLedger ->
     ay_pbig_AffectedClauseReconstruction
       reconstructionLedger graphLedger reconstructionWitness ->
     ay_pbig_Equisat originalCnf reducedCnf ->
     ay_pbig_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pbig_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pbig_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pbig_CheckerReplay
       bigCertificate checkerAccepted ->
     ay_pbig_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbig_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbig_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbig_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pbig_BinaryImplicationGraphEpochFailure
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (graphEpochDrift -> result) ->
    (coveredBinaryClauseMismatch -> result) ->
    (implicationWitnessMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pbig_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbig_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbig_Conj currentCnf recompute

def ay_pbig_DiagnosticBinaryImplicationGraphEpochReplay
    (currentCnf : Prop)
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbig_Conj
    (ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pbig_Conj
      (ay_pbig_RecomputeObligation currentCnf recompute)
      (ay_pbig_NoSemanticClaim diagnostic))

def ay_pbig_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pbig_Conj exitCode claim

def ay_pbig_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pbig_Disj
    (ay_pbig_ExitCodeSound exitCode (ay_pbig_Sat originalCnf model))
    (ay_pbig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pbig_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pbig_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbig_conj_left
    (left : Prop) (right : Prop) :
    ay_pbig_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbig_conj_right
    (left : Prop) (right : Prop) :
    ay_pbig_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbig_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pbig_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbig_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pbig_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbig_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pbig_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbig_conj_left (before -> after) (after -> before) eq

theorem ay_pbig_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pbig_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbig_conj_right (before -> after) (after -> before) eq

theorem ay_pbig_graph_epoch_ledger_applies
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop) :
    ay_pbig_GraphEpochLedger
      graphEpoch graphLedger epochWitness ->
    graphEpoch ->
    graphLedger := by
  intro accepted raw
  exact
    (ay_pbig_conj_right epochWitness
      (graphEpoch -> graphLedger) accepted) raw

theorem ay_pbig_binary_clause_coverage_clause
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop) :
    ay_pbig_BinaryClauseCoverage
      binaryClause coveredBinaryClause binaryCoverageWitness ->
    binaryClause := by
  intro accepted
  exact accepted binaryClause
    (fun _ledger pair =>
      pair binaryClause
        (fun duplicate _tautology => duplicate))

theorem ay_pbig_binary_clause_coverage_covered
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop) :
    ay_pbig_BinaryClauseCoverage
      binaryClause coveredBinaryClause binaryCoverageWitness ->
    coveredBinaryClause := by
  intro accepted
  exact accepted coveredBinaryClause
    (fun _ledger pair =>
      pair coveredBinaryClause
        (fun _duplicate tautology => tautology))

theorem ay_pbig_implication_witness_ledger
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop) :
    ay_pbig_ImplicationWitnessLedger
      affectedClause implicationWitness implicationLedger ->
    affectedClause ->
    implicationWitness := by
  intro accepted original
  exact
    (ay_pbig_conj_right implicationLedger
      (affectedClause -> implicationWitness) accepted) original

theorem ay_pbig_affected_clause_reconstruction_records
    (reconstructionLedger : Prop) (graphLedger : Prop)
    (reconstructionWitness : Prop) :
    ay_pbig_AffectedClauseReconstruction
      reconstructionLedger graphLedger reconstructionWitness ->
    graphLedger ->
    reconstructionLedger := by
  intro accepted canonical
  exact
    (ay_pbig_conj_right reconstructionWitness
      (graphLedger -> reconstructionLedger) accepted) canonical

theorem ay_pbig_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop)
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop)
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bigCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbig_AcceptedBinaryImplicationGraphEpochReplay
      originalCnf reducedCnf graphEpoch graphLedger
      epochWitness binaryClause coveredBinaryClause
      binaryCoverageWitness affectedClause implicationWitness implicationLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness bigCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbig_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pbig_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pbig_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop)
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop)
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bigCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbig_AcceptedBinaryImplicationGraphEpochReplay
      originalCnf reducedCnf graphEpoch graphLedger
      epochWitness binaryClause coveredBinaryClause
      binaryCoverageWitness affectedClause implicationWitness implicationLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness bigCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbig_CheckerReplay bigCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pbig_CheckerReplay bigCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pbig_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (graphEpoch : Prop) (graphLedger : Prop)
    (epochWitness : Prop)
    (binaryClause : Prop) (coveredBinaryClause : Prop)
    (binaryCoverageWitness : Prop)
    (affectedClause : Prop) (implicationWitness : Prop)
    (implicationLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bigCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbig_AcceptedBinaryImplicationGraphEpochReplay
      originalCnf reducedCnf graphEpoch graphLedger
      epochWitness binaryClause coveredBinaryClause
      binaryCoverageWitness affectedClause implicationWitness implicationLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness bigCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbig_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbig_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pbig_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pbig_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pbig_Sat reducedCnf reducedModel ->
    ay_pbig_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pbig_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbig_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pbig_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pbig_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pbig_Sat originalCnf model ->
    ay_pbig_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pbig_disj_left
    (ay_pbig_ExitCodeSound exitCode (ay_pbig_Sat originalCnf model))
    (ay_pbig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbig_conj_intro exitCode
      (ay_pbig_Sat originalCnf model) exit sat)

theorem ay_pbig_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pbig_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pbig_disj_right
    (ay_pbig_ExitCodeSound exitCode (ay_pbig_Sat originalCnf model))
    (ay_pbig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbig_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pbig_failure_graph_epoch_drift
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    graphEpochDrift ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hEpoch h

theorem ay_pbig_failure_binary_coverage_gap
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coveredBinaryClauseMismatch ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleCandidate h

theorem ay_pbig_failure_implication_witness_mismatch
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    implicationWitnessMismatch ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_pbig_failure_coverage_gap
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_pbig_failure_reconstruction_gap
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pbig_failure_stale_fingerprint
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleFingerprint h

theorem ay_pbig_failure_unchecked_replay
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pbig_failure_build_drift
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pbig_failure_audit_contradiction
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pbig_diagnostic_no_claim
    (currentCnf : Prop)
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbig_DiagnosticBinaryImplicationGraphEpochReplay
      currentCnf graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pbig_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbig_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pbig_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pbig_diagnostic_recompute
    (currentCnf : Prop)
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbig_DiagnosticBinaryImplicationGraphEpochReplay
      currentCnf graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pbig_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbig_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pbig_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pbig_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (graphEpochDrift : Prop) (coveredBinaryClauseMismatch : Prop)
    (implicationWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbig_RecomputeObligation currentCnf recompute ->
    ay_pbig_NoSemanticClaim diagnostic ->
    ay_pbig_DiagnosticBinaryImplicationGraphEpochReplay
      currentCnf graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pbig_conj_intro
    (ay_pbig_BinaryImplicationGraphEpochFailure
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pbig_Conj
      (ay_pbig_RecomputeObligation currentCnf recompute)
      (ay_pbig_NoSemanticClaim diagnostic))
    (ay_pbig_failure_unchecked_replay
      graphEpochDrift coveredBinaryClauseMismatch implicationWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_pbig_conj_intro
      (ay_pbig_RecomputeObligation currentCnf recompute)
      (ay_pbig_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
