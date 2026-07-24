-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Occurrence-list epoch replay soundness for preprocessing. The
-- propositions stand for occurrence epoch ledgers, literal-to-clause coverage,
-- transform witness ledgers, affected-clause reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pole_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pole_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pole_Equisat (before : Prop) (after : Prop) :=
  ay_pole_Conj (before -> after) (after -> before)

def ay_pole_Sat (cnf : Prop) (model : Prop) :=
  ay_pole_Conj cnf model

def ay_pole_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pole_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pole_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pole_OccurrenceEpochLedger
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop) :=
  ay_pole_Conj epochWitness
    (occurrenceEpoch -> occurrenceLedger)

def ay_pole_LiteralClauseCoverage
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop) :=
  ay_pole_Conj literalCoverageWitness
    (ay_pole_Conj literalOccurrence coveredClause)

def ay_pole_TransformWitnessLedger
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pole_Conj transformLedger (transformedClause -> transformWitness)

def ay_pole_AffectedClauseReconstruction
    (reconstructionLedger : Prop) (occurrenceLedger : Prop)
    (reconstructionWitness : Prop) :=
  ay_pole_Conj reconstructionWitness
    (occurrenceLedger -> reconstructionLedger)

def ay_pole_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pole_Sat reducedCnf reducedModel ->
    ay_pole_Sat originalCnf originalModel

def ay_pole_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pole_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pole_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pole_Conj fingerprintWitness
    (ay_pole_IdMatch originalFingerprint reducedFingerprint)

def ay_pole_CheckerReplay
    (occurrenceCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pole_Conj occurrenceCertificate checkerAccepted

def ay_pole_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pole_Conj baselineSolver baselineAvailable

def ay_pole_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pole_Conj binaryFingerprint buildReproducible

def ay_pole_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pole_Conj validatorAccepted validatorVersion

def ay_pole_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pole_Conj auditAppended auditAppendOnly

def ay_pole_AcceptedOccurrenceListEpochReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop)
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop)
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (occurrenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pole_OccurrenceEpochLedger
       occurrenceEpoch occurrenceLedger epochWitness ->
     ay_pole_LiteralClauseCoverage
       literalOccurrence coveredClause literalCoverageWitness ->
     ay_pole_TransformWitnessLedger
       transformedClause transformWitness transformLedger ->
     ay_pole_AffectedClauseReconstruction
       reconstructionLedger occurrenceLedger reconstructionWitness ->
     ay_pole_Equisat originalCnf reducedCnf ->
     ay_pole_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pole_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pole_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pole_CheckerReplay
       occurrenceCertificate checkerAccepted ->
     ay_pole_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pole_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pole_ValidatorGate validatorAccepted validatorVersion ->
     ay_pole_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pole_OccurrenceListEpochFailure
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (epochDrift -> result) ->
    (staleOccurrenceList -> result) ->
    (transformWitnessMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pole_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pole_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pole_Conj currentCnf recompute

def ay_pole_DiagnosticOccurrenceListEpochReplay
    (currentCnf : Prop)
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pole_Conj
    (ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pole_Conj
      (ay_pole_RecomputeObligation currentCnf recompute)
      (ay_pole_NoSemanticClaim diagnostic))

def ay_pole_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pole_Conj exitCode claim

def ay_pole_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pole_Disj
    (ay_pole_ExitCodeSound exitCode (ay_pole_Sat originalCnf model))
    (ay_pole_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pole_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pole_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pole_conj_left
    (left : Prop) (right : Prop) :
    ay_pole_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pole_conj_right
    (left : Prop) (right : Prop) :
    ay_pole_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pole_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pole_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pole_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pole_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pole_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pole_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pole_conj_left (before -> after) (after -> before) eq

theorem ay_pole_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pole_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pole_conj_right (before -> after) (after -> before) eq

theorem ay_pole_occurrence_epoch_ledger_applies
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop) :
    ay_pole_OccurrenceEpochLedger
      occurrenceEpoch occurrenceLedger epochWitness ->
    occurrenceEpoch ->
    occurrenceLedger := by
  intro accepted raw
  exact
    (ay_pole_conj_right epochWitness
      (occurrenceEpoch -> occurrenceLedger) accepted) raw

theorem ay_pole_literal_clause_coverage_literal
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop) :
    ay_pole_LiteralClauseCoverage
      literalOccurrence coveredClause literalCoverageWitness ->
    literalOccurrence := by
  intro accepted
  exact accepted literalOccurrence
    (fun _ledger pair =>
      pair literalOccurrence
        (fun duplicate _tautology => duplicate))

theorem ay_pole_literal_clause_coverage_clause
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop) :
    ay_pole_LiteralClauseCoverage
      literalOccurrence coveredClause literalCoverageWitness ->
    coveredClause := by
  intro accepted
  exact accepted coveredClause
    (fun _ledger pair =>
      pair coveredClause
        (fun _duplicate tautology => tautology))

theorem ay_pole_transform_witness_ledger
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pole_TransformWitnessLedger
      transformedClause transformWitness transformLedger ->
    transformedClause ->
    transformWitness := by
  intro accepted original
  exact
    (ay_pole_conj_right transformLedger
      (transformedClause -> transformWitness) accepted) original

theorem ay_pole_affected_clause_reconstruction_records
    (reconstructionLedger : Prop) (occurrenceLedger : Prop)
    (reconstructionWitness : Prop) :
    ay_pole_AffectedClauseReconstruction
      reconstructionLedger occurrenceLedger reconstructionWitness ->
    occurrenceLedger ->
    reconstructionLedger := by
  intro accepted canonical
  exact
    (ay_pole_conj_right reconstructionWitness
      (occurrenceLedger -> reconstructionLedger) accepted) canonical

theorem ay_pole_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop)
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop)
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (occurrenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pole_AcceptedOccurrenceListEpochReplay
      originalCnf reducedCnf occurrenceEpoch occurrenceLedger
      epochWitness literalOccurrence coveredClause
      literalCoverageWitness transformedClause transformWitness transformLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness occurrenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pole_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pole_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pole_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop)
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop)
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (occurrenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pole_AcceptedOccurrenceListEpochReplay
      originalCnf reducedCnf occurrenceEpoch occurrenceLedger
      epochWitness literalOccurrence coveredClause
      literalCoverageWitness transformedClause transformWitness transformLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness occurrenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pole_CheckerReplay occurrenceCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pole_CheckerReplay occurrenceCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pole_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (occurrenceEpoch : Prop) (occurrenceLedger : Prop)
    (epochWitness : Prop)
    (literalOccurrence : Prop) (coveredClause : Prop)
    (literalCoverageWitness : Prop)
    (transformedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (occurrenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pole_AcceptedOccurrenceListEpochReplay
      originalCnf reducedCnf occurrenceEpoch occurrenceLedger
      epochWitness literalOccurrence coveredClause
      literalCoverageWitness transformedClause transformWitness transformLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness occurrenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pole_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pole_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pole_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pole_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pole_Sat reducedCnf reducedModel ->
    ay_pole_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pole_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pole_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pole_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pole_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pole_Sat originalCnf model ->
    ay_pole_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pole_disj_left
    (ay_pole_ExitCodeSound exitCode (ay_pole_Sat originalCnf model))
    (ay_pole_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pole_conj_intro exitCode
      (ay_pole_Sat originalCnf model) exit sat)

theorem ay_pole_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pole_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pole_disj_right
    (ay_pole_ExitCodeSound exitCode (ay_pole_Sat originalCnf model))
    (ay_pole_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pole_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pole_failure_epoch_drift
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    epochDrift ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hEpoch h

theorem ay_pole_failure_stale_occurrence_list
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleOccurrenceList ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleCandidate h

theorem ay_pole_failure_transform_witness_mismatch
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    transformWitnessMismatch ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_pole_failure_coverage_gap
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_pole_failure_reconstruction_gap
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pole_failure_stale_fingerprint
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleFingerprint h

theorem ay_pole_failure_unchecked_replay
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pole_failure_build_drift
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pole_failure_audit_contradiction
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pole_diagnostic_no_claim
    (currentCnf : Prop)
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pole_DiagnosticOccurrenceListEpochReplay
      currentCnf epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pole_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pole_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pole_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pole_diagnostic_recompute
    (currentCnf : Prop)
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pole_DiagnosticOccurrenceListEpochReplay
      currentCnf epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pole_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pole_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pole_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pole_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (epochDrift : Prop) (staleOccurrenceList : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pole_RecomputeObligation currentCnf recompute ->
    ay_pole_NoSemanticClaim diagnostic ->
    ay_pole_DiagnosticOccurrenceListEpochReplay
      currentCnf epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pole_conj_intro
    (ay_pole_OccurrenceListEpochFailure
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pole_Conj
      (ay_pole_RecomputeObligation currentCnf recompute)
      (ay_pole_NoSemanticClaim diagnostic))
    (ay_pole_failure_unchecked_replay
      epochDrift staleOccurrenceList transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_pole_conj_intro
      (ay_pole_RecomputeObligation currentCnf recompute)
      (ay_pole_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
