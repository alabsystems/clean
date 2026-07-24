-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-index epoch replay soundness for preprocessing. The
-- propositions stand for index epoch ledgers, candidate-clause coverage,
-- subsumption witness ledgers, affected-clause reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_psie_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psie_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_psie_Equisat (before : Prop) (after : Prop) :=
  ay_psie_Conj (before -> after) (after -> before)

def ay_psie_Sat (cnf : Prop) (model : Prop) :=
  ay_psie_Conj cnf model

def ay_psie_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_psie_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_psie_Conj (leftId -> rightId) (rightId -> leftId)

def ay_psie_IndexEpochLedger
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop) :=
  ay_psie_Conj epochWitness
    (indexEpoch -> indexLedger)

def ay_psie_CandidateClauseCoverage
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop) :=
  ay_psie_Conj candidateCoverageWitness
    (ay_psie_Conj candidateClause coveredCandidate)

def ay_psie_SubsumptionWitnessLedger
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :=
  ay_psie_Conj witnessLedger (subsumedClause -> subsumptionWitness)

def ay_psie_AffectedClauseReconstruction
    (reconstructionLedger : Prop) (indexLedger : Prop)
    (reconstructionWitness : Prop) :=
  ay_psie_Conj reconstructionWitness
    (indexLedger -> reconstructionLedger)

def ay_psie_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_psie_Sat reducedCnf reducedModel ->
    ay_psie_Sat originalCnf originalModel

def ay_psie_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_psie_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_psie_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psie_Conj fingerprintWitness
    (ay_psie_IdMatch originalFingerprint reducedFingerprint)

def ay_psie_CheckerReplay
    (subsumptionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_psie_Conj subsumptionCertificate checkerAccepted

def ay_psie_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_psie_Conj baselineSolver baselineAvailable

def ay_psie_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_psie_Conj binaryFingerprint buildReproducible

def ay_psie_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_psie_Conj validatorAccepted validatorVersion

def ay_psie_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_psie_Conj auditAppended auditAppendOnly

def ay_psie_AcceptedSubsumptionIndexEpochReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop)
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_psie_IndexEpochLedger
       indexEpoch indexLedger epochWitness ->
     ay_psie_CandidateClauseCoverage
       candidateClause coveredCandidate candidateCoverageWitness ->
     ay_psie_SubsumptionWitnessLedger
       subsumedClause subsumptionWitness witnessLedger ->
     ay_psie_AffectedClauseReconstruction
       reconstructionLedger indexLedger reconstructionWitness ->
     ay_psie_Equisat originalCnf reducedCnf ->
     ay_psie_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_psie_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_psie_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_psie_CheckerReplay
       subsumptionCertificate checkerAccepted ->
     ay_psie_FallbackBaseline baselineSolver baselineAvailable ->
     ay_psie_BuildEvidence binaryFingerprint buildReproducible ->
     ay_psie_ValidatorGate validatorAccepted validatorVersion ->
     ay_psie_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_psie_SubsumptionIndexEpochFailure
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (epochDrift -> result) ->
    (staleCandidateIndex -> result) ->
    (witnessMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_psie_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_psie_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_psie_Conj currentCnf recompute

def ay_psie_DiagnosticSubsumptionIndexEpochReplay
    (currentCnf : Prop)
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_psie_Conj
    (ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_psie_Conj
      (ay_psie_RecomputeObligation currentCnf recompute)
      (ay_psie_NoSemanticClaim diagnostic))

def ay_psie_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_psie_Conj exitCode claim

def ay_psie_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_psie_Disj
    (ay_psie_ExitCodeSound exitCode (ay_psie_Sat originalCnf model))
    (ay_psie_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_psie_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_psie_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_psie_conj_left
    (left : Prop) (right : Prop) :
    ay_psie_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_psie_conj_right
    (left : Prop) (right : Prop) :
    ay_psie_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_psie_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_psie_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_psie_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_psie_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_psie_equisat_forward
    (before : Prop) (after : Prop) :
    ay_psie_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_psie_conj_left (before -> after) (after -> before) eq

theorem ay_psie_equisat_backward
    (before : Prop) (after : Prop) :
    ay_psie_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_psie_conj_right (before -> after) (after -> before) eq

theorem ay_psie_index_epoch_ledger_applies
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop) :
    ay_psie_IndexEpochLedger
      indexEpoch indexLedger epochWitness ->
    indexEpoch ->
    indexLedger := by
  intro accepted raw
  exact
    (ay_psie_conj_right epochWitness
      (indexEpoch -> indexLedger) accepted) raw

theorem ay_psie_candidate_clause_coverage_forward
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop) :
    ay_psie_CandidateClauseCoverage
      candidateClause coveredCandidate candidateCoverageWitness ->
    candidateClause := by
  intro accepted
  exact accepted candidateClause
    (fun _ledger pair =>
      pair candidateClause
        (fun duplicate _tautology => duplicate))

theorem ay_psie_candidate_clause_coverage_backward
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop) :
    ay_psie_CandidateClauseCoverage
      candidateClause coveredCandidate candidateCoverageWitness ->
    coveredCandidate := by
  intro accepted
  exact accepted coveredCandidate
    (fun _ledger pair =>
      pair coveredCandidate
        (fun _duplicate tautology => tautology))

theorem ay_psie_subsumption_witness_ledger
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop) :
    ay_psie_SubsumptionWitnessLedger
      subsumedClause subsumptionWitness witnessLedger ->
    subsumedClause ->
    subsumptionWitness := by
  intro accepted original
  exact
    (ay_psie_conj_right witnessLedger
      (subsumedClause -> subsumptionWitness) accepted) original

theorem ay_psie_affected_clause_reconstruction_records
    (reconstructionLedger : Prop) (indexLedger : Prop)
    (reconstructionWitness : Prop) :
    ay_psie_AffectedClauseReconstruction
      reconstructionLedger indexLedger reconstructionWitness ->
    indexLedger ->
    reconstructionLedger := by
  intro accepted canonical
  exact
    (ay_psie_conj_right reconstructionWitness
      (indexLedger -> reconstructionLedger) accepted) canonical

theorem ay_psie_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop)
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psie_AcceptedSubsumptionIndexEpochReplay
      originalCnf reducedCnf indexEpoch indexLedger
      epochWitness candidateClause coveredCandidate
      candidateCoverageWitness subsumedClause subsumptionWitness witnessLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness subsumptionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psie_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_psie_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_psie_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop)
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psie_AcceptedSubsumptionIndexEpochReplay
      originalCnf reducedCnf indexEpoch indexLedger
      epochWitness candidateClause coveredCandidate
      candidateCoverageWitness subsumedClause subsumptionWitness witnessLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness subsumptionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psie_CheckerReplay subsumptionCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_psie_CheckerReplay subsumptionCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_psie_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (indexEpoch : Prop) (indexLedger : Prop)
    (epochWitness : Prop)
    (candidateClause : Prop) (coveredCandidate : Prop)
    (candidateCoverageWitness : Prop)
    (subsumedClause : Prop) (subsumptionWitness : Prop)
    (witnessLedger : Prop)
    (reconstructionLedger : Prop) (reconstructionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psie_AcceptedSubsumptionIndexEpochReplay
      originalCnf reducedCnf indexEpoch indexLedger
      epochWitness candidateClause coveredCandidate
      candidateCoverageWitness subsumedClause subsumptionWitness witnessLedger
      reconstructionLedger reconstructionWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness subsumptionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psie_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_psie_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_psie_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_psie_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_psie_Sat reducedCnf reducedModel ->
    ay_psie_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_psie_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_psie_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_psie_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_psie_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_psie_Sat originalCnf model ->
    ay_psie_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_psie_disj_left
    (ay_psie_ExitCodeSound exitCode (ay_psie_Sat originalCnf model))
    (ay_psie_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_psie_conj_intro exitCode
      (ay_psie_Sat originalCnf model) exit sat)

theorem ay_psie_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_psie_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_psie_disj_right
    (ay_psie_ExitCodeSound exitCode (ay_psie_Sat originalCnf model))
    (ay_psie_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_psie_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_psie_failure_epoch_drift
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    epochDrift ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hEpoch h

theorem ay_psie_failure_stale_candidate_index
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleCandidateIndex ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleCandidate h

theorem ay_psie_failure_witness_mismatch
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    witnessMismatch ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_psie_failure_coverage_gap
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_psie_failure_reconstruction_gap
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_psie_failure_stale_fingerprint
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleFingerprint h

theorem ay_psie_failure_unchecked_replay
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_psie_failure_build_drift
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_psie_failure_audit_contradiction
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_psie_diagnostic_no_claim
    (currentCnf : Prop)
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psie_DiagnosticSubsumptionIndexEpochReplay
      currentCnf epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_psie_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_psie_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_psie_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_psie_diagnostic_recompute
    (currentCnf : Prop)
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psie_DiagnosticSubsumptionIndexEpochReplay
      currentCnf epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_psie_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_psie_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_psie_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_psie_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (epochDrift : Prop) (staleCandidateIndex : Prop)
    (witnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_psie_RecomputeObligation currentCnf recompute ->
    ay_psie_NoSemanticClaim diagnostic ->
    ay_psie_DiagnosticSubsumptionIndexEpochReplay
      currentCnf epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_psie_conj_intro
    (ay_psie_SubsumptionIndexEpochFailure
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_psie_Conj
      (ay_psie_RecomputeObligation currentCnf recompute)
      (ay_psie_NoSemanticClaim diagnostic))
    (ay_psie_failure_unchecked_replay
      epochDrift staleCandidateIndex witnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_psie_conj_intro
      (ay_psie_RecomputeObligation currentCnf recompute)
      (ay_psie_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
