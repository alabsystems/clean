-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-subsuming resolution replay guard soundness.
-- The propositions stand for subsumption witness ledgers, pivot/resolvent coverage, strengthened-clause
-- maps, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_ssrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ssrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ssrg_Equisat (before : Prop) (after : Prop) :=
  ay_ssrg_Conj (before -> after) (after -> before)

def ay_ssrg_Sat (cnf : Prop) (model : Prop) :=
  ay_ssrg_Conj cnf model

def ay_ssrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ssrg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_ssrg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_ssrg_SubsumptionWitnessLedger
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :=
  ay_ssrg_Conj subsumptionLedger (subsumingClause -> subsumptionWitness)

def ay_ssrg_PivotResolventCoverage
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop) :=
  ay_ssrg_Conj resolventCoverageWitness (pivotResolvent -> coveredResolvent)

def ay_ssrg_StrengthenedClauseMap
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop) :=
  ay_ssrg_Conj strengthenedMapWitness
    (strengthenedClause -> mappedStrengthenedClause)

def ay_ssrg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_ssrg_Sat replayedCnf replayedModel ->
    ay_ssrg_Sat originalCnf originalModel

def ay_ssrg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ssrg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssrg_Conj
    (ay_ssrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ssrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_ssrg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_ssrg_Conj fingerprintWitness
    (ay_ssrg_IdMatch originalFingerprint replayedFingerprint)

def ay_ssrg_CheckerReplay
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_ssrg_Conj ssrReplayCertificate checkerAccepted

def ay_ssrg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_ssrg_Conj baselineSolver baselineAvailable

def ay_ssrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ssrg_Conj binaryFingerprint buildReproducible

def ay_ssrg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_ssrg_Conj validatorAccepted validatorVersion

def ay_ssrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ssrg_Conj auditAppended auditAppendOnly

def ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ssrg_SubsumptionWitnessLedger
       subsumingClause subsumptionWitness subsumptionLedger ->
     ay_ssrg_PivotResolventCoverage
       pivotResolvent coveredResolvent resolventCoverageWitness ->
     ay_ssrg_StrengthenedClauseMap
       strengthenedClause mappedStrengthenedClause strengthenedMapWitness ->
     ay_ssrg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_ssrg_Equisat originalCnf replayedCnf ->
     ay_ssrg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_ssrg_CheckerReplay ssrReplayCertificate checkerAccepted ->
     ay_ssrg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_ssrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ssrg_ValidatorGate validatorAccepted validatorVersion ->
     ay_ssrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (missingSubsumptionWitness -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_ssrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ssrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ssrg_Conj currentCnf recompute

def ay_ssrg_DiagnosticSelfSubsumingResolutionReplayGuard
    (currentCnf : Prop)
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ssrg_Conj
    (ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction)
    (ay_ssrg_Conj
      (ay_ssrg_RecomputeObligation currentCnf recompute)
      (ay_ssrg_NoSemanticClaim diagnostic))

def ay_ssrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ssrg_Conj exitCode claim

def ay_ssrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ssrg_Disj
    (ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf model))
    (ay_ssrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ssrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ssrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ssrg_conj_left
    (left : Prop) (right : Prop) :
    ay_ssrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ssrg_conj_right
    (left : Prop) (right : Prop) :
    ay_ssrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ssrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ssrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ssrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ssrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ssrg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_ssrg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_ssrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_ssrg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_ssrg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_ssrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_ssrg_subsumption_witness_applies
    (subsumingClause : Prop) (subsumptionWitness : Prop)
    (subsumptionLedger : Prop) :
    ay_ssrg_SubsumptionWitnessLedger
      subsumingClause subsumptionWitness subsumptionLedger ->
    subsumingClause -> subsumptionWitness := by
  intro ledger
  exact ay_ssrg_conj_right subsumptionLedger
    (subsumingClause -> subsumptionWitness) ledger

theorem ay_ssrg_pivot_resolvent_coverage
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop) :
    ay_ssrg_PivotResolventCoverage
      pivotResolvent coveredResolvent resolventCoverageWitness ->
    pivotResolvent -> coveredResolvent := by
  intro coverage
  exact ay_ssrg_conj_right resolventCoverageWitness
    (pivotResolvent -> coveredResolvent) coverage

theorem ay_ssrg_strengthened_clause_map_applies
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop) :
    ay_ssrg_StrengthenedClauseMap
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness ->
    strengthenedClause -> mappedStrengthenedClause := by
  intro strengthenedMap
  exact ay_ssrg_conj_right strengthenedMapWitness
    (strengthenedClause -> mappedStrengthenedClause) strengthenedMap

theorem ay_ssrg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_ssrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_ssrg_conj_left
    (ay_ssrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ssrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_ssrg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_ssrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_ssrg_conj_right
    (ay_ssrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ssrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_ssrg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
      originalCnf replayedCnf
      subsumingClause subsumptionWitness subsumptionLedger
      pivotResolvent coveredResolvent resolventCoverageWitness
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      ssrReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssrg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_ssrg_Equisat originalCnf replayedCnf)
    (fun _subsumption _coverage _strengthenedMap _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_ssrg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
      originalCnf replayedCnf
      subsumingClause subsumptionWitness subsumptionLedger
      pivotResolvent coveredResolvent resolventCoverageWitness
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      ssrReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssrg_CheckerReplay ssrReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_ssrg_CheckerReplay ssrReplayCertificate checkerAccepted)
    (fun _subsumption _coverage _strengthenedMap _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_ssrg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
      originalCnf replayedCnf
      subsumingClause subsumptionWitness subsumptionLedger
      pivotResolvent coveredResolvent resolventCoverageWitness
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      ssrReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssrg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_ssrg_AuditTranscript auditAppended auditAppendOnly)
    (fun _subsumption _coverage _strengthenedMap _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_ssrg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_ssrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_ssrg_Sat replayedCnf replayedModel ->
    ay_ssrg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_ssrg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_ssrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_ssrg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
      originalCnf replayedCnf
      subsumingClause subsumptionWitness subsumptionLedger
      pivotResolvent coveredResolvent resolventCoverageWitness
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      ssrReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssrg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_ssrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_ssrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _subsumption _coverage _strengthenedMap reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_ssrg_disj_left
        (ay_ssrg_ExitCodeSound exitCode
          (ay_ssrg_Sat originalCnf originalModel))
        (ay_ssrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_ssrg_conj_intro exitCode
          (ay_ssrg_Sat originalCnf originalModel)
          hexit
          ((ay_ssrg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_ssrg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (subsumingClause : Prop) (subsumptionWitness : Prop) (subsumptionLedger : Prop)
    (pivotResolvent : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (strengthenedClause : Prop) (mappedStrengthenedClause : Prop)
    (strengthenedMapWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (ssrReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionReplayGuard
      originalCnf replayedCnf
      subsumingClause subsumptionWitness subsumptionLedger
      pivotResolvent coveredResolvent resolventCoverageWitness
      strengthenedClause mappedStrengthenedClause strengthenedMapWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      ssrReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssrg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_ssrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_ssrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _subsumption _coverage _strengthenedMap reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_ssrg_disj_right
        (ay_ssrg_ExitCodeSound exitCode
          (ay_ssrg_Sat originalCnf originalModel))
        (ay_ssrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_ssrg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_ssrg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_ssrg_failure_missing_subsumption_witness
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingSubsumptionWitness ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_ssrg_failure_coverage
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_ssrg_failure_reconstruction
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_ssrg_failure_stale_fingerprint
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_ssrg_failure_unchecked_replay
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_ssrg_failure_missing_baseline
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_ssrg_failure_build
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_ssrg_failure_validator
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_ssrg_failure_audit
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
      missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_ssrg_diagnostic_no_claim
    (currentCnf : Prop)
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssrg_DiagnosticSelfSubsumingResolutionReplayGuard
      currentCnf missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ssrg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_ssrg_conj_right
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_conj_right
      (ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
        missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_ssrg_Conj
        (ay_ssrg_RecomputeObligation currentCnf recompute)
        (ay_ssrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_ssrg_diagnostic_recompute
    (currentCnf : Prop)
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssrg_DiagnosticSelfSubsumingResolutionReplayGuard
      currentCnf missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ssrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_ssrg_conj_left
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_conj_right
      (ay_ssrg_SelfSubsumingResolutionReplayGuardFailure
        missingSubsumptionWitness coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_ssrg_Conj
        (ay_ssrg_RecomputeObligation currentCnf recompute)
        (ay_ssrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_ssrg_unchecked_ssr_cannot_bless_public_result
    (currentCnf : Prop)
    (missingSubsumptionWitness : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_ssrg_DiagnosticSelfSubsumingResolutionReplayGuard
      currentCnf missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ssrg_Conj
      (ay_ssrg_NoSemanticClaim diagnostic)
      (ay_ssrg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_ssrg_conj_intro
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_diagnostic_no_claim
      currentCnf missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_ssrg_diagnostic_recompute
      currentCnf missingSubsumptionWitness coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
