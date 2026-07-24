-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-elimination replay guard soundness.
-- The propositions stand for elimination witness ledgers, resolvent coverage, eliminated-variable
-- maps, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_veeg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_veeg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_veeg_Equisat (before : Prop) (after : Prop) :=
  ay_veeg_Conj (before -> after) (after -> before)

def ay_veeg_Sat (cnf : Prop) (model : Prop) :=
  ay_veeg_Conj cnf model

def ay_veeg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_veeg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_veeg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_veeg_EliminationWitnessLedger
    (eliminatedVariable : Prop) (eliminationWitness : Prop)
    (eliminationLedger : Prop) :=
  ay_veeg_Conj eliminationLedger (eliminatedVariable -> eliminationWitness)

def ay_veeg_EliminatedVariableMap
    (eliminatedVariable : Prop) (reconstructedVariable : Prop)
    (variableMapWitness : Prop) :=
  ay_veeg_Conj variableMapWitness
    (eliminatedVariable -> reconstructedVariable)

def ay_veeg_ResolventCoverage
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop) :=
  ay_veeg_Conj resolventCoverageWitness (resolventClause -> coveredResolvent)

def ay_veeg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_veeg_Sat replayedCnf replayedModel ->
    ay_veeg_Sat originalCnf originalModel

def ay_veeg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_veeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_veeg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_veeg_Conj
    (ay_veeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_veeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_veeg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_veeg_Conj fingerprintWitness
    (ay_veeg_IdMatch originalFingerprint replayedFingerprint)

def ay_veeg_CheckerReplay
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_veeg_Conj eliminationReplayCertificate checkerAccepted

def ay_veeg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_veeg_Conj baselineSolver baselineAvailable

def ay_veeg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_veeg_Conj binaryFingerprint buildReproducible

def ay_veeg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_veeg_Conj validatorAccepted validatorVersion

def ay_veeg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_veeg_Conj auditAppended auditAppendOnly

def ay_veeg_AcceptedVariableEliminationReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_veeg_EliminationWitnessLedger
       eliminatedVariable eliminationWitness eliminationLedger ->
     ay_veeg_EliminatedVariableMap
       eliminatedVariable reconstructedVariable variableMapWitness ->
     ay_veeg_ResolventCoverage
       resolventClause coveredResolvent resolventCoverageWitness ->
     ay_veeg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_veeg_Equisat originalCnf replayedCnf ->
     ay_veeg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_veeg_CheckerReplay eliminationReplayCertificate checkerAccepted ->
     ay_veeg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_veeg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_veeg_ValidatorGate validatorAccepted validatorVersion ->
     ay_veeg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_veeg_VariableEliminationReplayGuardFailure
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (missingEliminationWitness -> result) ->
    (variableMapMismatch -> result) ->
    (resolventCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_veeg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_veeg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_veeg_Conj currentCnf recompute

def ay_veeg_DiagnosticVariableEliminationReplayGuard
    (currentCnf : Prop)
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_veeg_Conj
    (ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure auditContradiction)
    (ay_veeg_Conj
      (ay_veeg_RecomputeObligation currentCnf recompute)
      (ay_veeg_NoSemanticClaim diagnostic))

def ay_veeg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_veeg_Conj exitCode claim

def ay_veeg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_veeg_Disj
    (ay_veeg_ExitCodeSound exitCode (ay_veeg_Sat originalCnf model))
    (ay_veeg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_veeg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_veeg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_veeg_conj_left
    (left : Prop) (right : Prop) :
    ay_veeg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_veeg_conj_right
    (left : Prop) (right : Prop) :
    ay_veeg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_veeg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_veeg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_veeg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_veeg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_veeg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_veeg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_veeg_conj_left (before -> after) (after -> before) eqsat

theorem ay_veeg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_veeg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_veeg_conj_right (before -> after) (after -> before) eqsat

theorem ay_veeg_elimination_witness_applies
    (eliminatedVariable : Prop) (eliminationWitness : Prop)
    (eliminationLedger : Prop) :
    ay_veeg_EliminationWitnessLedger
      eliminatedVariable eliminationWitness eliminationLedger ->
    eliminatedVariable -> eliminationWitness := by
  intro ledger
  exact ay_veeg_conj_right eliminationLedger
    (eliminatedVariable -> eliminationWitness) ledger

theorem ay_veeg_eliminated_variable_map_applies
    (eliminatedVariable : Prop) (reconstructedVariable : Prop)
    (variableMapWitness : Prop) :
    ay_veeg_EliminatedVariableMap
      eliminatedVariable reconstructedVariable variableMapWitness ->
    eliminatedVariable -> reconstructedVariable := by
  intro representativeMap
  exact ay_veeg_conj_right variableMapWitness
    (eliminatedVariable -> reconstructedVariable) representativeMap

theorem ay_veeg_resolvent_coverage
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop) :
    ay_veeg_ResolventCoverage
      resolventClause coveredResolvent resolventCoverageWitness ->
    resolventClause -> coveredResolvent := by
  intro coverage
  exact ay_veeg_conj_right resolventCoverageWitness
    (resolventClause -> coveredResolvent) coverage

theorem ay_veeg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_veeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_veeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_veeg_conj_left
    (ay_veeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_veeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_veeg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_veeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_veeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_veeg_conj_right
    (ay_veeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_veeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_veeg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_veeg_AcceptedVariableEliminationReplayGuard
      originalCnf replayedCnf
      eliminatedVariable eliminationWitness eliminationLedger
      reconstructedVariable variableMapWitness
      resolventClause coveredResolvent resolventCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      eliminationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_veeg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_veeg_Equisat originalCnf replayedCnf)
    (fun _equivalence _representativeMap _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_veeg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_veeg_AcceptedVariableEliminationReplayGuard
      originalCnf replayedCnf
      eliminatedVariable eliminationWitness eliminationLedger
      reconstructedVariable variableMapWitness
      resolventClause coveredResolvent resolventCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      eliminationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_veeg_CheckerReplay eliminationReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_veeg_CheckerReplay eliminationReplayCertificate checkerAccepted)
    (fun _equivalence _representativeMap _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_veeg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_veeg_AcceptedVariableEliminationReplayGuard
      originalCnf replayedCnf
      eliminatedVariable eliminationWitness eliminationLedger
      reconstructedVariable variableMapWitness
      resolventClause coveredResolvent resolventCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      eliminationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_veeg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_veeg_AuditTranscript auditAppended auditAppendOnly)
    (fun _equivalence _representativeMap _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_veeg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_veeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_veeg_Sat replayedCnf replayedModel ->
    ay_veeg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_veeg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_veeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_veeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_veeg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_veeg_AcceptedVariableEliminationReplayGuard
      originalCnf replayedCnf
      eliminatedVariable eliminationWitness eliminationLedger
      reconstructedVariable variableMapWitness
      resolventClause coveredResolvent resolventCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      eliminationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_veeg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_veeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_veeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equivalence _representativeMap _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_veeg_disj_left
        (ay_veeg_ExitCodeSound exitCode
          (ay_veeg_Sat originalCnf originalModel))
        (ay_veeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_veeg_conj_intro exitCode
          (ay_veeg_Sat originalCnf originalModel)
          hexit
          ((ay_veeg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_veeg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (eliminationWitness : Prop) (eliminationLedger : Prop)
    (reconstructedVariable : Prop) (variableMapWitness : Prop)
    (resolventClause : Prop) (coveredResolvent : Prop)
    (resolventCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (eliminationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_veeg_AcceptedVariableEliminationReplayGuard
      originalCnf replayedCnf
      eliminatedVariable eliminationWitness eliminationLedger
      reconstructedVariable variableMapWitness
      resolventClause coveredResolvent resolventCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      eliminationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_veeg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_veeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_veeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equivalence _representativeMap _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_veeg_disj_right
        (ay_veeg_ExitCodeSound exitCode
          (ay_veeg_Sat originalCnf originalModel))
        (ay_veeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_veeg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_veeg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_veeg_failure_missing_elimination_witness
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingEliminationWitness ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_veeg_failure_eliminated_variable_map
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    variableMapMismatch ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case representative_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact representative_case failure

theorem ay_veeg_failure_coverage
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    resolventCoverageGap ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_veeg_failure_reconstruction
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_veeg_failure_stale_fingerprint
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_veeg_failure_unchecked_replay
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_veeg_failure_missing_baseline
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_veeg_failure_build
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_veeg_failure_validator
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_veeg_failure_audit
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_veeg_VariableEliminationReplayGuardFailure
      missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_veeg_diagnostic_no_claim
    (currentCnf : Prop)
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_veeg_DiagnosticVariableEliminationReplayGuard
      currentCnf missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_veeg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_veeg_conj_right
    (ay_veeg_RecomputeObligation currentCnf recompute)
    (ay_veeg_NoSemanticClaim diagnostic)
    (ay_veeg_conj_right
      (ay_veeg_VariableEliminationReplayGuardFailure
        missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_veeg_Conj
        (ay_veeg_RecomputeObligation currentCnf recompute)
        (ay_veeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_veeg_diagnostic_recompute
    (currentCnf : Prop)
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_veeg_DiagnosticVariableEliminationReplayGuard
      currentCnf missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_veeg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_veeg_conj_left
    (ay_veeg_RecomputeObligation currentCnf recompute)
    (ay_veeg_NoSemanticClaim diagnostic)
    (ay_veeg_conj_right
      (ay_veeg_VariableEliminationReplayGuardFailure
        missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_veeg_Conj
        (ay_veeg_RecomputeObligation currentCnf recompute)
        (ay_veeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_veeg_unchecked_elimination_cannot_bless_public_result
    (currentCnf : Prop)
    (missingEliminationWitness : Prop) (variableMapMismatch : Prop)
    (resolventCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_veeg_DiagnosticVariableEliminationReplayGuard
      currentCnf missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_veeg_Conj
      (ay_veeg_NoSemanticClaim diagnostic)
      (ay_veeg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_veeg_conj_intro
    (ay_veeg_NoSemanticClaim diagnostic)
    (ay_veeg_RecomputeObligation currentCnf recompute)
    (ay_veeg_diagnostic_no_claim
      currentCnf missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_veeg_diagnostic_recompute
      currentCnf missingEliminationWitness variableMapMismatch resolventCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
