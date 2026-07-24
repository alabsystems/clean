-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- XOR/Gaussian-elimination replay guard soundness.
-- The propositions stand for XOR-system manifests, pivot/elimination witnesses,
-- auxiliary variable maps, affected-clause coverage, reconstruction hooks,
-- fingerprints, checker replay, fallback/build/validator gates, audit evidence,
-- diagnostics, and public SAT/UNSAT reports.

def ay_pxge_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pxge_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pxge_Equisat (before : Prop) (after : Prop) :=
  ay_pxge_Conj (before -> after) (after -> before)

def ay_pxge_Sat (cnf : Prop) (model : Prop) :=
  ay_pxge_Conj cnf model

def ay_pxge_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pxge_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pxge_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pxge_XorSystemManifest
    (xorSystem : Prop) (encodedSystem : Prop)
    (systemManifest : Prop) :=
  ay_pxge_Conj systemManifest (xorSystem -> encodedSystem)

def ay_pxge_PivotEliminationWitnessLedger
    (pivotRows : Prop) (eliminationWitness : Prop)
    (pivotLedger : Prop) :=
  ay_pxge_Conj pivotLedger (pivotRows -> eliminationWitness)

def ay_pxge_AuxVariableMap
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop) :=
  ay_pxge_Conj mapWitness (auxiliaryVariables -> encodedVariables)

def ay_pxge_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pxge_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pxge_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pxge_Sat replayedCnf replayedModel ->
    ay_pxge_Sat originalCnf originalModel

def ay_pxge_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pxge_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pxge_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pxge_Conj fingerprintWitness
    (ay_pxge_IdMatch originalFingerprint replayedFingerprint)

def ay_pxge_CheckerReplay
    (xorReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pxge_Conj xorReplayCertificate checkerAccepted

def ay_pxge_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pxge_Conj baselineSolver baselineAvailable

def ay_pxge_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pxge_Conj binaryFingerprint buildReproducible

def ay_pxge_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pxge_Conj validatorAccepted validatorVersion

def ay_pxge_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pxge_Conj auditAppended auditAppendOnly

def ay_pxge_AcceptedXorGaussianEliminationReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pxge_XorSystemManifest xorSystem encodedSystem systemManifest ->
     ay_pxge_PivotEliminationWitnessLedger
       pivotRows eliminationWitness pivotLedger ->
     ay_pxge_AuxVariableMap
       auxiliaryVariables encodedVariables mapWitness ->
     ay_pxge_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pxge_Equisat originalCnf replayedCnf ->
     ay_pxge_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_pxge_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_pxge_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pxge_CheckerReplay xorReplayCertificate checkerAccepted ->
     ay_pxge_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pxge_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pxge_ValidatorGate validatorAccepted validatorVersion ->
     ay_pxge_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pxge_XorGaussianEliminationReplayGuardFailure
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :=
  forall result : Prop,
    (systemFailure -> result) ->
    (pivotFailure -> result) ->
    (mapFailure -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pxge_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pxge_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pxge_Conj currentCnf recompute

def ay_pxge_DiagnosticXorGaussianEliminationReplayGuard
    (currentCnf : Prop)
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pxge_Conj
    (ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction)
    (ay_pxge_Conj
      (ay_pxge_RecomputeObligation currentCnf recompute)
      (ay_pxge_NoSemanticClaim diagnostic))

def ay_pxge_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pxge_Conj exitCode claim

def ay_pxge_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pxge_Disj
    (ay_pxge_ExitCodeSound exitCode (ay_pxge_Sat originalCnf model))
    (ay_pxge_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pxge_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pxge_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pxge_conj_left
    (left : Prop) (right : Prop) :
    ay_pxge_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pxge_conj_right
    (left : Prop) (right : Prop) :
    ay_pxge_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pxge_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pxge_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pxge_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pxge_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pxge_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pxge_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_pxge_conj_left (before -> after) (after -> before) eqsat

theorem ay_pxge_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pxge_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_pxge_conj_right (before -> after) (after -> before) eqsat

theorem ay_pxge_xor_system_manifest_applies
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop) :
    ay_pxge_XorSystemManifest xorSystem encodedSystem systemManifest ->
    xorSystem -> encodedSystem := by
  intro manifest
  exact ay_pxge_conj_right systemManifest
    (xorSystem -> encodedSystem) manifest

theorem ay_pxge_pivot_elimination_witness_ledger
    (pivotRows : Prop) (eliminationWitness : Prop)
    (pivotLedger : Prop) :
    ay_pxge_PivotEliminationWitnessLedger
      pivotRows eliminationWitness pivotLedger ->
    pivotRows -> eliminationWitness := by
  intro ledger
  exact ay_pxge_conj_right pivotLedger
    (pivotRows -> eliminationWitness) ledger

theorem ay_pxge_aux_variable_map_applies
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop) :
    ay_pxge_AuxVariableMap auxiliaryVariables encodedVariables mapWitness ->
    auxiliaryVariables -> encodedVariables := by
  intro auxMap
  exact ay_pxge_conj_right mapWitness
    (auxiliaryVariables -> encodedVariables) auxMap

theorem ay_pxge_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pxge_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause -> coveredClause := by
  intro coverage
  exact ay_pxge_conj_right coverageWitness
    (affectedClause -> coveredClause) coverage

theorem ay_pxge_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pxge_AcceptedXorGaussianEliminationReplayGuard
      originalCnf replayedCnf
      xorSystem encodedSystem systemManifest
      pivotRows eliminationWitness pivotLedger
      auxiliaryVariables encodedVariables mapWitness
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pxge_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pxge_Equisat originalCnf replayedCnf)
    (fun _system _pivot _map _coverage eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator _audit => eqsat)

theorem ay_pxge_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pxge_AcceptedXorGaussianEliminationReplayGuard
      originalCnf replayedCnf
      xorSystem encodedSystem systemManifest
      pivotRows eliminationWitness pivotLedger
      auxiliaryVariables encodedVariables mapWitness
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pxge_CheckerReplay xorReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pxge_CheckerReplay xorReplayCertificate checkerAccepted)
    (fun _system _pivot _map _coverage _eqsat _modelRecon _proofRecon
      _fingerprints checker _fallback _build _validator _audit => checker)

theorem ay_pxge_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pxge_AcceptedXorGaussianEliminationReplayGuard
      originalCnf replayedCnf
      xorSystem encodedSystem systemManifest
      pivotRows eliminationWitness pivotLedger
      auxiliaryVariables encodedVariables mapWitness
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pxge_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pxge_AuditEvidence auditAppended auditAppendOnly)
    (fun _system _pivot _map _coverage _eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator audit => audit)

theorem ay_pxge_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pxge_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pxge_Sat replayedCnf replayedModel ->
    ay_pxge_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pxge_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pxge_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pxge_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_pxge_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pxge_AcceptedXorGaussianEliminationReplayGuard
      originalCnf replayedCnf
      xorSystem encodedSystem systemManifest
      pivotRows eliminationWitness pivotLedger
      auxiliaryVariables encodedVariables mapWitness
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pxge_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_pxge_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_pxge_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _system _pivot _map _coverage _eqsat modelRecon
      _proofRecon _fingerprints _checker _fallback _build _validator _audit =>
      ay_pxge_disj_left
        (ay_pxge_ExitCodeSound exitCode
          (ay_pxge_Sat originalCnf originalModel))
        (ay_pxge_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pxge_conj_intro exitCode
          (ay_pxge_Sat originalCnf originalModel)
          hexit (modelRecon replayedSat)))

theorem ay_pxge_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorSystem : Prop) (encodedSystem : Prop) (systemManifest : Prop)
    (pivotRows : Prop) (eliminationWitness : Prop) (pivotLedger : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop) (mapWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop) (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pxge_AcceptedXorGaussianEliminationReplayGuard
      originalCnf replayedCnf
      xorSystem encodedSystem systemManifest
      pivotRows eliminationWitness pivotLedger
      auxiliaryVariables encodedVariables mapWitness
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pxge_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_pxge_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_pxge_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _system _pivot _map _coverage _eqsat _modelRecon proofRecon
      _fingerprints _checker _fallback _build _validator _audit =>
      ay_pxge_disj_right
        (ay_pxge_ExitCodeSound exitCode
          (ay_pxge_Sat originalCnf originalModel))
        (ay_pxge_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pxge_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit (proofRecon replayedReplay)))

theorem ay_pxge_failure_system
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    systemFailure ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result system_case _pivot_case _map_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact system_case failure

theorem ay_pxge_failure_pivot
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    pivotFailure ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case pivot_case _map_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact pivot_case failure

theorem ay_pxge_failure_map
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    mapFailure ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case map_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact map_case failure

theorem ay_pxge_failure_coverage
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    coverageGap ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact coverage_case failure

theorem ay_pxge_failure_reconstruction
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case _coverage_case
    reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact reconstruction_case failure

theorem ay_pxge_failure_stale_fingerprint
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case _coverage_case
    _reconstruction_case fingerprint_case _replay_case _build_case _audit_case
  exact fingerprint_case failure

theorem ay_pxge_failure_unchecked_replay
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case _coverage_case
    _reconstruction_case _fingerprint_case replay_case _build_case _audit_case
  exact replay_case failure

theorem ay_pxge_failure_build
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    buildDrift ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case build_case _audit_case
  exact build_case failure

theorem ay_pxge_failure_audit
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    auditContradiction ->
    ay_pxge_XorGaussianEliminationReplayGuardFailure
      systemFailure pivotFailure mapFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _system_case _pivot_case _map_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case audit_case
  exact audit_case failure

theorem ay_pxge_diagnostic_no_claim
    (currentCnf : Prop)
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pxge_DiagnosticXorGaussianEliminationReplayGuard
      currentCnf systemFailure pivotFailure mapFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pxge_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_pxge_conj_right
    (ay_pxge_RecomputeObligation currentCnf recompute)
    (ay_pxge_NoSemanticClaim diagnostic)
    (ay_pxge_conj_right
      (ay_pxge_XorGaussianEliminationReplayGuardFailure
        systemFailure pivotFailure mapFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pxge_Conj
        (ay_pxge_RecomputeObligation currentCnf recompute)
        (ay_pxge_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pxge_diagnostic_recompute
    (currentCnf : Prop)
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pxge_DiagnosticXorGaussianEliminationReplayGuard
      currentCnf systemFailure pivotFailure mapFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pxge_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_pxge_conj_left
    (ay_pxge_RecomputeObligation currentCnf recompute)
    (ay_pxge_NoSemanticClaim diagnostic)
    (ay_pxge_conj_right
      (ay_pxge_XorGaussianEliminationReplayGuardFailure
        systemFailure pivotFailure mapFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pxge_Conj
        (ay_pxge_RecomputeObligation currentCnf recompute)
        (ay_pxge_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pxge_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (systemFailure : Prop) (pivotFailure : Prop) (mapFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pxge_DiagnosticXorGaussianEliminationReplayGuard
      currentCnf systemFailure pivotFailure mapFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pxge_Conj
      (ay_pxge_NoSemanticClaim diagnostic)
      (ay_pxge_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_pxge_conj_intro
    (ay_pxge_NoSemanticClaim diagnostic)
    (ay_pxge_RecomputeObligation currentCnf recompute)
    (ay_pxge_diagnostic_no_claim
      currentCnf systemFailure pivotFailure mapFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
    (ay_pxge_diagnostic_recompute
      currentCnf systemFailure pivotFailure mapFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
