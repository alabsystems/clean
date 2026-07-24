-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cardinality/PB expansion replay guard soundness.
-- The propositions stand for expansion manifests, auxiliary variable maps,
-- transform witnesses, affected-clause coverage, reconstruction hooks,
-- fingerprints, checker replay, fallback/build/validator gates, audit evidence,
-- diagnostics, and public SAT/UNSAT reports.

def ay_pcce_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcce_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcce_Equisat (before : Prop) (after : Prop) :=
  ay_pcce_Conj (before -> after) (after -> before)

def ay_pcce_Sat (cnf : Prop) (model : Prop) :=
  ay_pcce_Conj cnf model

def ay_pcce_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcce_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcce_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcce_ExpansionManifest
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop) :=
  ay_pcce_Conj expansionManifest
    (cardinalityConstraint -> expandedClauses)

def ay_pcce_AuxVariableMap
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop) :=
  ay_pcce_Conj mapWitness (auxiliaryVariables -> encodedVariables)

def ay_pcce_TransformWitnessLedger
    (expandedClauses : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pcce_Conj transformLedger (expandedClauses -> transformWitness)

def ay_pcce_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pcce_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pcce_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pcce_Sat replayedCnf replayedModel ->
    ay_pcce_Sat originalCnf originalModel

def ay_pcce_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcce_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pcce_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcce_Conj fingerprintWitness
    (ay_pcce_IdMatch originalFingerprint replayedFingerprint)

def ay_pcce_CheckerReplay
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pcce_Conj expansionReplayCertificate checkerAccepted

def ay_pcce_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pcce_Conj baselineSolver baselineAvailable

def ay_pcce_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pcce_Conj binaryFingerprint buildReproducible

def ay_pcce_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pcce_Conj validatorAccepted validatorVersion

def ay_pcce_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pcce_Conj auditAppended auditAppendOnly

def ay_pcce_AcceptedCardinalityExpansionReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pcce_ExpansionManifest
       cardinalityConstraint expandedClauses expansionManifest ->
     ay_pcce_AuxVariableMap
       auxiliaryVariables encodedVariables mapWitness ->
     ay_pcce_TransformWitnessLedger
       expandedClauses transformWitness transformLedger ->
     ay_pcce_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pcce_Equisat originalCnf replayedCnf ->
     ay_pcce_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_pcce_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_pcce_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pcce_CheckerReplay expansionReplayCertificate checkerAccepted ->
     ay_pcce_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pcce_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pcce_ValidatorGate validatorAccepted validatorVersion ->
     ay_pcce_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pcce_CardinalityExpansionReplayGuardFailure
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (expansionFailure -> result) ->
    (mapFailure -> result) ->
    (witnessFailure -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pcce_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcce_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcce_Conj currentCnf recompute

def ay_pcce_DiagnosticCardinalityExpansionReplayGuard
    (currentCnf : Prop)
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcce_Conj
    (ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction)
    (ay_pcce_Conj
      (ay_pcce_RecomputeObligation currentCnf recompute)
      (ay_pcce_NoSemanticClaim diagnostic))

def ay_pcce_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcce_Conj exitCode claim

def ay_pcce_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcce_Disj
    (ay_pcce_ExitCodeSound exitCode (ay_pcce_Sat originalCnf model))
    (ay_pcce_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pcce_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcce_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcce_conj_left
    (left : Prop) (right : Prop) :
    ay_pcce_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcce_conj_right
    (left : Prop) (right : Prop) :
    ay_pcce_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcce_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcce_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcce_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcce_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcce_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcce_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_pcce_conj_left (before -> after) (after -> before) eqsat

theorem ay_pcce_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcce_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_pcce_conj_right (before -> after) (after -> before) eqsat

theorem ay_pcce_expansion_manifest_applies
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop) :
    ay_pcce_ExpansionManifest
      cardinalityConstraint expandedClauses expansionManifest ->
    cardinalityConstraint -> expandedClauses := by
  intro manifest
  exact ay_pcce_conj_right expansionManifest
    (cardinalityConstraint -> expandedClauses) manifest

theorem ay_pcce_aux_variable_map_applies
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop) :
    ay_pcce_AuxVariableMap auxiliaryVariables encodedVariables mapWitness ->
    auxiliaryVariables -> encodedVariables := by
  intro auxMap
  exact ay_pcce_conj_right mapWitness
    (auxiliaryVariables -> encodedVariables) auxMap

theorem ay_pcce_transform_witness_ledger
    (expandedClauses : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pcce_TransformWitnessLedger
      expandedClauses transformWitness transformLedger ->
    expandedClauses -> transformWitness := by
  intro ledger
  exact ay_pcce_conj_right transformLedger
    (expandedClauses -> transformWitness) ledger

theorem ay_pcce_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pcce_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause -> coveredClause := by
  intro coverage
  exact ay_pcce_conj_right coverageWitness
    (affectedClause -> coveredClause) coverage

theorem ay_pcce_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcce_AcceptedCardinalityExpansionReplayGuard
      originalCnf replayedCnf
      cardinalityConstraint expandedClauses expansionManifest
      auxiliaryVariables encodedVariables mapWitness
      transformWitness transformLedger
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      expansionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcce_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pcce_Equisat originalCnf replayedCnf)
    (fun _manifest _map _transform _coverage eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator _audit => eqsat)

theorem ay_pcce_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcce_AcceptedCardinalityExpansionReplayGuard
      originalCnf replayedCnf
      cardinalityConstraint expandedClauses expansionManifest
      auxiliaryVariables encodedVariables mapWitness
      transformWitness transformLedger
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      expansionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcce_CheckerReplay expansionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pcce_CheckerReplay expansionReplayCertificate checkerAccepted)
    (fun _manifest _map _transform _coverage _eqsat _modelRecon _proofRecon
      _fingerprints checker _fallback _build _validator _audit => checker)

theorem ay_pcce_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcce_AcceptedCardinalityExpansionReplayGuard
      originalCnf replayedCnf
      cardinalityConstraint expandedClauses expansionManifest
      auxiliaryVariables encodedVariables mapWitness
      transformWitness transformLedger
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      expansionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcce_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pcce_AuditEvidence auditAppended auditAppendOnly)
    (fun _manifest _map _transform _coverage _eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator audit => audit)

theorem ay_pcce_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pcce_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pcce_Sat replayedCnf replayedModel ->
    ay_pcce_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pcce_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcce_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pcce_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_pcce_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pcce_AcceptedCardinalityExpansionReplayGuard
      originalCnf replayedCnf
      cardinalityConstraint expandedClauses expansionManifest
      auxiliaryVariables encodedVariables mapWitness
      transformWitness transformLedger
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      expansionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcce_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_pcce_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_pcce_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _map _transform _coverage _eqsat modelRecon
      _proofRecon _fingerprints _checker _fallback _build _validator _audit =>
      ay_pcce_disj_left
        (ay_pcce_ExitCodeSound exitCode
          (ay_pcce_Sat originalCnf originalModel))
        (ay_pcce_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pcce_conj_intro exitCode
          (ay_pcce_Sat originalCnf originalModel)
          hexit (modelRecon replayedSat)))

theorem ay_pcce_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (expandedClauses : Prop)
    (expansionManifest : Prop)
    (auxiliaryVariables : Prop) (encodedVariables : Prop)
    (mapWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (expansionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pcce_AcceptedCardinalityExpansionReplayGuard
      originalCnf replayedCnf
      cardinalityConstraint expandedClauses expansionManifest
      auxiliaryVariables encodedVariables mapWitness
      transformWitness transformLedger
      affectedClause coveredClause coverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      expansionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcce_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_pcce_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_pcce_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _map _transform _coverage _eqsat _modelRecon proofRecon
      _fingerprints _checker _fallback _build _validator _audit =>
      ay_pcce_disj_right
        (ay_pcce_ExitCodeSound exitCode
          (ay_pcce_Sat originalCnf originalModel))
        (ay_pcce_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pcce_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit (proofRecon replayedReplay)))

theorem ay_pcce_failure_expansion
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    expansionFailure ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result expansion_case _map_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact expansion_case failure

theorem ay_pcce_failure_map
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    mapFailure ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case map_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact map_case failure

theorem ay_pcce_failure_witness
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    witnessFailure ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact witness_case failure

theorem ay_pcce_failure_coverage
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact coverage_case failure

theorem ay_pcce_failure_reconstruction
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case _coverage_case
    reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact reconstruction_case failure

theorem ay_pcce_failure_stale_fingerprint
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case _coverage_case
    _reconstruction_case fingerprint_case _replay_case _build_case _audit_case
  exact fingerprint_case failure

theorem ay_pcce_failure_unchecked_replay
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case replay_case _build_case _audit_case
  exact replay_case failure

theorem ay_pcce_failure_build
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case build_case _audit_case
  exact build_case failure

theorem ay_pcce_failure_audit
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pcce_CardinalityExpansionReplayGuardFailure
      expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _expansion_case _map_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case audit_case
  exact audit_case failure

theorem ay_pcce_diagnostic_no_claim
    (currentCnf : Prop)
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcce_DiagnosticCardinalityExpansionReplayGuard
      currentCnf expansionFailure mapFailure witnessFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pcce_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_pcce_conj_right
    (ay_pcce_RecomputeObligation currentCnf recompute)
    (ay_pcce_NoSemanticClaim diagnostic)
    (ay_pcce_conj_right
      (ay_pcce_CardinalityExpansionReplayGuardFailure
        expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pcce_Conj
        (ay_pcce_RecomputeObligation currentCnf recompute)
        (ay_pcce_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pcce_diagnostic_recompute
    (currentCnf : Prop)
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcce_DiagnosticCardinalityExpansionReplayGuard
      currentCnf expansionFailure mapFailure witnessFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pcce_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_pcce_conj_left
    (ay_pcce_RecomputeObligation currentCnf recompute)
    (ay_pcce_NoSemanticClaim diagnostic)
    (ay_pcce_conj_right
      (ay_pcce_CardinalityExpansionReplayGuardFailure
        expansionFailure mapFailure witnessFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pcce_Conj
        (ay_pcce_RecomputeObligation currentCnf recompute)
        (ay_pcce_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pcce_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (expansionFailure : Prop) (mapFailure : Prop)
    (witnessFailure : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pcce_DiagnosticCardinalityExpansionReplayGuard
      currentCnf expansionFailure mapFailure witnessFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pcce_Conj
      (ay_pcce_NoSemanticClaim diagnostic)
      (ay_pcce_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_pcce_conj_intro
    (ay_pcce_NoSemanticClaim diagnostic)
    (ay_pcce_RecomputeObligation currentCnf recompute)
    (ay_pcce_diagnostic_no_claim
      currentCnf expansionFailure mapFailure witnessFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
    (ay_pcce_diagnostic_recompute
      currentCnf expansionFailure mapFailure witnessFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
