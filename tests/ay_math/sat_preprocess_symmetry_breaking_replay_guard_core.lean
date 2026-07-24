-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Symmetry-breaking replay guard soundness.
-- The propositions stand for symmetry-group manifests, orbit representative
-- witnesses, added breaker-clause coverage, transform witnesses,
-- reconstruction hooks, fingerprints, checker replay, fallback/build/validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_psbg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psbg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_psbg_Equisat (before : Prop) (after : Prop) :=
  ay_psbg_Conj (before -> after) (after -> before)

def ay_psbg_Sat (cnf : Prop) (model : Prop) :=
  ay_psbg_Conj cnf model

def ay_psbg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_psbg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_psbg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_psbg_SymmetryGroupManifest
    (symmetryGroup : Prop) (groupAction : Prop)
    (groupManifest : Prop) :=
  ay_psbg_Conj groupManifest (symmetryGroup -> groupAction)

def ay_psbg_OrbitRepresentativeWitnessLedger
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop) :=
  ay_psbg_Conj orbitLedger (orbitElement -> representativeWitness)

def ay_psbg_BreakerClauseCoverage
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop) :=
  ay_psbg_Conj coverageWitness (breakerClause -> coveredBreakerClause)

def ay_psbg_TransformWitnessLedger
    (breakerClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_psbg_Conj transformLedger (breakerClause -> transformWitness)

def ay_psbg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_psbg_Sat replayedCnf replayedModel ->
    ay_psbg_Sat originalCnf originalModel

def ay_psbg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_psbg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_psbg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psbg_Conj fingerprintWitness
    (ay_psbg_IdMatch originalFingerprint replayedFingerprint)

def ay_psbg_CheckerReplay
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_psbg_Conj symmetryReplayCertificate checkerAccepted

def ay_psbg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_psbg_Conj baselineSolver baselineAvailable

def ay_psbg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_psbg_Conj binaryFingerprint buildReproducible

def ay_psbg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_psbg_Conj validatorAccepted validatorVersion

def ay_psbg_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_psbg_Conj auditAppended auditAppendOnly

def ay_psbg_AcceptedSymmetryBreakingReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_psbg_SymmetryGroupManifest
       symmetryGroup groupAction groupManifest ->
     ay_psbg_OrbitRepresentativeWitnessLedger
       orbitElement representativeWitness orbitLedger ->
     ay_psbg_BreakerClauseCoverage
       breakerClause coveredBreakerClause coverageWitness ->
     ay_psbg_TransformWitnessLedger
       breakerClause transformWitness transformLedger ->
     ay_psbg_Equisat originalCnf replayedCnf ->
     ay_psbg_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_psbg_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_psbg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_psbg_CheckerReplay symmetryReplayCertificate checkerAccepted ->
     ay_psbg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_psbg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_psbg_ValidatorGate validatorAccepted validatorVersion ->
     ay_psbg_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_psbg_SymmetryBreakingReplayGuardFailure
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :=
  forall result : Prop,
    (groupFailure -> result) ->
    (orbitFailure -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_psbg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_psbg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_psbg_Conj currentCnf recompute

def ay_psbg_DiagnosticSymmetryBreakingReplayGuard
    (currentCnf : Prop)
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_psbg_Conj
    (ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction)
    (ay_psbg_Conj
      (ay_psbg_RecomputeObligation currentCnf recompute)
      (ay_psbg_NoSemanticClaim diagnostic))

def ay_psbg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_psbg_Conj exitCode claim

def ay_psbg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_psbg_Disj
    (ay_psbg_ExitCodeSound exitCode (ay_psbg_Sat originalCnf model))
    (ay_psbg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_psbg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_psbg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_psbg_conj_left
    (left : Prop) (right : Prop) :
    ay_psbg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_psbg_conj_right
    (left : Prop) (right : Prop) :
    ay_psbg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_psbg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_psbg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_psbg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_psbg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_psbg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_psbg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_psbg_conj_left (before -> after) (after -> before) eqsat

theorem ay_psbg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_psbg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_psbg_conj_right (before -> after) (after -> before) eqsat

theorem ay_psbg_symmetry_group_manifest_applies
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop) :
    ay_psbg_SymmetryGroupManifest symmetryGroup groupAction groupManifest ->
    symmetryGroup -> groupAction := by
  intro manifest
  exact ay_psbg_conj_right groupManifest
    (symmetryGroup -> groupAction) manifest

theorem ay_psbg_orbit_representative_witness_ledger
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop) :
    ay_psbg_OrbitRepresentativeWitnessLedger
      orbitElement representativeWitness orbitLedger ->
    orbitElement -> representativeWitness := by
  intro ledger
  exact ay_psbg_conj_right orbitLedger
    (orbitElement -> representativeWitness) ledger

theorem ay_psbg_breaker_clause_coverage
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop) :
    ay_psbg_BreakerClauseCoverage
      breakerClause coveredBreakerClause coverageWitness ->
    breakerClause -> coveredBreakerClause := by
  intro coverage
  exact ay_psbg_conj_right coverageWitness
    (breakerClause -> coveredBreakerClause) coverage

theorem ay_psbg_transform_witness_ledger
    (breakerClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_psbg_TransformWitnessLedger
      breakerClause transformWitness transformLedger ->
    breakerClause -> transformWitness := by
  intro ledger
  exact ay_psbg_conj_right transformLedger
    (breakerClause -> transformWitness) ledger

theorem ay_psbg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psbg_AcceptedSymmetryBreakingReplayGuard
      originalCnf replayedCnf
      symmetryGroup groupAction groupManifest
      orbitElement representativeWitness orbitLedger
      breakerClause coveredBreakerClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psbg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_psbg_Equisat originalCnf replayedCnf)
    (fun _group _orbit _coverage _transform eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator _audit => eqsat)

theorem ay_psbg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psbg_AcceptedSymmetryBreakingReplayGuard
      originalCnf replayedCnf
      symmetryGroup groupAction groupManifest
      orbitElement representativeWitness orbitLedger
      breakerClause coveredBreakerClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psbg_CheckerReplay symmetryReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_psbg_CheckerReplay symmetryReplayCertificate checkerAccepted)
    (fun _group _orbit _coverage _transform _eqsat _modelRecon _proofRecon
      _fingerprints checker _fallback _build _validator _audit => checker)

theorem ay_psbg_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_psbg_AcceptedSymmetryBreakingReplayGuard
      originalCnf replayedCnf
      symmetryGroup groupAction groupManifest
      orbitElement representativeWitness orbitLedger
      breakerClause coveredBreakerClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psbg_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_psbg_AuditEvidence auditAppended auditAppendOnly)
    (fun _group _orbit _coverage _transform _eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator audit => audit)

theorem ay_psbg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_psbg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_psbg_Sat replayedCnf replayedModel ->
    ay_psbg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_psbg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_psbg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_psbg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_psbg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_psbg_AcceptedSymmetryBreakingReplayGuard
      originalCnf replayedCnf
      symmetryGroup groupAction groupManifest
      orbitElement representativeWitness orbitLedger
      breakerClause coveredBreakerClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psbg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_psbg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_psbg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _group _orbit _coverage _transform _eqsat modelRecon
      _proofRecon _fingerprints _checker _fallback _build _validator _audit =>
      ay_psbg_disj_left
        (ay_psbg_ExitCodeSound exitCode
          (ay_psbg_Sat originalCnf originalModel))
        (ay_psbg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_psbg_conj_intro exitCode
          (ay_psbg_Sat originalCnf originalModel)
          hexit (modelRecon replayedSat)))

theorem ay_psbg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGroup : Prop) (groupAction : Prop) (groupManifest : Prop)
    (orbitElement : Prop) (representativeWitness : Prop)
    (orbitLedger : Prop)
    (breakerClause : Prop) (coveredBreakerClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_psbg_AcceptedSymmetryBreakingReplayGuard
      originalCnf replayedCnf
      symmetryGroup groupAction groupManifest
      orbitElement representativeWitness orbitLedger
      breakerClause coveredBreakerClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_psbg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_psbg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_psbg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _group _orbit _coverage _transform _eqsat _modelRecon proofRecon
      _fingerprints _checker _fallback _build _validator _audit =>
      ay_psbg_disj_right
        (ay_psbg_ExitCodeSound exitCode
          (ay_psbg_Sat originalCnf originalModel))
        (ay_psbg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_psbg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit (proofRecon replayedReplay)))

theorem ay_psbg_failure_group
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    groupFailure ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result group_case _orbit_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact group_case failure

theorem ay_psbg_failure_orbit
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    orbitFailure ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case orbit_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact orbit_case failure

theorem ay_psbg_failure_coverage
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    coverageGap ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact coverage_case failure

theorem ay_psbg_failure_reconstruction
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    reconstructionGap ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case _coverage_case
    reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact reconstruction_case failure

theorem ay_psbg_failure_stale_fingerprint
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    staleFingerprint ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case _coverage_case
    _reconstruction_case fingerprint_case _replay_case _build_case _audit_case
  exact fingerprint_case failure

theorem ay_psbg_failure_unchecked_replay
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case _coverage_case
    _reconstruction_case _fingerprint_case replay_case _build_case _audit_case
  exact replay_case failure

theorem ay_psbg_failure_build
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    buildDrift ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case build_case _audit_case
  exact build_case failure

theorem ay_psbg_failure_audit
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    auditContradiction ->
    ay_psbg_SymmetryBreakingReplayGuardFailure
      groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _group_case _orbit_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case audit_case
  exact audit_case failure

theorem ay_psbg_diagnostic_no_claim
    (currentCnf : Prop)
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psbg_DiagnosticSymmetryBreakingReplayGuard
      currentCnf groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction
      recompute diagnostic ->
    ay_psbg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_psbg_conj_right
    (ay_psbg_RecomputeObligation currentCnf recompute)
    (ay_psbg_NoSemanticClaim diagnostic)
    (ay_psbg_conj_right
      (ay_psbg_SymmetryBreakingReplayGuardFailure
        groupFailure orbitFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_psbg_Conj
        (ay_psbg_RecomputeObligation currentCnf recompute)
        (ay_psbg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_psbg_diagnostic_recompute
    (currentCnf : Prop)
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psbg_DiagnosticSymmetryBreakingReplayGuard
      currentCnf groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction
      recompute diagnostic ->
    ay_psbg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_psbg_conj_left
    (ay_psbg_RecomputeObligation currentCnf recompute)
    (ay_psbg_NoSemanticClaim diagnostic)
    (ay_psbg_conj_right
      (ay_psbg_SymmetryBreakingReplayGuardFailure
        groupFailure orbitFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_psbg_Conj
        (ay_psbg_RecomputeObligation currentCnf recompute)
        (ay_psbg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_psbg_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (groupFailure : Prop) (orbitFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_psbg_DiagnosticSymmetryBreakingReplayGuard
      currentCnf groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction
      recompute diagnostic ->
    ay_psbg_Conj
      (ay_psbg_NoSemanticClaim diagnostic)
      (ay_psbg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_psbg_conj_intro
    (ay_psbg_NoSemanticClaim diagnostic)
    (ay_psbg_RecomputeObligation currentCnf recompute)
    (ay_psbg_diagnostic_no_claim
      currentCnf groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction
      recompute diagnostic diagnosticBundle)
    (ay_psbg_diagnostic_recompute
      currentCnf groupFailure orbitFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction
      recompute diagnostic diagnosticBundle)
