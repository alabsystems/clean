-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-substitution replay guard soundness.
-- The propositions stand for equivalence-class manifests, substitution
-- witnesses, affected-clause coverage, transform witnesses, reconstruction
-- hooks, fingerprints, checker replay, fallback/build/validator gates, audit
-- evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pesr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pesr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pesr_Equisat (before : Prop) (after : Prop) :=
  ay_pesr_Conj (before -> after) (after -> before)

def ay_pesr_Sat (cnf : Prop) (model : Prop) :=
  ay_pesr_Conj cnf model

def ay_pesr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pesr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pesr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pesr_EquivalenceClassManifest
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop) :=
  ay_pesr_Conj manifestWitness
    (equivalenceClass -> representativeLiteral)

def ay_pesr_SubstitutionWitnessLedger
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop) :=
  ay_pesr_Conj substitutionLedger
    (substitutedLiteral -> substitutionWitness)

def ay_pesr_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pesr_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pesr_TransformWitnessLedger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pesr_Conj transformLedger (affectedClause -> transformWitness)

def ay_pesr_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pesr_Sat replayedCnf replayedModel ->
    ay_pesr_Sat originalCnf originalModel

def ay_pesr_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pesr_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pesr_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pesr_Conj fingerprintWitness
    (ay_pesr_IdMatch originalFingerprint replayedFingerprint)

def ay_pesr_CheckerReplay
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pesr_Conj substitutionReplayCertificate checkerAccepted

def ay_pesr_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pesr_Conj baselineSolver baselineAvailable

def ay_pesr_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pesr_Conj binaryFingerprint buildReproducible

def ay_pesr_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pesr_Conj validatorAccepted validatorVersion

def ay_pesr_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pesr_Conj auditAppended auditAppendOnly

def ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pesr_EquivalenceClassManifest
       equivalenceClass representativeLiteral manifestWitness ->
     ay_pesr_SubstitutionWitnessLedger
       substitutedLiteral substitutionWitness substitutionLedger ->
     ay_pesr_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pesr_TransformWitnessLedger
       affectedClause transformWitness transformLedger ->
     ay_pesr_Equisat originalCnf replayedCnf ->
     ay_pesr_ModelReconstruction
       replayedCnf originalCnf replayedModel originalModel ->
     ay_pesr_ProofReconstruction
       originalCnf replayedCnf certificate conflict ->
     ay_pesr_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pesr_CheckerReplay substitutionReplayCertificate checkerAccepted ->
     ay_pesr_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pesr_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pesr_ValidatorGate validatorAccepted validatorVersion ->
     ay_pesr_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pesr_EquivalenceSubstitutionReplayGuardFailure
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :=
  forall result : Prop,
    (equivalenceFailure -> result) ->
    (substitutionFailure -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pesr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pesr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pesr_Conj currentCnf recompute

def ay_pesr_DiagnosticEquivalenceSubstitutionReplayGuard
    (currentCnf : Prop)
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pesr_Conj
    (ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction)
    (ay_pesr_Conj
      (ay_pesr_RecomputeObligation currentCnf recompute)
      (ay_pesr_NoSemanticClaim diagnostic))

def ay_pesr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pesr_Conj exitCode claim

def ay_pesr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pesr_Disj
    (ay_pesr_ExitCodeSound exitCode (ay_pesr_Sat originalCnf model))
    (ay_pesr_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pesr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pesr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pesr_conj_left
    (left : Prop) (right : Prop) :
    ay_pesr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pesr_conj_right
    (left : Prop) (right : Prop) :
    ay_pesr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pesr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pesr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pesr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pesr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pesr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pesr_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_pesr_conj_left (before -> after) (after -> before) eqsat

theorem ay_pesr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pesr_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_pesr_conj_right (before -> after) (after -> before) eqsat

theorem ay_pesr_equivalence_class_manifest_applies
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop) :
    ay_pesr_EquivalenceClassManifest
      equivalenceClass representativeLiteral manifestWitness ->
    equivalenceClass -> representativeLiteral := by
  intro manifest
  exact ay_pesr_conj_right manifestWitness
    (equivalenceClass -> representativeLiteral) manifest

theorem ay_pesr_substitution_witness_ledger_applies
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop) :
    ay_pesr_SubstitutionWitnessLedger
      substitutedLiteral substitutionWitness substitutionLedger ->
    substitutedLiteral -> substitutionWitness := by
  intro ledger
  exact ay_pesr_conj_right substitutionLedger
    (substitutedLiteral -> substitutionWitness) ledger

theorem ay_pesr_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pesr_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause -> coveredClause := by
  intro coverage
  exact ay_pesr_conj_right coverageWitness
    (affectedClause -> coveredClause) coverage

theorem ay_pesr_transform_witness_ledger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pesr_TransformWitnessLedger
      affectedClause transformWitness transformLedger ->
    affectedClause -> transformWitness := by
  intro ledger
  exact ay_pesr_conj_right transformLedger
    (affectedClause -> transformWitness) ledger

theorem ay_pesr_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
      originalCnf replayedCnf
      equivalenceClass representativeLiteral manifestWitness
      substitutedLiteral substitutionWitness substitutionLedger
      affectedClause coveredClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      substitutionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pesr_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pesr_Equisat originalCnf replayedCnf)
    (fun _equiv _subst _coverage _transform eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator _audit => eqsat)

theorem ay_pesr_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
      originalCnf replayedCnf
      equivalenceClass representativeLiteral manifestWitness
      substitutedLiteral substitutionWitness substitutionLedger
      affectedClause coveredClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      substitutionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pesr_CheckerReplay
      substitutionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pesr_CheckerReplay substitutionReplayCertificate checkerAccepted)
    (fun _equiv _subst _coverage _transform _eqsat _modelRecon _proofRecon
      _fingerprints checker _fallback _build _validator _audit => checker)

theorem ay_pesr_accepted_audit_evidence
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
      originalCnf replayedCnf
      equivalenceClass representativeLiteral manifestWitness
      substitutedLiteral substitutionWitness substitutionLedger
      affectedClause coveredClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      substitutionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pesr_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pesr_AuditEvidence auditAppended auditAppendOnly)
    (fun _equiv _subst _coverage _transform _eqsat _modelRecon _proofRecon
      _fingerprints _checker _fallback _build _validator audit => audit)

theorem ay_pesr_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pesr_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pesr_Sat replayedCnf replayedModel ->
    ay_pesr_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pesr_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pesr_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pesr_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_pesr_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
      originalCnf replayedCnf
      equivalenceClass representativeLiteral manifestWitness
      substitutedLiteral substitutionWitness substitutionLedger
      affectedClause coveredClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      substitutionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pesr_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_pesr_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_pesr_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equiv _subst _coverage _transform _eqsat modelRecon
      _proofRecon _fingerprints _checker _fallback _build _validator _audit =>
      ay_pesr_disj_left
        (ay_pesr_ExitCodeSound exitCode
          (ay_pesr_Sat originalCnf originalModel))
        (ay_pesr_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pesr_conj_intro exitCode
          (ay_pesr_Sat originalCnf originalModel)
          hexit (modelRecon replayedSat)))

theorem ay_pesr_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalenceClass : Prop) (representativeLiteral : Prop)
    (manifestWitness : Prop)
    (substitutedLiteral : Prop) (substitutionWitness : Prop)
    (substitutionLedger : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (transformWitness : Prop) (transformLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pesr_AcceptedEquivalenceSubstitutionReplayGuard
      originalCnf replayedCnf
      equivalenceClass representativeLiteral manifestWitness
      substitutedLiteral substitutionWitness substitutionLedger
      affectedClause coveredClause coverageWitness
      transformWitness transformLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      substitutionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pesr_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_pesr_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_pesr_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equiv _subst _coverage _transform _eqsat _modelRecon proofRecon
      _fingerprints _checker _fallback _build _validator _audit =>
      ay_pesr_disj_right
        (ay_pesr_ExitCodeSound exitCode
          (ay_pesr_Sat originalCnf originalModel))
        (ay_pesr_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pesr_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit (proofRecon replayedReplay)))

theorem ay_pesr_failure_equivalence
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    equivalenceFailure ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result equivalence_case _substitution_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact equivalence_case failure

theorem ay_pesr_failure_substitution
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    substitutionFailure ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case substitution_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact substitution_case failure

theorem ay_pesr_failure_coverage
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    coverageGap ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact coverage_case failure

theorem ay_pesr_failure_reconstruction
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case _coverage_case
    reconstruction_case _fingerprint_case _replay_case _build_case _audit_case
  exact reconstruction_case failure

theorem ay_pesr_failure_stale_fingerprint
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case _coverage_case
    _reconstruction_case fingerprint_case _replay_case _build_case _audit_case
  exact fingerprint_case failure

theorem ay_pesr_failure_unchecked_replay
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case _coverage_case
    _reconstruction_case _fingerprint_case replay_case _build_case _audit_case
  exact replay_case failure

theorem ay_pesr_failure_build
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    buildDrift ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case build_case _audit_case
  exact build_case failure

theorem ay_pesr_failure_audit
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    auditContradiction ->
    ay_pesr_EquivalenceSubstitutionReplayGuardFailure
      equivalenceFailure substitutionFailure coverageGap reconstructionGap
      staleFingerprint uncheckedReplay buildDrift auditContradiction := by
  intro failure result _equivalence_case _substitution_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _build_case audit_case
  exact audit_case failure

theorem ay_pesr_diagnostic_no_claim
    (currentCnf : Prop)
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pesr_DiagnosticEquivalenceSubstitutionReplayGuard
      currentCnf equivalenceFailure substitutionFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pesr_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_pesr_conj_right
    (ay_pesr_RecomputeObligation currentCnf recompute)
    (ay_pesr_NoSemanticClaim diagnostic)
    (ay_pesr_conj_right
      (ay_pesr_EquivalenceSubstitutionReplayGuardFailure
        equivalenceFailure substitutionFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pesr_Conj
        (ay_pesr_RecomputeObligation currentCnf recompute)
        (ay_pesr_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pesr_diagnostic_recompute
    (currentCnf : Prop)
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pesr_DiagnosticEquivalenceSubstitutionReplayGuard
      currentCnf equivalenceFailure substitutionFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pesr_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_pesr_conj_left
    (ay_pesr_RecomputeObligation currentCnf recompute)
    (ay_pesr_NoSemanticClaim diagnostic)
    (ay_pesr_conj_right
      (ay_pesr_EquivalenceSubstitutionReplayGuardFailure
        equivalenceFailure substitutionFailure coverageGap reconstructionGap
        staleFingerprint uncheckedReplay buildDrift auditContradiction)
      (ay_pesr_Conj
        (ay_pesr_RecomputeObligation currentCnf recompute)
        (ay_pesr_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pesr_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (equivalenceFailure : Prop) (substitutionFailure : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pesr_DiagnosticEquivalenceSubstitutionReplayGuard
      currentCnf equivalenceFailure substitutionFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pesr_Conj
      (ay_pesr_NoSemanticClaim diagnostic)
      (ay_pesr_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_pesr_conj_intro
    (ay_pesr_NoSemanticClaim diagnostic)
    (ay_pesr_RecomputeObligation currentCnf recompute)
    (ay_pesr_diagnostic_no_claim
      currentCnf equivalenceFailure substitutionFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
    (ay_pesr_diagnostic_recompute
      currentCnf equivalenceFailure substitutionFailure coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic diagnosticBundle)
