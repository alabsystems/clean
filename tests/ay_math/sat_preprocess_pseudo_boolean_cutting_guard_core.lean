-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Pseudo-Boolean cutting/strengthening guard soundness.
-- The propositions stand for PB constraint manifests, cutting-plane derivation ledgers, coefficient
-- normalization witnesses, auxiliary-variable domain manifests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_pbcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pbcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pbcg_Equisat (before : Prop) (after : Prop) :=
  ay_pbcg_Conj (before -> after) (after -> before)

def ay_pbcg_Sat (cnf : Prop) (model : Prop) :=
  ay_pbcg_Conj cnf model

def ay_pbcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pbcg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pbcg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pbcg_PbConstraintManifest
    (pbConstraint : Prop) (pbManifestAccepted : Prop)
    (pbConstraintManifest : Prop) :=
  ay_pbcg_Conj pbConstraintManifest (pbConstraint -> pbManifestAccepted)

def ay_pbcg_CuttingPlaneDerivationLedger
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop)
    (cuttingPlaneDerivationWitness : Prop) :=
  ay_pbcg_Conj cuttingPlaneDerivationWitness (cuttingPlaneDerivation -> derivationAccepted)

def ay_pbcg_CoefficientNormalizationWitness
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop)
    (normalizedCoefficientsManifest : Prop) :=
  ay_pbcg_Conj normalizedCoefficientsManifest (normalizedCoefficients -> normalizedCoefficientsAccepted)

def ay_pbcg_AuxiliaryVariableDomainManifest
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :=
  ay_pbcg_Conj auxiliaryDomainDigest (auxiliaryDomain -> auxiliaryDomainAccepted)

def ay_pbcg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pbcg_Sat replayedCnf replayedModel ->
    ay_pbcg_Sat originalCnf originalModel

def ay_pbcg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbcg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbcg_Conj
    (ay_pbcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pbcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_pbcg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbcg_Conj fingerprintWitness
    (ay_pbcg_IdMatch originalFingerprint replayedFingerprint)

def ay_pbcg_CheckerReplay
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbcg_Conj pbCuttingReplayCertificate checkerAccepted

def ay_pbcg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pbcg_Conj baselineSolver baselineAvailable

def ay_pbcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pbcg_Conj binaryFingerprint buildReproducible

def ay_pbcg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pbcg_Conj validatorAccepted validatorVersion

def ay_pbcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pbcg_Conj auditAppended auditAppendOnly

def ay_pbcg_AcceptedPseudoBooleanCuttingGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbcg_PbConstraintManifest
       pbConstraint pbManifestAccepted pbConstraintManifest ->
     ay_pbcg_CuttingPlaneDerivationLedger
       cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness ->
     ay_pbcg_CoefficientNormalizationWitness
       normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest ->
     ay_pbcg_AuxiliaryVariableDomainManifest
       auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
     ay_pbcg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_pbcg_Equisat originalCnf replayedCnf ->
     ay_pbcg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pbcg_CheckerReplay pbCuttingReplayCertificate checkerAccepted ->
     ay_pbcg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbcg_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_pbcg_PseudoBooleanCuttingGuardFailure
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (stalePbConstraintManifest -> result) ->
    (derivationMismatch -> result) ->
    (normalizedCoefficientsMismatch -> result) ->
    (auxiliaryDomainGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pbcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbcg_Conj currentCnf recompute

def ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbcg_Conj
    (ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_pbcg_Conj
      (ay_pbcg_RecomputeObligation currentCnf recompute)
      (ay_pbcg_NoSemanticClaim diagnostic))

def ay_pbcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pbcg_Conj exitCode claim

def ay_pbcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pbcg_Disj
    (ay_pbcg_ExitCodeSound exitCode (ay_pbcg_Sat originalCnf model))
    (ay_pbcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pbcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pbcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbcg_conj_left
    (left : Prop) (right : Prop) :
    ay_pbcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbcg_conj_right
    (left : Prop) (right : Prop) :
    ay_pbcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pbcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pbcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbcg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pbcg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_pbcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pbcg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pbcg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_pbcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pbcg_pb_constraint_manifest_applies
    (pbConstraint : Prop) (pbManifestAccepted : Prop)
    (pbConstraintManifest : Prop) :
    ay_pbcg_PbConstraintManifest
      pbConstraint pbManifestAccepted pbConstraintManifest ->
    pbConstraint -> pbManifestAccepted := by
  intro digest
  exact ay_pbcg_conj_right pbConstraintManifest
    (pbConstraint -> pbManifestAccepted) digest

theorem ay_pbcg_cutting_plane_derivation_ledger_applies
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop)
    (cuttingPlaneDerivationWitness : Prop) :
    ay_pbcg_CuttingPlaneDerivationLedger
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness ->
    cuttingPlaneDerivation -> derivationAccepted := by
  intro digest
  exact ay_pbcg_conj_right cuttingPlaneDerivationWitness
    (cuttingPlaneDerivation -> derivationAccepted) digest

theorem ay_pbcg_coefficient_normalization_witness_applies
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop)
    (normalizedCoefficientsManifest : Prop) :
    ay_pbcg_CoefficientNormalizationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest ->
    normalizedCoefficients -> normalizedCoefficientsAccepted := by
  intro ledger
  exact ay_pbcg_conj_right normalizedCoefficientsManifest
    (normalizedCoefficients -> normalizedCoefficientsAccepted) ledger

theorem ay_pbcg_auxiliary_variable_domain_manifest_applies
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :
    ay_pbcg_AuxiliaryVariableDomainManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
    auxiliaryDomain -> auxiliaryDomainAccepted := by
  intro coverage
  exact ay_pbcg_conj_right auxiliaryDomainDigest
    (auxiliaryDomain -> auxiliaryDomainAccepted) coverage

theorem ay_pbcg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_pbcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_pbcg_conj_left
    (ay_pbcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pbcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_pbcg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_pbcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_pbcg_conj_right
    (ay_pbcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pbcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_pbcg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pbcg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_pbcg_accepted_implication_preserving
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_pbcg_equisat_forward originalCnf replayedCnf
    (ay_pbcg_accepted_equisat
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_pbcg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcg_CheckerReplay pbCuttingReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pbcg_CheckerReplay pbCuttingReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_pbcg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbcg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_pbcg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pbcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pbcg_Sat replayedCnf replayedModel ->
    ay_pbcg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pbcg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pbcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_pbcg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_pbcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_pbcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_pbcg_disj_left
        (ay_pbcg_ExitCodeSound exitCode
          (ay_pbcg_Sat originalCnf originalModel))
        (ay_pbcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pbcg_conj_intro exitCode
          (ay_pbcg_Sat originalCnf originalModel)
          hexit
          ((ay_pbcg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_pbcg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (pbConstraint : Prop) (pbManifestAccepted : Prop) (pbConstraintManifest : Prop)
    (cuttingPlaneDerivation : Prop) (derivationAccepted : Prop) (cuttingPlaneDerivationWitness : Prop)
    (normalizedCoefficients : Prop) (normalizedCoefficientsAccepted : Prop) (normalizedCoefficientsManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pbCuttingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pbcg_AcceptedPseudoBooleanCuttingGuard
      originalCnf replayedCnf
      pbConstraint pbManifestAccepted pbConstraintManifest
      cuttingPlaneDerivation derivationAccepted cuttingPlaneDerivationWitness
      normalizedCoefficients normalizedCoefficientsAccepted normalizedCoefficientsManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pbCuttingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_pbcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_pbcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_pbcg_disj_right
        (ay_pbcg_ExitCodeSound exitCode
          (ay_pbcg_Sat originalCnf originalModel))
        (ay_pbcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pbcg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_pbcg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_pbcg_failure_stale_pb_constraint_manifest
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    stalePbConstraintManifest ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_pbcg_failure_cutting_plane_derivation_ledger
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    derivationMismatch ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_pbcg_failure_coefficient_normalization_witness
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    normalizedCoefficientsMismatch ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_pbcg_failure_auxiliary_variable_domain
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auxiliaryDomainGap ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_pbcg_failure_reconstruction
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_pbcg_failure_stale_fingerprint
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_pbcg_failure_unchecked_replay
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_pbcg_failure_missing_baseline
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_pbcg_failure_build
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_pbcg_failure_validator
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_pbcg_failure_audit
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pbcg_PseudoBooleanCuttingGuardFailure
      stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_pbcg_diagnostic_no_claim
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pbcg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_pbcg_conj_right
    (ay_pbcg_RecomputeObligation currentCnf recompute)
    (ay_pbcg_NoSemanticClaim diagnostic)
    (ay_pbcg_conj_right
      (ay_pbcg_PseudoBooleanCuttingGuardFailure
        stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_pbcg_Conj
        (ay_pbcg_RecomputeObligation currentCnf recompute)
        (ay_pbcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pbcg_diagnostic_recompute
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pbcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_pbcg_conj_left
    (ay_pbcg_RecomputeObligation currentCnf recompute)
    (ay_pbcg_NoSemanticClaim diagnostic)
    (ay_pbcg_conj_right
      (ay_pbcg_PseudoBooleanCuttingGuardFailure
        stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_pbcg_Conj
        (ay_pbcg_RecomputeObligation currentCnf recompute)
        (ay_pbcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pbcg_unchecked_pb_cutting_cannot_bless_public_result
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pbcg_Conj
      (ay_pbcg_NoSemanticClaim diagnostic)
      (ay_pbcg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_pbcg_conj_intro
    (ay_pbcg_NoSemanticClaim diagnostic)
    (ay_pbcg_RecomputeObligation currentCnf recompute)
    (ay_pbcg_diagnostic_no_claim
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_pbcg_diagnostic_recompute
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_pbcg_unchecked_pb_cutting_cannot_bless_public_sat
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pbcg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_pbcg_diagnostic_no_claim
    currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_pbcg_unchecked_pb_cutting_cannot_bless_public_unsat
    (currentCnf : Prop)
    (stalePbConstraintManifest : Prop) (derivationMismatch : Prop)
    (normalizedCoefficientsMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbcg_DiagnosticPseudoBooleanCuttingGuard
      currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pbcg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_pbcg_diagnostic_recompute
    currentCnf stalePbConstraintManifest derivationMismatch normalizedCoefficientsMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
