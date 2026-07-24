-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cardinality/pseudo-Boolean encoding guard soundness.
-- The propositions stand for original cardinality constraint manifests, encoding schema witnesses, auxiliary-variable
-- domain manifests, clause coverage digests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_cecg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cecg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cecg_Equisat (before : Prop) (after : Prop) :=
  ay_cecg_Conj (before -> after) (after -> before)

def ay_cecg_Sat (cnf : Prop) (model : Prop) :=
  ay_cecg_Conj cnf model

def ay_cecg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cecg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_cecg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_cecg_CardinalityConstraintManifest
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop)
    (cardinalityConstraintManifest : Prop) :=
  ay_cecg_Conj cardinalityConstraintManifest (cardinalityConstraint -> constraintManifestAccepted)

def ay_cecg_EncodingSchemaWitness
    (encodingSchema : Prop) (schemaAccepted : Prop)
    (encodingSchemaWitness : Prop) :=
  ay_cecg_Conj encodingSchemaWitness (encodingSchema -> schemaAccepted)

def ay_cecg_AuxiliaryVariableDomainManifest
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainManifest : Prop) :=
  ay_cecg_Conj auxiliaryDomainManifest (auxiliaryDomain -> auxiliaryDomainAccepted)

def ay_cecg_ClauseCoverageDigest
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop) :=
  ay_cecg_Conj clauseCoverageDigest (clauseCoverage -> clauseCoverageAccepted)

def ay_cecg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_cecg_Sat replayedCnf replayedModel ->
    ay_cecg_Sat originalCnf originalModel

def ay_cecg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cecg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cecg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cecg_Conj
    (ay_cecg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cecg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_cecg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_cecg_Conj fingerprintWitness
    (ay_cecg_IdMatch originalFingerprint replayedFingerprint)

def ay_cecg_CheckerReplay
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_cecg_Conj encodingReplayCertificate checkerAccepted

def ay_cecg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cecg_Conj baselineSolver baselineAvailable

def ay_cecg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cecg_Conj binaryFingerprint buildReproducible

def ay_cecg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cecg_Conj validatorAccepted validatorVersion

def ay_cecg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cecg_Conj auditAppended auditAppendOnly

def ay_cecg_AcceptedCardinalityEncodingGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cecg_CardinalityConstraintManifest
       cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest ->
     ay_cecg_EncodingSchemaWitness
       encodingSchema schemaAccepted encodingSchemaWitness ->
     ay_cecg_AuxiliaryVariableDomainManifest
       auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest ->
     ay_cecg_ClauseCoverageDigest
       clauseCoverage clauseCoverageAccepted clauseCoverageDigest ->
     ay_cecg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_cecg_Equisat originalCnf replayedCnf ->
     ay_cecg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_cecg_CheckerReplay encodingReplayCertificate checkerAccepted ->
     ay_cecg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cecg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cecg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cecg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cecg_CardinalityEncodingGuardFailure
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleCardinalityConstraintManifest -> result) ->
    (schemaMismatch -> result) ->
    (auxiliaryDomainMismatch -> result) ->
    (clauseCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_cecg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cecg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cecg_Conj currentCnf recompute

def ay_cecg_DiagnosticCardinalityEncodingGuard
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cecg_Conj
    (ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_cecg_Conj
      (ay_cecg_RecomputeObligation currentCnf recompute)
      (ay_cecg_NoSemanticClaim diagnostic))

def ay_cecg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cecg_Conj exitCode claim

def ay_cecg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cecg_Disj
    (ay_cecg_ExitCodeSound exitCode (ay_cecg_Sat originalCnf model))
    (ay_cecg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cecg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cecg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cecg_conj_left
    (left : Prop) (right : Prop) :
    ay_cecg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cecg_conj_right
    (left : Prop) (right : Prop) :
    ay_cecg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cecg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cecg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cecg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cecg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cecg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_cecg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_cecg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cecg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_cecg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_cecg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cecg_cardinality_constraint_manifest_applies
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop)
    (cardinalityConstraintManifest : Prop) :
    ay_cecg_CardinalityConstraintManifest
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest ->
    cardinalityConstraint -> constraintManifestAccepted := by
  intro digest
  exact ay_cecg_conj_right cardinalityConstraintManifest
    (cardinalityConstraint -> constraintManifestAccepted) digest

theorem ay_cecg_encoding_schema_witness_applies
    (encodingSchema : Prop) (schemaAccepted : Prop)
    (encodingSchemaWitness : Prop) :
    ay_cecg_EncodingSchemaWitness
      encodingSchema schemaAccepted encodingSchemaWitness ->
    encodingSchema -> schemaAccepted := by
  intro digest
  exact ay_cecg_conj_right encodingSchemaWitness
    (encodingSchema -> schemaAccepted) digest

theorem ay_cecg_auxiliary_variable_domain_manifest_applies
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainManifest : Prop) :
    ay_cecg_AuxiliaryVariableDomainManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest ->
    auxiliaryDomain -> auxiliaryDomainAccepted := by
  intro ledger
  exact ay_cecg_conj_right auxiliaryDomainManifest
    (auxiliaryDomain -> auxiliaryDomainAccepted) ledger

theorem ay_cecg_clause_coverage_digest_applies
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop) :
    ay_cecg_ClauseCoverageDigest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest ->
    clauseCoverage -> clauseCoverageAccepted := by
  intro coverage
  exact ay_cecg_conj_right clauseCoverageDigest
    (clauseCoverage -> clauseCoverageAccepted) coverage

theorem ay_cecg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cecg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cecg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_cecg_conj_left
    (ay_cecg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cecg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cecg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cecg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cecg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_cecg_conj_right
    (ay_cecg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cecg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cecg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cecg_AcceptedCardinalityEncodingGuard
      originalCnf replayedCnf
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest
      encodingSchema schemaAccepted encodingSchemaWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      encodingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cecg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_cecg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_cecg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cecg_AcceptedCardinalityEncodingGuard
      originalCnf replayedCnf
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest
      encodingSchema schemaAccepted encodingSchemaWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      encodingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cecg_CheckerReplay encodingReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_cecg_CheckerReplay encodingReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_cecg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cecg_AcceptedCardinalityEncodingGuard
      originalCnf replayedCnf
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest
      encodingSchema schemaAccepted encodingSchemaWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      encodingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cecg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_cecg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_cecg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_cecg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_cecg_Sat replayedCnf replayedModel ->
    ay_cecg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_cecg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cecg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_cecg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_cecg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cecg_AcceptedCardinalityEncodingGuard
      originalCnf replayedCnf
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest
      encodingSchema schemaAccepted encodingSchemaWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      encodingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cecg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_cecg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_cecg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_cecg_disj_left
        (ay_cecg_ExitCodeSound exitCode
          (ay_cecg_Sat originalCnf originalModel))
        (ay_cecg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cecg_conj_intro exitCode
          (ay_cecg_Sat originalCnf originalModel)
          hexit
          ((ay_cecg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_cecg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (cardinalityConstraint : Prop) (constraintManifestAccepted : Prop) (cardinalityConstraintManifest : Prop)
    (encodingSchema : Prop) (schemaAccepted : Prop) (encodingSchemaWitness : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop) (auxiliaryDomainManifest : Prop)
    (clauseCoverage : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (encodingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cecg_AcceptedCardinalityEncodingGuard
      originalCnf replayedCnf
      cardinalityConstraint constraintManifestAccepted cardinalityConstraintManifest
      encodingSchema schemaAccepted encodingSchemaWitness
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainManifest
      clauseCoverage clauseCoverageAccepted clauseCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      encodingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cecg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_cecg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_cecg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_cecg_disj_right
        (ay_cecg_ExitCodeSound exitCode
          (ay_cecg_Sat originalCnf originalModel))
        (ay_cecg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cecg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_cecg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_cecg_failure_stale_cardinality_constraint_manifest
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleCardinalityConstraintManifest ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_cecg_failure_encoding_schema_witness
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    schemaMismatch ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_cecg_failure_auxiliary_variable_domain_manifest
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auxiliaryDomainMismatch ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_cecg_failure_clause_coverage
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    clauseCoverageGap ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_cecg_failure_reconstruction
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_cecg_failure_stale_fingerprint
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_cecg_failure_unchecked_replay
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_cecg_failure_missing_baseline
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_cecg_failure_build
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_cecg_failure_validator
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_cecg_failure_audit
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_cecg_CardinalityEncodingGuardFailure
      staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_cecg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cecg_DiagnosticCardinalityEncodingGuard
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cecg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_cecg_conj_right
    (ay_cecg_RecomputeObligation currentCnf recompute)
    (ay_cecg_NoSemanticClaim diagnostic)
    (ay_cecg_conj_right
      (ay_cecg_CardinalityEncodingGuardFailure
        staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cecg_Conj
        (ay_cecg_RecomputeObligation currentCnf recompute)
        (ay_cecg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cecg_diagnostic_recompute
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cecg_DiagnosticCardinalityEncodingGuard
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cecg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_cecg_conj_left
    (ay_cecg_RecomputeObligation currentCnf recompute)
    (ay_cecg_NoSemanticClaim diagnostic)
    (ay_cecg_conj_right
      (ay_cecg_CardinalityEncodingGuardFailure
        staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cecg_Conj
        (ay_cecg_RecomputeObligation currentCnf recompute)
        (ay_cecg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cecg_unchecked_encoding_cannot_bless_public_result
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cecg_DiagnosticCardinalityEncodingGuard
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cecg_Conj
      (ay_cecg_NoSemanticClaim diagnostic)
      (ay_cecg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_cecg_conj_intro
    (ay_cecg_NoSemanticClaim diagnostic)
    (ay_cecg_RecomputeObligation currentCnf recompute)
    (ay_cecg_diagnostic_no_claim
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_cecg_diagnostic_recompute
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_cecg_unchecked_encoding_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cecg_DiagnosticCardinalityEncodingGuard
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cecg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_cecg_diagnostic_no_claim
    currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_cecg_unchecked_encoding_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleCardinalityConstraintManifest : Prop) (schemaMismatch : Prop)
    (auxiliaryDomainMismatch : Prop)
    (clauseCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cecg_DiagnosticCardinalityEncodingGuard
      currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cecg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_cecg_diagnostic_recompute
    currentCnf staleCardinalityConstraintManifest schemaMismatch auxiliaryDomainMismatch clauseCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
