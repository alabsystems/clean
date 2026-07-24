-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Gate hash-consing guard soundness.
-- The propositions stand for gate signature digests, canonical representative witnesses, merge/substitution
-- coverage digests, auxiliary-variable domain manifests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_ghcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ghcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ghcg_Equisat (before : Prop) (after : Prop) :=
  ay_ghcg_Conj (before -> after) (after -> before)

def ay_ghcg_Sat (cnf : Prop) (model : Prop) :=
  ay_ghcg_Conj cnf model

def ay_ghcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ghcg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_ghcg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_ghcg_GateSignatureDigest
    (gateSignature : Prop) (gateSignatureAccepted : Prop)
    (gateSignatureManifest : Prop) :=
  ay_ghcg_Conj gateSignatureManifest (gateSignature -> gateSignatureAccepted)

def ay_ghcg_CanonicalRepresentativeWitness
    (canonicalRepresentative : Prop) (representativeAccepted : Prop)
    (canonicalRepresentativeWitness : Prop) :=
  ay_ghcg_Conj canonicalRepresentativeWitness (canonicalRepresentative -> representativeAccepted)

def ay_ghcg_MergeSubstitutionCoverageDigest
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop)
    (mergeSubstitutionCoverageManifest : Prop) :=
  ay_ghcg_Conj mergeSubstitutionCoverageManifest (mergeSubstitutionCoverage -> mergeSubstitutionCoverageAccepted)

def ay_ghcg_AuxiliaryVariableDomainManifest
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :=
  ay_ghcg_Conj auxiliaryDomainDigest (auxiliaryDomain -> auxiliaryDomainAccepted)

def ay_ghcg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_ghcg_Sat replayedCnf replayedModel ->
    ay_ghcg_Sat originalCnf originalModel

def ay_ghcg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ghcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ghcg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ghcg_Conj
    (ay_ghcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ghcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_ghcg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_ghcg_Conj fingerprintWitness
    (ay_ghcg_IdMatch originalFingerprint replayedFingerprint)

def ay_ghcg_CheckerReplay
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_ghcg_Conj hashconsingReplayCertificate checkerAccepted

def ay_ghcg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_ghcg_Conj baselineSolver baselineAvailable

def ay_ghcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ghcg_Conj binaryFingerprint buildReproducible

def ay_ghcg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_ghcg_Conj validatorAccepted validatorVersion

def ay_ghcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ghcg_Conj auditAppended auditAppendOnly

def ay_ghcg_AcceptedGateHashconsingGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ghcg_GateSignatureDigest
       gateSignature gateSignatureAccepted gateSignatureManifest ->
     ay_ghcg_CanonicalRepresentativeWitness
       canonicalRepresentative representativeAccepted canonicalRepresentativeWitness ->
     ay_ghcg_MergeSubstitutionCoverageDigest
       mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest ->
     ay_ghcg_AuxiliaryVariableDomainManifest
       auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
     ay_ghcg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_ghcg_Equisat originalCnf replayedCnf ->
     ay_ghcg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_ghcg_CheckerReplay hashconsingReplayCertificate checkerAccepted ->
     ay_ghcg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_ghcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ghcg_ValidatorGate validatorAccepted validatorVersion ->
     ay_ghcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ghcg_GateHashconsingGuardFailure
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleGateSignatureDigest -> result) ->
    (representativeMismatch -> result) ->
    (mergeSubstitutionCoverageMismatch -> result) ->
    (auxiliaryDomainGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_ghcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ghcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ghcg_Conj currentCnf recompute

def ay_ghcg_DiagnosticGateHashconsingGuard
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ghcg_Conj
    (ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_ghcg_Conj
      (ay_ghcg_RecomputeObligation currentCnf recompute)
      (ay_ghcg_NoSemanticClaim diagnostic))

def ay_ghcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ghcg_Conj exitCode claim

def ay_ghcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ghcg_Disj
    (ay_ghcg_ExitCodeSound exitCode (ay_ghcg_Sat originalCnf model))
    (ay_ghcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ghcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ghcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ghcg_conj_left
    (left : Prop) (right : Prop) :
    ay_ghcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ghcg_conj_right
    (left : Prop) (right : Prop) :
    ay_ghcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ghcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ghcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ghcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ghcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ghcg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_ghcg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_ghcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_ghcg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_ghcg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_ghcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_ghcg_gate_signature_digest_applies
    (gateSignature : Prop) (gateSignatureAccepted : Prop)
    (gateSignatureManifest : Prop) :
    ay_ghcg_GateSignatureDigest
      gateSignature gateSignatureAccepted gateSignatureManifest ->
    gateSignature -> gateSignatureAccepted := by
  intro digest
  exact ay_ghcg_conj_right gateSignatureManifest
    (gateSignature -> gateSignatureAccepted) digest

theorem ay_ghcg_canonical_representative_witness_applies
    (canonicalRepresentative : Prop) (representativeAccepted : Prop)
    (canonicalRepresentativeWitness : Prop) :
    ay_ghcg_CanonicalRepresentativeWitness
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness ->
    canonicalRepresentative -> representativeAccepted := by
  intro digest
  exact ay_ghcg_conj_right canonicalRepresentativeWitness
    (canonicalRepresentative -> representativeAccepted) digest

theorem ay_ghcg_merge_substitution_coverage_digest_applies
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop)
    (mergeSubstitutionCoverageManifest : Prop) :
    ay_ghcg_MergeSubstitutionCoverageDigest
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest ->
    mergeSubstitutionCoverage -> mergeSubstitutionCoverageAccepted := by
  intro ledger
  exact ay_ghcg_conj_right mergeSubstitutionCoverageManifest
    (mergeSubstitutionCoverage -> mergeSubstitutionCoverageAccepted) ledger

theorem ay_ghcg_auxiliary_variable_domain_manifest_applies
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :
    ay_ghcg_AuxiliaryVariableDomainManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
    auxiliaryDomain -> auxiliaryDomainAccepted := by
  intro coverage
  exact ay_ghcg_conj_right auxiliaryDomainDigest
    (auxiliaryDomain -> auxiliaryDomainAccepted) coverage

theorem ay_ghcg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ghcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_ghcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_ghcg_conj_left
    (ay_ghcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ghcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_ghcg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ghcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_ghcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_ghcg_conj_right
    (ay_ghcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_ghcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_ghcg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ghcg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_ghcg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_ghcg_accepted_forward_map
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_ghcg_equisat_forward originalCnf replayedCnf
    (ay_ghcg_accepted_equisat
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_ghcg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ghcg_CheckerReplay hashconsingReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_ghcg_CheckerReplay hashconsingReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_ghcg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ghcg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_ghcg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_ghcg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_ghcg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_ghcg_Sat replayedCnf replayedModel ->
    ay_ghcg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_ghcg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ghcg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_ghcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_ghcg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ghcg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_ghcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_ghcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_ghcg_disj_left
        (ay_ghcg_ExitCodeSound exitCode
          (ay_ghcg_Sat originalCnf originalModel))
        (ay_ghcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_ghcg_conj_intro exitCode
          (ay_ghcg_Sat originalCnf originalModel)
          hexit
          ((ay_ghcg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_ghcg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (gateSignature : Prop) (gateSignatureAccepted : Prop) (gateSignatureManifest : Prop)
    (canonicalRepresentative : Prop) (representativeAccepted : Prop) (canonicalRepresentativeWitness : Prop)
    (mergeSubstitutionCoverage : Prop) (mergeSubstitutionCoverageAccepted : Prop) (mergeSubstitutionCoverageManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (hashconsingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_ghcg_AcceptedGateHashconsingGuard
      originalCnf replayedCnf
      gateSignature gateSignatureAccepted gateSignatureManifest
      canonicalRepresentative representativeAccepted canonicalRepresentativeWitness
      mergeSubstitutionCoverage mergeSubstitutionCoverageAccepted mergeSubstitutionCoverageManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      hashconsingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ghcg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_ghcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_ghcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_ghcg_disj_right
        (ay_ghcg_ExitCodeSound exitCode
          (ay_ghcg_Sat originalCnf originalModel))
        (ay_ghcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_ghcg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_ghcg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_ghcg_failure_stale_gate_signature_digest
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleGateSignatureDigest ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_ghcg_failure_canonical_representative_witness
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    representativeMismatch ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_ghcg_failure_merge_substitution_coverage_digest
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    mergeSubstitutionCoverageMismatch ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_ghcg_failure_auxiliary_variable_domain
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auxiliaryDomainGap ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_ghcg_failure_reconstruction
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_ghcg_failure_stale_fingerprint
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_ghcg_failure_unchecked_replay
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_ghcg_failure_missing_baseline
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_ghcg_failure_build
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_ghcg_failure_validator
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_ghcg_failure_audit
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_ghcg_GateHashconsingGuardFailure
      staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_ghcg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ghcg_DiagnosticGateHashconsingGuard
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ghcg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_ghcg_conj_right
    (ay_ghcg_RecomputeObligation currentCnf recompute)
    (ay_ghcg_NoSemanticClaim diagnostic)
    (ay_ghcg_conj_right
      (ay_ghcg_GateHashconsingGuardFailure
        staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_ghcg_Conj
        (ay_ghcg_RecomputeObligation currentCnf recompute)
        (ay_ghcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_ghcg_diagnostic_recompute
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ghcg_DiagnosticGateHashconsingGuard
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ghcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_ghcg_conj_left
    (ay_ghcg_RecomputeObligation currentCnf recompute)
    (ay_ghcg_NoSemanticClaim diagnostic)
    (ay_ghcg_conj_right
      (ay_ghcg_GateHashconsingGuardFailure
        staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_ghcg_Conj
        (ay_ghcg_RecomputeObligation currentCnf recompute)
        (ay_ghcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_ghcg_unchecked_hashconsing_cannot_bless_public_result
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_ghcg_DiagnosticGateHashconsingGuard
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ghcg_Conj
      (ay_ghcg_NoSemanticClaim diagnostic)
      (ay_ghcg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_ghcg_conj_intro
    (ay_ghcg_NoSemanticClaim diagnostic)
    (ay_ghcg_RecomputeObligation currentCnf recompute)
    (ay_ghcg_diagnostic_no_claim
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_ghcg_diagnostic_recompute
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_ghcg_unchecked_hashconsing_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_ghcg_DiagnosticGateHashconsingGuard
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ghcg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_ghcg_diagnostic_no_claim
    currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_ghcg_unchecked_hashconsing_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleGateSignatureDigest : Prop) (representativeMismatch : Prop)
    (mergeSubstitutionCoverageMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_ghcg_DiagnosticGateHashconsingGuard
      currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_ghcg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_ghcg_diagnostic_recompute
    currentCnf staleGateSignatureDigest representativeMismatch mergeSubstitutionCoverageMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
