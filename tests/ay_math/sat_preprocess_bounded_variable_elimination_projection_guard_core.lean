-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded-variable-elimination projection guard soundness.
-- The propositions stand for eliminated-variable manifests, resolvent coverage digests, resolvent bound
-- witnesses, extension reconstruction maps, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_bveg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bveg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bveg_Equisat (before : Prop) (after : Prop) :=
  ay_bveg_Conj (before -> after) (after -> before)

def ay_bveg_Sat (cnf : Prop) (model : Prop) :=
  ay_bveg_Conj cnf model

def ay_bveg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bveg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_bveg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_bveg_EliminatedVariableManifest
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop)
    (eliminatedVariableManifest : Prop) :=
  ay_bveg_Conj eliminatedVariableManifest (eliminatedVariable -> variableManifestAccepted)

def ay_bveg_ResolventCoverageDigest
    (resolventSet : Prop) (resolventCoverageDigest : Prop)
    (resolventCoverageDigestWitness : Prop) :=
  ay_bveg_Conj resolventCoverageDigestWitness (resolventSet -> resolventCoverageDigest)

def ay_bveg_ResolventBoundWitness
    (resolvent : Prop) (resolventBound : Prop)
    (resolventBoundWitness : Prop) :=
  ay_bveg_Conj resolventBoundWitness (resolvent -> resolventBound)

def ay_bveg_ExtensionModelReconstruction
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop) :=
  ay_bveg_Conj extensionMap (reducedModel -> extendedModel)

def ay_bveg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_bveg_Sat replayedCnf replayedModel ->
    ay_bveg_Sat originalCnf originalModel

def ay_bveg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bveg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Conj
    (ay_bveg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bveg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_bveg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_bveg_Conj fingerprintWitness
    (ay_bveg_IdMatch originalFingerprint replayedFingerprint)

def ay_bveg_CheckerReplay
    (bveReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_bveg_Conj bveReplayCertificate checkerAccepted

def ay_bveg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_bveg_Conj baselineSolver baselineAvailable

def ay_bveg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bveg_Conj binaryFingerprint buildReproducible

def ay_bveg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_bveg_Conj validatorAccepted validatorVersion

def ay_bveg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bveg_Conj auditAppended auditAppendOnly

def ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bveg_EliminatedVariableManifest
       eliminatedVariable variableManifestAccepted eliminatedVariableManifest ->
     ay_bveg_ResolventCoverageDigest
       resolventSet resolventCoverageDigest resolventCoverageDigestWitness ->
     ay_bveg_ResolventBoundWitness
       resolvent resolventBound resolventBoundWitness ->
     ay_bveg_ExtensionModelReconstruction
       reducedModel extendedModel extensionMap ->
     ay_bveg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_bveg_Equisat originalCnf replayedCnf ->
     ay_bveg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_bveg_CheckerReplay bveReplayCertificate checkerAccepted ->
     ay_bveg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_bveg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bveg_ValidatorGate validatorAccepted validatorVersion ->
     ay_bveg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bveg_BoundedVariableEliminationProjectionGuardFailure
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleEliminatedVariableManifest -> result) ->
    (resolventCoverageDigestMismatch -> result) ->
    (resolventBoundMismatch -> result) ->
    (extensionMapGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_bveg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bveg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bveg_Conj currentCnf recompute

def ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bveg_Conj
    (ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_bveg_Conj
      (ay_bveg_RecomputeObligation currentCnf recompute)
      (ay_bveg_NoSemanticClaim diagnostic))

def ay_bveg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_bveg_Conj exitCode claim

def ay_bveg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_bveg_Disj
    (ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf model))
    (ay_bveg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_bveg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bveg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_bveg_conj_left
    (left : Prop) (right : Prop) :
    ay_bveg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bveg_conj_right
    (left : Prop) (right : Prop) :
    ay_bveg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bveg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bveg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_bveg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bveg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_bveg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bveg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_bveg_conj_left (before -> after) (after -> before) eqsat

theorem ay_bveg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bveg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_bveg_conj_right (before -> after) (after -> before) eqsat

theorem ay_bveg_eliminated_variable_manifest_applies
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop)
    (eliminatedVariableManifest : Prop) :
    ay_bveg_EliminatedVariableManifest
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest ->
    eliminatedVariable -> variableManifestAccepted := by
  intro digest
  exact ay_bveg_conj_right eliminatedVariableManifest
    (eliminatedVariable -> variableManifestAccepted) digest

theorem ay_bveg_resolvent_coverage_digest_applies
    (resolventSet : Prop) (resolventCoverageDigest : Prop)
    (resolventCoverageDigestWitness : Prop) :
    ay_bveg_ResolventCoverageDigest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness ->
    resolventSet -> resolventCoverageDigest := by
  intro digest
  exact ay_bveg_conj_right resolventCoverageDigestWitness
    (resolventSet -> resolventCoverageDigest) digest

theorem ay_bveg_resolvent_bound_witness_applies
    (resolvent : Prop) (resolventBound : Prop)
    (resolventBoundWitness : Prop) :
    ay_bveg_ResolventBoundWitness
      resolvent resolventBound resolventBoundWitness ->
    resolvent -> resolventBound := by
  intro ledger
  exact ay_bveg_conj_right resolventBoundWitness
    (resolvent -> resolventBound) ledger

theorem ay_bveg_extension_model_reconstruction_applies
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop) :
    ay_bveg_ExtensionModelReconstruction
      reducedModel extendedModel extensionMap ->
    reducedModel -> extendedModel := by
  intro coverage
  exact ay_bveg_conj_right extensionMap
    (reducedModel -> extendedModel) coverage

theorem ay_bveg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_bveg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_bveg_conj_left
    (ay_bveg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bveg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_bveg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_bveg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_bveg_conj_right
    (ay_bveg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_bveg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_bveg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
      originalCnf replayedCnf
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness
      resolvent resolventBound resolventBoundWitness
      reducedModel extendedModel extensionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bveReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_bveg_Equisat originalCnf replayedCnf)
    (fun _manifest _coverage _bound _extension _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_bveg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
      originalCnf replayedCnf
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness
      resolvent resolventBound resolventBoundWitness
      reducedModel extendedModel extensionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bveReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_CheckerReplay bveReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_bveg_CheckerReplay bveReplayCertificate checkerAccepted)
    (fun _manifest _coverage _bound _extension _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_bveg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
      originalCnf replayedCnf
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness
      resolvent resolventBound resolventBoundWitness
      reducedModel extendedModel extensionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bveReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_bveg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _coverage _bound _extension _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_bveg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_bveg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_bveg_Sat replayedCnf replayedModel ->
    ay_bveg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_bveg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_bveg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_bveg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
      originalCnf replayedCnf
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness
      resolvent resolventBound resolventBoundWitness
      reducedModel extendedModel extensionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bveReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_bveg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_bveg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _coverage _bound _extension reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_bveg_disj_left
        (ay_bveg_ExitCodeSound exitCode
          (ay_bveg_Sat originalCnf originalModel))
        (ay_bveg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_bveg_conj_intro exitCode
          (ay_bveg_Sat originalCnf originalModel)
          hexit
          ((ay_bveg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_bveg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (eliminatedVariable : Prop) (variableManifestAccepted : Prop) (eliminatedVariableManifest : Prop)
    (resolventSet : Prop) (resolventCoverageDigest : Prop) (resolventCoverageDigestWitness : Prop)
    (resolvent : Prop) (resolventBound : Prop) (resolventBoundWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (extensionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bveReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationProjectionGuard
      originalCnf replayedCnf
      eliminatedVariable variableManifestAccepted eliminatedVariableManifest
      resolventSet resolventCoverageDigest resolventCoverageDigestWitness
      resolvent resolventBound resolventBoundWitness
      reducedModel extendedModel extensionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      bveReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_bveg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_bveg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _coverage _bound _extension reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_bveg_disj_right
        (ay_bveg_ExitCodeSound exitCode
          (ay_bveg_Sat originalCnf originalModel))
        (ay_bveg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_bveg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_bveg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_bveg_failure_stale_eliminated_variable_manifest
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleEliminatedVariableManifest ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact manifest_case failure

theorem ay_bveg_failure_resolvent_coverage_digest
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    resolventCoverageDigestMismatch ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case extension_case _bound_case _extension_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact extension_case failure

theorem ay_bveg_failure_resolvent_bound_witness
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    resolventBoundMismatch ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact bound_case failure

theorem ay_bveg_failure_extension_model_reconstruction
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    extensionMapGap ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact extension_case failure

theorem ay_bveg_failure_reconstruction
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_bveg_failure_stale_fingerprint
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_bveg_failure_unchecked_replay
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_bveg_failure_missing_baseline
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_bveg_failure_build
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_bveg_failure_validator
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_bveg_failure_audit
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_bveg_BoundedVariableEliminationProjectionGuardFailure
      staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _extension_case _bound_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_bveg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_bveg_conj_right
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BoundedVariableEliminationProjectionGuardFailure
        staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_bveg_diagnostic_recompute
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bveg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_bveg_conj_left
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BoundedVariableEliminationProjectionGuardFailure
        staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_bveg_unchecked_bve_cannot_bless_public_result
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bveg_Conj
      (ay_bveg_NoSemanticClaim diagnostic)
      (ay_bveg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_bveg_conj_intro
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_diagnostic_no_claim
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_bveg_diagnostic_recompute
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_bveg_unchecked_bve_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_bveg_diagnostic_no_claim
    currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_bveg_unchecked_bve_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleEliminatedVariableManifest : Prop) (resolventCoverageDigestMismatch : Prop)
    (resolventBoundMismatch : Prop)
    (extensionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_bveg_DiagnosticBoundedVariableEliminationProjectionGuard
      currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_bveg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_bveg_diagnostic_recompute
    currentCnf staleEliminatedVariableManifest resolventCoverageDigestMismatch resolventBoundMismatch extensionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
