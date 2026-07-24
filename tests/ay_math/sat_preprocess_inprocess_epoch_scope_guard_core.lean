-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Inprocess epoch/scope guard soundness.
-- The propositions stand for inprocess epoch ledgers, assumption/scope stack
-- digests, transform manifests, reconstruction witness ledgers, replay hooks,
-- fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_iesg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_iesg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_iesg_Equisat (before : Prop) (after : Prop) :=
  ay_iesg_Conj (before -> after) (after -> before)

def ay_iesg_Sat (cnf : Prop) (model : Prop) :=
  ay_iesg_Conj cnf model

def ay_iesg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_iesg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_iesg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_iesg_InprocessEpochLedger
    (inprocessEpoch : Prop) (epochAccepted : Prop)
    (epochAcceptedWitness : Prop) :=
  ay_iesg_Conj epochAcceptedWitness (inprocessEpoch -> epochAccepted)

def ay_iesg_ScopeStackDigest
    (scopeStack : Prop) (scopeStackWitness : Prop)
    (scopeStackLedger : Prop) :=
  ay_iesg_Conj scopeStackLedger (scopeStack -> scopeStackWitness)

def ay_iesg_TransformManifest
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop) :=
  ay_iesg_Conj transformManifest (transformInput -> transformOutput)

def ay_iesg_ReconstructionWitnessLedger
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop) :=
  ay_iesg_Conj reconstructionOutputWitness (reconstructionInput -> reconstructionOutput)

def ay_iesg_ReplayReconstructionWitness
    (scopeStack : Prop) (replayHook : Prop)
    (replayLedger : Prop) :=
  ay_iesg_Conj replayLedger
    (scopeStack -> replayHook)

def ay_iesg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_iesg_Sat replayedCnf replayedModel ->
    ay_iesg_Sat originalCnf originalModel

def ay_iesg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_iesg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_iesg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_iesg_Conj
    (ay_iesg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_iesg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_iesg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_iesg_Conj fingerprintWitness
    (ay_iesg_IdMatch originalFingerprint replayedFingerprint)

def ay_iesg_CheckerReplay
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_iesg_Conj scopeStackReplayCertificate checkerAccepted

def ay_iesg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_iesg_Conj baselineSolver baselineAvailable

def ay_iesg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_iesg_Conj binaryFingerprint buildReproducible

def ay_iesg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_iesg_Conj validatorAccepted validatorVersion

def ay_iesg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_iesg_Conj auditAppended auditAppendOnly

def ay_iesg_AcceptedInprocessEpochScopeGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_iesg_InprocessEpochLedger
       inprocessEpoch epochAccepted epochAcceptedWitness ->
     ay_iesg_ScopeStackDigest
       scopeStack scopeStackWitness scopeStackLedger ->
     ay_iesg_TransformManifest
       transformInput transformOutput transformManifest ->
     ay_iesg_ReconstructionWitnessLedger
       reconstructionInput reconstructionOutput reconstructionOutputWitness ->
     ay_iesg_ReplayReconstructionWitness
       scopeStack replayHook replayLedger ->
     ay_iesg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_iesg_Equisat originalCnf replayedCnf ->
     ay_iesg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_iesg_CheckerReplay scopeStackReplayCertificate checkerAccepted ->
     ay_iesg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_iesg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_iesg_ValidatorGate validatorAccepted validatorVersion ->
     ay_iesg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_iesg_InprocessEpochScopeGuardFailure
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleEpoch -> result) ->
    (scopeDigestMismatch -> result) ->
    (transformManifestMismatch -> result) ->
    (reconstructionLedgerMismatch -> result) ->
    (replayHookMismatch -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_iesg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_iesg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_iesg_Conj currentCnf recompute

def ay_iesg_DiagnosticInprocessEpochScopeGuard
    (currentCnf : Prop)
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_iesg_Conj
    (ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch
      replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction)
    (ay_iesg_Conj
      (ay_iesg_RecomputeObligation currentCnf recompute)
      (ay_iesg_NoSemanticClaim diagnostic))

def ay_iesg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_iesg_Conj exitCode claim

def ay_iesg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_iesg_Disj
    (ay_iesg_ExitCodeSound exitCode (ay_iesg_Sat originalCnf model))
    (ay_iesg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_iesg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_iesg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_iesg_conj_left
    (left : Prop) (right : Prop) :
    ay_iesg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_iesg_conj_right
    (left : Prop) (right : Prop) :
    ay_iesg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_iesg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_iesg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_iesg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_iesg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_iesg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_iesg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_iesg_conj_left (before -> after) (after -> before) eqsat

theorem ay_iesg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_iesg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_iesg_conj_right (before -> after) (after -> before) eqsat

theorem ay_iesg_inprocess_epoch_ledger_applies
    (inprocessEpoch : Prop) (epochAccepted : Prop)
    (epochAcceptedWitness : Prop) :
    ay_iesg_InprocessEpochLedger
      inprocessEpoch epochAccepted epochAcceptedWitness ->
    inprocessEpoch -> epochAccepted := by
  intro digest
  exact ay_iesg_conj_right epochAcceptedWitness
    (inprocessEpoch -> epochAccepted) digest

theorem ay_iesg_scope_stack_digest_applies
    (scopeStack : Prop) (scopeStackWitness : Prop)
    (scopeStackLedger : Prop) :
    ay_iesg_ScopeStackDigest
      scopeStack scopeStackWitness scopeStackLedger ->
    scopeStack -> scopeStackWitness := by
  intro ledger
  exact ay_iesg_conj_right scopeStackLedger
    (scopeStack -> scopeStackWitness) ledger

theorem ay_iesg_transform_manifest
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop) :
    ay_iesg_TransformManifest
      transformInput transformOutput transformManifest ->
    transformInput -> transformOutput := by
  intro coverage
  exact ay_iesg_conj_right transformManifest
    (transformInput -> transformOutput) coverage

theorem ay_iesg_reconstruction_witness_ledger_applies
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop) :
    ay_iesg_ReconstructionWitnessLedger
      reconstructionInput reconstructionOutput reconstructionOutputWitness ->
    reconstructionInput -> reconstructionOutput := by
  intro extension
  exact ay_iesg_conj_right reconstructionOutputWitness
    (reconstructionInput -> reconstructionOutput) extension

theorem ay_iesg_replay_reconstruction_witness_applies
    (scopeStack : Prop) (replayHook : Prop)
    (replayLedger : Prop) :
    ay_iesg_ReplayReconstructionWitness
      scopeStack replayHook replayLedger ->
    scopeStack -> replayHook := by
  intro ledger
  exact ay_iesg_conj_right replayLedger
    (scopeStack -> replayHook) ledger

theorem ay_iesg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_iesg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_iesg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_iesg_conj_left
    (ay_iesg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_iesg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_iesg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_iesg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_iesg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_iesg_conj_right
    (ay_iesg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_iesg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_iesg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_iesg_AcceptedInprocessEpochScopeGuard
      originalCnf replayedCnf
      inprocessEpoch epochAccepted epochAcceptedWitness
      scopeStack scopeStackWitness scopeStackLedger
      transformInput transformOutput transformManifest
      reconstructionInput reconstructionOutput reconstructionOutputWitness
      replayHook replayLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      scopeStackReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_iesg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_iesg_Equisat originalCnf replayedCnf)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_iesg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_iesg_AcceptedInprocessEpochScopeGuard
      originalCnf replayedCnf
      inprocessEpoch epochAccepted epochAcceptedWitness
      scopeStack scopeStackWitness scopeStackLedger
      transformInput transformOutput transformManifest
      reconstructionInput reconstructionOutput reconstructionOutputWitness
      replayHook replayLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      scopeStackReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_iesg_CheckerReplay scopeStackReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_iesg_CheckerReplay scopeStackReplayCertificate checkerAccepted)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_iesg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_iesg_AcceptedInprocessEpochScopeGuard
      originalCnf replayedCnf
      inprocessEpoch epochAccepted epochAcceptedWitness
      scopeStack scopeStackWitness scopeStackLedger
      transformInput transformOutput transformManifest
      reconstructionInput reconstructionOutput reconstructionOutputWitness
      replayHook replayLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      scopeStackReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_iesg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_iesg_AuditTranscript auditAppended auditAppendOnly)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_iesg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_iesg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_iesg_Sat replayedCnf replayedModel ->
    ay_iesg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_iesg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_iesg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_iesg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_iesg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_iesg_AcceptedInprocessEpochScopeGuard
      originalCnf replayedCnf
      inprocessEpoch epochAccepted epochAcceptedWitness
      scopeStack scopeStackWitness scopeStackLedger
      transformInput transformOutput transformManifest
      reconstructionInput reconstructionOutput reconstructionOutputWitness
      replayHook replayLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      scopeStackReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_iesg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_iesg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_iesg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _cache _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_iesg_disj_left
        (ay_iesg_ExitCodeSound exitCode
          (ay_iesg_Sat originalCnf originalModel))
        (ay_iesg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_iesg_conj_intro exitCode
          (ay_iesg_Sat originalCnf originalModel)
          hexit
          ((ay_iesg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_iesg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (inprocessEpoch : Prop) (epochAccepted : Prop) (epochAcceptedWitness : Prop)
    (scopeStack : Prop) (scopeStackWitness : Prop) (scopeStackLedger : Prop)
    (transformInput : Prop) (transformOutput : Prop)
    (transformManifest : Prop)
    (reconstructionInput : Prop) (reconstructionOutput : Prop)
    (reconstructionOutputWitness : Prop)
    (replayHook : Prop) (replayLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (scopeStackReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_iesg_AcceptedInprocessEpochScopeGuard
      originalCnf replayedCnf
      inprocessEpoch epochAccepted epochAcceptedWitness
      scopeStack scopeStackWitness scopeStackLedger
      transformInput transformOutput transformManifest
      reconstructionInput reconstructionOutput reconstructionOutputWitness
      replayHook replayLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      scopeStackReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_iesg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_iesg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_iesg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _cache _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_iesg_disj_right
        (ay_iesg_ExitCodeSound exitCode
          (ay_iesg_Sat originalCnf originalModel))
        (ay_iesg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_iesg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_iesg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_iesg_failure_stale_epoch
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleEpoch ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result cache_case _assumption_case _coverage_case _trail_case
    _contradiction_case _reconstruction_case _fingerprint_case _replay_case
    _baseline_case _build_case _validator_case _audit_case
  exact cache_case failure

theorem ay_iesg_failure_scope_digest
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    scopeDigestMismatch ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_iesg_failure_transform_manifest
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    transformManifestMismatch ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_iesg_failure_reconstruction_ledger
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionLedgerMismatch ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case trail_case _contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact trail_case failure

theorem ay_iesg_failure_missing_replay_reconstruction_witness
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    replayHookMismatch ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact contradiction_case failure

theorem ay_iesg_failure_reconstruction
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_iesg_failure_stale_fingerprint
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_iesg_failure_unchecked_replay
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_iesg_failure_missing_baseline
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_iesg_failure_build
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_iesg_failure_validator
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_iesg_failure_audit
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_iesg_InprocessEpochScopeGuardFailure
      staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_iesg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_iesg_DiagnosticInprocessEpochScopeGuard
      currentCnf staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_iesg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_iesg_conj_right
    (ay_iesg_RecomputeObligation currentCnf recompute)
    (ay_iesg_NoSemanticClaim diagnostic)
    (ay_iesg_conj_right
      (ay_iesg_InprocessEpochScopeGuardFailure
        staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_iesg_Conj
        (ay_iesg_RecomputeObligation currentCnf recompute)
        (ay_iesg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_iesg_diagnostic_recompute
    (currentCnf : Prop)
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_iesg_DiagnosticInprocessEpochScopeGuard
      currentCnf staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_iesg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_iesg_conj_left
    (ay_iesg_RecomputeObligation currentCnf recompute)
    (ay_iesg_NoSemanticClaim diagnostic)
    (ay_iesg_conj_right
      (ay_iesg_InprocessEpochScopeGuardFailure
        staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_iesg_Conj
        (ay_iesg_RecomputeObligation currentCnf recompute)
        (ay_iesg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_iesg_unchecked_inprocessing_cannot_bless_public_result
    (currentCnf : Prop)
    (staleEpoch : Prop) (scopeDigestMismatch : Prop)
    (transformManifestMismatch : Prop)
    (reconstructionLedgerMismatch : Prop)
    (replayHookMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_iesg_DiagnosticInprocessEpochScopeGuard
      currentCnf staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_iesg_Conj
      (ay_iesg_NoSemanticClaim diagnostic)
      (ay_iesg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_iesg_conj_intro
    (ay_iesg_NoSemanticClaim diagnostic)
    (ay_iesg_RecomputeObligation currentCnf recompute)
    (ay_iesg_diagnostic_no_claim
      currentCnf staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_iesg_diagnostic_recompute
      currentCnf staleEpoch scopeDigestMismatch transformManifestMismatch reconstructionLedgerMismatch replayHookMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
