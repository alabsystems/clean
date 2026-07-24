-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Watched-clause epoch guard soundness.
-- The propositions stand for watched-clause epoch ledgers, watched-clause digests, propagation trail
-- digests, transform coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_wceg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_wceg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_wceg_Equisat (before : Prop) (after : Prop) :=
  ay_wceg_Conj (before -> after) (after -> before)

def ay_wceg_Sat (cnf : Prop) (model : Prop) :=
  ay_wceg_Conj cnf model

def ay_wceg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_wceg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_wceg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_wceg_WatchedClauseEpochLedger
    (watchedClauseEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :=
  ay_wceg_Conj epochLedger (watchedClauseEpoch -> epochAccepted)

def ay_wceg_WatchedClauseDigest
    (watchedClauseState : Prop) (watchedClauseDigest : Prop)
    (watchedClauseDigestWitness : Prop) :=
  ay_wceg_Conj watchedClauseDigestWitness (watchedClauseState -> watchedClauseDigest)

def ay_wceg_PropagationTrailDigest
    (propagationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :=
  ay_wceg_Conj trailDigestWitness (propagationTrail -> trailDigest)

def ay_wceg_TransformCoverage
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop) :=
  ay_wceg_Conj transformCoverageWitness (transformInput -> coveredTransform)

def ay_wceg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_wceg_Sat replayedCnf replayedModel ->
    ay_wceg_Sat originalCnf originalModel

def ay_wceg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_wceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_wceg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_wceg_Conj
    (ay_wceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_wceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_wceg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_wceg_Conj fingerprintWitness
    (ay_wceg_IdMatch originalFingerprint replayedFingerprint)

def ay_wceg_CheckerReplay
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_wceg_Conj watchedClauseReplayCertificate checkerAccepted

def ay_wceg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_wceg_Conj baselineSolver baselineAvailable

def ay_wceg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_wceg_Conj binaryFingerprint buildReproducible

def ay_wceg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_wceg_Conj validatorAccepted validatorVersion

def ay_wceg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_wceg_Conj auditAppended auditAppendOnly

def ay_wceg_AcceptedWatchedClauseEpochGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_wceg_WatchedClauseEpochLedger
       watchedClauseEpoch epochAccepted epochLedger ->
     ay_wceg_WatchedClauseDigest
       watchedClauseState watchedClauseDigest watchedClauseDigestWitness ->
     ay_wceg_PropagationTrailDigest
       propagationTrail trailDigest trailDigestWitness ->
     ay_wceg_TransformCoverage
       transformInput coveredTransform transformCoverageWitness ->
     ay_wceg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_wceg_Equisat originalCnf replayedCnf ->
     ay_wceg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_wceg_CheckerReplay watchedClauseReplayCertificate checkerAccepted ->
     ay_wceg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_wceg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_wceg_ValidatorGate validatorAccepted validatorVersion ->
     ay_wceg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_wceg_WatchedClauseEpochGuardFailure
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleWatchedClauseEpoch -> result) ->
    (watchedClauseDigestMismatch -> result) ->
    (trailDigestMismatch -> result) ->
    (transformCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_wceg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_wceg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_wceg_Conj currentCnf recompute

def ay_wceg_DiagnosticWatchedClauseEpochGuard
    (currentCnf : Prop)
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_wceg_Conj
    (ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_wceg_Conj
      (ay_wceg_RecomputeObligation currentCnf recompute)
      (ay_wceg_NoSemanticClaim diagnostic))

def ay_wceg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_wceg_Conj exitCode claim

def ay_wceg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_wceg_Disj
    (ay_wceg_ExitCodeSound exitCode (ay_wceg_Sat originalCnf model))
    (ay_wceg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_wceg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_wceg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_wceg_conj_left
    (left : Prop) (right : Prop) :
    ay_wceg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_wceg_conj_right
    (left : Prop) (right : Prop) :
    ay_wceg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_wceg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_wceg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_wceg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_wceg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_wceg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_wceg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_wceg_conj_left (before -> after) (after -> before) eqsat

theorem ay_wceg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_wceg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_wceg_conj_right (before -> after) (after -> before) eqsat

theorem ay_wceg_watched_clause_epoch_ledger_applies
    (watchedClauseEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :
    ay_wceg_WatchedClauseEpochLedger
      watchedClauseEpoch epochAccepted epochLedger ->
    watchedClauseEpoch -> epochAccepted := by
  intro digest
  exact ay_wceg_conj_right epochLedger
    (watchedClauseEpoch -> epochAccepted) digest

theorem ay_wceg_watched_clause_digest_applies
    (watchedClauseState : Prop) (watchedClauseDigest : Prop)
    (watchedClauseDigestWitness : Prop) :
    ay_wceg_WatchedClauseDigest
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness ->
    watchedClauseState -> watchedClauseDigest := by
  intro digest
  exact ay_wceg_conj_right watchedClauseDigestWitness
    (watchedClauseState -> watchedClauseDigest) digest

theorem ay_wceg_propagation_trail_digest_applies
    (propagationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :
    ay_wceg_PropagationTrailDigest
      propagationTrail trailDigest trailDigestWitness ->
    propagationTrail -> trailDigest := by
  intro ledger
  exact ay_wceg_conj_right trailDigestWitness
    (propagationTrail -> trailDigest) ledger

theorem ay_wceg_transform_coverage
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop) :
    ay_wceg_TransformCoverage
      transformInput coveredTransform transformCoverageWitness ->
    transformInput -> coveredTransform := by
  intro coverage
  exact ay_wceg_conj_right transformCoverageWitness
    (transformInput -> coveredTransform) coverage

theorem ay_wceg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_wceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_wceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_wceg_conj_left
    (ay_wceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_wceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_wceg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_wceg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_wceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_wceg_conj_right
    (ay_wceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_wceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_wceg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_wceg_AcceptedWatchedClauseEpochGuard
      originalCnf replayedCnf
      watchedClauseEpoch epochAccepted epochLedger
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness
      propagationTrail trailDigest trailDigestWitness
      transformInput coveredTransform transformCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      watchedClauseReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_wceg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_wceg_Equisat originalCnf replayedCnf)
    (fun _epoch _digest _trail _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_wceg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_wceg_AcceptedWatchedClauseEpochGuard
      originalCnf replayedCnf
      watchedClauseEpoch epochAccepted epochLedger
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness
      propagationTrail trailDigest trailDigestWitness
      transformInput coveredTransform transformCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      watchedClauseReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_wceg_CheckerReplay watchedClauseReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_wceg_CheckerReplay watchedClauseReplayCertificate checkerAccepted)
    (fun _epoch _digest _trail _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_wceg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_wceg_AcceptedWatchedClauseEpochGuard
      originalCnf replayedCnf
      watchedClauseEpoch epochAccepted epochLedger
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness
      propagationTrail trailDigest trailDigestWitness
      transformInput coveredTransform transformCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      watchedClauseReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_wceg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_wceg_AuditTranscript auditAppended auditAppendOnly)
    (fun _epoch _digest _trail _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_wceg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_wceg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_wceg_Sat replayedCnf replayedModel ->
    ay_wceg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_wceg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_wceg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_wceg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_wceg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_wceg_AcceptedWatchedClauseEpochGuard
      originalCnf replayedCnf
      watchedClauseEpoch epochAccepted epochLedger
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness
      propagationTrail trailDigest trailDigestWitness
      transformInput coveredTransform transformCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      watchedClauseReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_wceg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_wceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_wceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _trail _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_wceg_disj_left
        (ay_wceg_ExitCodeSound exitCode
          (ay_wceg_Sat originalCnf originalModel))
        (ay_wceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_wceg_conj_intro exitCode
          (ay_wceg_Sat originalCnf originalModel)
          hexit
          ((ay_wceg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_wceg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (watchedClauseEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (watchedClauseState : Prop) (watchedClauseDigest : Prop) (watchedClauseDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (transformInput : Prop) (coveredTransform : Prop)
    (transformCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (watchedClauseReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_wceg_AcceptedWatchedClauseEpochGuard
      originalCnf replayedCnf
      watchedClauseEpoch epochAccepted epochLedger
      watchedClauseState watchedClauseDigest watchedClauseDigestWitness
      propagationTrail trailDigest trailDigestWitness
      transformInput coveredTransform transformCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      watchedClauseReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_wceg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_wceg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_wceg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _trail _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_wceg_disj_right
        (ay_wceg_ExitCodeSound exitCode
          (ay_wceg_Sat originalCnf originalModel))
        (ay_wceg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_wceg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_wceg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_wceg_failure_stale_epoch
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleWatchedClauseEpoch ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact epoch_case failure

theorem ay_wceg_failure_watched_clause_digest
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    watchedClauseDigestMismatch ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case digest_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case failure

theorem ay_wceg_failure_propagation_trail_digest
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    trailDigestMismatch ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_wceg_failure_transform_coverage
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    transformCoverageGap ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_wceg_failure_reconstruction
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_wceg_failure_stale_fingerprint
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_wceg_failure_unchecked_replay
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_wceg_failure_missing_baseline
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_wceg_failure_build
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_wceg_failure_validator
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_wceg_failure_audit
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_wceg_WatchedClauseEpochGuardFailure
      staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_wceg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_wceg_DiagnosticWatchedClauseEpochGuard
      currentCnf staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_wceg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_wceg_conj_right
    (ay_wceg_RecomputeObligation currentCnf recompute)
    (ay_wceg_NoSemanticClaim diagnostic)
    (ay_wceg_conj_right
      (ay_wceg_WatchedClauseEpochGuardFailure
        staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_wceg_Conj
        (ay_wceg_RecomputeObligation currentCnf recompute)
        (ay_wceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_wceg_diagnostic_recompute
    (currentCnf : Prop)
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_wceg_DiagnosticWatchedClauseEpochGuard
      currentCnf staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_wceg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_wceg_conj_left
    (ay_wceg_RecomputeObligation currentCnf recompute)
    (ay_wceg_NoSemanticClaim diagnostic)
    (ay_wceg_conj_right
      (ay_wceg_WatchedClauseEpochGuardFailure
        staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_wceg_Conj
        (ay_wceg_RecomputeObligation currentCnf recompute)
        (ay_wceg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_wceg_unchecked_watched_clause_state_cannot_bless_public_result
    (currentCnf : Prop)
    (staleWatchedClauseEpoch : Prop) (watchedClauseDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (transformCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_wceg_DiagnosticWatchedClauseEpochGuard
      currentCnf staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_wceg_Conj
      (ay_wceg_NoSemanticClaim diagnostic)
      (ay_wceg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_wceg_conj_intro
    (ay_wceg_NoSemanticClaim diagnostic)
    (ay_wceg_RecomputeObligation currentCnf recompute)
    (ay_wceg_diagnostic_no_claim
      currentCnf staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_wceg_diagnostic_recompute
      currentCnf staleWatchedClauseEpoch watchedClauseDigestMismatch trailDigestMismatch transformCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
