-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Unit-queue epoch guard soundness.
-- The propositions stand for unit queue epoch ledgers, unit queue digests, propagation trail
-- digests, derived unit coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_uqeg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_uqeg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_uqeg_Equisat (before : Prop) (after : Prop) :=
  ay_uqeg_Conj (before -> after) (after -> before)

def ay_uqeg_Sat (cnf : Prop) (model : Prop) :=
  ay_uqeg_Conj cnf model

def ay_uqeg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_uqeg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_uqeg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_uqeg_UnitQueueEpochLedger
    (unitQueueEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :=
  ay_uqeg_Conj epochLedger (unitQueueEpoch -> epochAccepted)

def ay_uqeg_UnitQueueDigest
    (unitQueue : Prop) (queueDigest : Prop)
    (queueDigestWitness : Prop) :=
  ay_uqeg_Conj queueDigestWitness (unitQueue -> queueDigest)

def ay_uqeg_PropagationTrailDigest
    (propagationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :=
  ay_uqeg_Conj trailDigestWitness (propagationTrail -> trailDigest)

def ay_uqeg_DerivedUnitCoverage
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop) :=
  ay_uqeg_Conj derivedUnitCoverageWitness (derivedUnit -> coveredDerivedUnit)

def ay_uqeg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_uqeg_Sat replayedCnf replayedModel ->
    ay_uqeg_Sat originalCnf originalModel

def ay_uqeg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_uqeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_uqeg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_uqeg_Conj
    (ay_uqeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_uqeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_uqeg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_uqeg_Conj fingerprintWitness
    (ay_uqeg_IdMatch originalFingerprint replayedFingerprint)

def ay_uqeg_CheckerReplay
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_uqeg_Conj unitQueueReplayCertificate checkerAccepted

def ay_uqeg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_uqeg_Conj baselineSolver baselineAvailable

def ay_uqeg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_uqeg_Conj binaryFingerprint buildReproducible

def ay_uqeg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_uqeg_Conj validatorAccepted validatorVersion

def ay_uqeg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_uqeg_Conj auditAppended auditAppendOnly

def ay_uqeg_AcceptedUnitQueueEpochGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_uqeg_UnitQueueEpochLedger
       unitQueueEpoch epochAccepted epochLedger ->
     ay_uqeg_UnitQueueDigest
       unitQueue queueDigest queueDigestWitness ->
     ay_uqeg_PropagationTrailDigest
       propagationTrail trailDigest trailDigestWitness ->
     ay_uqeg_DerivedUnitCoverage
       derivedUnit coveredDerivedUnit derivedUnitCoverageWitness ->
     ay_uqeg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_uqeg_Equisat originalCnf replayedCnf ->
     ay_uqeg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_uqeg_CheckerReplay unitQueueReplayCertificate checkerAccepted ->
     ay_uqeg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_uqeg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_uqeg_ValidatorGate validatorAccepted validatorVersion ->
     ay_uqeg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_uqeg_UnitQueueEpochGuardFailure
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleQueueEpoch -> result) ->
    (queueDigestMismatch -> result) ->
    (trailDigestMismatch -> result) ->
    (derivedUnitCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_uqeg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_uqeg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_uqeg_Conj currentCnf recompute

def ay_uqeg_DiagnosticUnitQueueEpochGuard
    (currentCnf : Prop)
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_uqeg_Conj
    (ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_uqeg_Conj
      (ay_uqeg_RecomputeObligation currentCnf recompute)
      (ay_uqeg_NoSemanticClaim diagnostic))

def ay_uqeg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_uqeg_Conj exitCode claim

def ay_uqeg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_uqeg_Disj
    (ay_uqeg_ExitCodeSound exitCode (ay_uqeg_Sat originalCnf model))
    (ay_uqeg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_uqeg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_uqeg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_uqeg_conj_left
    (left : Prop) (right : Prop) :
    ay_uqeg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_uqeg_conj_right
    (left : Prop) (right : Prop) :
    ay_uqeg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_uqeg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_uqeg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_uqeg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_uqeg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_uqeg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_uqeg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_uqeg_conj_left (before -> after) (after -> before) eqsat

theorem ay_uqeg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_uqeg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_uqeg_conj_right (before -> after) (after -> before) eqsat

theorem ay_uqeg_unit_queue_epoch_ledger_applies
    (unitQueueEpoch : Prop) (epochAccepted : Prop)
    (epochLedger : Prop) :
    ay_uqeg_UnitQueueEpochLedger
      unitQueueEpoch epochAccepted epochLedger ->
    unitQueueEpoch -> epochAccepted := by
  intro digest
  exact ay_uqeg_conj_right epochLedger
    (unitQueueEpoch -> epochAccepted) digest

theorem ay_uqeg_unit_queue_digest_applies
    (unitQueue : Prop) (queueDigest : Prop)
    (queueDigestWitness : Prop) :
    ay_uqeg_UnitQueueDigest
      unitQueue queueDigest queueDigestWitness ->
    unitQueue -> queueDigest := by
  intro digest
  exact ay_uqeg_conj_right queueDigestWitness
    (unitQueue -> queueDigest) digest

theorem ay_uqeg_propagation_trail_digest_applies
    (propagationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :
    ay_uqeg_PropagationTrailDigest
      propagationTrail trailDigest trailDigestWitness ->
    propagationTrail -> trailDigest := by
  intro ledger
  exact ay_uqeg_conj_right trailDigestWitness
    (propagationTrail -> trailDigest) ledger

theorem ay_uqeg_derived_unit_coverage
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop) :
    ay_uqeg_DerivedUnitCoverage
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness ->
    derivedUnit -> coveredDerivedUnit := by
  intro coverage
  exact ay_uqeg_conj_right derivedUnitCoverageWitness
    (derivedUnit -> coveredDerivedUnit) coverage

theorem ay_uqeg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_uqeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_uqeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_uqeg_conj_left
    (ay_uqeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_uqeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_uqeg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_uqeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_uqeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_uqeg_conj_right
    (ay_uqeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_uqeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_uqeg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_uqeg_AcceptedUnitQueueEpochGuard
      originalCnf replayedCnf
      unitQueueEpoch epochAccepted epochLedger
      unitQueue queueDigest queueDigestWitness
      propagationTrail trailDigest trailDigestWitness
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      unitQueueReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_uqeg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_uqeg_Equisat originalCnf replayedCnf)
    (fun _epoch _digest _trail _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_uqeg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_uqeg_AcceptedUnitQueueEpochGuard
      originalCnf replayedCnf
      unitQueueEpoch epochAccepted epochLedger
      unitQueue queueDigest queueDigestWitness
      propagationTrail trailDigest trailDigestWitness
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      unitQueueReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_uqeg_CheckerReplay unitQueueReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_uqeg_CheckerReplay unitQueueReplayCertificate checkerAccepted)
    (fun _epoch _digest _trail _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_uqeg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_uqeg_AcceptedUnitQueueEpochGuard
      originalCnf replayedCnf
      unitQueueEpoch epochAccepted epochLedger
      unitQueue queueDigest queueDigestWitness
      propagationTrail trailDigest trailDigestWitness
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      unitQueueReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_uqeg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_uqeg_AuditTranscript auditAppended auditAppendOnly)
    (fun _epoch _digest _trail _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_uqeg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_uqeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_uqeg_Sat replayedCnf replayedModel ->
    ay_uqeg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_uqeg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_uqeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_uqeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_uqeg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_uqeg_AcceptedUnitQueueEpochGuard
      originalCnf replayedCnf
      unitQueueEpoch epochAccepted epochLedger
      unitQueue queueDigest queueDigestWitness
      propagationTrail trailDigest trailDigestWitness
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      unitQueueReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_uqeg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_uqeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_uqeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _trail _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_uqeg_disj_left
        (ay_uqeg_ExitCodeSound exitCode
          (ay_uqeg_Sat originalCnf originalModel))
        (ay_uqeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_uqeg_conj_intro exitCode
          (ay_uqeg_Sat originalCnf originalModel)
          hexit
          ((ay_uqeg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_uqeg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (unitQueueEpoch : Prop) (epochAccepted : Prop) (epochLedger : Prop)
    (unitQueue : Prop) (queueDigest : Prop) (queueDigestWitness : Prop)
    (propagationTrail : Prop) (trailDigest : Prop) (trailDigestWitness : Prop)
    (derivedUnit : Prop) (coveredDerivedUnit : Prop)
    (derivedUnitCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (unitQueueReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_uqeg_AcceptedUnitQueueEpochGuard
      originalCnf replayedCnf
      unitQueueEpoch epochAccepted epochLedger
      unitQueue queueDigest queueDigestWitness
      propagationTrail trailDigest trailDigestWitness
      derivedUnit coveredDerivedUnit derivedUnitCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      unitQueueReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_uqeg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_uqeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_uqeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _epoch _digest _trail _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_uqeg_disj_right
        (ay_uqeg_ExitCodeSound exitCode
          (ay_uqeg_Sat originalCnf originalModel))
        (ay_uqeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_uqeg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_uqeg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_uqeg_failure_stale_epoch
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleQueueEpoch ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact epoch_case failure

theorem ay_uqeg_failure_unit_queue_digest
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    queueDigestMismatch ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case digest_case _witness_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case failure

theorem ay_uqeg_failure_propagation_trail_digest
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    trailDigestMismatch ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_uqeg_failure_derived_unit_coverage
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    derivedUnitCoverageGap ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_uqeg_failure_reconstruction
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_uqeg_failure_stale_fingerprint
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_uqeg_failure_unchecked_replay
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_uqeg_failure_missing_baseline
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_uqeg_failure_build
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_uqeg_failure_validator
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_uqeg_failure_audit
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_uqeg_UnitQueueEpochGuardFailure
      staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _epoch_case _digest_case _witness_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_uqeg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_uqeg_DiagnosticUnitQueueEpochGuard
      currentCnf staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_uqeg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_uqeg_conj_right
    (ay_uqeg_RecomputeObligation currentCnf recompute)
    (ay_uqeg_NoSemanticClaim diagnostic)
    (ay_uqeg_conj_right
      (ay_uqeg_UnitQueueEpochGuardFailure
        staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_uqeg_Conj
        (ay_uqeg_RecomputeObligation currentCnf recompute)
        (ay_uqeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_uqeg_diagnostic_recompute
    (currentCnf : Prop)
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_uqeg_DiagnosticUnitQueueEpochGuard
      currentCnf staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_uqeg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_uqeg_conj_left
    (ay_uqeg_RecomputeObligation currentCnf recompute)
    (ay_uqeg_NoSemanticClaim diagnostic)
    (ay_uqeg_conj_right
      (ay_uqeg_UnitQueueEpochGuardFailure
        staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_uqeg_Conj
        (ay_uqeg_RecomputeObligation currentCnf recompute)
        (ay_uqeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_uqeg_unchecked_queue_state_cannot_bless_public_result
    (currentCnf : Prop)
    (staleQueueEpoch : Prop) (queueDigestMismatch : Prop)
    (trailDigestMismatch : Prop)
    (derivedUnitCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_uqeg_DiagnosticUnitQueueEpochGuard
      currentCnf staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_uqeg_Conj
      (ay_uqeg_NoSemanticClaim diagnostic)
      (ay_uqeg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_uqeg_conj_intro
    (ay_uqeg_NoSemanticClaim diagnostic)
    (ay_uqeg_RecomputeObligation currentCnf recompute)
    (ay_uqeg_diagnostic_no_claim
      currentCnf staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_uqeg_diagnostic_recompute
      currentCnf staleQueueEpoch queueDigestMismatch trailDigestMismatch derivedUnitCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
