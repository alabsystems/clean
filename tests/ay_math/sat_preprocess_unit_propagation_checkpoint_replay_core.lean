-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Unit-propagation checkpoint replay soundness for preprocessing. The
-- propositions stand for unit queue checkpoints, implication ledgers,
-- clause coverage, trail/level snapshots, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pupc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pupc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pupc_Equisat (before : Prop) (after : Prop) :=
  ay_pupc_Conj (before -> after) (after -> before)

def ay_pupc_Sat (cnf : Prop) (model : Prop) :=
  ay_pupc_Conj cnf model

def ay_pupc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pupc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pupc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pupc_UnitQueueCheckpoint
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop) :=
  ay_pupc_Conj checkpointWitness
    (unitQueue -> checkpointQueue)

def ay_pupc_ImplicationLedger
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop) :=
  ay_pupc_Conj implicationLedger
    (ay_pupc_Conj impliedLiteral implicationReason)

def ay_pupc_ClauseCoverage
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pupc_Conj coverageWitness (touchedClause -> coveredClause)

def ay_pupc_TrailLevelSnapshot
    (checkpointLedger : Prop) (checkpointQueue : Prop)
    (ledgerWitness : Prop) :=
  ay_pupc_Conj ledgerWitness
    (checkpointQueue -> checkpointLedger)

def ay_pupc_ModelReconstruction
    (checkpointCnf : Prop) (originalCnf : Prop)
    (checkpointModel : Prop) (originalModel : Prop) :=
  ay_pupc_Sat checkpointCnf checkpointModel ->
    ay_pupc_Sat originalCnf originalModel

def ay_pupc_ProofReconstruction
    (originalCnf : Prop) (checkpointCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pupc_Replay checkpointCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pupc_FingerprintAgreement
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pupc_Conj fingerprintWitness
    (ay_pupc_IdMatch originalFingerprint checkpointFingerprint)

def ay_pupc_CheckerReplay
    (checkpointCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pupc_Conj checkpointCertificate checkerAccepted

def ay_pupc_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pupc_Conj baselineSolver baselineAvailable

def ay_pupc_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pupc_Conj binaryFingerprint buildReproducible

def ay_pupc_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pupc_Conj validatorAccepted validatorVersion

def ay_pupc_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pupc_Conj auditAppended auditAppendOnly

def ay_pupc_AcceptedUnitPropagationCheckpointReplay
    (originalCnf : Prop) (checkpointCnf : Prop)
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop)
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop)
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (checkpointLedger : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (checkpointCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pupc_UnitQueueCheckpoint
       unitQueue checkpointQueue checkpointWitness ->
     ay_pupc_ImplicationLedger
       impliedLiteral implicationReason implicationLedger ->
     ay_pupc_ClauseCoverage
       touchedClause coveredClause coverageWitness ->
     ay_pupc_TrailLevelSnapshot
       checkpointLedger checkpointQueue ledgerWitness ->
     ay_pupc_Equisat originalCnf checkpointCnf ->
     ay_pupc_ModelReconstruction
       checkpointCnf originalCnf checkpointModel originalModel ->
     ay_pupc_ProofReconstruction
       originalCnf checkpointCnf certificate conflict ->
     ay_pupc_FingerprintAgreement
       originalFingerprint checkpointFingerprint fingerprintWitness ->
     ay_pupc_CheckerReplay
       checkpointCertificate checkerAccepted ->
     ay_pupc_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pupc_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pupc_ValidatorGate validatorAccepted validatorVersion ->
     ay_pupc_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pupc_CheckpointFailure
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (trailLevelMismatch : Prop) :=
  ay_pupc_Disj checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))

def ay_pupc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pupc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pupc_Conj currentCnf recompute

def ay_pupc_DiagnosticUnitPropagationCheckpointReplay
    (currentCnf : Prop)
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pupc_Conj
    (ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch)
    (ay_pupc_Conj
      (ay_pupc_RecomputeObligation currentCnf recompute)
      (ay_pupc_NoSemanticClaim diagnostic))

def ay_pupc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pupc_Conj exitCode claim

def ay_pupc_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pupc_Disj
    (ay_pupc_ExitCodeSound exitCode (ay_pupc_Sat originalCnf model))
    (ay_pupc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pupc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pupc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pupc_conj_left
    (left : Prop) (right : Prop) :
    ay_pupc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pupc_conj_right
    (left : Prop) (right : Prop) :
    ay_pupc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pupc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pupc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pupc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pupc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pupc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pupc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pupc_conj_left (before -> after) (after -> before) eq

theorem ay_pupc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pupc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pupc_conj_right (before -> after) (after -> before) eq

theorem ay_pupc_unit_queue_checkpoint_applies
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop) :
    ay_pupc_UnitQueueCheckpoint
      unitQueue checkpointQueue checkpointWitness ->
    unitQueue ->
    checkpointQueue := by
  intro accepted raw
  exact
    (ay_pupc_conj_right checkpointWitness
      (unitQueue -> checkpointQueue) accepted) raw

theorem ay_pupc_implication_ledger_literal
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop) :
    ay_pupc_ImplicationLedger
      impliedLiteral implicationReason implicationLedger ->
    impliedLiteral := by
  intro accepted
  exact accepted impliedLiteral
    (fun _ledger pair =>
      pair impliedLiteral
        (fun duplicate _tautology => duplicate))

theorem ay_pupc_implication_ledger_reason
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop) :
    ay_pupc_ImplicationLedger
      impliedLiteral implicationReason implicationLedger ->
    implicationReason := by
  intro accepted
  exact accepted implicationReason
    (fun _ledger pair =>
      pair implicationReason
        (fun _duplicate tautology => tautology))

theorem ay_pupc_clause_coverage
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pupc_ClauseCoverage
      touchedClause coveredClause coverageWitness ->
    touchedClause ->
    coveredClause := by
  intro accepted original
  exact
    (ay_pupc_conj_right coverageWitness
      (touchedClause -> coveredClause) accepted) original

theorem ay_pupc_checkpoint_ledger_records
    (checkpointLedger : Prop) (checkpointQueue : Prop)
    (ledgerWitness : Prop) :
    ay_pupc_TrailLevelSnapshot
      checkpointLedger checkpointQueue ledgerWitness ->
    checkpointQueue ->
    checkpointLedger := by
  intro accepted canonical
  exact
    (ay_pupc_conj_right ledgerWitness
      (checkpointQueue -> checkpointLedger) accepted) canonical

theorem ay_pupc_accepted_equisat
    (originalCnf : Prop) (checkpointCnf : Prop)
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop)
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop)
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (checkpointLedger : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (checkpointCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pupc_AcceptedUnitPropagationCheckpointReplay
      originalCnf checkpointCnf unitQueue checkpointQueue
      checkpointWitness impliedLiteral implicationReason
      implicationLedger touchedClause coveredClause coverageWitness
      checkpointLedger ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness checkpointCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pupc_Equisat originalCnf checkpointCnf := by
  intro accepted
  exact accepted (ay_pupc_Equisat originalCnf checkpointCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pupc_accepted_checker_replay
    (originalCnf : Prop) (checkpointCnf : Prop)
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop)
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop)
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (checkpointLedger : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (checkpointCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pupc_AcceptedUnitPropagationCheckpointReplay
      originalCnf checkpointCnf unitQueue checkpointQueue
      checkpointWitness impliedLiteral implicationReason
      implicationLedger touchedClause coveredClause coverageWitness
      checkpointLedger ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness checkpointCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pupc_CheckerReplay checkpointCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pupc_CheckerReplay checkpointCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pupc_accepted_audit_evidence
    (originalCnf : Prop) (checkpointCnf : Prop)
    (unitQueue : Prop) (checkpointQueue : Prop)
    (checkpointWitness : Prop)
    (impliedLiteral : Prop) (implicationReason : Prop)
    (implicationLedger : Prop)
    (touchedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (checkpointLedger : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (checkpointCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pupc_AcceptedUnitPropagationCheckpointReplay
      originalCnf checkpointCnf unitQueue checkpointQueue
      checkpointWitness impliedLiteral implicationReason
      implicationLedger touchedClause coveredClause coverageWitness
      checkpointLedger ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness checkpointCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pupc_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pupc_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pupc_sat_pullback
    (checkpointCnf : Prop) (originalCnf : Prop)
    (checkpointModel : Prop) (originalModel : Prop) :
    ay_pupc_ModelReconstruction
      checkpointCnf originalCnf checkpointModel originalModel ->
    ay_pupc_Sat checkpointCnf checkpointModel ->
    ay_pupc_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pupc_unsat_pushback
    (originalCnf : Prop) (checkpointCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pupc_ProofReconstruction
      originalCnf checkpointCnf certificate conflict ->
    ay_pupc_Replay checkpointCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pupc_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pupc_Sat originalCnf model ->
    ay_pupc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pupc_disj_left
    (ay_pupc_ExitCodeSound exitCode (ay_pupc_Sat originalCnf model))
    (ay_pupc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pupc_conj_intro exitCode
      (ay_pupc_Sat originalCnf model) exit sat)

theorem ay_pupc_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pupc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pupc_disj_right
    (ay_pupc_ExitCodeSound exitCode (ay_pupc_Sat originalCnf model))
    (ay_pupc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pupc_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pupc_failure_checkpoint_drift
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    checkpointDrift ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro drift
  exact ay_pupc_disj_left checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    drift

theorem ay_pupc_failure_implication_mismatch
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    implicationMismatch ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro mismatch
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_left implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      mismatch)

theorem ay_pupc_failure_coverage_gap
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    coverageGap ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro gap
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_left coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        gap))

theorem ay_pupc_failure_stale_fingerprint
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    staleFingerprint ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro stale
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_right coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        (ay_pupc_disj_left staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))
          stale)))

theorem ay_pupc_failure_unchecked_replay
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    uncheckedReplay ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro unchecked
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_right coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        (ay_pupc_disj_right staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))
          (ay_pupc_disj_left uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))
            unchecked))))

theorem ay_pupc_failure_build_drift
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    buildDrift ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro drift
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_right coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        (ay_pupc_disj_right staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))
          (ay_pupc_disj_right uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))
            (ay_pupc_disj_left buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)
              drift)))))

theorem ay_pupc_failure_audit_contradiction
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    auditContradiction ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro auditBad
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_right coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        (ay_pupc_disj_right staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))
          (ay_pupc_disj_right uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))
            (ay_pupc_disj_right buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)
              (ay_pupc_disj_left auditContradiction trailLevelMismatch
                auditBad))))))

theorem ay_pupc_failure_trail_level_mismatch
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop) :
    trailLevelMismatch ->
    ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch := by
  intro mismatch
  exact ay_pupc_disj_right checkpointDrift
    (ay_pupc_Disj implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))))
    (ay_pupc_disj_right implicationMismatch
      (ay_pupc_Disj coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))))
      (ay_pupc_disj_right coverageGap
        (ay_pupc_Disj staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))))
        (ay_pupc_disj_right staleFingerprint
          (ay_pupc_Disj uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)))
          (ay_pupc_disj_right uncheckedReplay
            (ay_pupc_Disj buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch))
            (ay_pupc_disj_right buildDrift
              (ay_pupc_Disj auditContradiction trailLevelMismatch)
              (ay_pupc_disj_right auditContradiction trailLevelMismatch
                mismatch))))))

theorem ay_pupc_diagnostic_no_claim
    (currentCnf : Prop)
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pupc_DiagnosticUnitPropagationCheckpointReplay
      currentCnf checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch recompute diagnostic ->
    ay_pupc_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pupc_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pupc_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pupc_diagnostic_recompute
    (currentCnf : Prop)
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pupc_DiagnosticUnitPropagationCheckpointReplay
      currentCnf checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch recompute diagnostic ->
    ay_pupc_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pupc_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pupc_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pupc_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (checkpointDrift : Prop) (implicationMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (trailLevelMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pupc_RecomputeObligation currentCnf recompute ->
    ay_pupc_NoSemanticClaim diagnostic ->
    ay_pupc_DiagnosticUnitPropagationCheckpointReplay
      currentCnf checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pupc_conj_intro
    (ay_pupc_CheckpointFailure
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch)
    (ay_pupc_Conj
      (ay_pupc_RecomputeObligation currentCnf recompute)
      (ay_pupc_NoSemanticClaim diagnostic))
    (ay_pupc_failure_unchecked_replay
      checkpointDrift implicationMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction trailLevelMismatch unchecked)
    (ay_pupc_conj_intro
      (ay_pupc_RecomputeObligation currentCnf recompute)
      (ay_pupc_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
