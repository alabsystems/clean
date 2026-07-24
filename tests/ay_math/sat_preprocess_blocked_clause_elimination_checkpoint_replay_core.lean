-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause-elimination checkpoint replay soundness for preprocessing. The
-- propositions stand for blocked-clause checkpoints, blocking-literal witnesses,
-- affected-clause coverage, model/proof reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pbcp_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pbcp_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pbcp_Equisat (before : Prop) (after : Prop) :=
  ay_pbcp_Conj (before -> after) (after -> before)

def ay_pbcp_Sat (cnf : Prop) (model : Prop) :=
  ay_pbcp_Conj cnf model

def ay_pbcp_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pbcp_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pbcp_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pbcp_BlockedClauseCheckpoint
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop) :=
  ay_pbcp_Conj checkpointWitness
    (blockedClause -> bceCheckpoint)

def ay_pbcp_BlockingLiteralWitness
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop) :=
  ay_pbcp_Conj witnessProof
    (ay_pbcp_Conj blockingLiteral blockingWitness)

def ay_pbcp_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pbcp_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pbcp_CheckpointReconstruction
    (reconstructionWitness : Prop) (bceCheckpoint : Prop)
    (ledgerWitness : Prop) :=
  ay_pbcp_Conj ledgerWitness
    (bceCheckpoint -> reconstructionWitness)

def ay_pbcp_ModelReconstruction
    (checkpointCnf : Prop) (originalCnf : Prop)
    (checkpointModel : Prop) (originalModel : Prop) :=
  ay_pbcp_Sat checkpointCnf checkpointModel ->
    ay_pbcp_Sat originalCnf originalModel

def ay_pbcp_ProofReconstruction
    (originalCnf : Prop) (checkpointCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pbcp_Replay checkpointCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pbcp_FingerprintAgreement
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pbcp_Conj fingerprintWitness
    (ay_pbcp_IdMatch originalFingerprint checkpointFingerprint)

def ay_pbcp_CheckerReplay
    (bceCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pbcp_Conj bceCertificate checkerAccepted

def ay_pbcp_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pbcp_Conj baselineSolver baselineAvailable

def ay_pbcp_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pbcp_Conj binaryFingerprint buildReproducible

def ay_pbcp_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pbcp_Conj validatorAccepted validatorVersion

def ay_pbcp_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pbcp_Conj auditAppended auditAppendOnly

def ay_pbcp_AcceptedBlockedClauseCheckpointReplay
    (originalCnf : Prop) (checkpointCnf : Prop)
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop)
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reconstructionWitness : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pbcp_BlockedClauseCheckpoint
       blockedClause bceCheckpoint checkpointWitness ->
     ay_pbcp_BlockingLiteralWitness
       blockingLiteral blockingWitness witnessProof ->
     ay_pbcp_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pbcp_CheckpointReconstruction
       reconstructionWitness bceCheckpoint ledgerWitness ->
     ay_pbcp_Equisat originalCnf checkpointCnf ->
     ay_pbcp_ModelReconstruction
       checkpointCnf originalCnf checkpointModel originalModel ->
     ay_pbcp_ProofReconstruction
       originalCnf checkpointCnf certificate conflict ->
     ay_pbcp_FingerprintAgreement
       originalFingerprint checkpointFingerprint fingerprintWitness ->
     ay_pbcp_CheckerReplay
       bceCertificate checkerAccepted ->
     ay_pbcp_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pbcp_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pbcp_ValidatorGate validatorAccepted validatorVersion ->
     ay_pbcp_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pbcp_BlockedClauseCheckpointFailure
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (reconstructionWitnessGap : Prop) :=
  ay_pbcp_Disj checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))

def ay_pbcp_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pbcp_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pbcp_Conj currentCnf recompute

def ay_pbcp_DiagnosticBlockedClauseCheckpointReplay
    (currentCnf : Prop)
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pbcp_Conj
    (ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap)
    (ay_pbcp_Conj
      (ay_pbcp_RecomputeObligation currentCnf recompute)
      (ay_pbcp_NoSemanticClaim diagnostic))

def ay_pbcp_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pbcp_Conj exitCode claim

def ay_pbcp_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pbcp_Disj
    (ay_pbcp_ExitCodeSound exitCode (ay_pbcp_Sat originalCnf model))
    (ay_pbcp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pbcp_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pbcp_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbcp_conj_left
    (left : Prop) (right : Prop) :
    ay_pbcp_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbcp_conj_right
    (left : Prop) (right : Prop) :
    ay_pbcp_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbcp_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pbcp_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbcp_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pbcp_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbcp_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pbcp_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbcp_conj_left (before -> after) (after -> before) eq

theorem ay_pbcp_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pbcp_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbcp_conj_right (before -> after) (after -> before) eq

theorem ay_pbcp_blocked_clause_checkpoint_applies
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop) :
    ay_pbcp_BlockedClauseCheckpoint
      blockedClause bceCheckpoint checkpointWitness ->
    blockedClause ->
    bceCheckpoint := by
  intro accepted raw
  exact
    (ay_pbcp_conj_right checkpointWitness
      (blockedClause -> bceCheckpoint) accepted) raw

theorem ay_pbcp_blocking_literal_witness_literal
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop) :
    ay_pbcp_BlockingLiteralWitness
      blockingLiteral blockingWitness witnessProof ->
    blockingLiteral := by
  intro accepted
  exact accepted blockingLiteral
    (fun _ledger pair =>
      pair blockingLiteral
        (fun duplicate _tautology => duplicate))

theorem ay_pbcp_blocking_literal_witness_proof
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop) :
    ay_pbcp_BlockingLiteralWitness
      blockingLiteral blockingWitness witnessProof ->
    blockingWitness := by
  intro accepted
  exact accepted blockingWitness
    (fun _ledger pair =>
      pair blockingWitness
        (fun _duplicate tautology => tautology))

theorem ay_pbcp_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pbcp_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause ->
    coveredClause := by
  intro accepted original
  exact
    (ay_pbcp_conj_right coverageWitness
      (affectedClause -> coveredClause) accepted) original

theorem ay_pbcp_checkpoint_reconstruction_records
    (reconstructionWitness : Prop) (bceCheckpoint : Prop)
    (ledgerWitness : Prop) :
    ay_pbcp_CheckpointReconstruction
      reconstructionWitness bceCheckpoint ledgerWitness ->
    bceCheckpoint ->
    reconstructionWitness := by
  intro accepted canonical
  exact
    (ay_pbcp_conj_right ledgerWitness
      (bceCheckpoint -> reconstructionWitness) accepted) canonical

theorem ay_pbcp_accepted_equisat
    (originalCnf : Prop) (checkpointCnf : Prop)
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop)
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reconstructionWitness : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcp_AcceptedBlockedClauseCheckpointReplay
      originalCnf checkpointCnf blockedClause bceCheckpoint
      checkpointWitness blockingLiteral blockingWitness
      witnessProof affectedClause coveredClause coverageWitness
      reconstructionWitness ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcp_Equisat originalCnf checkpointCnf := by
  intro accepted
  exact accepted (ay_pbcp_Equisat originalCnf checkpointCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pbcp_accepted_checker_replay
    (originalCnf : Prop) (checkpointCnf : Prop)
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop)
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reconstructionWitness : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcp_AcceptedBlockedClauseCheckpointReplay
      originalCnf checkpointCnf blockedClause bceCheckpoint
      checkpointWitness blockingLiteral blockingWitness
      witnessProof affectedClause coveredClause coverageWitness
      reconstructionWitness ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcp_CheckerReplay bceCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pbcp_CheckerReplay bceCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pbcp_accepted_audit_evidence
    (originalCnf : Prop) (checkpointCnf : Prop)
    (blockedClause : Prop) (bceCheckpoint : Prop)
    (checkpointWitness : Prop)
    (blockingLiteral : Prop) (blockingWitness : Prop)
    (witnessProof : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (reconstructionWitness : Prop) (ledgerWitness : Prop)
    (checkpointModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (checkpointFingerprint : Prop)
    (fingerprintWitness : Prop)
    (bceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pbcp_AcceptedBlockedClauseCheckpointReplay
      originalCnf checkpointCnf blockedClause bceCheckpoint
      checkpointWitness blockingLiteral blockingWitness
      witnessProof affectedClause coveredClause coverageWitness
      reconstructionWitness ledgerWitness checkpointModel originalModel
      certificate conflict originalFingerprint checkpointFingerprint
      fingerprintWitness bceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pbcp_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pbcp_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pbcp_sat_pullback
    (checkpointCnf : Prop) (originalCnf : Prop)
    (checkpointModel : Prop) (originalModel : Prop) :
    ay_pbcp_ModelReconstruction
      checkpointCnf originalCnf checkpointModel originalModel ->
    ay_pbcp_Sat checkpointCnf checkpointModel ->
    ay_pbcp_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pbcp_unsat_pushback
    (originalCnf : Prop) (checkpointCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pbcp_ProofReconstruction
      originalCnf checkpointCnf certificate conflict ->
    ay_pbcp_Replay checkpointCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pbcp_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pbcp_Sat originalCnf model ->
    ay_pbcp_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pbcp_disj_left
    (ay_pbcp_ExitCodeSound exitCode (ay_pbcp_Sat originalCnf model))
    (ay_pbcp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbcp_conj_intro exitCode
      (ay_pbcp_Sat originalCnf model) exit sat)

theorem ay_pbcp_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pbcp_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pbcp_disj_right
    (ay_pbcp_ExitCodeSound exitCode (ay_pbcp_Sat originalCnf model))
    (ay_pbcp_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pbcp_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pbcp_failure_checkpoint_drift
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    checkpointDrift ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro drift
  exact ay_pbcp_disj_left checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    drift

theorem ay_pbcp_failure_blocking_witness_mismatch
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    blockingWitnessMismatch ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro mismatch
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_left blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      mismatch)

theorem ay_pbcp_failure_coverage_gap
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    coverageGap ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro gap
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_left coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        gap))

theorem ay_pbcp_failure_stale_fingerprint
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    staleFingerprint ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro stale
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_right coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        (ay_pbcp_disj_left staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))
          stale)))

theorem ay_pbcp_failure_unchecked_replay
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    uncheckedReplay ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro unchecked
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_right coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        (ay_pbcp_disj_right staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))
          (ay_pbcp_disj_left uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))
            unchecked))))

theorem ay_pbcp_failure_build_drift
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    buildDrift ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro drift
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_right coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        (ay_pbcp_disj_right staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))
          (ay_pbcp_disj_right uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))
            (ay_pbcp_disj_left buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)
              drift)))))

theorem ay_pbcp_failure_audit_contradiction
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    auditContradiction ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro auditBad
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_right coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        (ay_pbcp_disj_right staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))
          (ay_pbcp_disj_right uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))
            (ay_pbcp_disj_right buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)
              (ay_pbcp_disj_left auditContradiction reconstructionWitnessGap
                auditBad))))))

theorem ay_pbcp_failure_reconstruction_gap
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop) :
    reconstructionWitnessGap ->
    ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap := by
  intro mismatch
  exact ay_pbcp_disj_right checkpointDrift
    (ay_pbcp_Disj blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))))
    (ay_pbcp_disj_right blockingWitnessMismatch
      (ay_pbcp_Disj coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))))
      (ay_pbcp_disj_right coverageGap
        (ay_pbcp_Disj staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))))
        (ay_pbcp_disj_right staleFingerprint
          (ay_pbcp_Disj uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)))
          (ay_pbcp_disj_right uncheckedReplay
            (ay_pbcp_Disj buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap))
            (ay_pbcp_disj_right buildDrift
              (ay_pbcp_Disj auditContradiction reconstructionWitnessGap)
              (ay_pbcp_disj_right auditContradiction reconstructionWitnessGap
                mismatch))))))

theorem ay_pbcp_diagnostic_no_claim
    (currentCnf : Prop)
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbcp_DiagnosticBlockedClauseCheckpointReplay
      currentCnf checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap recompute diagnostic ->
    ay_pbcp_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbcp_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pbcp_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pbcp_diagnostic_recompute
    (currentCnf : Prop)
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pbcp_DiagnosticBlockedClauseCheckpointReplay
      currentCnf checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap recompute diagnostic ->
    ay_pbcp_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pbcp_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pbcp_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pbcp_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (checkpointDrift : Prop) (blockingWitnessMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionWitnessGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pbcp_RecomputeObligation currentCnf recompute ->
    ay_pbcp_NoSemanticClaim diagnostic ->
    ay_pbcp_DiagnosticBlockedClauseCheckpointReplay
      currentCnf checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pbcp_conj_intro
    (ay_pbcp_BlockedClauseCheckpointFailure
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap)
    (ay_pbcp_Conj
      (ay_pbcp_RecomputeObligation currentCnf recompute)
      (ay_pbcp_NoSemanticClaim diagnostic))
    (ay_pbcp_failure_unchecked_replay
      checkpointDrift blockingWitnessMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionWitnessGap unchecked)
    (ay_pbcp_conj_intro
      (ay_pbcp_RecomputeObligation currentCnf recompute)
      (ay_pbcp_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
