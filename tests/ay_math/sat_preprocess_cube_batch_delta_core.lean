-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cube-batch preprocessing delta soundness. The propositions stand for a
-- bounded batch of cube-specialized frames, delta certificates, stage chains,
-- reconstruction maps, aggregate batch digests, diagnostics, and public
-- SAT/UNSAT outcomes.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyCubeFrame (baseCnf : Prop) (cubeAssumptions : Prop) :=
  AyConj baseCnf cubeAssumptions

def AyDeltaCertificate
    (cubeFrame : Prop) (preprocessedFrame : Prop) (deltaWitness : Prop) :=
  AyConj deltaWitness (AyEquisat cubeFrame preprocessedFrame)

def AyStageChain
    (preprocessedFrame : Prop) (finalFrame : Prop) (stageWitness : Prop) :=
  AyConj stageWitness (AyEquisat preprocessedFrame finalFrame)

def AyReconstructionMap
    (finalFrame : Prop) (cubeFrame : Prop)
    (finalModel : Prop) (cubeModel : Prop) :=
  AyConj
    (AySat finalFrame finalModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame finalFrame)

def AyCubeDeltaEntry
    (cubeFrame : Prop) (preprocessedFrame : Prop) (finalFrame : Prop)
    (deltaWitness : Prop) (stageWitness : Prop)
    (finalModel : Prop) (cubeModel : Prop) :=
  AyConj
    (AyDeltaCertificate cubeFrame preprocessedFrame deltaWitness)
    (AyConj
      (AyStageChain preprocessedFrame finalFrame stageWitness)
      (AyReconstructionMap finalFrame cubeFrame finalModel cubeModel))

def AyCubeBatch
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyCubeDeltaEntry
      cube1Frame pre1Frame final1Frame delta1 stage1
      final1Model cube1Model)
    (AyConj
      (AyCubeDeltaEntry
        cube2Frame pre2Frame final2Frame delta2 stage2
        final2Model cube2Model)
      (AyDigestMatch aggregateDigest runDigest))

def AyBatchFailure
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop) :=
  AyDisj missingCube
    (AyDisj duplicateCube (AyDisj digestMismatch stageMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentBatch : Prop) (recompute : Prop) :=
  AyConj currentBatch recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedCubeBatchLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyCubeBatch
      cube1Frame pre1Frame final1Frame delta1 stage1
      final1Model cube1Model cube2Frame pre2Frame final2Frame
      delta2 stage2 final2Model cube2Model aggregateDigest runDigest)
    nextLog

def AyDiagnosticCubeBatchLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentBatch : Prop)
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyBatchFailure
        missingCube duplicateCube digestMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentBatch recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (cubeFrame : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat cubeFrame model))
    (AyExitCodeSound exitCode (certificate -> cubeFrame -> conflict))

theorem ay_pcbd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcbd_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcbd_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcbd_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcbd_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcbd_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcbd_conj_left (before -> after) (after -> before) eq

theorem ay_pcbd_entry_reconstruction
    (cubeFrame : Prop) (preFrame : Prop) (finalFrame : Prop)
    (deltaWitness : Prop) (stageWitness : Prop)
    (finalModel : Prop) (cubeModel : Prop) :
    AyCubeDeltaEntry
      cubeFrame preFrame finalFrame deltaWitness stageWitness
      finalModel cubeModel ->
    AyReconstructionMap finalFrame cubeFrame finalModel cubeModel := by
  intro entry
  exact ay_pcbd_conj_right
    (AyStageChain preFrame finalFrame stageWitness)
    (AyReconstructionMap finalFrame cubeFrame finalModel cubeModel)
    (ay_pcbd_conj_right
      (AyDeltaCertificate cubeFrame preFrame deltaWitness)
      (AyConj
        (AyStageChain preFrame finalFrame stageWitness)
        (AyReconstructionMap finalFrame cubeFrame finalModel cubeModel))
      entry)

theorem ay_pcbd_reconstruct_sat
    (finalFrame : Prop) (cubeFrame : Prop)
    (finalModel : Prop) (cubeModel : Prop) :
    AyReconstructionMap finalFrame cubeFrame finalModel cubeModel ->
    AySat finalFrame finalModel ->
    AySat cubeFrame cubeModel := by
  intro reconstruction
  exact ay_pcbd_conj_left
    (AySat finalFrame finalModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame finalFrame)
    reconstruction

theorem ay_pcbd_reconstruction_equisat
    (finalFrame : Prop) (cubeFrame : Prop)
    (finalModel : Prop) (cubeModel : Prop) :
    AyReconstructionMap finalFrame cubeFrame finalModel cubeModel ->
    AyEquisat cubeFrame finalFrame := by
  intro reconstruction
  exact ay_pcbd_conj_right
    (AySat finalFrame finalModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame finalFrame)
    reconstruction

theorem ay_pcbd_batch_first
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop) :
    AyCubeBatch
      cube1Frame pre1Frame final1Frame delta1 stage1 final1Model
      cube1Model cube2Frame pre2Frame final2Frame delta2 stage2
      final2Model cube2Model aggregateDigest runDigest ->
    AyCubeDeltaEntry
      cube1Frame pre1Frame final1Frame delta1 stage1
      final1Model cube1Model := by
  intro batch
  exact ay_pcbd_conj_left
    (AyCubeDeltaEntry
      cube1Frame pre1Frame final1Frame delta1 stage1
      final1Model cube1Model)
    (AyConj
      (AyCubeDeltaEntry
        cube2Frame pre2Frame final2Frame delta2 stage2
        final2Model cube2Model)
      (AyDigestMatch aggregateDigest runDigest))
    batch

theorem ay_pcbd_log_batch
    (previousLog : Prop) (nextLog : Prop)
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop) :
    AyAcceptedCubeBatchLogEntry
      previousLog nextLog cube1Frame pre1Frame final1Frame delta1
      stage1 final1Model cube1Model cube2Frame pre2Frame final2Frame
      delta2 stage2 final2Model cube2Model aggregateDigest runDigest ->
    AyCubeBatch
      cube1Frame pre1Frame final1Frame delta1 stage1 final1Model
      cube1Model cube2Frame pre2Frame final2Frame delta2 stage2
      final2Model cube2Model aggregateDigest runDigest := by
  intro entry
  exact ay_pcbd_conj_left
    (AyCubeBatch
      cube1Frame pre1Frame final1Frame delta1 stage1 final1Model
      cube1Model cube2Frame pre2Frame final2Frame delta2 stage2
      final2Model cube2Model aggregateDigest runDigest)
    nextLog
    (ay_pcbd_conj_right previousLog
      (AyConj
        (AyCubeBatch
          cube1Frame pre1Frame final1Frame delta1 stage1 final1Model
          cube1Model cube2Frame pre2Frame final2Frame delta2 stage2
          final2Model cube2Model aggregateDigest runDigest)
        nextLog)
      entry)

theorem ay_pcbd_public_sat_first
    (previousLog : Prop) (nextLog : Prop)
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedCubeBatchLogEntry
      previousLog nextLog cube1Frame pre1Frame final1Frame delta1
      stage1 final1Model cube1Model cube2Frame pre2Frame final2Frame
      delta2 stage2 final2Model cube2Model aggregateDigest runDigest ->
    AySat final1Frame final1Model ->
    exitCode ->
    AyPublicResult cube1Frame cube1Model certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pcbd_disj_left
    (AyExitCodeSound exitCode (AySat cube1Frame cube1Model))
    (AyExitCodeSound exitCode (certificate -> cube1Frame -> conflict))
    (ay_pcbd_conj_intro exitCode (AySat cube1Frame cube1Model)
      hexit
      (ay_pcbd_reconstruct_sat final1Frame cube1Frame
        final1Model cube1Model
        (ay_pcbd_entry_reconstruction cube1Frame pre1Frame final1Frame
          delta1 stage1 final1Model cube1Model
          (ay_pcbd_batch_first cube1Frame pre1Frame final1Frame delta1
            stage1 final1Model cube1Model cube2Frame pre2Frame
            final2Frame delta2 stage2 final2Model cube2Model
            aggregateDigest runDigest
            (ay_pcbd_log_batch previousLog nextLog cube1Frame pre1Frame
              final1Frame delta1 stage1 final1Model cube1Model
              cube2Frame pre2Frame final2Frame delta2 stage2 final2Model
              cube2Model aggregateDigest runDigest entry)))
        sat))

theorem ay_pcbd_public_unsat_first
    (previousLog : Prop) (nextLog : Prop)
    (cube1Frame : Prop) (pre1Frame : Prop) (final1Frame : Prop)
    (delta1 : Prop) (stage1 : Prop) (final1Model : Prop)
    (cube1Model : Prop)
    (cube2Frame : Prop) (pre2Frame : Prop) (final2Frame : Prop)
    (delta2 : Prop) (stage2 : Prop) (final2Model : Prop)
    (cube2Model : Prop)
    (aggregateDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedCubeBatchLogEntry
      previousLog nextLog cube1Frame pre1Frame final1Frame delta1
      stage1 final1Model cube1Model cube2Frame pre2Frame final2Frame
      delta2 stage2 final2Model cube2Model aggregateDigest runDigest ->
    AyReplay final1Frame certificate conflict ->
    exitCode ->
    AyPublicResult cube1Frame cube1Model certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pcbd_disj_right
    (AyExitCodeSound exitCode (AySat cube1Frame cube1Model))
    (AyExitCodeSound exitCode (certificate -> cube1Frame -> conflict))
    (ay_pcbd_conj_intro exitCode
      (certificate -> cube1Frame -> conflict)
      hexit
      (fun hcertificate hcube =>
        replay
          (ay_pcbd_equisat_forward cube1Frame final1Frame
            (ay_pcbd_reconstruction_equisat final1Frame cube1Frame
              final1Model cube1Model
              (ay_pcbd_entry_reconstruction cube1Frame pre1Frame final1Frame
                delta1 stage1 final1Model cube1Model
                (ay_pcbd_batch_first cube1Frame pre1Frame final1Frame
                  delta1 stage1 final1Model cube1Model cube2Frame pre2Frame
                  final2Frame delta2 stage2 final2Model cube2Model
                  aggregateDigest runDigest
                  (ay_pcbd_log_batch previousLog nextLog cube1Frame
                    pre1Frame final1Frame delta1 stage1 final1Model
                    cube1Model cube2Frame pre2Frame final2Frame delta2
                    stage2 final2Model cube2Model aggregateDigest runDigest
                    entry))))
            hcube)
          hcertificate))

theorem ay_pcbd_failure_missing
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop) :
    missingCube ->
    AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch := by
  intro hfailure
  exact ay_pcbd_disj_left missingCube
    (AyDisj duplicateCube (AyDisj digestMismatch stageMismatch))
    hfailure

theorem ay_pcbd_failure_duplicate
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop) :
    duplicateCube ->
    AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch := by
  intro hfailure
  exact ay_pcbd_disj_right missingCube
    (AyDisj duplicateCube (AyDisj digestMismatch stageMismatch))
    (ay_pcbd_disj_left duplicateCube
      (AyDisj digestMismatch stageMismatch)
      hfailure)

theorem ay_pcbd_failure_digest
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop) :
    digestMismatch ->
    AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch := by
  intro hfailure
  exact ay_pcbd_disj_right missingCube
    (AyDisj duplicateCube (AyDisj digestMismatch stageMismatch))
    (ay_pcbd_disj_right duplicateCube
      (AyDisj digestMismatch stageMismatch)
      (ay_pcbd_disj_left digestMismatch stageMismatch hfailure))

theorem ay_pcbd_failure_stage
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop) :
    stageMismatch ->
    AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch := by
  intro hfailure
  exact ay_pcbd_disj_right missingCube
    (AyDisj duplicateCube (AyDisj digestMismatch stageMismatch))
    (ay_pcbd_disj_right duplicateCube
      (AyDisj digestMismatch stageMismatch)
      (ay_pcbd_disj_right digestMismatch stageMismatch hfailure))

theorem ay_pcbd_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentBatch : Prop)
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCubeBatchLogEntry
      previousLog nextLog currentBatch missingCube duplicateCube
      digestMismatch stageMismatch recompute diagnostic ->
    AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch := by
  intro entry
  exact ay_pcbd_conj_left
    (AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentBatch recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pcbd_conj_left
      (AyConj
        (AyBatchFailure
          missingCube duplicateCube digestMismatch stageMismatch)
        (AyConj
          (AyRecomputeObligation currentBatch recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pcbd_conj_right previousLog
        (AyConj
          (AyConj
            (AyBatchFailure
              missingCube duplicateCube digestMismatch stageMismatch)
            (AyConj
              (AyRecomputeObligation currentBatch recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pcbd_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentBatch : Prop)
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCubeBatchLogEntry
      previousLog nextLog currentBatch missingCube duplicateCube
      digestMismatch stageMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pcbd_conj_right
    (AyRecomputeObligation currentBatch recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pcbd_conj_right
      (AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentBatch recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pcbd_conj_left
        (AyConj
          (AyBatchFailure
            missingCube duplicateCube digestMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentBatch recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pcbd_conj_right previousLog
          (AyConj
            (AyConj
              (AyBatchFailure
                missingCube duplicateCube digestMismatch stageMismatch)
              (AyConj
                (AyRecomputeObligation currentBatch recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pcbd_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentBatch : Prop)
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCubeBatchLogEntry
      previousLog nextLog currentBatch missingCube duplicateCube
      digestMismatch stageMismatch recompute diagnostic ->
    AyRecomputeObligation currentBatch recompute := by
  intro entry
  exact ay_pcbd_conj_left
    (AyRecomputeObligation currentBatch recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pcbd_conj_right
      (AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentBatch recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pcbd_conj_left
        (AyConj
          (AyBatchFailure
            missingCube duplicateCube digestMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentBatch recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pcbd_conj_right previousLog
          (AyConj
            (AyConj
              (AyBatchFailure
                missingCube duplicateCube digestMismatch stageMismatch)
              (AyConj
                (AyRecomputeObligation currentBatch recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pcbd_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentBatch : Prop)
    (missingCube : Prop) (duplicateCube : Prop)
    (digestMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCubeBatchLogEntry
      previousLog nextLog currentBatch missingCube duplicateCube
      digestMismatch stageMismatch recompute diagnostic ->
    AyConj
      (AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentBatch recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pcbd_conj_intro
    (AyBatchFailure missingCube duplicateCube digestMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentBatch recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pcbd_diagnostic_failure previousLog nextLog currentBatch
      missingCube duplicateCube digestMismatch stageMismatch recompute
      diagnostic entry)
    (ay_pcbd_conj_intro
      (AyRecomputeObligation currentBatch recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pcbd_diagnostic_recompute previousLog nextLog currentBatch
        missingCube duplicateCube digestMismatch stageMismatch recompute
        diagnostic entry)
      (ay_pcbd_diagnostic_no_claim previousLog nextLog currentBatch
        missingCube duplicateCube digestMismatch stageMismatch recompute
        diagnostic entry))
