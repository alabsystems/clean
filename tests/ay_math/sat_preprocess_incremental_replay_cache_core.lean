-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental preprocessing replay-cache soundness. The propositions stand for
-- original fingerprints, assumption frames, stage chains, cache epochs,
-- reconstruction maps, stale incremental diagnostics, and public SAT/UNSAT
-- outcomes.

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

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyFingerprintMatch (cachedFingerprint : Prop) (currentFingerprint : Prop) :=
  AyIdMatch cachedFingerprint currentFingerprint

def AyAssumptionFrameMatch
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :=
  AyEquisat cachedAssumptions currentAssumptions

def AyStageChain
    (originalFrame : Prop) (intermediateFrame : Prop)
    (finalFrame : Prop) (stage1 : Prop) (stage2 : Prop) :=
  AyConj stage1
    (AyConj stage2
      (AyConj
        (AyEquisat originalFrame intermediateFrame)
        (AyEquisat intermediateFrame finalFrame)))

def AyReconstructionMap
    (finalFrame : Prop) (originalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalFrame finalModel -> AySat originalFrame originalModel)
    (AyEquisat originalFrame finalFrame)

def AyIncrementalReplayCacheHit
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop) :=
  AyConj
    (AyFingerprintMatch cachedFingerprint currentFingerprint)
    (AyConj
      (AyAssumptionFrameMatch cachedAssumptions currentAssumptions)
      (AyConj
        (AyIdMatch cachedEpoch currentEpoch)
        (AyConj
          (AyStageChain originalFrame intermediateFrame finalFrame
            stage1 stage2)
          (AyReconstructionMap finalFrame originalFrame
            finalModel originalModel))))

def AyIncrementalCacheFailure
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop) :=
  AyDisj fingerprintMismatch
    (AyDisj assumptionMismatch (AyDisj epochMismatch stageMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentFrame : Prop) (recompute : Prop) :=
  AyConj currentFrame recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedIncrementalReplayLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyIncrementalReplayCacheHit
      originalFrame intermediateFrame finalFrame finalModel originalModel
      cachedFingerprint currentFingerprint cachedAssumptions
      currentAssumptions cachedEpoch currentEpoch stage1 stage2)
    nextLog

def AyDiagnosticIncrementalReplayLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyIncrementalCacheFailure
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (originalFrame : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat originalFrame model))
    (AyExitCodeSound exitCode (certificate -> originalFrame -> conflict))

theorem ay_pirc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pirc_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pirc_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pirc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pirc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pirc_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pirc_conj_left (before -> after) (after -> before) eq

theorem ay_pirc_hit_reconstruction
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop) :
    AyIncrementalReplayCacheHit
      originalFrame intermediateFrame finalFrame finalModel originalModel
      cachedFingerprint currentFingerprint cachedAssumptions
      currentAssumptions cachedEpoch currentEpoch stage1 stage2 ->
    AyReconstructionMap finalFrame originalFrame finalModel originalModel := by
  intro hit
  exact ay_pirc_conj_right
    (AyStageChain originalFrame intermediateFrame finalFrame stage1 stage2)
    (AyReconstructionMap finalFrame originalFrame finalModel originalModel)
    (ay_pirc_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyStageChain originalFrame intermediateFrame finalFrame
          stage1 stage2)
        (AyReconstructionMap finalFrame originalFrame
          finalModel originalModel))
      (ay_pirc_conj_right
        (AyAssumptionFrameMatch cachedAssumptions currentAssumptions)
        (AyConj
          (AyIdMatch cachedEpoch currentEpoch)
          (AyConj
            (AyStageChain originalFrame intermediateFrame finalFrame
              stage1 stage2)
            (AyReconstructionMap finalFrame originalFrame
              finalModel originalModel)))
        (ay_pirc_conj_right
          (AyFingerprintMatch cachedFingerprint currentFingerprint)
          (AyConj
            (AyAssumptionFrameMatch cachedAssumptions currentAssumptions)
            (AyConj
              (AyIdMatch cachedEpoch currentEpoch)
              (AyConj
                (AyStageChain originalFrame intermediateFrame finalFrame
                  stage1 stage2)
                (AyReconstructionMap finalFrame originalFrame
                  finalModel originalModel))))
          hit)))

theorem ay_pirc_reconstruct_sat
    (finalFrame : Prop) (originalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalFrame originalFrame finalModel originalModel ->
    AySat finalFrame finalModel ->
    AySat originalFrame originalModel := by
  intro reconstruction
  exact ay_pirc_conj_left
    (AySat finalFrame finalModel -> AySat originalFrame originalModel)
    (AyEquisat originalFrame finalFrame)
    reconstruction

theorem ay_pirc_reconstruction_equisat
    (finalFrame : Prop) (originalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalFrame originalFrame finalModel originalModel ->
    AyEquisat originalFrame finalFrame := by
  intro reconstruction
  exact ay_pirc_conj_right
    (AySat finalFrame finalModel -> AySat originalFrame originalModel)
    (AyEquisat originalFrame finalFrame)
    reconstruction

theorem ay_pirc_log_hit
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop) :
    AyAcceptedIncrementalReplayLogEntry
      previousLog nextLog originalFrame intermediateFrame finalFrame
      finalModel originalModel cachedFingerprint currentFingerprint
      cachedAssumptions currentAssumptions cachedEpoch currentEpoch
      stage1 stage2 ->
    AyIncrementalReplayCacheHit
      originalFrame intermediateFrame finalFrame finalModel originalModel
      cachedFingerprint currentFingerprint cachedAssumptions
      currentAssumptions cachedEpoch currentEpoch stage1 stage2 := by
  intro entry
  exact ay_pirc_conj_left
    (AyIncrementalReplayCacheHit
      originalFrame intermediateFrame finalFrame finalModel originalModel
      cachedFingerprint currentFingerprint cachedAssumptions
      currentAssumptions cachedEpoch currentEpoch stage1 stage2)
    nextLog
    (ay_pirc_conj_right previousLog
      (AyConj
        (AyIncrementalReplayCacheHit
          originalFrame intermediateFrame finalFrame finalModel originalModel
          cachedFingerprint currentFingerprint cachedAssumptions
          currentAssumptions cachedEpoch currentEpoch stage1 stage2)
        nextLog)
      entry)

theorem ay_pirc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedIncrementalReplayLogEntry
      previousLog nextLog originalFrame intermediateFrame finalFrame
      finalModel originalModel cachedFingerprint currentFingerprint
      cachedAssumptions currentAssumptions cachedEpoch currentEpoch
      stage1 stage2 ->
    AySat finalFrame finalModel ->
    exitCode ->
    AyPublicResult originalFrame originalModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pirc_disj_left
    (AyExitCodeSound exitCode (AySat originalFrame originalModel))
    (AyExitCodeSound exitCode (certificate -> originalFrame -> conflict))
    (ay_pirc_conj_intro exitCode (AySat originalFrame originalModel)
      hexit
      (ay_pirc_reconstruct_sat finalFrame originalFrame finalModel
        originalModel
        (ay_pirc_hit_reconstruction originalFrame intermediateFrame
          finalFrame finalModel originalModel cachedFingerprint
          currentFingerprint cachedAssumptions currentAssumptions
          cachedEpoch currentEpoch stage1 stage2
          (ay_pirc_log_hit previousLog nextLog originalFrame
            intermediateFrame finalFrame finalModel originalModel
            cachedFingerprint currentFingerprint cachedAssumptions
            currentAssumptions cachedEpoch currentEpoch stage1 stage2 entry))
        sat))

theorem ay_pirc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (intermediateFrame : Prop) (finalFrame : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedFingerprint : Prop) (currentFingerprint : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (stage1 : Prop) (stage2 : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedIncrementalReplayLogEntry
      previousLog nextLog originalFrame intermediateFrame finalFrame
      finalModel originalModel cachedFingerprint currentFingerprint
      cachedAssumptions currentAssumptions cachedEpoch currentEpoch
      stage1 stage2 ->
    AyReplay finalFrame certificate conflict ->
    exitCode ->
    AyPublicResult originalFrame originalModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pirc_disj_right
    (AyExitCodeSound exitCode (AySat originalFrame originalModel))
    (AyExitCodeSound exitCode (certificate -> originalFrame -> conflict))
    (ay_pirc_conj_intro exitCode
      (certificate -> originalFrame -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_pirc_equisat_forward originalFrame finalFrame
            (ay_pirc_reconstruction_equisat finalFrame originalFrame
              finalModel originalModel
              (ay_pirc_hit_reconstruction originalFrame intermediateFrame
                finalFrame finalModel originalModel cachedFingerprint
                currentFingerprint cachedAssumptions currentAssumptions
                cachedEpoch currentEpoch stage1 stage2
                (ay_pirc_log_hit previousLog nextLog originalFrame
                  intermediateFrame finalFrame finalModel originalModel
                  cachedFingerprint currentFingerprint cachedAssumptions
                  currentAssumptions cachedEpoch currentEpoch stage1 stage2
                  entry)))
            horiginal)
          hcertificate))

theorem ay_pirc_failure_fingerprint
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop) :
    fingerprintMismatch ->
    AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch := by
  intro hfailure
  exact ay_pirc_disj_left fingerprintMismatch
    (AyDisj assumptionMismatch (AyDisj epochMismatch stageMismatch))
    hfailure

theorem ay_pirc_failure_assumptions
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop) :
    assumptionMismatch ->
    AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch := by
  intro hfailure
  exact ay_pirc_disj_right fingerprintMismatch
    (AyDisj assumptionMismatch (AyDisj epochMismatch stageMismatch))
    (ay_pirc_disj_left assumptionMismatch
      (AyDisj epochMismatch stageMismatch)
      hfailure)

theorem ay_pirc_failure_epoch
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop) :
    epochMismatch ->
    AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch := by
  intro hfailure
  exact ay_pirc_disj_right fingerprintMismatch
    (AyDisj assumptionMismatch (AyDisj epochMismatch stageMismatch))
    (ay_pirc_disj_right assumptionMismatch
      (AyDisj epochMismatch stageMismatch)
      (ay_pirc_disj_left epochMismatch stageMismatch hfailure))

theorem ay_pirc_failure_stage
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop) :
    stageMismatch ->
    AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch := by
  intro hfailure
  exact ay_pirc_disj_right fingerprintMismatch
    (AyDisj assumptionMismatch (AyDisj epochMismatch stageMismatch))
    (ay_pirc_disj_right assumptionMismatch
      (AyDisj epochMismatch stageMismatch)
      (ay_pirc_disj_right epochMismatch stageMismatch hfailure))

theorem ay_pirc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticIncrementalReplayLogEntry
      previousLog nextLog currentFrame fingerprintMismatch
      assumptionMismatch epochMismatch stageMismatch recompute diagnostic ->
    AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch := by
  intro entry
  exact ay_pirc_conj_left
    (AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pirc_conj_left
      (AyConj
        (AyIncrementalCacheFailure
          fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
        (AyConj
          (AyRecomputeObligation currentFrame recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pirc_conj_right previousLog
        (AyConj
          (AyConj
            (AyIncrementalCacheFailure
              fingerprintMismatch assumptionMismatch epochMismatch
              stageMismatch)
            (AyConj
              (AyRecomputeObligation currentFrame recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pirc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticIncrementalReplayLogEntry
      previousLog nextLog currentFrame fingerprintMismatch
      assumptionMismatch epochMismatch stageMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pirc_conj_right
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pirc_conj_right
      (AyIncrementalCacheFailure
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pirc_conj_left
        (AyConj
          (AyIncrementalCacheFailure
            fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pirc_conj_right previousLog
          (AyConj
            (AyConj
              (AyIncrementalCacheFailure
                fingerprintMismatch assumptionMismatch epochMismatch
                stageMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pirc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticIncrementalReplayLogEntry
      previousLog nextLog currentFrame fingerprintMismatch
      assumptionMismatch epochMismatch stageMismatch recompute diagnostic ->
    AyRecomputeObligation currentFrame recompute := by
  intro entry
  exact ay_pirc_conj_left
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pirc_conj_right
      (AyIncrementalCacheFailure
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pirc_conj_left
        (AyConj
          (AyIncrementalCacheFailure
            fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pirc_conj_right previousLog
          (AyConj
            (AyConj
              (AyIncrementalCacheFailure
                fingerprintMismatch assumptionMismatch epochMismatch
                stageMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pirc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (fingerprintMismatch : Prop) (assumptionMismatch : Prop)
    (epochMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticIncrementalReplayLogEntry
      previousLog nextLog currentFrame fingerprintMismatch
      assumptionMismatch epochMismatch stageMismatch recompute diagnostic ->
    AyConj
      (AyIncrementalCacheFailure
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pirc_conj_intro
    (AyIncrementalCacheFailure
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pirc_diagnostic_failure previousLog nextLog currentFrame
      fingerprintMismatch assumptionMismatch epochMismatch stageMismatch
      recompute diagnostic entry)
    (ay_pirc_conj_intro
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pirc_diagnostic_recompute previousLog nextLog currentFrame
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch
        recompute diagnostic entry)
      (ay_pirc_diagnostic_no_claim previousLog nextLog currentFrame
        fingerprintMismatch assumptionMismatch epochMismatch stageMismatch
        recompute diagnostic entry))
