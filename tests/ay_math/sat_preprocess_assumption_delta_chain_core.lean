-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption-delta preprocessing chain soundness. The propositions stand for
-- base/cube fingerprints, assumption frames, delta certificates, stage chains,
-- reconstruction maps, diagnostics, and public SAT/UNSAT outcomes.

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

def AyAssumptionFrame (baseFormula : Prop) (assumptions : Prop) :=
  AyConj baseFormula assumptions

def AyDeltaCertificate
    (baseFrame : Prop) (specializedFrame : Prop) (deltaWitness : Prop) :=
  AyConj deltaWitness (AyEquisat baseFrame specializedFrame)

def AyStageChain
    (specializedFrame : Prop) (intermediateFrame : Prop)
    (finalFrame : Prop) (stage1 : Prop) (stage2 : Prop) :=
  AyConj stage1
    (AyConj stage2
      (AyConj
        (AyEquisat specializedFrame intermediateFrame)
        (AyEquisat intermediateFrame finalFrame)))

def AyReconstructionMap
    (finalFrame : Prop) (baseFrame : Prop)
    (finalModel : Prop) (baseModel : Prop) :=
  AyConj
    (AySat finalFrame finalModel -> AySat baseFrame baseModel)
    (AyEquisat baseFrame finalFrame)

def AyAcceptedAssumptionDelta
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop) :=
  AyConj
    (AyIdMatch baseFingerprint runFingerprint)
    (AyConj
      (AyEquisat cachedAssumptions runAssumptions)
      (AyConj
        (AyDeltaCertificate baseFrame specializedFrame deltaWitness)
        (AyConj
          (AyStageChain specializedFrame intermediateFrame finalFrame
            stage1 stage2)
          (AyReconstructionMap finalFrame baseFrame
            finalModel baseModel))))

def AyAssumptionDeltaFailure
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop) :=
  AyDisj staleDelta
    (AyDisj wrongFrame (AyDisj fingerprintMismatch stageMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentFrame : Prop) (recompute : Prop) :=
  AyConj currentFrame recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedAssumptionDeltaLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedAssumptionDelta
      baseFrame specializedFrame intermediateFrame finalFrame
      baseFingerprint runFingerprint cachedAssumptions runAssumptions
      deltaWitness stage1 stage2 finalModel baseModel)
    nextLog

def AyDiagnosticAssumptionDeltaLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyAssumptionDeltaFailure
        staleDelta wrongFrame fingerprintMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (baseFrame : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat baseFrame model))
    (AyExitCodeSound exitCode (certificate -> baseFrame -> conflict))

theorem ay_padc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_padc_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_padc_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_padc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_padc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_padc_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_padc_conj_left (before -> after) (after -> before) eq

theorem ay_padc_delta_witness
    (baseFrame : Prop) (specializedFrame : Prop) (deltaWitness : Prop) :
    AyDeltaCertificate baseFrame specializedFrame deltaWitness ->
    deltaWitness := by
  intro cert
  exact ay_padc_conj_left deltaWitness
    (AyEquisat baseFrame specializedFrame)
    cert

theorem ay_padc_delta_equisat
    (baseFrame : Prop) (specializedFrame : Prop) (deltaWitness : Prop) :
    AyDeltaCertificate baseFrame specializedFrame deltaWitness ->
    AyEquisat baseFrame specializedFrame := by
  intro cert
  exact ay_padc_conj_right deltaWitness
    (AyEquisat baseFrame specializedFrame)
    cert

theorem ay_padc_hit_reconstruction
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop) :
    AyAcceptedAssumptionDelta
      baseFrame specializedFrame intermediateFrame finalFrame
      baseFingerprint runFingerprint cachedAssumptions runAssumptions
      deltaWitness stage1 stage2 finalModel baseModel ->
    AyReconstructionMap finalFrame baseFrame finalModel baseModel := by
  intro hit
  exact ay_padc_conj_right
    (AyStageChain specializedFrame intermediateFrame finalFrame stage1 stage2)
    (AyReconstructionMap finalFrame baseFrame finalModel baseModel)
    (ay_padc_conj_right
      (AyDeltaCertificate baseFrame specializedFrame deltaWitness)
      (AyConj
        (AyStageChain specializedFrame intermediateFrame finalFrame
          stage1 stage2)
        (AyReconstructionMap finalFrame baseFrame finalModel baseModel))
      (ay_padc_conj_right
        (AyEquisat cachedAssumptions runAssumptions)
        (AyConj
          (AyDeltaCertificate baseFrame specializedFrame deltaWitness)
          (AyConj
            (AyStageChain specializedFrame intermediateFrame finalFrame
              stage1 stage2)
            (AyReconstructionMap finalFrame baseFrame finalModel baseModel)))
        (ay_padc_conj_right
          (AyIdMatch baseFingerprint runFingerprint)
          (AyConj
            (AyEquisat cachedAssumptions runAssumptions)
            (AyConj
              (AyDeltaCertificate baseFrame specializedFrame deltaWitness)
              (AyConj
                (AyStageChain specializedFrame intermediateFrame finalFrame
                  stage1 stage2)
                (AyReconstructionMap finalFrame baseFrame
                  finalModel baseModel))))
          hit)))

theorem ay_padc_reconstruct_sat
    (finalFrame : Prop) (baseFrame : Prop)
    (finalModel : Prop) (baseModel : Prop) :
    AyReconstructionMap finalFrame baseFrame finalModel baseModel ->
    AySat finalFrame finalModel ->
    AySat baseFrame baseModel := by
  intro reconstruction
  exact ay_padc_conj_left
    (AySat finalFrame finalModel -> AySat baseFrame baseModel)
    (AyEquisat baseFrame finalFrame)
    reconstruction

theorem ay_padc_reconstruction_equisat
    (finalFrame : Prop) (baseFrame : Prop)
    (finalModel : Prop) (baseModel : Prop) :
    AyReconstructionMap finalFrame baseFrame finalModel baseModel ->
    AyEquisat baseFrame finalFrame := by
  intro reconstruction
  exact ay_padc_conj_right
    (AySat finalFrame finalModel -> AySat baseFrame baseModel)
    (AyEquisat baseFrame finalFrame)
    reconstruction

theorem ay_padc_log_hit
    (previousLog : Prop) (nextLog : Prop)
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop) :
    AyAcceptedAssumptionDeltaLogEntry
      previousLog nextLog baseFrame specializedFrame intermediateFrame
      finalFrame baseFingerprint runFingerprint cachedAssumptions
      runAssumptions deltaWitness stage1 stage2 finalModel baseModel ->
    AyAcceptedAssumptionDelta
      baseFrame specializedFrame intermediateFrame finalFrame
      baseFingerprint runFingerprint cachedAssumptions runAssumptions
      deltaWitness stage1 stage2 finalModel baseModel := by
  intro entry
  exact ay_padc_conj_left
    (AyAcceptedAssumptionDelta
      baseFrame specializedFrame intermediateFrame finalFrame
      baseFingerprint runFingerprint cachedAssumptions runAssumptions
      deltaWitness stage1 stage2 finalModel baseModel)
    nextLog
    (ay_padc_conj_right previousLog
      (AyConj
        (AyAcceptedAssumptionDelta
          baseFrame specializedFrame intermediateFrame finalFrame
          baseFingerprint runFingerprint cachedAssumptions runAssumptions
          deltaWitness stage1 stage2 finalModel baseModel)
        nextLog)
      entry)

theorem ay_padc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedAssumptionDeltaLogEntry
      previousLog nextLog baseFrame specializedFrame intermediateFrame
      finalFrame baseFingerprint runFingerprint cachedAssumptions
      runAssumptions deltaWitness stage1 stage2 finalModel baseModel ->
    AySat finalFrame finalModel ->
    exitCode ->
    AyPublicResult baseFrame baseModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_padc_disj_left
    (AyExitCodeSound exitCode (AySat baseFrame baseModel))
    (AyExitCodeSound exitCode (certificate -> baseFrame -> conflict))
    (ay_padc_conj_intro exitCode (AySat baseFrame baseModel)
      hexit
      (ay_padc_reconstruct_sat finalFrame baseFrame finalModel baseModel
        (ay_padc_hit_reconstruction baseFrame specializedFrame
          intermediateFrame finalFrame baseFingerprint runFingerprint
          cachedAssumptions runAssumptions deltaWitness stage1 stage2
          finalModel baseModel
          (ay_padc_log_hit previousLog nextLog baseFrame specializedFrame
            intermediateFrame finalFrame baseFingerprint runFingerprint
            cachedAssumptions runAssumptions deltaWitness stage1 stage2
            finalModel baseModel entry))
        sat))

theorem ay_padc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (baseFrame : Prop) (specializedFrame : Prop)
    (intermediateFrame : Prop) (finalFrame : Prop)
    (baseFingerprint : Prop) (runFingerprint : Prop)
    (cachedAssumptions : Prop) (runAssumptions : Prop)
    (deltaWitness : Prop) (stage1 : Prop) (stage2 : Prop)
    (finalModel : Prop) (baseModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedAssumptionDeltaLogEntry
      previousLog nextLog baseFrame specializedFrame intermediateFrame
      finalFrame baseFingerprint runFingerprint cachedAssumptions
      runAssumptions deltaWitness stage1 stage2 finalModel baseModel ->
    AyReplay finalFrame certificate conflict ->
    exitCode ->
    AyPublicResult baseFrame baseModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_padc_disj_right
    (AyExitCodeSound exitCode (AySat baseFrame baseModel))
    (AyExitCodeSound exitCode (certificate -> baseFrame -> conflict))
    (ay_padc_conj_intro exitCode
      (certificate -> baseFrame -> conflict)
      hexit
      (fun hcertificate hbase =>
        replay
          (ay_padc_equisat_forward baseFrame finalFrame
            (ay_padc_reconstruction_equisat finalFrame baseFrame
              finalModel baseModel
              (ay_padc_hit_reconstruction baseFrame specializedFrame
                intermediateFrame finalFrame baseFingerprint runFingerprint
                cachedAssumptions runAssumptions deltaWitness stage1 stage2
                finalModel baseModel
                (ay_padc_log_hit previousLog nextLog baseFrame
                  specializedFrame intermediateFrame finalFrame
                  baseFingerprint runFingerprint cachedAssumptions
                  runAssumptions deltaWitness stage1 stage2 finalModel
                  baseModel entry)))
            hbase)
          hcertificate))

theorem ay_padc_failure_stale
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop) :
    staleDelta ->
    AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch := by
  intro hfailure
  exact ay_padc_disj_left staleDelta
    (AyDisj wrongFrame (AyDisj fingerprintMismatch stageMismatch))
    hfailure

theorem ay_padc_failure_wrong_frame
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop) :
    wrongFrame ->
    AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch := by
  intro hfailure
  exact ay_padc_disj_right staleDelta
    (AyDisj wrongFrame (AyDisj fingerprintMismatch stageMismatch))
    (ay_padc_disj_left wrongFrame
      (AyDisj fingerprintMismatch stageMismatch)
      hfailure)

theorem ay_padc_failure_fingerprint
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop) :
    fingerprintMismatch ->
    AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch := by
  intro hfailure
  exact ay_padc_disj_right staleDelta
    (AyDisj wrongFrame (AyDisj fingerprintMismatch stageMismatch))
    (ay_padc_disj_right wrongFrame
      (AyDisj fingerprintMismatch stageMismatch)
      (ay_padc_disj_left fingerprintMismatch stageMismatch hfailure))

theorem ay_padc_failure_stage
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop) :
    stageMismatch ->
    AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch := by
  intro hfailure
  exact ay_padc_disj_right staleDelta
    (AyDisj wrongFrame (AyDisj fingerprintMismatch stageMismatch))
    (ay_padc_disj_right wrongFrame
      (AyDisj fingerprintMismatch stageMismatch)
      (ay_padc_disj_right fingerprintMismatch stageMismatch hfailure))

theorem ay_padc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticAssumptionDeltaLogEntry
      previousLog nextLog currentFrame staleDelta wrongFrame
      fingerprintMismatch stageMismatch recompute diagnostic ->
    AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch := by
  intro entry
  exact ay_padc_conj_left
    (AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_padc_conj_left
      (AyConj
        (AyAssumptionDeltaFailure
          staleDelta wrongFrame fingerprintMismatch stageMismatch)
        (AyConj
          (AyRecomputeObligation currentFrame recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_padc_conj_right previousLog
        (AyConj
          (AyConj
            (AyAssumptionDeltaFailure
              staleDelta wrongFrame fingerprintMismatch stageMismatch)
            (AyConj
              (AyRecomputeObligation currentFrame recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_padc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticAssumptionDeltaLogEntry
      previousLog nextLog currentFrame staleDelta wrongFrame
      fingerprintMismatch stageMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_padc_conj_right
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_padc_conj_right
      (AyAssumptionDeltaFailure
        staleDelta wrongFrame fingerprintMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_padc_conj_left
        (AyConj
          (AyAssumptionDeltaFailure
            staleDelta wrongFrame fingerprintMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_padc_conj_right previousLog
          (AyConj
            (AyConj
              (AyAssumptionDeltaFailure
                staleDelta wrongFrame fingerprintMismatch stageMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_padc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticAssumptionDeltaLogEntry
      previousLog nextLog currentFrame staleDelta wrongFrame
      fingerprintMismatch stageMismatch recompute diagnostic ->
    AyRecomputeObligation currentFrame recompute := by
  intro entry
  exact ay_padc_conj_left
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_padc_conj_right
      (AyAssumptionDeltaFailure
        staleDelta wrongFrame fingerprintMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_padc_conj_left
        (AyConj
          (AyAssumptionDeltaFailure
            staleDelta wrongFrame fingerprintMismatch stageMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_padc_conj_right previousLog
          (AyConj
            (AyConj
              (AyAssumptionDeltaFailure
                staleDelta wrongFrame fingerprintMismatch stageMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_padc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (staleDelta : Prop) (wrongFrame : Prop)
    (fingerprintMismatch : Prop) (stageMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticAssumptionDeltaLogEntry
      previousLog nextLog currentFrame staleDelta wrongFrame
      fingerprintMismatch stageMismatch recompute diagnostic ->
    AyConj
      (AyAssumptionDeltaFailure
        staleDelta wrongFrame fingerprintMismatch stageMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_padc_conj_intro
    (AyAssumptionDeltaFailure
      staleDelta wrongFrame fingerprintMismatch stageMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_padc_diagnostic_failure previousLog nextLog currentFrame
      staleDelta wrongFrame fingerprintMismatch stageMismatch recompute
      diagnostic entry)
    (ay_padc_conj_intro
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_padc_diagnostic_recompute previousLog nextLog currentFrame
        staleDelta wrongFrame fingerprintMismatch stageMismatch recompute
        diagnostic entry)
      (ay_padc_diagnostic_no_claim previousLog nextLog currentFrame
        staleDelta wrongFrame fingerprintMismatch stageMismatch recompute
        diagnostic entry))
