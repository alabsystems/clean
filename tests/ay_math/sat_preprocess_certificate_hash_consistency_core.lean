-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing certificate hash consistency. The propositions stand for
-- per-stage certificate hashes, aggregate digests, stage-order evidence,
-- reconstruction maps, formula fingerprints, diagnostics, and public
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

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyStageHashBundle
    (subsumptionHash : Prop) (vivificationHash : Prop)
    (bceHash : Prop) (bveHash : Prop) :=
  AyConj subsumptionHash
    (AyConj vivificationHash (AyConj bceHash bveHash))

def AyHashConsistency
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop) :=
  AyConj stageHashes
    (AyConj aggregateDigest (AyConj stageOrder formulaFingerprint))

def AyReconstructionMap
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)

def AyAcceptedHashBundle
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :=
  AyConj
    (AyHashConsistency
      stageHashes aggregateDigest stageOrder formulaFingerprint)
    (AyConj
      (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyIdMatch cachedFingerprint runFingerprint)))

def AyHashGateFailure
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop) :=
  AyDisj stageHashMismatch
    (AyDisj aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedHashBundle
      originalCnf finalCnf stageHashes aggregateDigest stageOrder
      formulaFingerprint finalModel originalModel cachedDigest runDigest
      cachedFingerprint runFingerprint)
    nextLog

def AyDiagnosticHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyHashGateFailure
        stageHashMismatch aggregateMismatch
        stageOrderMismatch fingerprintMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat originalCnf model))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pchc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pchc_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pchc_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pchc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pchc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pchc_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pchc_conj_left (before -> after) (after -> before) eq

theorem ay_pchc_stage_hash_subsumption
    (subsumptionHash : Prop) (vivificationHash : Prop)
    (bceHash : Prop) (bveHash : Prop) :
    AyStageHashBundle
      subsumptionHash vivificationHash bceHash bveHash ->
    subsumptionHash := by
  intro bundle
  exact ay_pchc_conj_left subsumptionHash
    (AyConj vivificationHash (AyConj bceHash bveHash))
    bundle

theorem ay_pchc_stage_hash_vivification
    (subsumptionHash : Prop) (vivificationHash : Prop)
    (bceHash : Prop) (bveHash : Prop) :
    AyStageHashBundle
      subsumptionHash vivificationHash bceHash bveHash ->
    vivificationHash := by
  intro bundle
  exact ay_pchc_conj_left vivificationHash
    (AyConj bceHash bveHash)
    (ay_pchc_conj_right subsumptionHash
      (AyConj vivificationHash (AyConj bceHash bveHash))
      bundle)

theorem ay_pchc_hash_stage_order
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop) :
    AyHashConsistency
      stageHashes aggregateDigest stageOrder formulaFingerprint ->
    stageOrder := by
  intro consistency
  exact ay_pchc_conj_left stageOrder formulaFingerprint
    (ay_pchc_conj_right aggregateDigest
      (AyConj stageOrder formulaFingerprint)
      (ay_pchc_conj_right stageHashes
        (AyConj aggregateDigest
          (AyConj stageOrder formulaFingerprint))
        consistency))

theorem ay_pchc_hash_fingerprint
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop) :
    AyHashConsistency
      stageHashes aggregateDigest stageOrder formulaFingerprint ->
    formulaFingerprint := by
  intro consistency
  exact ay_pchc_conj_right stageOrder formulaFingerprint
    (ay_pchc_conj_right aggregateDigest
      (AyConj stageOrder formulaFingerprint)
      (ay_pchc_conj_right stageHashes
        (AyConj aggregateDigest
          (AyConj stageOrder formulaFingerprint))
        consistency))

theorem ay_pchc_report_consistency
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :
    AyAcceptedHashBundle
      originalCnf finalCnf stageHashes aggregateDigest stageOrder
      formulaFingerprint finalModel originalModel cachedDigest runDigest
      cachedFingerprint runFingerprint ->
    AyHashConsistency
      stageHashes aggregateDigest stageOrder formulaFingerprint := by
  intro accepted
  exact ay_pchc_conj_left
    (AyHashConsistency
      stageHashes aggregateDigest stageOrder formulaFingerprint)
    (AyConj
      (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyIdMatch cachedFingerprint runFingerprint)))
    accepted

theorem ay_pchc_report_reconstruction
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :
    AyAcceptedHashBundle
      originalCnf finalCnf stageHashes aggregateDigest stageOrder
      formulaFingerprint finalModel originalModel cachedDigest runDigest
      cachedFingerprint runFingerprint ->
    AyReconstructionMap finalCnf originalCnf finalModel originalModel := by
  intro accepted
  exact ay_pchc_conj_left
    (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
    (AyConj
      (AyDigestMatch cachedDigest runDigest)
      (AyIdMatch cachedFingerprint runFingerprint))
    (ay_pchc_conj_right
      (AyHashConsistency
        stageHashes aggregateDigest stageOrder formulaFingerprint)
      (AyConj
        (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
        (AyConj
          (AyDigestMatch cachedDigest runDigest)
          (AyIdMatch cachedFingerprint runFingerprint)))
      accepted)

theorem ay_pchc_reconstruct_sat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pchc_conj_left
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)
    reconstruction

theorem ay_pchc_reconstruction_equisat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    AyEquisat originalCnf finalCnf := by
  intro reconstruction
  exact ay_pchc_conj_right
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)
    reconstruction

theorem ay_pchc_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :
    AyAcceptedHashLogEntry
      previousLog nextLog originalCnf finalCnf stageHashes
      aggregateDigest stageOrder formulaFingerprint finalModel
      originalModel cachedDigest runDigest cachedFingerprint
      runFingerprint ->
    AyAcceptedHashBundle
      originalCnf finalCnf stageHashes aggregateDigest stageOrder
      formulaFingerprint finalModel originalModel cachedDigest runDigest
      cachedFingerprint runFingerprint := by
  intro entry
  exact ay_pchc_conj_left
    (AyAcceptedHashBundle
      originalCnf finalCnf stageHashes aggregateDigest stageOrder
      formulaFingerprint finalModel originalModel cachedDigest runDigest
      cachedFingerprint runFingerprint)
    nextLog
    (ay_pchc_conj_right previousLog
      (AyConj
        (AyAcceptedHashBundle
          originalCnf finalCnf stageHashes aggregateDigest stageOrder
          formulaFingerprint finalModel originalModel cachedDigest runDigest
          cachedFingerprint runFingerprint)
        nextLog)
      entry)

theorem ay_pchc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedHashLogEntry
      previousLog nextLog originalCnf finalCnf stageHashes
      aggregateDigest stageOrder formulaFingerprint finalModel
      originalModel cachedDigest runDigest cachedFingerprint
      runFingerprint ->
    AySat finalCnf finalModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pchc_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pchc_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pchc_reconstruct_sat finalCnf originalCnf
        finalModel originalModel
        (ay_pchc_report_reconstruction originalCnf finalCnf
          stageHashes aggregateDigest stageOrder formulaFingerprint
          finalModel originalModel cachedDigest runDigest cachedFingerprint
          runFingerprint
          (ay_pchc_log_report previousLog nextLog originalCnf finalCnf
            stageHashes aggregateDigest stageOrder formulaFingerprint
            finalModel originalModel cachedDigest runDigest cachedFingerprint
            runFingerprint entry))
        sat))

theorem ay_pchc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (stageOrder : Prop) (formulaFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedHashLogEntry
      previousLog nextLog originalCnf finalCnf stageHashes
      aggregateDigest stageOrder formulaFingerprint finalModel
      originalModel cachedDigest runDigest cachedFingerprint
      runFingerprint ->
    AyReplay finalCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pchc_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pchc_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_pchc_equisat_forward originalCnf finalCnf
            (ay_pchc_reconstruction_equisat finalCnf originalCnf
              finalModel originalModel
              (ay_pchc_report_reconstruction originalCnf finalCnf
                stageHashes aggregateDigest stageOrder formulaFingerprint
                finalModel originalModel cachedDigest runDigest
                cachedFingerprint runFingerprint
                (ay_pchc_log_report previousLog nextLog originalCnf
                  finalCnf stageHashes aggregateDigest stageOrder
                  formulaFingerprint finalModel originalModel cachedDigest
                  runDigest cachedFingerprint runFingerprint entry)))
            horiginal)
          hcertificate))

theorem ay_pchc_failure_stage_hash
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop) :
    stageHashMismatch ->
    AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch := by
  intro hfailure
  exact ay_pchc_disj_left stageHashMismatch
    (AyDisj aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch))
    hfailure

theorem ay_pchc_failure_aggregate
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop) :
    aggregateMismatch ->
    AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch := by
  intro hfailure
  exact ay_pchc_disj_right stageHashMismatch
    (AyDisj aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch))
    (ay_pchc_disj_left aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch)
      hfailure)

theorem ay_pchc_failure_stage_order
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop) :
    stageOrderMismatch ->
    AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch := by
  intro hfailure
  exact ay_pchc_disj_right stageHashMismatch
    (AyDisj aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch))
    (ay_pchc_disj_right aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch)
      (ay_pchc_disj_left stageOrderMismatch fingerprintMismatch hfailure))

theorem ay_pchc_failure_fingerprint
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop) :
    fingerprintMismatch ->
    AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch := by
  intro hfailure
  exact ay_pchc_disj_right stageHashMismatch
    (AyDisj aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch))
    (ay_pchc_disj_right aggregateMismatch
      (AyDisj stageOrderMismatch fingerprintMismatch)
      (ay_pchc_disj_right stageOrderMismatch fingerprintMismatch hfailure))

theorem ay_pchc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticHashLogEntry
      previousLog nextLog currentCnf stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch recompute diagnostic ->
    AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch := by
  intro entry
  exact ay_pchc_conj_left
    (AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pchc_conj_left
      (AyConj
        (AyHashGateFailure
          stageHashMismatch aggregateMismatch
          stageOrderMismatch fingerprintMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pchc_conj_right previousLog
        (AyConj
          (AyConj
            (AyHashGateFailure
              stageHashMismatch aggregateMismatch
              stageOrderMismatch fingerprintMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pchc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticHashLogEntry
      previousLog nextLog currentCnf stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pchc_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pchc_conj_right
      (AyHashGateFailure
        stageHashMismatch aggregateMismatch
        stageOrderMismatch fingerprintMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pchc_conj_left
        (AyConj
          (AyHashGateFailure
            stageHashMismatch aggregateMismatch
            stageOrderMismatch fingerprintMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pchc_conj_right previousLog
          (AyConj
            (AyConj
              (AyHashGateFailure
                stageHashMismatch aggregateMismatch
                stageOrderMismatch fingerprintMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pchc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticHashLogEntry
      previousLog nextLog currentCnf stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pchc_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pchc_conj_right
      (AyHashGateFailure
        stageHashMismatch aggregateMismatch
        stageOrderMismatch fingerprintMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pchc_conj_left
        (AyConj
          (AyHashGateFailure
            stageHashMismatch aggregateMismatch
            stageOrderMismatch fingerprintMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pchc_conj_right previousLog
          (AyConj
            (AyConj
              (AyHashGateFailure
                stageHashMismatch aggregateMismatch
                stageOrderMismatch fingerprintMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pchc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageHashMismatch : Prop) (aggregateMismatch : Prop)
    (stageOrderMismatch : Prop) (fingerprintMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticHashLogEntry
      previousLog nextLog currentCnf stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch recompute diagnostic ->
    AyConj
      (AyHashGateFailure
        stageHashMismatch aggregateMismatch
        stageOrderMismatch fingerprintMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pchc_conj_intro
    (AyHashGateFailure
      stageHashMismatch aggregateMismatch
      stageOrderMismatch fingerprintMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pchc_diagnostic_failure previousLog nextLog currentCnf
      stageHashMismatch aggregateMismatch stageOrderMismatch
      fingerprintMismatch recompute diagnostic entry)
    (ay_pchc_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pchc_diagnostic_recompute previousLog nextLog currentCnf
        stageHashMismatch aggregateMismatch stageOrderMismatch
        fingerprintMismatch recompute diagnostic entry)
      (ay_pchc_diagnostic_no_claim previousLog nextLog currentCnf
        stageHashMismatch aggregateMismatch stageOrderMismatch
        fingerprintMismatch recompute diagnostic entry))
