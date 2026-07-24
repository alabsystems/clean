-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing certificate-chain replay soundness. The propositions stand for
-- stage-consumption evidence, hash/fingerprint agreement, composed
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

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyStageConsumes
    (inputCnf : Prop) (outputCnf : Prop) (stageCertificate : Prop) :=
  AyConj stageCertificate (AyEquisat inputCnf outputCnf)

def AyReplayChain
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop) :=
  AyConj
    (AyStageConsumes originalCnf stage1Cnf stage1Certificate)
    (AyConj
      (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
      (AyStageConsumes stage2Cnf finalCnf stage3Certificate))

def AyHashFingerprintAgreement
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop) :=
  AyConj
    stageHashes
    (AyConj
      aggregateDigest
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyIdMatch cachedFingerprint runFingerprint)))

def AyComposedReconstruction
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)

def AyAcceptedChainReplay
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AyReplayChain
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate)
    (AyConj
      (AyHashFingerprintAgreement
        stageHashes aggregateDigest cachedDigest runDigest
        cachedFingerprint runFingerprint)
      (AyComposedReconstruction
        finalCnf originalCnf finalModel originalModel))

def AyChainReplayFailure
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop) :=
  AyDisj stageGap
    (AyDisj stageReorder (AyDisj staleReplayState hashMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedChainReplayLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedChainReplay
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest
      cachedFingerprint runFingerprint finalModel originalModel)
    nextLog

def AyDiagnosticChainReplayLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyChainReplayFailure
        stageGap stageReorder staleReplayState hashMismatch)
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

theorem ay_pccr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pccr_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pccr_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pccr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pccr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pccr_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pccr_conj_left (before -> after) (after -> before) eq

theorem ay_pccr_stage_certificate
    (inputCnf : Prop) (outputCnf : Prop) (stageCertificate : Prop) :
    AyStageConsumes inputCnf outputCnf stageCertificate ->
    stageCertificate := by
  intro stage
  exact ay_pccr_conj_left stageCertificate
    (AyEquisat inputCnf outputCnf)
    stage

theorem ay_pccr_stage_equisat
    (inputCnf : Prop) (outputCnf : Prop) (stageCertificate : Prop) :
    AyStageConsumes inputCnf outputCnf stageCertificate ->
    AyEquisat inputCnf outputCnf := by
  intro stage
  exact ay_pccr_conj_right stageCertificate
    (AyEquisat inputCnf outputCnf)
    stage

theorem ay_pccr_chain_stage1
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop) :
    AyReplayChain
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate ->
    AyStageConsumes originalCnf stage1Cnf stage1Certificate := by
  intro chain
  exact ay_pccr_conj_left
    (AyStageConsumes originalCnf stage1Cnf stage1Certificate)
    (AyConj
      (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
      (AyStageConsumes stage2Cnf finalCnf stage3Certificate))
    chain

theorem ay_pccr_chain_original_to_final
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop) :
    AyReplayChain
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate ->
    originalCnf ->
    finalCnf := by
  intro chain horiginal
  have h1 : AyStageConsumes originalCnf stage1Cnf stage1Certificate :=
    ay_pccr_chain_stage1 originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate chain
  have rest :
      AyConj
        (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
        (AyStageConsumes stage2Cnf finalCnf stage3Certificate) :=
    ay_pccr_conj_right
      (AyStageConsumes originalCnf stage1Cnf stage1Certificate)
      (AyConj
        (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
        (AyStageConsumes stage2Cnf finalCnf stage3Certificate))
      chain
  have h2 : AyStageConsumes stage1Cnf stage2Cnf stage2Certificate :=
    ay_pccr_conj_left
      (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
      (AyStageConsumes stage2Cnf finalCnf stage3Certificate)
      rest
  have h3 : AyStageConsumes stage2Cnf finalCnf stage3Certificate :=
    ay_pccr_conj_right
      (AyStageConsumes stage1Cnf stage2Cnf stage2Certificate)
      (AyStageConsumes stage2Cnf finalCnf stage3Certificate)
      rest
  exact ay_pccr_equisat_forward stage2Cnf finalCnf
    (ay_pccr_stage_equisat stage2Cnf finalCnf stage3Certificate h3)
    (ay_pccr_equisat_forward stage1Cnf stage2Cnf
      (ay_pccr_stage_equisat stage1Cnf stage2Cnf stage2Certificate h2)
      (ay_pccr_equisat_forward originalCnf stage1Cnf
        (ay_pccr_stage_equisat originalCnf stage1Cnf stage1Certificate h1)
        horiginal))

theorem ay_pccr_report_chain
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyAcceptedChainReplay
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest
      cachedFingerprint runFingerprint finalModel originalModel ->
    AyReplayChain
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate := by
  intro accepted
  exact ay_pccr_conj_left
    (AyReplayChain
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate)
    (AyConj
      (AyHashFingerprintAgreement
        stageHashes aggregateDigest cachedDigest runDigest
        cachedFingerprint runFingerprint)
      (AyComposedReconstruction
        finalCnf originalCnf finalModel originalModel))
    accepted

theorem ay_pccr_report_reconstruction
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyAcceptedChainReplay
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest
      cachedFingerprint runFingerprint finalModel originalModel ->
    AyComposedReconstruction finalCnf originalCnf finalModel originalModel := by
  intro accepted
  exact ay_pccr_conj_right
    (AyHashFingerprintAgreement
      stageHashes aggregateDigest cachedDigest runDigest
      cachedFingerprint runFingerprint)
    (AyComposedReconstruction finalCnf originalCnf finalModel originalModel)
    (ay_pccr_conj_right
      (AyReplayChain
        originalCnf stage1Cnf stage2Cnf finalCnf
        stage1Certificate stage2Certificate stage3Certificate)
      (AyConj
        (AyHashFingerprintAgreement
          stageHashes aggregateDigest cachedDigest runDigest
          cachedFingerprint runFingerprint)
        (AyComposedReconstruction
          finalCnf originalCnf finalModel originalModel))
      accepted)

theorem ay_pccr_reconstruct_sat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyComposedReconstruction finalCnf originalCnf finalModel originalModel ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pccr_conj_left
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)
    reconstruction

theorem ay_pccr_reconstruction_equisat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyComposedReconstruction finalCnf originalCnf finalModel originalModel ->
    AyEquisat originalCnf finalCnf := by
  intro reconstruction
  exact ay_pccr_conj_right
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf finalCnf)
    reconstruction

theorem ay_pccr_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyAcceptedChainReplayLogEntry
      previousLog nextLog originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
      runFingerprint finalModel originalModel ->
    AyAcceptedChainReplay
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
      runFingerprint finalModel originalModel := by
  intro entry
  exact ay_pccr_conj_left
    (AyAcceptedChainReplay
      originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
      runFingerprint finalModel originalModel)
    nextLog
    (ay_pccr_conj_right previousLog
      (AyConj
        (AyAcceptedChainReplay
          originalCnf stage1Cnf stage2Cnf finalCnf
          stage1Certificate stage2Certificate stage3Certificate
          stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
          runFingerprint finalModel originalModel)
        nextLog)
      entry)

theorem ay_pccr_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedChainReplayLogEntry
      previousLog nextLog originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
      runFingerprint finalModel originalModel ->
    AySat finalCnf finalModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pccr_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pccr_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pccr_reconstruct_sat finalCnf originalCnf finalModel originalModel
        (ay_pccr_report_reconstruction originalCnf stage1Cnf stage2Cnf
          finalCnf stage1Certificate stage2Certificate stage3Certificate
          stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
          runFingerprint finalModel originalModel
          (ay_pccr_log_report previousLog nextLog originalCnf stage1Cnf
            stage2Cnf finalCnf stage1Certificate stage2Certificate
            stage3Certificate stageHashes aggregateDigest cachedDigest
            runDigest cachedFingerprint runFingerprint finalModel
            originalModel entry))
        sat))

theorem ay_pccr_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (stage1Cnf : Prop)
    (stage2Cnf : Prop) (finalCnf : Prop)
    (stage1Certificate : Prop) (stage2Certificate : Prop)
    (stage3Certificate : Prop)
    (stageHashes : Prop) (aggregateDigest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedFingerprint : Prop) (runFingerprint : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedChainReplayLogEntry
      previousLog nextLog originalCnf stage1Cnf stage2Cnf finalCnf
      stage1Certificate stage2Certificate stage3Certificate
      stageHashes aggregateDigest cachedDigest runDigest cachedFingerprint
      runFingerprint finalModel originalModel ->
    AyReplay finalCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pccr_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pccr_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_pccr_chain_original_to_final originalCnf stage1Cnf stage2Cnf
            finalCnf stage1Certificate stage2Certificate stage3Certificate
            (ay_pccr_report_chain originalCnf stage1Cnf stage2Cnf finalCnf
              stage1Certificate stage2Certificate stage3Certificate
              stageHashes aggregateDigest cachedDigest runDigest
              cachedFingerprint runFingerprint finalModel originalModel
              (ay_pccr_log_report previousLog nextLog originalCnf stage1Cnf
                stage2Cnf finalCnf stage1Certificate stage2Certificate
                stage3Certificate stageHashes aggregateDigest cachedDigest
                runDigest cachedFingerprint runFingerprint finalModel
                originalModel entry))
            horiginal)
          hcertificate))

theorem ay_pccr_failure_gap
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop) :
    stageGap ->
    AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch := by
  intro hgap
  exact ay_pccr_disj_left stageGap
    (AyDisj stageReorder (AyDisj staleReplayState hashMismatch))
    hgap

theorem ay_pccr_failure_reorder
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop) :
    stageReorder ->
    AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch := by
  intro hreorder
  exact ay_pccr_disj_right stageGap
    (AyDisj stageReorder (AyDisj staleReplayState hashMismatch))
    (ay_pccr_disj_left stageReorder
      (AyDisj staleReplayState hashMismatch)
      hreorder)

theorem ay_pccr_failure_stale
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop) :
    staleReplayState ->
    AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch := by
  intro hstale
  exact ay_pccr_disj_right stageGap
    (AyDisj stageReorder (AyDisj staleReplayState hashMismatch))
    (ay_pccr_disj_right stageReorder
      (AyDisj staleReplayState hashMismatch)
      (ay_pccr_disj_left staleReplayState hashMismatch hstale))

theorem ay_pccr_failure_hash
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop) :
    hashMismatch ->
    AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch := by
  intro hhash
  exact ay_pccr_disj_right stageGap
    (AyDisj stageReorder (AyDisj staleReplayState hashMismatch))
    (ay_pccr_disj_right stageReorder
      (AyDisj staleReplayState hashMismatch)
      (ay_pccr_disj_right staleReplayState hashMismatch hhash))

theorem ay_pccr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticChainReplayLogEntry
      previousLog nextLog currentCnf stageGap stageReorder
      staleReplayState hashMismatch recompute diagnostic ->
    AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch := by
  intro entry
  exact ay_pccr_conj_left
    (AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pccr_conj_left
      (AyConj
        (AyChainReplayFailure
          stageGap stageReorder staleReplayState hashMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pccr_conj_right previousLog
        (AyConj
          (AyConj
            (AyChainReplayFailure
              stageGap stageReorder staleReplayState hashMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pccr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticChainReplayLogEntry
      previousLog nextLog currentCnf stageGap stageReorder
      staleReplayState hashMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pccr_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pccr_conj_right
      (AyChainReplayFailure
        stageGap stageReorder staleReplayState hashMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pccr_conj_left
        (AyConj
          (AyChainReplayFailure
            stageGap stageReorder staleReplayState hashMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pccr_conj_right previousLog
          (AyConj
            (AyConj
              (AyChainReplayFailure
                stageGap stageReorder staleReplayState hashMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pccr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticChainReplayLogEntry
      previousLog nextLog currentCnf stageGap stageReorder
      staleReplayState hashMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pccr_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pccr_conj_right
      (AyChainReplayFailure
        stageGap stageReorder staleReplayState hashMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pccr_conj_left
        (AyConj
          (AyChainReplayFailure
            stageGap stageReorder staleReplayState hashMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pccr_conj_right previousLog
          (AyConj
            (AyConj
              (AyChainReplayFailure
                stageGap stageReorder staleReplayState hashMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pccr_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (stageGap : Prop) (stageReorder : Prop)
    (staleReplayState : Prop) (hashMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticChainReplayLogEntry
      previousLog nextLog currentCnf stageGap stageReorder
      staleReplayState hashMismatch recompute diagnostic ->
    AyConj
      (AyChainReplayFailure
        stageGap stageReorder staleReplayState hashMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pccr_conj_intro
    (AyChainReplayFailure
      stageGap stageReorder staleReplayState hashMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pccr_diagnostic_failure previousLog nextLog currentCnf
      stageGap stageReorder staleReplayState hashMismatch recompute
      diagnostic entry)
    (ay_pccr_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pccr_diagnostic_recompute previousLog nextLog currentCnf
        stageGap stageReorder staleReplayState hashMismatch recompute
        diagnostic entry)
      (ay_pccr_diagnostic_no_claim previousLog nextLog currentCnf
        stageGap stageReorder staleReplayState hashMismatch recompute
        diagnostic entry))
