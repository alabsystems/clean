-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cache-gated preprocessing pipeline soundness. The propositions stand for
-- integrated clause-elimination pipelines, manifest/digest/epoch cache keys,
-- fresh cache hits, recomputation obligations, stale/missing/failed caches,
-- audit entries, and public SAT/UNSAT outcomes.

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

def AyPipelineArtifact (originalCnf : Prop) (finalCnf : Prop) :=
  AyEquisat originalCnf finalCnf

def AyReconstructionMap
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)

def AyPipelineCacheKey
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedPipelineReport
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPipelineArtifact originalCnf finalCnf)
    (AyConj
      (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
      (AyConj
        pipelineWitness
        (AyPipelineCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyFreshPipelineCacheHit
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop) :=
  AyConj cacheEntry
    (AyAcceptedPipelineReport
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)

def AyCacheGateFailure
    (staleCache : Prop) (missingCache : Prop)
    (failedStage : Prop) :=
  AyDisj staleCache (AyDisj missingCache failedStage)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedCacheHitLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyFreshPipelineCacheHit
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest cacheEntry)
    nextLog

def AyDiagnosticCacheGateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleCache : Prop) (missingCache : Prop)
    (failedStage : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyCacheGateFailure staleCache missingCache failedStage)
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

theorem ay_ppcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ppcg_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ppcg_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ppcg_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ppcg_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ppcg_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_ppcg_conj_left (before -> after) (after -> before) eq

theorem ay_ppcg_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_ppcg_conj_right (before -> after) (after -> before) eq

theorem ay_ppcg_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_ppcg_conj_left cnf model sat

theorem ay_ppcg_report_artifact
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyPipelineArtifact originalCnf finalCnf := by
  intro accepted
  exact ay_ppcg_conj_left
    (AyPipelineArtifact originalCnf finalCnf)
    (AyConj
      (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
      (AyConj
        pipelineWitness
        (AyPipelineCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_ppcg_report_reconstruction
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReconstructionMap finalCnf originalCnf finalModel originalModel := by
  intro accepted
  exact ay_ppcg_conj_left
    (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
    (AyConj
      pipelineWitness
      (AyPipelineCacheKey
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_ppcg_conj_right
      (AyPipelineArtifact originalCnf finalCnf)
      (AyConj
        (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
        (AyConj
          pipelineWitness
          (AyPipelineCacheKey
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_ppcg_hit_report
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop) :
    AyFreshPipelineCacheHit
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest cacheEntry ->
    AyAcceptedPipelineReport
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest := by
  intro hit
  exact ay_ppcg_conj_right cacheEntry
    (AyAcceptedPipelineReport
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest)
    hit

theorem ay_ppcg_log_hit
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop) :
    AyAcceptedCacheHitLogEntry
      previousLog nextLog originalCnf finalCnf finalModel originalModel
      pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cacheEntry ->
    AyFreshPipelineCacheHit
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest cacheEntry := by
  intro entry
  exact ay_ppcg_conj_left
    (AyFreshPipelineCacheHit
      originalCnf finalCnf finalModel originalModel pipelineWitness
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest cacheEntry)
    nextLog
    (ay_ppcg_conj_right previousLog
      (AyConj
        (AyFreshPipelineCacheHit
          originalCnf finalCnf finalModel originalModel pipelineWitness
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest cacheEntry)
        nextLog)
      entry)

theorem ay_ppcg_reconstruct_sat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_ppcg_conj_left
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)
    reconstruction

theorem ay_ppcg_fresh_cache_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop) :
    AyAcceptedCacheHitLogEntry
      previousLog nextLog originalCnf finalCnf finalModel originalModel
      pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cacheEntry ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro entry
  intro sat
  exact ay_ppcg_reconstruct_sat finalCnf originalCnf finalModel originalModel
    (ay_ppcg_report_reconstruction originalCnf finalCnf finalModel
      originalModel pipelineWitness cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest
      (ay_ppcg_hit_report originalCnf finalCnf finalModel originalModel
        pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest cacheEntry
        (ay_ppcg_log_hit previousLog nextLog originalCnf finalCnf
          finalModel originalModel pipelineWitness cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest cacheEntry
          entry)))
    sat

theorem ay_ppcg_fresh_cache_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedCacheHitLogEntry
      previousLog nextLog originalCnf finalCnf finalModel originalModel
      pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cacheEntry ->
    AyReplay finalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro entry
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_ppcg_equisat_forward originalCnf finalCnf
      (ay_ppcg_report_artifact originalCnf finalCnf finalModel
        originalModel pipelineWitness cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        (ay_ppcg_hit_report originalCnf finalCnf finalModel originalModel
          pipelineWitness cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest cacheEntry
          (ay_ppcg_log_hit previousLog nextLog originalCnf finalCnf
            finalModel originalModel pipelineWitness cachedEpoch currentEpoch
            cachedManifest runManifest cachedDigest runDigest cacheEntry
            entry)))
      horiginal)
    hcertificate

theorem ay_ppcg_public_sat_from_cache
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedCacheHitLogEntry
      previousLog nextLog originalCnf finalCnf finalModel originalModel
      pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cacheEntry ->
    AySat finalCnf finalModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro sat
  intro hexit
  exact ay_ppcg_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_ppcg_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_ppcg_fresh_cache_sat previousLog nextLog originalCnf finalCnf
        finalModel originalModel pipelineWitness cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest cacheEntry
        entry sat))

theorem ay_ppcg_public_unsat_from_cache
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (pipelineWitness : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cacheEntry : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedCacheHitLogEntry
      previousLog nextLog originalCnf finalCnf finalModel originalModel
      pipelineWitness cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cacheEntry ->
    AyReplay finalCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro replay
  intro hexit
  exact ay_ppcg_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_ppcg_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_ppcg_fresh_cache_unsat previousLog nextLog originalCnf finalCnf
        finalModel originalModel pipelineWitness cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest cacheEntry
        certificate conflict entry replay))

theorem ay_ppcg_failure_stale
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop) :
    staleCache -> AyCacheGateFailure staleCache missingCache failedStage := by
  intro hstale
  exact ay_ppcg_disj_left staleCache
    (AyDisj missingCache failedStage)
    hstale

theorem ay_ppcg_failure_missing
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop) :
    missingCache -> AyCacheGateFailure staleCache missingCache failedStage := by
  intro hmissing
  exact ay_ppcg_disj_right staleCache
    (AyDisj missingCache failedStage)
    (ay_ppcg_disj_left missingCache failedStage hmissing)

theorem ay_ppcg_failure_stage
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop) :
    failedStage -> AyCacheGateFailure staleCache missingCache failedStage := by
  intro hfailed
  exact ay_ppcg_disj_right staleCache
    (AyDisj missingCache failedStage)
    (ay_ppcg_disj_right missingCache failedStage hfailed)

theorem ay_ppcg_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCacheGateLogEntry
      previousLog nextLog currentCnf staleCache missingCache failedStage
      recompute diagnostic ->
    AyCacheGateFailure staleCache missingCache failedStage := by
  intro entry
  exact ay_ppcg_conj_left
    (AyCacheGateFailure staleCache missingCache failedStage)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_ppcg_conj_left
      (AyConj
        (AyCacheGateFailure staleCache missingCache failedStage)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_ppcg_conj_right previousLog
        (AyConj
          (AyConj
            (AyCacheGateFailure staleCache missingCache failedStage)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_ppcg_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCacheGateLogEntry
      previousLog nextLog currentCnf staleCache missingCache failedStage
      recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_ppcg_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_ppcg_conj_right
      (AyCacheGateFailure staleCache missingCache failedStage)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_ppcg_conj_left
        (AyConj
          (AyCacheGateFailure staleCache missingCache failedStage)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_ppcg_conj_right previousLog
          (AyConj
            (AyConj
              (AyCacheGateFailure staleCache missingCache failedStage)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_ppcg_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCacheGateLogEntry
      previousLog nextLog currentCnf staleCache missingCache failedStage
      recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_ppcg_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_ppcg_conj_right
      (AyCacheGateFailure staleCache missingCache failedStage)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_ppcg_conj_left
        (AyConj
          (AyCacheGateFailure staleCache missingCache failedStage)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_ppcg_conj_right previousLog
          (AyConj
            (AyConj
              (AyCacheGateFailure staleCache missingCache failedStage)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_preprocess_pipeline_cache_gate_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleCache : Prop) (missingCache : Prop) (failedStage : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticCacheGateLogEntry
      previousLog nextLog currentCnf staleCache missingCache failedStage
      recompute diagnostic ->
    AyConj
      (AyCacheGateFailure staleCache missingCache failedStage)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_ppcg_conj_intro
    (AyCacheGateFailure staleCache missingCache failedStage)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_ppcg_diagnostic_failure previousLog nextLog currentCnf
      staleCache missingCache failedStage recompute diagnostic entry)
    (ay_ppcg_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_ppcg_diagnostic_recompute previousLog nextLog currentCnf
        staleCache missingCache failedStage recompute diagnostic entry)
      (ay_ppcg_diagnostic_no_claim previousLog nextLog currentCnf
        staleCache missingCache failedStage recompute diagnostic entry))
