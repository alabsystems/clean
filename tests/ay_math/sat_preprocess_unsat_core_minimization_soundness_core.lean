-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT-core minimization soundness after preprocessing. The propositions
-- stand for original/preprocessed incremental frames, core witnesses,
-- minimized core witnesses, projection maps, cache guards, audit entries,
-- diagnostic minimization failures, and public UNSAT/no-claim reports.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyPreprocessMap (originalFrame : Prop) (preprocessedFrame : Prop) :=
  AyEquisat originalFrame preprocessedFrame

def AyCoreProjection (minimizedCore : Prop) (originalAssumptions : Prop) :=
  minimizedCore -> originalAssumptions

def AyCoreMinimization (preprocessedCore : Prop) (minimizedCore : Prop) :=
  AyConj minimizedCore (minimizedCore -> preprocessedCore)

def AyPreprocessedUnsatCore
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj preprocessedCore (AyReplay preprocessedFrame certificate conflict)

def AyMinimizedUnsatCore
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (minimizedCore : Prop) (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCoreMinimization preprocessedCore minimizedCore)
    (AyReplay preprocessedFrame certificate conflict)

def AyCoreGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedMinimizedProjection
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPreprocessMap originalFrame preprocessedFrame)
    (AyConj
      (AyCoreMinimization preprocessedCore minimizedCore)
      (AyConj
        (AyCoreProjection minimizedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyMinimizationFailure
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop)
    (digestMismatch : Prop) :=
  AyDisj droppedAssumptionMismatch
    (AyDisj projectionMismatch digestMismatch)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentFrame : Prop) (recompute : Prop) :=
  AyConj currentFrame recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedMinimizedCoreLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticMinimizedCoreLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyMinimizationFailure
        droppedAssumptionMismatch projectionMismatch digestMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicUnsatReport
    (originalFrame : Prop) (originalAssumptions : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyExitCodeSound exitCode
    (AyConj originalAssumptions (certificate -> originalFrame -> conflict))

theorem ay_pucm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pucm_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pucm_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pucm_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pucm_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pucm_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pucm_conj_left (before -> after) (after -> before) eq

theorem ay_pucm_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pucm_conj_right (before -> after) (after -> before) eq

theorem ay_pucm_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pucm_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pucm_digest_match_forward
    (cachedDigest : Prop) (runDigest : Prop) :
    AyDigestMatch cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro hmatch
  intro hcached
  exact ay_pucm_conj_left
    (cachedDigest -> runDigest)
    (runDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pucm_core_witness
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    preprocessedCore := by
  intro core
  exact ay_pucm_conj_left preprocessedCore
    (AyReplay preprocessedFrame certificate conflict)
    core

theorem ay_pucm_core_replay
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    AyReplay preprocessedFrame certificate conflict := by
  intro core
  exact ay_pucm_conj_right preprocessedCore
    (AyReplay preprocessedFrame certificate conflict)
    core

theorem ay_pucm_minimized_core
    (preprocessedCore : Prop) (minimizedCore : Prop) :
    AyCoreMinimization preprocessedCore minimizedCore ->
    minimizedCore := by
  intro minimized
  exact ay_pucm_conj_left minimizedCore
    (minimizedCore -> preprocessedCore)
    minimized

theorem ay_pucm_minimized_subset
    (preprocessedCore : Prop) (minimizedCore : Prop) :
    AyCoreMinimization preprocessedCore minimizedCore ->
    minimizedCore ->
    preprocessedCore := by
  intro minimized
  exact ay_pucm_conj_right minimizedCore
    (minimizedCore -> preprocessedCore)
    minimized

theorem ay_pucm_guards_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedEpoch currentEpoch := by
  intro guards
  exact ay_pucm_conj_left
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))
    guards

theorem ay_pucm_guards_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyIdMatch cachedManifest runManifest := by
  intro guards
  exact ay_pucm_conj_left
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pucm_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      guards)

theorem ay_pucm_guards_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyDigestMatch cachedDigest runDigest := by
  intro guards
  exact ay_pucm_conj_right
    (AyIdMatch cachedManifest runManifest)
    (AyDigestMatch cachedDigest runDigest)
    (ay_pucm_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyDigestMatch cachedDigest runDigest))
      guards)

theorem ay_pucm_projection_map
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyPreprocessMap originalFrame preprocessedFrame := by
  intro accepted
  exact ay_pucm_conj_left
    (AyPreprocessMap originalFrame preprocessedFrame)
    (AyConj
      (AyCoreMinimization preprocessedCore minimizedCore)
      (AyConj
        (AyCoreProjection minimizedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pucm_projection_minimization
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyCoreMinimization preprocessedCore minimizedCore := by
  intro accepted
  exact ay_pucm_conj_left
    (AyCoreMinimization preprocessedCore minimizedCore)
    (AyConj
      (AyCoreProjection minimizedCore originalAssumptions)
      (AyCoreGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pucm_conj_right
      (AyPreprocessMap originalFrame preprocessedFrame)
      (AyConj
        (AyCoreMinimization preprocessedCore minimizedCore)
        (AyConj
          (AyCoreProjection minimizedCore originalAssumptions)
          (AyCoreGuards
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pucm_projection_core
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyCoreProjection minimizedCore originalAssumptions := by
  intro accepted
  exact ay_pucm_conj_left
    (AyCoreProjection minimizedCore originalAssumptions)
    (AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pucm_conj_right
      (AyCoreMinimization preprocessedCore minimizedCore)
      (AyConj
        (AyCoreProjection minimizedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pucm_conj_right
        (AyPreprocessMap originalFrame preprocessedFrame)
        (AyConj
          (AyCoreMinimization preprocessedCore minimizedCore)
          (AyConj
            (AyCoreProjection minimizedCore originalAssumptions)
            (AyCoreGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pucm_projection_guards
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro accepted
  exact ay_pucm_conj_right
    (AyCoreProjection minimizedCore originalAssumptions)
    (AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pucm_conj_right
      (AyCoreMinimization preprocessedCore minimizedCore)
      (AyConj
        (AyCoreProjection minimizedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pucm_conj_right
        (AyPreprocessMap originalFrame preprocessedFrame)
        (AyConj
          (AyCoreMinimization preprocessedCore minimizedCore)
          (AyConj
            (AyCoreProjection minimizedCore originalAssumptions)
            (AyCoreGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pucm_accepted_log_projection
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore minimizedCore originalAssumptions cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pucm_conj_left
    (AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog
    (ay_pucm_conj_right previousLog
      (AyConj
        (AyAcceptedMinimizedProjection
          originalFrame preprocessedFrame preprocessedCore minimizedCore
          originalAssumptions cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pucm_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore minimizedCore originalAssumptions cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyConj previousLog nextLog := by
  intro entry
  exact ay_pucm_conj_intro previousLog nextLog
    (ay_pucm_conj_left previousLog
      (AyConj
        (AyAcceptedMinimizedProjection
          originalFrame preprocessedFrame preprocessedCore minimizedCore
          originalAssumptions cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)
    (ay_pucm_conj_right
      (AyAcceptedMinimizedProjection
        originalFrame preprocessedFrame preprocessedCore minimizedCore
        originalAssumptions cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest)
      nextLog
      (ay_pucm_conj_right previousLog
        (AyConj
          (AyAcceptedMinimizedProjection
            originalFrame preprocessedFrame preprocessedCore minimizedCore
            originalAssumptions cachedEpoch currentEpoch cachedManifest
            runManifest cachedDigest runDigest)
          nextLog)
        entry))

theorem ay_pucm_minimized_core_sound
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (minimizedCore : Prop) (certificate : Prop) (conflict : Prop) :
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    AyCoreMinimization preprocessedCore minimizedCore ->
    AyMinimizedUnsatCore
      preprocessedFrame preprocessedCore minimizedCore certificate conflict := by
  intro core
  intro minimized
  exact ay_pucm_conj_intro
    (AyCoreMinimization preprocessedCore minimizedCore)
    (AyReplay preprocessedFrame certificate conflict)
    minimized
    (ay_pucm_core_replay preprocessedFrame preprocessedCore
      certificate conflict core)

theorem ay_pucm_original_to_preprocessed
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    originalFrame ->
    preprocessedFrame := by
  intro accepted
  exact ay_pucm_equisat_forward originalFrame preprocessedFrame
    (ay_pucm_projection_map originalFrame preprocessedFrame
      preprocessedCore minimizedCore originalAssumptions cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest
      accepted)

theorem ay_pucm_projected_minimized_assumptions
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedMinimizedProjection
      originalFrame preprocessedFrame preprocessedCore minimizedCore
      originalAssumptions cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    originalAssumptions := by
  intro accepted
  exact ay_pucm_projection_core originalFrame preprocessedFrame
    preprocessedCore minimizedCore originalAssumptions cachedEpoch
    currentEpoch cachedManifest runManifest cachedDigest runDigest
    accepted
    (ay_pucm_minimized_core preprocessedCore minimizedCore
      (ay_pucm_projection_minimization originalFrame preprocessedFrame
        preprocessedCore minimizedCore originalAssumptions cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest
        accepted))

theorem ay_pucm_invalid_dropped_assumption
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop) :
    droppedAssumptionMismatch ->
    AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch := by
  intro hdropped
  exact ay_pucm_disj_left droppedAssumptionMismatch
    (AyDisj projectionMismatch digestMismatch)
    hdropped

theorem ay_pucm_invalid_projection
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop) :
    projectionMismatch ->
    AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch := by
  intro hprojection
  exact ay_pucm_disj_right droppedAssumptionMismatch
    (AyDisj projectionMismatch digestMismatch)
    (ay_pucm_disj_left projectionMismatch digestMismatch hprojection)

theorem ay_pucm_invalid_digest
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop) :
    digestMismatch ->
    AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch := by
  intro hdigest
  exact ay_pucm_disj_right droppedAssumptionMismatch
    (AyDisj projectionMismatch digestMismatch)
    (ay_pucm_disj_right projectionMismatch digestMismatch hdigest)

theorem ay_pucm_invalid_log_entry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticMinimizedCoreLogEntry
      previousLog nextLog currentFrame droppedAssumptionMismatch
      projectionMismatch digestMismatch recompute diagnostic ->
    AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch := by
  intro entry
  exact ay_pucm_conj_left
    (AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pucm_conj_left
      (AyConj
        (AyMinimizationFailure
          droppedAssumptionMismatch projectionMismatch digestMismatch)
        (AyConj
          (AyRecomputeObligation currentFrame recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pucm_conj_right previousLog
        (AyConj
          (AyConj
            (AyMinimizationFailure
              droppedAssumptionMismatch projectionMismatch digestMismatch)
            (AyConj
              (AyRecomputeObligation currentFrame recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pucm_invalid_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticMinimizedCoreLogEntry
      previousLog nextLog currentFrame droppedAssumptionMismatch
      projectionMismatch digestMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pucm_conj_right
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pucm_conj_right
      (AyMinimizationFailure
        droppedAssumptionMismatch projectionMismatch digestMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pucm_conj_left
        (AyConj
          (AyMinimizationFailure
            droppedAssumptionMismatch projectionMismatch digestMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pucm_conj_right previousLog
          (AyConj
            (AyConj
              (AyMinimizationFailure
                droppedAssumptionMismatch projectionMismatch digestMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pucm_invalid_log_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticMinimizedCoreLogEntry
      previousLog nextLog currentFrame droppedAssumptionMismatch
      projectionMismatch digestMismatch recompute diagnostic ->
    AyRecomputeObligation currentFrame recompute := by
  intro entry
  exact ay_pucm_conj_left
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pucm_conj_right
      (AyMinimizationFailure
        droppedAssumptionMismatch projectionMismatch digestMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pucm_conj_left
        (AyConj
          (AyMinimizationFailure
            droppedAssumptionMismatch projectionMismatch digestMismatch)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pucm_conj_right previousLog
          (AyConj
            (AyConj
              (AyMinimizationFailure
                droppedAssumptionMismatch projectionMismatch digestMismatch)
              (AyConj
                (AyRecomputeObligation currentFrame recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pucm_public_unsat_report_intro
    (originalFrame : Prop) (originalAssumptions : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    originalAssumptions ->
    (certificate -> originalFrame -> conflict) ->
    AyPublicUnsatReport
      originalFrame originalAssumptions certificate conflict exitCode := by
  intro hexit
  intro hassumptions
  intro hreplay
  exact ay_pucm_conj_intro exitCode
    (AyConj originalAssumptions
      (certificate -> originalFrame -> conflict))
    hexit
    (ay_pucm_conj_intro originalAssumptions
      (certificate -> originalFrame -> conflict)
      hassumptions
      hreplay)

theorem ay_preprocess_unsat_core_minimized_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (minimizedCore : Prop)
    (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedMinimizedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore minimizedCore originalAssumptions cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    exitCode ->
    AyPublicUnsatReport
      originalFrame originalAssumptions certificate conflict exitCode := by
  intro log_entry
  intro core
  intro hexit
  exact ay_pucm_public_unsat_report_intro
    originalFrame originalAssumptions certificate conflict exitCode
    hexit
    (ay_pucm_projected_minimized_assumptions originalFrame
      preprocessedFrame preprocessedCore minimizedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest
      (ay_pucm_accepted_log_projection previousLog nextLog
        originalFrame preprocessedFrame preprocessedCore minimizedCore
        originalAssumptions cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest log_entry))
    (fun hcertificate horiginal =>
      ay_pucm_core_replay preprocessedFrame preprocessedCore
        certificate conflict core
        (ay_pucm_original_to_preprocessed originalFrame preprocessedFrame
          preprocessedCore minimizedCore originalAssumptions cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest
          (ay_pucm_accepted_log_projection previousLog nextLog
            originalFrame preprocessedFrame preprocessedCore minimizedCore
            originalAssumptions cachedEpoch currentEpoch cachedManifest
            runManifest cachedDigest runDigest log_entry)
          horiginal)
        hcertificate)

theorem ay_preprocess_unsat_core_minimization_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop)
    (droppedAssumptionMismatch : Prop)
    (projectionMismatch : Prop) (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticMinimizedCoreLogEntry
      previousLog nextLog currentFrame droppedAssumptionMismatch
      projectionMismatch digestMismatch recompute diagnostic ->
    AyConj
      (AyMinimizationFailure
        droppedAssumptionMismatch projectionMismatch digestMismatch)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pucm_conj_intro
    (AyMinimizationFailure
      droppedAssumptionMismatch projectionMismatch digestMismatch)
    (AyConj
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pucm_invalid_log_entry previousLog nextLog currentFrame
      droppedAssumptionMismatch projectionMismatch digestMismatch
      recompute diagnostic entry)
    (ay_pucm_conj_intro
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pucm_invalid_log_recompute previousLog nextLog currentFrame
        droppedAssumptionMismatch projectionMismatch digestMismatch
        recompute diagnostic entry)
      (ay_pucm_invalid_log_no_claim previousLog nextLog currentFrame
        droppedAssumptionMismatch projectionMismatch digestMismatch
        recompute diagnostic entry))
