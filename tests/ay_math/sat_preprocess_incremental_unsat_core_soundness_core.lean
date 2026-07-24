-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental UNSAT-core projection through preprocessing. The propositions
-- stand for incremental clause/assumption frames, preprocessing maps, core
-- witnesses over preprocessed frames, projected original assumptions, guard
-- evidence, invalidation diagnostics, and public UNSAT/no-claim reports.

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

def AyIncrementalFrame
    (baseCnf : Prop) (clauses : Prop) (assumptions : Prop) :=
  AyConj baseCnf (AyConj clauses assumptions)

def AyPreprocessMap (originalFrame : Prop) (preprocessedFrame : Prop) :=
  AyEquisat originalFrame preprocessedFrame

def AyCoreProjection (preprocessedCore : Prop) (originalAssumptions : Prop) :=
  preprocessedCore -> originalAssumptions

def AyPreprocessedUnsatCore
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj preprocessedCore (AyReplay preprocessedFrame certificate conflict)

def AyCoreGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyEquisat cachedAssumptions currentAssumptions)))

def AyAcceptedCoreProjection
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :=
  AyConj
    (AyPreprocessMap originalFrame preprocessedFrame)
    (AyConj
      (AyCoreProjection preprocessedCore originalAssumptions)
      (AyCoreGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest cachedAssumptions currentAssumptions))

def AyCoreInvalidation
    (changedAssumptions : Prop) (staleMap : Prop) :=
  AyDisj changedAssumptions staleMap

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentFrame : Prop) (recompute : Prop) :=
  AyConj currentFrame recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedCoreLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions)
    nextLog

def AyInvalidCoreLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedAssumptions : Prop)
    (staleMap : Prop) (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyCoreInvalidation changedAssumptions staleMap)
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

theorem ay_pic_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pic_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pic_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pic_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pic_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pic_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pic_conj_left (before -> after) (after -> before) eq

theorem ay_pic_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pic_conj_right (before -> after) (after -> before) eq

theorem ay_pic_frame_base
    (baseCnf : Prop) (clauses : Prop) (assumptions : Prop) :
    AyIncrementalFrame baseCnf clauses assumptions ->
    baseCnf := by
  intro frame
  exact ay_pic_conj_left baseCnf (AyConj clauses assumptions) frame

theorem ay_pic_frame_assumptions
    (baseCnf : Prop) (clauses : Prop) (assumptions : Prop) :
    AyIncrementalFrame baseCnf clauses assumptions ->
    assumptions := by
  intro frame
  exact ay_pic_conj_right clauses assumptions
    (ay_pic_conj_right baseCnf (AyConj clauses assumptions) frame)

theorem ay_pic_id_match_forward
    (leftId : Prop) (rightId : Prop) :
    AyIdMatch leftId rightId ->
    leftId ->
    rightId := by
  intro hmatch
  intro hleft
  exact ay_pic_conj_left (leftId -> rightId) (rightId -> leftId)
    hmatch hleft

theorem ay_pic_digest_match_forward
    (cachedDigest : Prop) (runDigest : Prop) :
    AyDigestMatch cachedDigest runDigest ->
    cachedDigest ->
    runDigest := by
  intro hmatch
  intro hcached
  exact ay_pic_conj_left
    (cachedDigest -> runDigest)
    (runDigest -> cachedDigest)
    hmatch
    hcached

theorem ay_pic_core_witness
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    preprocessedCore := by
  intro core
  exact ay_pic_conj_left preprocessedCore
    (AyReplay preprocessedFrame certificate conflict)
    core

theorem ay_pic_core_replay
    (preprocessedFrame : Prop) (preprocessedCore : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    AyReplay preprocessedFrame certificate conflict := by
  intro core
  exact ay_pic_conj_right preprocessedCore
    (AyReplay preprocessedFrame certificate conflict)
    core

theorem ay_pic_guards_epoch
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyIdMatch cachedEpoch currentEpoch := by
  intro guards
  exact ay_pic_conj_left
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyEquisat cachedAssumptions currentAssumptions)))
    guards

theorem ay_pic_guards_manifest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyIdMatch cachedManifest runManifest := by
  intro guards
  exact ay_pic_conj_left
    (AyIdMatch cachedManifest runManifest)
    (AyConj
      (AyDigestMatch cachedDigest runDigest)
      (AyEquisat cachedAssumptions currentAssumptions))
    (ay_pic_conj_right
      (AyIdMatch cachedEpoch currentEpoch)
      (AyConj
        (AyIdMatch cachedManifest runManifest)
        (AyConj
          (AyDigestMatch cachedDigest runDigest)
          (AyEquisat cachedAssumptions currentAssumptions)))
      guards)

theorem ay_pic_guards_digest
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyDigestMatch cachedDigest runDigest := by
  intro guards
  exact ay_pic_conj_left
    (AyDigestMatch cachedDigest runDigest)
    (AyEquisat cachedAssumptions currentAssumptions)
    (ay_pic_conj_right
      (AyIdMatch cachedManifest runManifest)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyEquisat cachedAssumptions currentAssumptions))
      (ay_pic_conj_right
        (AyIdMatch cachedEpoch currentEpoch)
        (AyConj
          (AyIdMatch cachedManifest runManifest)
          (AyConj
            (AyDigestMatch cachedDigest runDigest)
            (AyEquisat cachedAssumptions currentAssumptions)))
        guards))

theorem ay_pic_guards_assumptions
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyEquisat cachedAssumptions currentAssumptions := by
  intro guards
  exact ay_pic_conj_right
    (AyDigestMatch cachedDigest runDigest)
    (AyEquisat cachedAssumptions currentAssumptions)
    (ay_pic_conj_right
      (AyIdMatch cachedManifest runManifest)
      (AyConj
        (AyDigestMatch cachedDigest runDigest)
        (AyEquisat cachedAssumptions currentAssumptions))
      (ay_pic_conj_right
        (AyIdMatch cachedEpoch currentEpoch)
        (AyConj
          (AyIdMatch cachedManifest runManifest)
          (AyConj
            (AyDigestMatch cachedDigest runDigest)
            (AyEquisat cachedAssumptions currentAssumptions)))
        guards))

theorem ay_pic_projection_map
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyPreprocessMap originalFrame preprocessedFrame := by
  intro accepted
  exact ay_pic_conj_left
    (AyPreprocessMap originalFrame preprocessedFrame)
    (AyConj
      (AyCoreProjection preprocessedCore originalAssumptions)
      (AyCoreGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest cachedAssumptions currentAssumptions))
    accepted

theorem ay_pic_projection_core
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyCoreProjection preprocessedCore originalAssumptions := by
  intro accepted
  exact ay_pic_conj_left
    (AyCoreProjection preprocessedCore originalAssumptions)
    (AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions)
    (ay_pic_conj_right
      (AyPreprocessMap originalFrame preprocessedFrame)
      (AyConj
        (AyCoreProjection preprocessedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest cachedAssumptions currentAssumptions))
      accepted)

theorem ay_pic_projection_guards
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions := by
  intro accepted
  exact ay_pic_conj_right
    (AyCoreProjection preprocessedCore originalAssumptions)
    (AyCoreGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions)
    (ay_pic_conj_right
      (AyPreprocessMap originalFrame preprocessedFrame)
      (AyConj
        (AyCoreProjection preprocessedCore originalAssumptions)
        (AyCoreGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest cachedAssumptions currentAssumptions))
      accepted)

theorem ay_pic_original_to_preprocessed
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    originalFrame ->
    preprocessedFrame := by
  intro accepted
  exact ay_pic_equisat_forward originalFrame preprocessedFrame
    (ay_pic_projection_map originalFrame preprocessedFrame
      preprocessedCore originalAssumptions cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      cachedAssumptions currentAssumptions accepted)

theorem ay_pic_projected_core_assumptions
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    preprocessedCore ->
    originalAssumptions := by
  intro accepted
  exact ay_pic_projection_core originalFrame preprocessedFrame
    preprocessedCore originalAssumptions cachedEpoch currentEpoch
    cachedManifest runManifest cachedDigest runDigest
    cachedAssumptions currentAssumptions accepted

theorem ay_pic_accepted_log_projection
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore originalAssumptions cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      cachedAssumptions currentAssumptions ->
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions := by
  intro log_entry
  exact ay_pic_conj_left
    (AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions)
    nextLog
    (ay_pic_conj_right previousLog
      (AyConj
        (AyAcceptedCoreProjection
          originalFrame preprocessedFrame preprocessedCore originalAssumptions
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest cachedAssumptions currentAssumptions)
        nextLog)
      log_entry)

theorem ay_pic_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop) :
    AyAcceptedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore originalAssumptions cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      cachedAssumptions currentAssumptions ->
    AyConj previousLog nextLog := by
  intro log_entry
  exact ay_pic_conj_intro previousLog nextLog
    (ay_pic_conj_left previousLog
      (AyConj
        (AyAcceptedCoreProjection
          originalFrame preprocessedFrame preprocessedCore originalAssumptions
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest cachedAssumptions currentAssumptions)
        nextLog)
      log_entry)
    (ay_pic_conj_right
      (AyAcceptedCoreProjection
        originalFrame preprocessedFrame preprocessedCore originalAssumptions
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest cachedAssumptions currentAssumptions)
      nextLog
      (ay_pic_conj_right previousLog
        (AyConj
          (AyAcceptedCoreProjection
            originalFrame preprocessedFrame preprocessedCore originalAssumptions
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest cachedAssumptions currentAssumptions)
          nextLog)
        log_entry))

theorem ay_pic_invalidation_assumptions
    (changedAssumptions : Prop) (staleMap : Prop) :
    changedAssumptions ->
    AyCoreInvalidation changedAssumptions staleMap := by
  exact ay_pic_disj_left changedAssumptions staleMap

theorem ay_pic_invalidation_stale_map
    (changedAssumptions : Prop) (staleMap : Prop) :
    staleMap ->
    AyCoreInvalidation changedAssumptions staleMap := by
  exact ay_pic_disj_right changedAssumptions staleMap

theorem ay_pic_invalid_log_entry
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedAssumptions : Prop)
    (staleMap : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidCoreLogEntry
      previousLog nextLog currentFrame changedAssumptions
      staleMap recompute diagnostic ->
    AyConj
      (AyCoreInvalidation changedAssumptions staleMap)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pic_conj_left
    (AyConj
      (AyCoreInvalidation changedAssumptions staleMap)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog
    (ay_pic_conj_right previousLog
      (AyConj
        (AyConj
          (AyCoreInvalidation changedAssumptions staleMap)
          (AyConj
            (AyRecomputeObligation currentFrame recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog)
      log_entry)

theorem ay_pic_invalid_log_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedAssumptions : Prop)
    (staleMap : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidCoreLogEntry
      previousLog nextLog currentFrame changedAssumptions
      staleMap recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pic_conj_right
    (AyRecomputeObligation currentFrame recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pic_conj_right
      (AyCoreInvalidation changedAssumptions staleMap)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pic_invalid_log_entry previousLog nextLog currentFrame
        changedAssumptions staleMap recompute diagnostic log_entry))

theorem ay_pic_invalid_log_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedAssumptions : Prop)
    (staleMap : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidCoreLogEntry
      previousLog nextLog currentFrame changedAssumptions
      staleMap recompute diagnostic ->
    recompute := by
  intro log_entry
  exact ay_pic_conj_right currentFrame recompute
    (ay_pic_conj_left
      (AyRecomputeObligation currentFrame recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pic_conj_right
        (AyCoreInvalidation changedAssumptions staleMap)
        (AyConj
          (AyRecomputeObligation currentFrame recompute)
          (AyNoSemanticClaim diagnostic))
        (ay_pic_invalid_log_entry previousLog nextLog currentFrame
          changedAssumptions staleMap recompute diagnostic log_entry)))

theorem ay_pic_unsat_core_sound
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedCoreProjection
      originalFrame preprocessedFrame preprocessedCore originalAssumptions
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest cachedAssumptions currentAssumptions ->
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    certificate ->
    originalFrame ->
    AyConj originalAssumptions conflict := by
  intro accepted
  intro core
  intro hcertificate
  intro horiginal
  exact ay_pic_conj_intro originalAssumptions conflict
    (ay_pic_projected_core_assumptions originalFrame preprocessedFrame
      preprocessedCore originalAssumptions cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest cachedAssumptions
      currentAssumptions accepted
      (ay_pic_core_witness preprocessedFrame preprocessedCore
        certificate conflict core))
    (ay_pic_core_replay preprocessedFrame preprocessedCore
      certificate conflict core
      (ay_pic_original_to_preprocessed originalFrame preprocessedFrame
        preprocessedCore originalAssumptions cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest cachedAssumptions
        currentAssumptions accepted horiginal)
      hcertificate)

theorem ay_pic_public_unsat_report_intro
    (originalFrame : Prop) (originalAssumptions : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    AyConj originalAssumptions (certificate -> originalFrame -> conflict) ->
    AyPublicUnsatReport originalFrame originalAssumptions
      certificate conflict exitCode := by
  intro hexit
  intro claim
  exact ay_pic_conj_intro exitCode
    (AyConj originalAssumptions
      (certificate -> originalFrame -> conflict))
    hexit
    claim

theorem ay_preprocess_incremental_unsat_core_public_sound
    (previousLog : Prop) (nextLog : Prop)
    (originalFrame : Prop) (preprocessedFrame : Prop)
    (preprocessedCore : Prop) (originalAssumptions : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (cachedAssumptions : Prop) (currentAssumptions : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedCoreLogEntry
      previousLog nextLog originalFrame preprocessedFrame
      preprocessedCore originalAssumptions cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest
      cachedAssumptions currentAssumptions ->
    AyPreprocessedUnsatCore
      preprocessedFrame preprocessedCore certificate conflict ->
    exitCode ->
    AyPublicUnsatReport originalFrame originalAssumptions
      certificate conflict exitCode := by
  intro log_entry
  intro core
  intro hexit
  exact ay_pic_public_unsat_report_intro
    originalFrame originalAssumptions certificate conflict exitCode
    hexit
    (ay_pic_conj_intro originalAssumptions
      (certificate -> originalFrame -> conflict)
      (ay_pic_projected_core_assumptions originalFrame preprocessedFrame
        preprocessedCore originalAssumptions cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        cachedAssumptions currentAssumptions
        (ay_pic_accepted_log_projection previousLog nextLog
          originalFrame preprocessedFrame preprocessedCore
          originalAssumptions cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest cachedAssumptions
          currentAssumptions log_entry)
        (ay_pic_core_witness preprocessedFrame preprocessedCore
          certificate conflict core))
      (fun hcertificate horiginal =>
        ay_pic_core_replay preprocessedFrame preprocessedCore
          certificate conflict core
          (ay_pic_original_to_preprocessed originalFrame preprocessedFrame
            preprocessedCore originalAssumptions cachedEpoch currentEpoch
            cachedManifest runManifest cachedDigest runDigest
            cachedAssumptions currentAssumptions
            (ay_pic_accepted_log_projection previousLog nextLog
              originalFrame preprocessedFrame preprocessedCore
              originalAssumptions cachedEpoch currentEpoch cachedManifest
              runManifest cachedDigest runDigest cachedAssumptions
              currentAssumptions log_entry)
            horiginal)
          hcertificate))

theorem ay_preprocess_incremental_unsat_core_invalid_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentFrame : Prop) (changedAssumptions : Prop)
    (staleMap : Prop) (recompute : Prop) (diagnostic : Prop) :
    AyInvalidCoreLogEntry
      previousLog nextLog currentFrame changedAssumptions
      staleMap recompute diagnostic ->
    AyConj
      (AyCoreInvalidation changedAssumptions staleMap)
      (AyConj
        (AyRecomputeObligation currentFrame recompute)
        (AyNoSemanticClaim diagnostic)) := by
  exact ay_pic_invalid_log_entry previousLog nextLog currentFrame
    changedAssumptions staleMap recompute diagnostic
