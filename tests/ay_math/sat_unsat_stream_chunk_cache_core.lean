-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cached checked UNSAT stream chunks for ay. Propositions stand for cache keys,
-- compressed chunks, visible chunks, checkpoint guards, accumulator lookups,
-- cache-hit acceptance, stale-cache fallback, and UNSAT claims. Guard-matched
-- cache entries preserve checkpoint/resume original-UNSAT soundness; stale
-- entries only produce the explicit no-claim fallback.

def AyUSCCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSCCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSCCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSCCEquisat (before : Prop) (after : Prop) :=
  AyUSCCConj (before -> after) (after -> before)

def AyUSCCCacheKey
    (chunkKey : Prop) (checkpointKey : Prop)
    (guardKey : Prop) :=
  AyUSCCConj chunkKey
    (AyUSCCConj checkpointKey guardKey)

def AyUSCCCompressedProjection
    (compressedChunk : Prop) (visibleChunk : Prop) :=
  AyUSCCMap compressedChunk visibleChunk

def AyUSCCCheckpointCompatibility
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) :=
  AyUSCCConj cacheGuard
    (AyUSCCConj currentGuard
      (AyUSCCMap cacheGuard checkpointSnapshot))

def AyUSCCAcceptedCacheReuse
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :=
  AyUSCCConj
    (AyUSCCMap visibleChunk checkpointSnapshot)
    (AyUSCCMap checkpointSnapshot finalAccumulator)

def AyUSCCFinalAccumulatorLookup
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUSCCConj
    (AyUSCCMap finalAccumulator emptyClause)
    (AyUSCCMap emptyClause visibleUnsat)

def AyUSCCPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCCConj
    (AyUSCCEquisat originalCNF visibleCNF)
    (AyUSCCMap visibleUnsat originalUnsat)

def AyUSCCGuardMatchedCache
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCCConj visibleChunk
    (AyUSCCConj
      (AyUSCCCacheKey chunkKey checkpointKey guardKey)
      (AyUSCCConj
        (AyUSCCCompressedProjection compressedChunk visibleChunk)
        (AyUSCCConj
          (AyUSCCCheckpointCompatibility
            cacheGuard currentGuard checkpointSnapshot)
          (AyUSCCConj
            (AyUSCCAcceptedCacheReuse
              visibleChunk checkpointSnapshot finalAccumulator)
            (AyUSCCConj
              (AyUSCCFinalAccumulatorLookup
                finalAccumulator emptyClause visibleUnsat)
              (AyUSCCPreprocessTransport
                originalCNF visibleCNF visibleUnsat originalUnsat))))))

def AyUSCCStaleCacheEntry
    (chunkKey : Prop) (checkpointKey : Prop)
    (guardKey : Prop) (fallbackNoClaim : Prop) :=
  AyUSCCConj
    (AyUSCCCacheKey chunkKey checkpointKey guardKey)
    fallbackNoClaim

def AyUSCCDirectResumeContract
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCCConj
    (AyUSCCMap visibleChunk checkpointSnapshot)
    (AyUSCCConj
      (AyUSCCMap checkpointSnapshot finalAccumulator)
      (AyUSCCConj
        (AyUSCCMap finalAccumulator emptyClause)
        (AyUSCCConj
          (AyUSCCMap emptyClause visibleUnsat)
          (AyUSCCMap visibleUnsat originalUnsat))))

theorem ay_uscc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSCCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uscc_conj_left
    (p : Prop) (q : Prop) :
    AyUSCCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uscc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSCCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uscc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSCCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uscc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSCCEquisat before after := by
  intro forward
  intro backward
  exact ay_uscc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_uscc_equisat_forward
    (before : Prop) (after : Prop) :
    AyUSCCEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_uscc_equisat_backward
    (before : Prop) (after : Prop) :
    AyUSCCEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_uscc_cache_key_chunk
    (chunkKey : Prop) (checkpointKey : Prop)
    (guardKey : Prop) :
    AyUSCCCacheKey chunkKey checkpointKey guardKey ->
    chunkKey := by
  intro key
  exact ay_uscc_conj_left chunkKey
    (AyUSCCConj checkpointKey guardKey)
    key

theorem ay_uscc_project_visible_chunk
    (compressedChunk : Prop) (visibleChunk : Prop) :
    AyUSCCCompressedProjection compressedChunk visibleChunk ->
    compressedChunk ->
    visibleChunk := by
  intro projection
  exact projection

theorem ay_uscc_compatible_checkpoint
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) :
    AyUSCCCheckpointCompatibility
      cacheGuard currentGuard checkpointSnapshot ->
    checkpointSnapshot := by
  intro compatibility
  exact compatibility checkpointSnapshot
    (fun hguard tail =>
      tail checkpointSnapshot
        (fun _current guard_to_checkpoint =>
          guard_to_checkpoint hguard))

theorem ay_uscc_reuse_checkpoint
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCCAcceptedCacheReuse
      visibleChunk checkpointSnapshot finalAccumulator ->
    visibleChunk ->
    checkpointSnapshot := by
  intro reuse
  exact reuse (visibleChunk -> checkpointSnapshot)
    (fun visible_to_checkpoint _checkpoint_to_final =>
      visible_to_checkpoint)

theorem ay_uscc_reuse_final_accumulator
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCCAcceptedCacheReuse
      visibleChunk checkpointSnapshot finalAccumulator ->
    checkpointSnapshot ->
    finalAccumulator := by
  intro reuse
  exact reuse (checkpointSnapshot -> finalAccumulator)
    (fun _visible_to_checkpoint checkpoint_to_final =>
      checkpoint_to_final)

theorem ay_uscc_reuse_final_from_visible
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCCAcceptedCacheReuse
      visibleChunk checkpointSnapshot finalAccumulator ->
    visibleChunk ->
    finalAccumulator := by
  intro reuse
  intro hvisible
  exact ay_uscc_reuse_final_accumulator
    visibleChunk checkpointSnapshot finalAccumulator reuse
    (ay_uscc_reuse_checkpoint
      visibleChunk checkpointSnapshot finalAccumulator reuse hvisible)

theorem ay_uscc_final_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCCFinalAccumulatorLookup
      finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro lookup
  exact lookup (finalAccumulator -> emptyClause)
    (fun final_to_empty _empty_to_unsat => final_to_empty)

theorem ay_uscc_empty_visible_unsat
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCCFinalAccumulatorLookup
      finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro lookup
  exact lookup (emptyClause -> visibleUnsat)
    (fun _final_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_uscc_preprocess_unsat_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_uscc_matched_visible_chunk
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    visibleChunk := by
  intro cache
  exact ay_uscc_conj_left visibleChunk
    (AyUSCCConj
      (AyUSCCCacheKey chunkKey checkpointKey guardKey)
      (AyUSCCConj
        (AyUSCCCompressedProjection compressedChunk visibleChunk)
        (AyUSCCConj
          (AyUSCCCheckpointCompatibility
            cacheGuard currentGuard checkpointSnapshot)
          (AyUSCCConj
            (AyUSCCAcceptedCacheReuse
              visibleChunk checkpointSnapshot finalAccumulator)
            (AyUSCCConj
              (AyUSCCFinalAccumulatorLookup
                finalAccumulator emptyClause visibleUnsat)
              (AyUSCCPreprocessTransport
                originalCNF visibleCNF visibleUnsat originalUnsat))))))
    cache

theorem ay_uscc_matched_key
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCCCacheKey chunkKey checkpointKey guardKey := by
  intro cache
  exact cache (AyUSCCCacheKey chunkKey checkpointKey guardKey)
    (fun _visible tail =>
      tail (AyUSCCCacheKey chunkKey checkpointKey guardKey)
        (fun key _rest => key))

theorem ay_uscc_matched_reuse
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCCAcceptedCacheReuse
      visibleChunk checkpointSnapshot finalAccumulator := by
  intro cache
  exact cache
    (AyUSCCAcceptedCacheReuse
      visibleChunk checkpointSnapshot finalAccumulator)
    (fun _visible tail =>
      tail
        (AyUSCCAcceptedCacheReuse
          visibleChunk checkpointSnapshot finalAccumulator)
        (fun _key rest =>
          rest
            (AyUSCCAcceptedCacheReuse
              visibleChunk checkpointSnapshot finalAccumulator)
            (fun _projection tail2 =>
              tail2
                (AyUSCCAcceptedCacheReuse
                  visibleChunk checkpointSnapshot finalAccumulator)
                (fun _compatibility tail3 =>
                  tail3
                    (AyUSCCAcceptedCacheReuse
                      visibleChunk checkpointSnapshot finalAccumulator)
                    (fun reuse _tail => reuse)))))

theorem ay_uscc_matched_final_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCCFinalAccumulatorLookup
      finalAccumulator emptyClause visibleUnsat := by
  intro cache
  exact cache
    (AyUSCCFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
    (fun _visible tail =>
      tail
        (AyUSCCFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
        (fun _key rest =>
          rest
            (AyUSCCFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
            (fun _projection tail2 =>
              tail2
                (AyUSCCFinalAccumulatorLookup
                  finalAccumulator emptyClause visibleUnsat)
                (fun _compatibility tail3 =>
                  tail3
                    (AyUSCCFinalAccumulatorLookup
                      finalAccumulator emptyClause visibleUnsat)
                    (fun _reuse tail4 =>
                      tail4
                        (AyUSCCFinalAccumulatorLookup
                          finalAccumulator emptyClause visibleUnsat)
                        (fun final_lookup _transport => final_lookup))))))

theorem ay_uscc_matched_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro cache
  exact cache
    (AyUSCCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _visible tail =>
      tail
        (AyUSCCPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _key rest =>
          rest
            (AyUSCCPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _projection tail2 =>
              tail2
                (AyUSCCPreprocessTransport
                  originalCNF visibleCNF visibleUnsat originalUnsat)
                (fun _compatibility tail3 =>
                  tail3
                    (AyUSCCPreprocessTransport
                      originalCNF visibleCNF visibleUnsat originalUnsat)
                    (fun _reuse tail4 =>
                      tail4
                        (AyUSCCPreprocessTransport
                          originalCNF visibleCNF visibleUnsat originalUnsat)
                        (fun _final_lookup transport => transport))))))

theorem ay_uscc_matched_final_accumulator
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    finalAccumulator := by
  intro cache
  exact ay_uscc_reuse_final_from_visible
    visibleChunk checkpointSnapshot finalAccumulator
    (ay_uscc_matched_reuse
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)
    (ay_uscc_matched_visible_chunk
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)

theorem ay_uscc_matched_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    visibleUnsat := by
  intro cache
  exact ay_uscc_empty_visible_unsat finalAccumulator emptyClause visibleUnsat
    (ay_uscc_matched_final_lookup
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)
    (ay_uscc_final_empty finalAccumulator emptyClause visibleUnsat
      (ay_uscc_matched_final_lookup
        originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
        visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat cache)
      (ay_uscc_matched_final_accumulator
        originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
        visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat cache))

theorem ay_uscc_guard_matched_cache_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro cache
  exact ay_uscc_preprocess_unsat_transport
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_uscc_matched_preprocess
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)
    (ay_uscc_matched_visible_unsat
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)

theorem ay_uscc_matched_to_direct_resume
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCCDirectResumeContract
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat := by
  intro cache
  exact ay_uscc_conj_intro
    (visibleChunk -> checkpointSnapshot)
    (AyUSCCConj
      (checkpointSnapshot -> finalAccumulator)
      (AyUSCCConj
        (finalAccumulator -> emptyClause)
        (AyUSCCConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat))))
    (ay_uscc_reuse_checkpoint visibleChunk checkpointSnapshot finalAccumulator
      (ay_uscc_matched_reuse
        originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
        visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat cache))
    (ay_uscc_conj_intro
      (checkpointSnapshot -> finalAccumulator)
      (AyUSCCConj
        (finalAccumulator -> emptyClause)
        (AyUSCCConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat)))
      (ay_uscc_reuse_final_accumulator
        visibleChunk checkpointSnapshot finalAccumulator
        (ay_uscc_matched_reuse
          originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
          visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
          emptyClause visibleUnsat originalUnsat cache))
      (ay_uscc_conj_intro
        (finalAccumulator -> emptyClause)
        (AyUSCCConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat))
        (ay_uscc_final_empty finalAccumulator emptyClause visibleUnsat
          (ay_uscc_matched_final_lookup
            originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
            visibleChunk cacheGuard currentGuard checkpointSnapshot
            finalAccumulator emptyClause visibleUnsat originalUnsat cache))
        (ay_uscc_conj_intro
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat)
          (ay_uscc_empty_visible_unsat finalAccumulator emptyClause visibleUnsat
            (ay_uscc_matched_final_lookup
              originalCNF visibleCNF chunkKey checkpointKey guardKey
              compressedChunk visibleChunk cacheGuard currentGuard
              checkpointSnapshot finalAccumulator emptyClause visibleUnsat
              originalUnsat cache))
          (ay_uscc_preprocess_unsat_transport
            originalCNF visibleCNF visibleUnsat originalUnsat
            (ay_uscc_matched_preprocess
              originalCNF visibleCNF chunkKey checkpointKey guardKey
              compressedChunk visibleChunk cacheGuard currentGuard
              checkpointSnapshot finalAccumulator emptyClause visibleUnsat
              originalUnsat cache)))))

theorem ay_uscc_direct_resume_original_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCDirectResumeContract visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    visibleChunk ->
    originalUnsat := by
  intro direct
  intro hvisible
  exact direct originalUnsat
    (fun visible_to_checkpoint tail =>
      tail originalUnsat
        (fun checkpoint_to_final tail2 =>
          tail2 originalUnsat
            (fun final_to_empty tail3 =>
              tail3 originalUnsat
                (fun empty_to_unsat unsat_to_original =>
                  unsat_to_original
                    (empty_to_unsat
                      (final_to_empty
                        (checkpoint_to_final
                          (visible_to_checkpoint hvisible))))))))

theorem ay_uscc_guard_matched_preserves_direct_soundness
    (originalCNF : Prop) (visibleCNF : Prop)
    (chunkKey : Prop) (checkpointKey : Prop) (guardKey : Prop)
    (compressedChunk : Prop) (visibleChunk : Prop)
    (cacheGuard : Prop) (currentGuard : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCCGuardMatchedCache originalCNF visibleCNF chunkKey checkpointKey
      guardKey compressedChunk visibleChunk cacheGuard currentGuard
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro cache
  exact ay_uscc_direct_resume_original_unsat
    visibleChunk checkpointSnapshot finalAccumulator emptyClause
    visibleUnsat originalUnsat
    (ay_uscc_matched_to_direct_resume
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)
    (ay_uscc_matched_visible_chunk
      originalCNF visibleCNF chunkKey checkpointKey guardKey compressedChunk
      visibleChunk cacheGuard currentGuard checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat cache)

theorem ay_uscc_stale_cache_no_claim
    (chunkKey : Prop) (checkpointKey : Prop)
    (guardKey : Prop) (fallbackNoClaim : Prop) :
    AyUSCCStaleCacheEntry
      chunkKey checkpointKey guardKey fallbackNoClaim ->
    fallbackNoClaim := by
  intro stale
  exact stale fallbackNoClaim
    (fun _key no_claim => no_claim)

theorem ay_uscc_stale_cache_cannot_claim_unsat
    (chunkKey : Prop) (checkpointKey : Prop)
    (guardKey : Prop) (fallbackNoClaim : Prop)
    (originalUnsat : Prop) :
    AyUSCCStaleCacheEntry
      chunkKey checkpointKey guardKey fallbackNoClaim ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro stale
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_uscc_stale_cache_no_claim
      chunkKey checkpointKey guardKey fallbackNoClaim stale)
    unsat
