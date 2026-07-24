-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT stream chunk cache eviction soundness for ay. Propositions stand for
-- cache entries, eviction policies, retained guard-matched chunks, stale or
-- missing entries, fallback direct checking, and no-claim outcomes. Retained
-- matched entries preserve direct stream soundness; evicted entries require a
-- direct recheck before any UNSAT claim.

def AyUSCEConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSCEDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSCEMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSCEEquisat (before : Prop) (after : Prop) :=
  AyUSCEConj (before -> after) (after -> before)

def AyUSCECacheEntry
    (chunkKey : Prop) (guardKey : Prop) (cachedChunk : Prop) :=
  AyUSCEConj chunkKey
    (AyUSCEConj guardKey cachedChunk)

def AyUSCEEvictionPolicy
    (cacheEntry : Prop) (retainedEntry : Prop)
    (evictedEntry : Prop) :=
  AyUSCEConj
    (AyUSCEMap cacheEntry retainedEntry)
    (AyUSCEMap cacheEntry evictedEntry)

def AyUSCERetainedMatchedChunk
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :=
  AyUSCEConj visibleChunk
    (AyUSCEConj currentGuard
      (AyUSCEConj
        (AyUSCEMap retainedEntry visibleChunk)
        (AyUSCEConj
          (AyUSCEMap visibleChunk checkpointSnapshot)
          (AyUSCEMap checkpointSnapshot finalAccumulator))))

def AyUSCEUnavailableChunk
    (staleEntry : Prop) (missingEntry : Prop) (fallbackNoClaim : Prop) :=
  AyUSCEConj fallbackNoClaim
    (AyUSCEDisj staleEntry missingEntry)

def AyUSCEFinalAccumulatorLookup
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUSCEConj
    (AyUSCEMap finalAccumulator emptyClause)
    (AyUSCEMap emptyClause visibleUnsat)

def AyUSCEPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCEConj
    (AyUSCEEquisat originalCNF visibleCNF)
    (AyUSCEMap visibleUnsat originalUnsat)

def AyUSCEDirectRecheck
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCEConj
    (AyUSCEMap visibleChunk checkpointSnapshot)
    (AyUSCEConj
      (AyUSCEMap checkpointSnapshot finalAccumulator)
      (AyUSCEConj
        (AyUSCEMap finalAccumulator emptyClause)
        (AyUSCEConj
          (AyUSCEMap emptyClause visibleUnsat)
          (AyUSCEMap visibleUnsat originalUnsat))))

def AyUSCERetainedSoundContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCEConj
    (AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator)
    (AyUSCEConj
      (AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
      (AyUSCEPreprocessTransport
        originalCNF visibleCNF visibleUnsat originalUnsat))

def AyUSCEEvictedRecheckContract
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCEConj
    (AyUSCEMap unavailable fallbackNoClaim)
    (AyUSCEDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat)

theorem ay_usce_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSCEConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usce_conj_left
    (p : Prop) (q : Prop) :
    AyUSCEConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usce_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSCEDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usce_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSCEDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usce_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSCEEquisat before after := by
  intro forward
  intro backward
  exact ay_usce_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_usce_equisat_forward
    (before : Prop) (after : Prop) :
    AyUSCEEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_usce_equisat_backward
    (before : Prop) (after : Prop) :
    AyUSCEEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_usce_cache_entry_chunk_key
    (chunkKey : Prop) (guardKey : Prop) (cachedChunk : Prop) :
    AyUSCECacheEntry chunkKey guardKey cachedChunk ->
    chunkKey := by
  intro entry
  exact ay_usce_conj_left chunkKey
    (AyUSCEConj guardKey cachedChunk)
    entry

theorem ay_usce_policy_retains
    (cacheEntry : Prop) (retainedEntry : Prop)
    (evictedEntry : Prop) :
    AyUSCEEvictionPolicy cacheEntry retainedEntry evictedEntry ->
    cacheEntry ->
    retainedEntry := by
  intro policy
  exact policy (cacheEntry -> retainedEntry)
    (fun keep _evict => keep)

theorem ay_usce_policy_evicts
    (cacheEntry : Prop) (retainedEntry : Prop)
    (evictedEntry : Prop) :
    AyUSCEEvictionPolicy cacheEntry retainedEntry evictedEntry ->
    cacheEntry ->
    evictedEntry := by
  intro policy
  exact policy (cacheEntry -> evictedEntry)
    (fun _keep evict => evict)

theorem ay_usce_retained_visible_chunk
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator ->
    visibleChunk := by
  intro retained
  exact ay_usce_conj_left visibleChunk
    (AyUSCEConj currentGuard
      (AyUSCEConj
        (AyUSCEMap retainedEntry visibleChunk)
        (AyUSCEConj
          (AyUSCEMap visibleChunk checkpointSnapshot)
          (AyUSCEMap checkpointSnapshot finalAccumulator))))
    retained

theorem ay_usce_retained_to_checkpoint
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator ->
    visibleChunk ->
    checkpointSnapshot := by
  intro retained
  exact retained (visibleChunk -> checkpointSnapshot)
    (fun _visible tail =>
      tail (visibleChunk -> checkpointSnapshot)
        (fun _guard maps =>
          maps (visibleChunk -> checkpointSnapshot)
            (fun _entry_to_visible resume_maps =>
              resume_maps (visibleChunk -> checkpointSnapshot)
                (fun visible_to_checkpoint _checkpoint_to_final =>
                  visible_to_checkpoint))))

theorem ay_usce_retained_to_final
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator ->
    checkpointSnapshot ->
    finalAccumulator := by
  intro retained
  exact retained (checkpointSnapshot -> finalAccumulator)
    (fun _visible tail =>
      tail (checkpointSnapshot -> finalAccumulator)
        (fun _guard maps =>
          maps (checkpointSnapshot -> finalAccumulator)
            (fun _entry_to_visible resume_maps =>
              resume_maps (checkpointSnapshot -> finalAccumulator)
                (fun _visible_to_checkpoint checkpoint_to_final =>
                  checkpoint_to_final))))

theorem ay_usce_retained_final_from_visible
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator ->
    visibleChunk ->
    finalAccumulator := by
  intro retained
  intro hvisible
  exact ay_usce_retained_to_final
    retainedEntry currentGuard visibleChunk checkpointSnapshot finalAccumulator
    retained
    (ay_usce_retained_to_checkpoint
      retainedEntry currentGuard visibleChunk checkpointSnapshot finalAccumulator
      retained hvisible)

theorem ay_usce_final_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro lookup
  exact lookup (finalAccumulator -> emptyClause)
    (fun final_to_empty _empty_to_unsat => final_to_empty)

theorem ay_usce_empty_visible_unsat
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro lookup
  exact lookup (emptyClause -> visibleUnsat)
    (fun _final_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_usce_preprocess_unsat_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCEPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_usce_retained_contract_chunk
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCERetainedSoundContract originalCNF visibleCNF retainedEntry
      currentGuard visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator := by
  intro contract
  exact ay_usce_conj_left
    (AyUSCERetainedMatchedChunk retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator)
    (AyUSCEConj
      (AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
      (AyUSCEPreprocessTransport
        originalCNF visibleCNF visibleUnsat originalUnsat))
    contract

theorem ay_usce_retained_contract_final_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCERetainedSoundContract originalCNF visibleCNF retainedEntry
      currentGuard visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat := by
  intro contract
  exact contract
    (AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
    (fun _retained tail =>
      tail
        (AyUSCEFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
        (fun final_lookup _transport => final_lookup))

theorem ay_usce_retained_contract_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCERetainedSoundContract originalCNF visibleCNF retainedEntry
      currentGuard visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSCEPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSCEPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _retained tail =>
      tail
        (AyUSCEPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _final_lookup transport => transport))

theorem ay_usce_retained_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCERetainedSoundContract originalCNF visibleCNF retainedEntry
      currentGuard visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    visibleUnsat := by
  intro contract
  exact ay_usce_empty_visible_unsat finalAccumulator emptyClause visibleUnsat
    (ay_usce_retained_contract_final_lookup
      originalCNF visibleCNF retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)
    (ay_usce_final_empty finalAccumulator emptyClause visibleUnsat
      (ay_usce_retained_contract_final_lookup
        originalCNF visibleCNF retainedEntry currentGuard visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat contract)
      (ay_usce_retained_final_from_visible
        retainedEntry currentGuard visibleChunk checkpointSnapshot
        finalAccumulator
        (ay_usce_retained_contract_chunk
          originalCNF visibleCNF retainedEntry currentGuard visibleChunk
          checkpointSnapshot finalAccumulator emptyClause visibleUnsat
          originalUnsat contract)
        (ay_usce_retained_visible_chunk
          retainedEntry currentGuard visibleChunk checkpointSnapshot
          finalAccumulator
          (ay_usce_retained_contract_chunk
            originalCNF visibleCNF retainedEntry currentGuard visibleChunk
            checkpointSnapshot finalAccumulator emptyClause visibleUnsat
            originalUnsat contract))))

theorem ay_usce_retained_matched_preserves_direct_soundness
    (originalCNF : Prop) (visibleCNF : Prop)
    (retainedEntry : Prop) (currentGuard : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCERetainedSoundContract originalCNF visibleCNF retainedEntry
      currentGuard visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_usce_preprocess_unsat_transport
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_usce_retained_contract_preprocess
      originalCNF visibleCNF retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)
    (ay_usce_retained_visible_unsat
      originalCNF visibleCNF retainedEntry currentGuard visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)

theorem ay_usce_unavailable_no_claim
    (staleEntry : Prop) (missingEntry : Prop) (fallbackNoClaim : Prop) :
    AyUSCEUnavailableChunk staleEntry missingEntry fallbackNoClaim ->
    fallbackNoClaim := by
  intro unavailable
  exact ay_usce_conj_left fallbackNoClaim
    (AyUSCEDisj staleEntry missingEntry)
    unavailable

theorem ay_usce_eviction_cannot_create_unsat_claim
    (staleEntry : Prop) (missingEntry : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSCEUnavailableChunk staleEntry missingEntry fallbackNoClaim ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro unavailable
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_usce_unavailable_no_claim staleEntry missingEntry fallbackNoClaim
      unavailable)
    unsat

theorem ay_usce_direct_recheck_original_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCEDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
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

theorem ay_usce_evicted_recheck_no_claim
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCEEvictedRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    unavailable ->
    fallbackNoClaim := by
  intro contract
  exact contract (unavailable -> fallbackNoClaim)
    (fun unavailable_to_no_claim _direct => unavailable_to_no_claim)

theorem ay_usce_evicted_recheck_direct
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCEEvictedRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCEDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSCEDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat)
    (fun _unavailable_to_no_claim direct => direct)

theorem ay_usce_evicted_requires_direct_recheck
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCEEvictedRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    visibleChunk ->
    originalUnsat := by
  intro contract
  intro hvisible
  exact ay_usce_direct_recheck_original_unsat
    visibleChunk checkpointSnapshot finalAccumulator emptyClause visibleUnsat
    originalUnsat
    (ay_usce_evicted_recheck_direct unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)
    hvisible
