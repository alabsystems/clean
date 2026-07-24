-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Manifest linkage for UNSAT stream cache/checkpoint artifacts. Propositions
-- stand for run-manifest stream ids, cache keys, checkpoint keys, guard
-- matches, retained cache chunks, missing/evicted fallback states, direct
-- recheck artifacts, and public UNSAT reports.

def AyUSMLConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSMLDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSMLMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSMLEquisat (before : Prop) (after : Prop) :=
  AyUSMLConj (before -> after) (after -> before)

def AyUSMLManifestKeys
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop) :=
  AyUSMLConj manifestStreamId
    (AyUSMLConj artifactStreamId
      (AyUSMLConj chunkCacheKey checkpointKey))

def AyUSMLMatchGuards
    (streamIdMatches : Prop) (guardMatches : Prop) :=
  AyUSMLConj streamIdMatches guardMatches

def AyUSMLRetainedChunk
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :=
  AyUSMLConj visibleChunk
    (AyUSMLConj
      (AyUSMLMap visibleChunk checkpointSnapshot)
      (AyUSMLMap checkpointSnapshot finalAccumulator))

def AyUSMLFinalLookup
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUSMLConj
    (AyUSMLMap finalAccumulator emptyClause)
    (AyUSMLMap emptyClause visibleUnsat)

def AyUSMLPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSMLConj
    (AyUSMLEquisat originalCNF visibleCNF)
    (AyUSMLMap visibleUnsat originalUnsat)

def AyUSMLManifestLinkedReuse
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSMLConj
    (AyUSMLManifestKeys
      manifestStreamId artifactStreamId chunkCacheKey checkpointKey)
    (AyUSMLConj
      (AyUSMLMatchGuards streamIdMatches guardMatches)
      (AyUSMLConj
        (AyUSMLRetainedChunk
          visibleChunk checkpointSnapshot finalAccumulator)
        (AyUSMLConj
          (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
          (AyUSMLPreprocessTransport
            originalCNF visibleCNF visibleUnsat originalUnsat))))

def AyUSMLUnavailableState
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :=
  AyUSMLConj fallbackNoClaim
    (AyUSMLDisj missingEntry evictedEntry)

def AyUSMLDirectRecheck
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSMLConj visibleChunk
    (AyUSMLConj
      (AyUSMLMap visibleChunk checkpointSnapshot)
      (AyUSMLConj
        (AyUSMLMap checkpointSnapshot finalAccumulator)
        (AyUSMLConj
          (AyUSMLMap finalAccumulator emptyClause)
          (AyUSMLConj
            (AyUSMLMap emptyClause visibleUnsat)
            (AyUSMLMap visibleUnsat originalUnsat)))))

def AyUSMLUnavailableRecheckContract
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSMLConj
    (AyUSMLMap unavailable fallbackNoClaim)
    (AyUSMLDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat)

def AyUSMLPublicUnsatReport
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :=
  AyUSMLDisj fallbackNoClaim originalUnsat

theorem ay_usml_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSMLConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usml_conj_left
    (p : Prop) (q : Prop) :
    AyUSMLConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usml_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSMLDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usml_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSMLDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usml_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSMLEquisat before after := by
  intro forward
  intro backward
  exact ay_usml_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_usml_equisat_forward
    (before : Prop) (after : Prop) :
    AyUSMLEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_usml_equisat_backward
    (before : Prop) (after : Prop) :
    AyUSMLEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_usml_manifest_stream_id
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop) :
    AyUSMLManifestKeys
      manifestStreamId artifactStreamId chunkCacheKey checkpointKey ->
    manifestStreamId := by
  intro keys
  exact ay_usml_conj_left manifestStreamId
    (AyUSMLConj artifactStreamId
      (AyUSMLConj chunkCacheKey checkpointKey))
    keys

theorem ay_usml_match_stream_id
    (streamIdMatches : Prop) (guardMatches : Prop) :
    AyUSMLMatchGuards streamIdMatches guardMatches ->
    streamIdMatches := by
  intro matches
  exact ay_usml_conj_left streamIdMatches guardMatches matches

theorem ay_usml_match_guard
    (streamIdMatches : Prop) (guardMatches : Prop) :
    AyUSMLMatchGuards streamIdMatches guardMatches ->
    guardMatches := by
  intro matches
  exact matches guardMatches (fun _stream guard => guard)

theorem ay_usml_retained_visible_chunk
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator ->
    visibleChunk := by
  intro retained
  exact ay_usml_conj_left visibleChunk
    (AyUSMLConj
      (visibleChunk -> checkpointSnapshot)
      (checkpointSnapshot -> finalAccumulator))
    retained

theorem ay_usml_retained_checkpoint
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator ->
    visibleChunk ->
    checkpointSnapshot := by
  intro retained
  exact retained (visibleChunk -> checkpointSnapshot)
    (fun _visible maps =>
      maps (visibleChunk -> checkpointSnapshot)
        (fun visible_to_checkpoint _checkpoint_to_final =>
          visible_to_checkpoint))

theorem ay_usml_retained_final_accumulator
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator ->
    checkpointSnapshot ->
    finalAccumulator := by
  intro retained
  exact retained (checkpointSnapshot -> finalAccumulator)
    (fun _visible maps =>
      maps (checkpointSnapshot -> finalAccumulator)
        (fun _visible_to_checkpoint checkpoint_to_final =>
          checkpoint_to_final))

theorem ay_usml_retained_final_from_chunk
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) :
    AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator ->
    finalAccumulator := by
  intro retained
  exact ay_usml_retained_final_accumulator
    visibleChunk checkpointSnapshot finalAccumulator retained
    (ay_usml_retained_checkpoint
      visibleChunk checkpointSnapshot finalAccumulator retained
      (ay_usml_retained_visible_chunk
        visibleChunk checkpointSnapshot finalAccumulator retained))

theorem ay_usml_final_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro lookup
  exact lookup (finalAccumulator -> emptyClause)
    (fun final_to_empty _empty_to_unsat => final_to_empty)

theorem ay_usml_empty_visible_unsat
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro lookup
  exact lookup (emptyClause -> visibleUnsat)
    (fun _final_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_usml_preprocess_unsat_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_usml_linked_keys
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSMLManifestKeys
      manifestStreamId artifactStreamId chunkCacheKey checkpointKey := by
  intro link
  exact ay_usml_conj_left
    (AyUSMLManifestKeys
      manifestStreamId artifactStreamId chunkCacheKey checkpointKey)
    (AyUSMLConj
      (AyUSMLMatchGuards streamIdMatches guardMatches)
      (AyUSMLConj
        (AyUSMLRetainedChunk
          visibleChunk checkpointSnapshot finalAccumulator)
        (AyUSMLConj
          (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
          (AyUSMLPreprocessTransport
            originalCNF visibleCNF visibleUnsat originalUnsat))))
    link

theorem ay_usml_linked_matches
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSMLMatchGuards streamIdMatches guardMatches := by
  intro link
  exact link (AyUSMLMatchGuards streamIdMatches guardMatches)
    (fun _keys tail =>
      tail (AyUSMLMatchGuards streamIdMatches guardMatches)
        (fun matches _rest => matches))

theorem ay_usml_linked_retained
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator := by
  intro link
  exact link (AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator)
    (fun _keys tail =>
      tail (AyUSMLRetainedChunk visibleChunk checkpointSnapshot finalAccumulator)
        (fun _matches rest =>
          rest
            (AyUSMLRetainedChunk
              visibleChunk checkpointSnapshot finalAccumulator)
            (fun retained _tail => retained)))

theorem ay_usml_linked_final_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat := by
  intro link
  exact link (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
    (fun _keys tail =>
      tail (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
        (fun _matches rest =>
          rest (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
            (fun _retained tail2 =>
              tail2 (AyUSMLFinalLookup finalAccumulator emptyClause visibleUnsat)
                (fun final_lookup _transport => final_lookup))))

theorem ay_usml_linked_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSMLPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro link
  exact link
    (AyUSMLPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _keys tail =>
      tail
        (AyUSMLPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _matches rest =>
          rest
            (AyUSMLPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _retained tail2 =>
              tail2
                (AyUSMLPreprocessTransport
                  originalCNF visibleCNF visibleUnsat originalUnsat)
                (fun _final_lookup transport => transport))))

theorem ay_usml_linked_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    visibleUnsat := by
  intro link
  exact ay_usml_empty_visible_unsat finalAccumulator emptyClause visibleUnsat
    (ay_usml_linked_final_lookup
      originalCNF visibleCNF manifestStreamId artifactStreamId chunkCacheKey
      checkpointKey streamIdMatches guardMatches visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat link)
    (ay_usml_final_empty finalAccumulator emptyClause visibleUnsat
      (ay_usml_linked_final_lookup
        originalCNF visibleCNF manifestStreamId artifactStreamId chunkCacheKey
        checkpointKey streamIdMatches guardMatches visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat link)
      (ay_usml_retained_final_from_chunk
        visibleChunk checkpointSnapshot finalAccumulator
        (ay_usml_linked_retained
          originalCNF visibleCNF manifestStreamId artifactStreamId
          chunkCacheKey checkpointKey streamIdMatches guardMatches
          visibleChunk checkpointSnapshot finalAccumulator emptyClause
          visibleUnsat originalUnsat link)))

theorem ay_usml_manifest_linked_reuse_sound
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    streamIdMatches ->
    guardMatches ->
    originalUnsat := by
  intro link
  intro _stream_match
  intro _guard_match
  exact ay_usml_preprocess_unsat_transport
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_usml_linked_preprocess
      originalCNF visibleCNF manifestStreamId artifactStreamId chunkCacheKey
      checkpointKey streamIdMatches guardMatches visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat link)
    (ay_usml_linked_visible_unsat
      originalCNF visibleCNF manifestStreamId artifactStreamId chunkCacheKey
      checkpointKey streamIdMatches guardMatches visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat link)

theorem ay_usml_report_unsat
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUSMLPublicUnsatReport fallbackNoClaim originalUnsat := by
  intro unsat
  exact ay_usml_disj_right fallbackNoClaim originalUnsat unsat

theorem ay_usml_unavailable_no_claim
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :
    AyUSMLUnavailableState missingEntry evictedEntry fallbackNoClaim ->
    fallbackNoClaim := by
  intro unavailable
  exact ay_usml_conj_left fallbackNoClaim
    (AyUSMLDisj missingEntry evictedEntry)
    unavailable

theorem ay_usml_missing_or_evicted_requires_no_claim
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSMLUnavailableState missingEntry evictedEntry fallbackNoClaim ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro unavailable
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_usml_unavailable_no_claim
      missingEntry evictedEntry fallbackNoClaim unavailable)
    unsat

theorem ay_usml_direct_recheck_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro direct
  exact direct originalUnsat
    (fun hvisible tail =>
      tail originalUnsat
        (fun visible_to_checkpoint tail2 =>
          tail2 originalUnsat
            (fun checkpoint_to_final tail3 =>
              tail3 originalUnsat
                (fun final_to_empty tail4 =>
                  tail4 originalUnsat
                    (fun empty_to_unsat unsat_to_original =>
                      unsat_to_original
                        (empty_to_unsat
                          (final_to_empty
                            (checkpoint_to_final
                              (visible_to_checkpoint hvisible)))))))))))

theorem ay_usml_unavailable_recheck_no_claim
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLUnavailableRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    unavailable ->
    fallbackNoClaim := by
  intro contract
  exact contract (unavailable -> fallbackNoClaim)
    (fun unavailable_to_no_claim _direct => unavailable_to_no_claim)

theorem ay_usml_unavailable_recheck_direct
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLUnavailableRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSMLDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSMLDirectRecheck visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat)
    (fun _unavailable_to_no_claim direct => direct)

theorem ay_usml_missing_evicted_recheck_report
    (unavailable : Prop) (fallbackNoClaim : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSMLUnavailableRecheckContract unavailable fallbackNoClaim visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSMLPublicUnsatReport fallbackNoClaim originalUnsat := by
  intro contract
  exact ay_usml_report_unsat fallbackNoClaim originalUnsat
    (ay_usml_direct_recheck_unsat
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat
      (ay_usml_unavailable_recheck_direct unavailable fallbackNoClaim
        visibleChunk checkpointSnapshot finalAccumulator emptyClause
        visibleUnsat originalUnsat contract))

theorem ay_usml_manifest_link_public_report
    (originalCNF : Prop) (visibleCNF : Prop)
    (manifestStreamId : Prop) (artifactStreamId : Prop)
    (chunkCacheKey : Prop) (checkpointKey : Prop)
    (streamIdMatches : Prop) (guardMatches : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (fallbackNoClaim : Prop) :
    AyUSMLManifestLinkedReuse originalCNF visibleCNF manifestStreamId
      artifactStreamId chunkCacheKey checkpointKey streamIdMatches
      guardMatches visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    streamIdMatches ->
    guardMatches ->
    AyUSMLPublicUnsatReport fallbackNoClaim originalUnsat := by
  intro link
  intro stream_match
  intro guard_match
  exact ay_usml_report_unsat fallbackNoClaim originalUnsat
    (ay_usml_manifest_linked_reuse_sound
      originalCNF visibleCNF manifestStreamId artifactStreamId chunkCacheKey
      checkpointKey streamIdMatches guardMatches visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat link stream_match guard_match)
