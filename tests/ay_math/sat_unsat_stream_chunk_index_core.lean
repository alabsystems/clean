-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Indexed chunk lookup for streaming UNSAT proof checking. Propositions stand
-- for chunk IDs, prefix/suffix indexes, checkpoint keys, compressed chunks,
-- visible chunks, accumulator snapshots, final accumulator lookup, and UNSAT
-- claims. The package proves indexed lookup preserves the same checkpoint /
-- resume original-UNSAT obligation as direct stream checking.

def AyUSCIConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSCIDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSCIMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSCIEquisat (before : Prop) (after : Prop) :=
  AyUSCIConj (before -> after) (after -> before)

def AyUSCIChunkIndex
    (chunkId : Prop) (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop) :=
  AyUSCIConj chunkId
    (AyUSCIConj prefixIndex
      (AyUSCIConj suffixIndex
        (AyUSCIConj checkpointKey finalAccumulatorKey)))

def AyUSCIIndexedLookup
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop) :=
  AyUSCIConj archive
    (AyUSCIConj prefixIndex
      (AyUSCIConj
        (AyUSCIChunkIndex
          chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey)
        (AyUSCIConj
          (AyUSCIMap prefixIndex compressedPrefix)
          (AyUSCIConj
            (AyUSCIMap suffixIndex compressedSuffix)
            (AyUSCIConj
              (AyUSCIMap checkpointKey checkpointSnapshot)
              (AyUSCIMap finalAccumulatorKey finalAccumulator))))))

def AyUSCIChunkProjection
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :=
  AyUSCIConj
    (AyUSCIMap compressedPrefix visiblePrefix)
    (AyUSCIMap compressedSuffix visibleSuffix)

def AyUSCIResumeCheck
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop) :=
  AyUSCIConj
    (AyUSCIMap visiblePrefix checkpointSnapshot)
    (AyUSCIConj
      (AyUSCIMap checkpointSnapshot visibleSuffix)
      (AyUSCIMap visibleSuffix finalAccumulator))

def AyUSCIFinalAccumulatorLookup
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUSCIConj
    (AyUSCIMap finalAccumulator emptyClause)
    (AyUSCIMap emptyClause visibleUnsat)

def AyUSCIPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCIConj
    (AyUSCIEquisat originalCNF visibleCNF)
    (AyUSCIMap visibleUnsat originalUnsat)

def AyUSCIIndexedStreamContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCIConj visiblePrefix
    (AyUSCIConj
      (AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        checkpointSnapshot finalAccumulator)
      (AyUSCIConj
        (AyUSCIChunkProjection
          compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
        (AyUSCIConj
          (AyUSCIResumeCheck
            visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator)
          (AyUSCIConj
            (AyUSCIFinalAccumulatorLookup
              finalAccumulator emptyClause visibleUnsat)
            (AyUSCIPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)))))

def AyUSCIDirectStreamContract
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCIConj
    (AyUSCIMap visiblePrefix checkpointSnapshot)
    (AyUSCIConj
      (AyUSCIMap checkpointSnapshot visibleSuffix)
      (AyUSCIConj
        (AyUSCIMap visibleSuffix finalAccumulator)
        (AyUSCIConj
          (AyUSCIMap finalAccumulator emptyClause)
          (AyUSCIConj
            (AyUSCIMap emptyClause visibleUnsat)
            (AyUSCIMap visibleUnsat originalUnsat)))))

theorem ay_usci_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSCIConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usci_conj_left
    (p : Prop) (q : Prop) :
    AyUSCIConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usci_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSCIDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usci_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSCIDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usci_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSCIEquisat before after := by
  intro forward
  intro backward
  exact ay_usci_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_usci_equisat_forward
    (before : Prop) (after : Prop) :
    AyUSCIEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_usci_equisat_backward
    (before : Prop) (after : Prop) :
    AyUSCIEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_usci_chunk_index_id
    (chunkId : Prop) (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop) :
    AyUSCIChunkIndex
      chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey ->
    chunkId := by
  intro index
  exact ay_usci_conj_left chunkId
    (AyUSCIConj prefixIndex
      (AyUSCIConj suffixIndex
        (AyUSCIConj checkpointKey finalAccumulatorKey)))
    index

theorem ay_usci_lookup_chunk_index
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop) :
    AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      checkpointSnapshot finalAccumulator ->
    AyUSCIChunkIndex
      chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey := by
  intro lookup
  exact lookup
    (AyUSCIChunkIndex
      chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey)
    (fun _archive tail =>
      tail
        (AyUSCIChunkIndex
          chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey)
        (fun _prefix rest =>
          rest
            (AyUSCIChunkIndex
              chunkId prefixIndex suffixIndex checkpointKey finalAccumulatorKey)
            (fun index _maps => index)))

theorem ay_usci_lookup_compressed_suffix
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop) :
    AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      checkpointSnapshot finalAccumulator ->
    compressedSuffix := by
  intro lookup
  exact lookup compressedSuffix
    (fun _archive tail =>
      tail compressedSuffix
        (fun _prefix rest =>
          rest compressedSuffix
            (fun index maps =>
              maps compressedSuffix
                (fun _prefix_to_compressed tail_maps =>
                  tail_maps compressedSuffix
                    (fun suffix_to_compressed _tail =>
                      suffix_to_compressed
                        (index suffixIndex
                          (fun _chunk tail_index =>
                            tail_index suffixIndex
                              (fun _prefix2 rest2 =>
                                rest2 suffixIndex
                                  (fun suffix _keys => suffix))))))))))

theorem ay_usci_project_prefix_visible
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :
    AyUSCIChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix ->
    compressedPrefix ->
    visiblePrefix := by
  intro projection
  exact projection (compressedPrefix -> visiblePrefix)
    (fun prefix_map _suffix_map => prefix_map)

theorem ay_usci_project_suffix_visible
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :
    AyUSCIChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix ->
    compressedSuffix ->
    visibleSuffix := by
  intro projection
  exact projection (compressedSuffix -> visibleSuffix)
    (fun _prefix_map suffix_map => suffix_map)

theorem ay_usci_resume_checkpoint
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop) :
    AyUSCIResumeCheck
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator ->
    visiblePrefix ->
    checkpointSnapshot := by
  intro resume
  exact resume (visiblePrefix -> checkpointSnapshot)
    (fun prefix_to_checkpoint _tail => prefix_to_checkpoint)

theorem ay_usci_resume_suffix
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop) :
    AyUSCIResumeCheck
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator ->
    checkpointSnapshot ->
    visibleSuffix := by
  intro resume
  exact resume (checkpointSnapshot -> visibleSuffix)
    (fun _prefix_to_checkpoint tail =>
      tail (checkpointSnapshot -> visibleSuffix)
        (fun checkpoint_to_suffix _suffix_to_final =>
          checkpoint_to_suffix))

theorem ay_usci_resume_final
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop) :
    AyUSCIResumeCheck
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator ->
    visibleSuffix ->
    finalAccumulator := by
  intro resume
  exact resume (visibleSuffix -> finalAccumulator)
    (fun _prefix_to_checkpoint tail =>
      tail (visibleSuffix -> finalAccumulator)
        (fun _checkpoint_to_suffix suffix_to_final => suffix_to_final))

theorem ay_usci_final_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCIFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro final_lookup
  exact final_lookup (finalAccumulator -> emptyClause)
    (fun final_to_empty _empty_to_unsat => final_to_empty)

theorem ay_usci_final_visible_unsat
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCIFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro final_lookup
  exact final_lookup (emptyClause -> visibleUnsat)
    (fun _final_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_usci_preprocess_unsat_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_usci_contract_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      checkpointSnapshot finalAccumulator := by
  intro contract
  exact contract
    (AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      checkpointSnapshot finalAccumulator)
    (fun _visible tail =>
      tail
        (AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
          checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
          checkpointSnapshot finalAccumulator)
        (fun lookup _rest => lookup))

theorem ay_usci_contract_projection
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix := by
  intro contract
  exact contract
    (AyUSCIChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
    (fun _visible tail =>
      tail
        (AyUSCIChunkProjection
          compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
        (fun _lookup rest =>
          rest
            (AyUSCIChunkProjection
              compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
            (fun projection _tail => projection)))

theorem ay_usci_contract_resume
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIResumeCheck
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator := by
  intro contract
  exact contract
    (AyUSCIResumeCheck
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator)
    (fun _visible tail =>
      tail
        (AyUSCIResumeCheck
          visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator)
        (fun _lookup rest =>
          rest
            (AyUSCIResumeCheck
              visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator)
            (fun _projection tail2 =>
              tail2
                (AyUSCIResumeCheck
                  visiblePrefix checkpointSnapshot visibleSuffix
                  finalAccumulator)
                (fun resume _tail => resume))))

theorem ay_usci_contract_final_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat := by
  intro contract
  exact contract
    (AyUSCIFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
    (fun _visible tail =>
      tail (AyUSCIFinalAccumulatorLookup finalAccumulator emptyClause visibleUnsat)
        (fun _lookup rest =>
          rest
            (AyUSCIFinalAccumulatorLookup
              finalAccumulator emptyClause visibleUnsat)
            (fun _projection tail2 =>
              tail2
                (AyUSCIFinalAccumulatorLookup
                  finalAccumulator emptyClause visibleUnsat)
                (fun _resume tail3 =>
                  tail3
                    (AyUSCIFinalAccumulatorLookup
                      finalAccumulator emptyClause visibleUnsat)
                    (fun final_lookup _transport => final_lookup)))))

theorem ay_usci_contract_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSCIPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _visible tail =>
      tail
        (AyUSCIPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _lookup rest =>
          rest
            (AyUSCIPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _projection tail2 =>
              tail2
                (AyUSCIPreprocessTransport
                  originalCNF visibleCNF visibleUnsat originalUnsat)
                (fun _resume tail3 =>
                  tail3
                    (AyUSCIPreprocessTransport
                      originalCNF visibleCNF visibleUnsat originalUnsat)
                    (fun _final_lookup transport => transport)))))

theorem ay_usci_indexed_visible_prefix
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    visiblePrefix := by
  intro contract
  exact ay_usci_conj_left visiblePrefix
    (AyUSCIConj
      (AyUSCIIndexedLookup archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        checkpointSnapshot finalAccumulator)
      (AyUSCIConj
        (AyUSCIChunkProjection
          compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
        (AyUSCIConj
          (AyUSCIResumeCheck
            visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator)
          (AyUSCIConj
            (AyUSCIFinalAccumulatorLookup
              finalAccumulator emptyClause visibleUnsat)
            (AyUSCIPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)))))
    contract

theorem ay_usci_indexed_checkpoint
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    checkpointSnapshot := by
  intro contract
  exact ay_usci_resume_checkpoint
    visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
    (ay_usci_contract_resume
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
    (ay_usci_indexed_visible_prefix
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)

theorem ay_usci_indexed_final_accumulator
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    finalAccumulator := by
  intro contract
  exact ay_usci_resume_final
    visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
    (ay_usci_contract_resume
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
    (ay_usci_resume_suffix
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
      (ay_usci_contract_resume
        originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat contract)
      (ay_usci_indexed_checkpoint
        originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat contract))

theorem ay_usci_indexed_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    visibleUnsat := by
  intro contract
  exact ay_usci_final_visible_unsat finalAccumulator emptyClause visibleUnsat
    (ay_usci_contract_final_lookup
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
    (ay_usci_final_empty finalAccumulator emptyClause visibleUnsat
      (ay_usci_contract_final_lookup
        originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat contract)
      (ay_usci_indexed_final_accumulator
        originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat contract))

theorem ay_usci_indexed_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_usci_preprocess_unsat_transport
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_usci_contract_preprocess
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
    (ay_usci_indexed_visible_unsat
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)

theorem ay_usci_direct_stream_original_unsat
    (visiblePrefix : Prop) (checkpointSnapshot : Prop)
    (visibleSuffix : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIDirectStreamContract visiblePrefix checkpointSnapshot visibleSuffix
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    visiblePrefix ->
    originalUnsat := by
  intro direct
  intro hprefix
  exact direct originalUnsat
    (fun prefix_to_checkpoint tail =>
      tail originalUnsat
        (fun checkpoint_to_suffix tail2 =>
          tail2 originalUnsat
            (fun suffix_to_final tail3 =>
              tail3 originalUnsat
                (fun final_to_empty tail4 =>
                  tail4 originalUnsat
                    (fun empty_to_unsat unsat_to_original =>
                      unsat_to_original
                        (empty_to_unsat
                          (final_to_empty
                            (suffix_to_final
                              (checkpoint_to_suffix
                                (prefix_to_checkpoint hprefix)))))))))))

theorem ay_usci_indexed_to_direct_stream
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSCIDirectStreamContract visiblePrefix checkpointSnapshot visibleSuffix
      finalAccumulator emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact ay_usci_conj_intro
    (visiblePrefix -> checkpointSnapshot)
    (AyUSCIConj
      (checkpointSnapshot -> visibleSuffix)
      (AyUSCIConj
        (visibleSuffix -> finalAccumulator)
        (AyUSCIConj
          (finalAccumulator -> emptyClause)
          (AyUSCIConj
            (emptyClause -> visibleUnsat)
            (visibleUnsat -> originalUnsat)))))
    (ay_usci_resume_checkpoint
      visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
      (ay_usci_contract_resume
        originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
        checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
        visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat contract))
    (ay_usci_conj_intro
      (checkpointSnapshot -> visibleSuffix)
      (AyUSCIConj
        (visibleSuffix -> finalAccumulator)
        (AyUSCIConj
          (finalAccumulator -> emptyClause)
          (AyUSCIConj
            (emptyClause -> visibleUnsat)
            (visibleUnsat -> originalUnsat))))
      (ay_usci_resume_suffix
        visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
        (ay_usci_contract_resume
          originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
          checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
          visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
          emptyClause visibleUnsat originalUnsat contract))
      (ay_usci_conj_intro
        (visibleSuffix -> finalAccumulator)
        (AyUSCIConj
          (finalAccumulator -> emptyClause)
          (AyUSCIConj
            (emptyClause -> visibleUnsat)
            (visibleUnsat -> originalUnsat)))
        (ay_usci_resume_final
          visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
          (ay_usci_contract_resume
            originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
            checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
            visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
            emptyClause visibleUnsat originalUnsat contract))
        (ay_usci_conj_intro
          (finalAccumulator -> emptyClause)
          (AyUSCIConj
            (emptyClause -> visibleUnsat)
            (visibleUnsat -> originalUnsat))
          (ay_usci_final_empty finalAccumulator emptyClause visibleUnsat
            (ay_usci_contract_final_lookup
              originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
              checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
              visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
              emptyClause visibleUnsat originalUnsat contract))
          (ay_usci_conj_intro
            (emptyClause -> visibleUnsat)
            (visibleUnsat -> originalUnsat)
            (ay_usci_final_visible_unsat
              finalAccumulator emptyClause visibleUnsat
              (ay_usci_contract_final_lookup
                originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
                checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
                visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
                emptyClause visibleUnsat originalUnsat contract))
            (ay_usci_preprocess_unsat_transport
              originalCNF visibleCNF visibleUnsat originalUnsat
              (ay_usci_contract_preprocess
                originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
                checkpointKey finalAccumulatorKey compressedPrefix
                compressedSuffix visiblePrefix visibleSuffix checkpointSnapshot
                finalAccumulator emptyClause visibleUnsat originalUnsat
                contract))))))

theorem ay_usci_index_lookup_preserves_direct_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (chunkId : Prop)
    (prefixIndex : Prop) (suffixIndex : Prop)
    (checkpointKey : Prop) (finalAccumulatorKey : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (checkpointSnapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCIIndexedStreamContract originalCNF visibleCNF archive chunkId
      prefixIndex suffixIndex checkpointKey finalAccumulatorKey
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_usci_direct_stream_original_unsat
    visiblePrefix checkpointSnapshot visibleSuffix finalAccumulator
    emptyClause visibleUnsat originalUnsat
    (ay_usci_indexed_to_direct_stream
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
    (ay_usci_indexed_visible_prefix
      originalCNF visibleCNF archive chunkId prefixIndex suffixIndex
      checkpointKey finalAccumulatorKey compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat contract)
