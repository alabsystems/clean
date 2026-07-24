-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Streaming UNSAT proof-checker contract for ay. Propositions stand for the
-- archive/manifest entry, compressed chunks, visible replay chunks,
-- accumulator states, final empty-clause witness, and UNSAT claims. The main
-- theorem shows that chunkwise accepted replay streams discharge the same
-- original-formula UNSAT obligation as a monolithic replay certificate.

def AyUPSCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPSCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPSCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPSCEquisat (before : Prop) (after : Prop) :=
  AyUPSCConj (before -> after) (after -> before)

def AyUPSCManifestLookup
    (archive : Prop) (manifestEntry : Prop) (compressedChunks : Prop) :=
  AyUPSCConj archive
    (AyUPSCConj manifestEntry
      (AyUPSCMap archive compressedChunks))

def AyUPSCChunkProjection
    (compressedChunks : Prop) (visibleChunks : Prop) :=
  AyUPSCMap compressedChunks visibleChunks

def AyUPSCChunkVerification
    (visibleChunks : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) :=
  AyUPSCConj
    (AyUPSCMap visibleChunks initialAccumulator)
    (AyUPSCMap initialAccumulator finalAccumulator)

def AyUPSCFinalEmptyWitness
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUPSCConj
    (AyUPSCMap finalAccumulator emptyClause)
    (AyUPSCMap emptyClause visibleUnsat)

def AyUPSCPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPSCConj
    (AyUPSCEquisat originalCNF visibleCNF)
    (AyUPSCMap visibleUnsat originalUnsat)

def AyUPSCStreamingContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPSCConj
    (AyUPSCManifestLookup archive manifestEntry compressedChunks)
    (AyUPSCConj
      (AyUPSCChunkProjection compressedChunks visibleChunks)
      (AyUPSCConj
        (AyUPSCChunkVerification
          visibleChunks initialAccumulator finalAccumulator)
        (AyUPSCConj
          (AyUPSCFinalEmptyWitness
            finalAccumulator emptyClause visibleUnsat)
          (AyUPSCPreprocessTransport
            originalCNF visibleCNF visibleUnsat originalUnsat))))

def AyUPSCMonolithicReplay
    (visibleReplay : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPSCConj
    (AyUPSCMap visibleReplay emptyClause)
    (AyUPSCConj
      (AyUPSCMap emptyClause visibleUnsat)
      (AyUPSCMap visibleUnsat originalUnsat))

theorem ay_upsc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPSCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upsc_conj_left
    (p : Prop) (q : Prop) :
    AyUPSCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upsc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPSCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upsc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPSCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upsc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUPSCEquisat before after := by
  intro forward
  intro backward
  exact ay_upsc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_upsc_equisat_forward
    (before : Prop) (after : Prop) :
    AyUPSCEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_upsc_equisat_backward
    (before : Prop) (after : Prop) :
    AyUPSCEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_upsc_manifest_chunks
    (archive : Prop) (manifestEntry : Prop) (compressedChunks : Prop) :
    AyUPSCManifestLookup archive manifestEntry compressedChunks ->
    compressedChunks := by
  intro lookup
  exact lookup compressedChunks
    (fun harchive tail =>
      tail compressedChunks
        (fun _entry archive_to_chunks => archive_to_chunks harchive))

theorem ay_upsc_project_visible_chunks
    (compressedChunks : Prop) (visibleChunks : Prop) :
    AyUPSCChunkProjection compressedChunks visibleChunks ->
    compressedChunks ->
    visibleChunks := by
  intro projection
  exact projection

theorem ay_upsc_verify_initial_accumulator
    (visibleChunks : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) :
    AyUPSCChunkVerification
      visibleChunks initialAccumulator finalAccumulator ->
    visibleChunks ->
    initialAccumulator := by
  intro verification
  exact verification (visibleChunks -> initialAccumulator)
    (fun chunks_to_initial _initial_to_final => chunks_to_initial)

theorem ay_upsc_verify_final_accumulator
    (visibleChunks : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) :
    AyUPSCChunkVerification
      visibleChunks initialAccumulator finalAccumulator ->
    initialAccumulator ->
    finalAccumulator := by
  intro verification
  exact verification (initialAccumulator -> finalAccumulator)
    (fun _chunks_to_initial initial_to_final => initial_to_final)

theorem ay_upsc_verify_final_from_chunks
    (visibleChunks : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) :
    AyUPSCChunkVerification
      visibleChunks initialAccumulator finalAccumulator ->
    visibleChunks ->
    finalAccumulator := by
  intro verification
  intro hchunks
  exact ay_upsc_verify_final_accumulator
    visibleChunks initialAccumulator finalAccumulator verification
    (ay_upsc_verify_initial_accumulator
      visibleChunks initialAccumulator finalAccumulator verification hchunks)

theorem ay_upsc_empty_from_accumulator
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro witness
  exact witness (finalAccumulator -> emptyClause)
    (fun accumulator_to_empty _empty_to_unsat => accumulator_to_empty)

theorem ay_upsc_visible_unsat_from_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro witness
  exact witness (emptyClause -> visibleUnsat)
    (fun _accumulator_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_upsc_visible_unsat_from_accumulator
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    visibleUnsat := by
  intro witness
  intro hfinal
  exact ay_upsc_visible_unsat_from_empty
    finalAccumulator emptyClause visibleUnsat witness
    (ay_upsc_empty_from_accumulator
      finalAccumulator emptyClause visibleUnsat witness hfinal)

theorem ay_upsc_preprocess_equisat
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    AyUPSCEquisat originalCNF visibleCNF := by
  intro transport
  exact ay_upsc_conj_left
    (AyUPSCEquisat originalCNF visibleCNF)
    (AyUPSCMap visibleUnsat originalUnsat)
    transport

theorem ay_upsc_preprocess_visible_to_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_upsc_stream_manifest
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCManifestLookup archive manifestEntry compressedChunks := by
  intro contract
  exact ay_upsc_conj_left
    (AyUPSCManifestLookup archive manifestEntry compressedChunks)
    (AyUPSCConj
      (AyUPSCChunkProjection compressedChunks visibleChunks)
      (AyUPSCConj
        (AyUPSCChunkVerification
          visibleChunks initialAccumulator finalAccumulator)
        (AyUPSCConj
          (AyUPSCFinalEmptyWitness
            finalAccumulator emptyClause visibleUnsat)
          (AyUPSCPreprocessTransport
            originalCNF visibleCNF visibleUnsat originalUnsat))))
    contract

theorem ay_upsc_stream_projection
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCChunkProjection compressedChunks visibleChunks := by
  intro contract
  exact contract (AyUPSCChunkProjection compressedChunks visibleChunks)
    (fun _lookup tail =>
      tail (AyUPSCChunkProjection compressedChunks visibleChunks)
        (fun projection _rest => projection))

theorem ay_upsc_stream_verification
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCChunkVerification
      visibleChunks initialAccumulator finalAccumulator := by
  intro contract
  exact contract
    (AyUPSCChunkVerification
      visibleChunks initialAccumulator finalAccumulator)
    (fun _lookup tail =>
      tail
        (AyUPSCChunkVerification
          visibleChunks initialAccumulator finalAccumulator)
        (fun _projection rest =>
          rest
            (AyUPSCChunkVerification
              visibleChunks initialAccumulator finalAccumulator)
            (fun verification _tail => verification)))

theorem ay_upsc_stream_empty_witness
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat := by
  intro contract
  exact contract
    (AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat)
    (fun _lookup tail =>
      tail
        (AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat)
        (fun _projection rest =>
          rest
            (AyUPSCFinalEmptyWitness finalAccumulator emptyClause visibleUnsat)
            (fun _verification final_tail =>
              final_tail
                (AyUPSCFinalEmptyWitness
                  finalAccumulator emptyClause visibleUnsat)
                (fun witness _transport => witness))))

theorem ay_upsc_stream_preprocess_transport
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUPSCPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _lookup tail =>
      tail
        (AyUPSCPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _projection rest =>
          rest
            (AyUPSCPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _verification final_tail =>
              final_tail
                (AyUPSCPreprocessTransport
                  originalCNF visibleCNF visibleUnsat originalUnsat)
                (fun _witness transport => transport))))

theorem ay_upsc_stream_visible_chunks
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    visibleChunks := by
  intro contract
  exact ay_upsc_project_visible_chunks compressedChunks visibleChunks
    (ay_upsc_stream_projection
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
    (ay_upsc_manifest_chunks archive manifestEntry compressedChunks
      (ay_upsc_stream_manifest
        originalCNF visibleCNF archive manifestEntry compressedChunks
        visibleChunks initialAccumulator finalAccumulator emptyClause
        visibleUnsat originalUnsat contract))

theorem ay_upsc_stream_final_accumulator
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    finalAccumulator := by
  intro contract
  exact ay_upsc_verify_final_from_chunks
    visibleChunks initialAccumulator finalAccumulator
    (ay_upsc_stream_verification
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
    (ay_upsc_stream_visible_chunks
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)

theorem ay_upsc_stream_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    visibleUnsat := by
  intro contract
  exact ay_upsc_visible_unsat_from_accumulator
    finalAccumulator emptyClause visibleUnsat
    (ay_upsc_stream_empty_witness
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
    (ay_upsc_stream_final_accumulator
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)

theorem ay_upsc_stream_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_upsc_preprocess_visible_to_original_unsat
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_upsc_stream_preprocess_transport
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
    (ay_upsc_stream_visible_unsat
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)

theorem ay_upsc_monolithic_empty_clause
    (visibleReplay : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCMonolithicReplay visibleReplay emptyClause
      visibleUnsat originalUnsat ->
    visibleReplay ->
    emptyClause := by
  intro monolithic
  exact monolithic (visibleReplay -> emptyClause)
    (fun replay_to_empty _tail => replay_to_empty)

theorem ay_upsc_monolithic_visible_unsat
    (visibleReplay : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCMonolithicReplay visibleReplay emptyClause
      visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro monolithic
  exact monolithic (emptyClause -> visibleUnsat)
    (fun _replay_to_empty tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_unsat _visible_to_original => empty_to_unsat))

theorem ay_upsc_monolithic_original_unsat
    (visibleReplay : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCMonolithicReplay visibleReplay emptyClause
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro monolithic
  exact monolithic (visibleUnsat -> originalUnsat)
    (fun _replay_to_empty tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_unsat visible_to_original => visible_to_original))

theorem ay_upsc_stream_to_monolithic_replay
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUPSCMonolithicReplay visibleChunks emptyClause
      visibleUnsat originalUnsat := by
  intro contract
  exact ay_upsc_conj_intro
    (visibleChunks -> emptyClause)
    (AyUPSCConj
      (emptyClause -> visibleUnsat)
      (visibleUnsat -> originalUnsat))
    (fun hchunks =>
      ay_upsc_empty_from_accumulator finalAccumulator emptyClause visibleUnsat
        (ay_upsc_stream_empty_witness
          originalCNF visibleCNF archive manifestEntry compressedChunks
          visibleChunks initialAccumulator finalAccumulator emptyClause
          visibleUnsat originalUnsat contract)
        (ay_upsc_verify_final_from_chunks
          visibleChunks initialAccumulator finalAccumulator
          (ay_upsc_stream_verification
            originalCNF visibleCNF archive manifestEntry compressedChunks
            visibleChunks initialAccumulator finalAccumulator emptyClause
            visibleUnsat originalUnsat contract)
          hchunks))
    (ay_upsc_conj_intro
      (emptyClause -> visibleUnsat)
      (visibleUnsat -> originalUnsat)
      (ay_upsc_visible_unsat_from_empty
        finalAccumulator emptyClause visibleUnsat
        (ay_upsc_stream_empty_witness
          originalCNF visibleCNF archive manifestEntry compressedChunks
          visibleChunks initialAccumulator finalAccumulator emptyClause
          visibleUnsat originalUnsat contract))
      (ay_upsc_preprocess_visible_to_original_unsat
        originalCNF visibleCNF visibleUnsat originalUnsat
        (ay_upsc_stream_preprocess_transport
          originalCNF visibleCNF archive manifestEntry compressedChunks
          visibleChunks initialAccumulator finalAccumulator emptyClause
          visibleUnsat originalUnsat contract)))

theorem ay_upsc_chunkwise_matches_monolithic_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifestEntry : Prop)
    (compressedChunks : Prop) (visibleChunks : Prop)
    (initialAccumulator : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPSCStreamingContract originalCNF visibleCNF archive manifestEntry
      compressedChunks visibleChunks initialAccumulator finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_upsc_monolithic_original_unsat
    visibleChunks emptyClause visibleUnsat originalUnsat
    (ay_upsc_stream_to_monolithic_replay
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
    (ay_upsc_stream_visible_unsat
      originalCNF visibleCNF archive manifestEntry compressedChunks
      visibleChunks initialAccumulator finalAccumulator emptyClause
      visibleUnsat originalUnsat contract)
