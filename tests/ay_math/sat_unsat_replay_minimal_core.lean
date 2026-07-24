-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal checked abstraction for full-stack UNSAT replay certificates. This
-- keeps only preprocessing projection, streaming replay, empty-clause
-- soundness, and transport to the original UNSAT claim.

def AyURMConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURMDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyURMEquisat (before : Prop) (after : Prop) :=
  AyURMConj (before -> after) (after -> before)

def AyURMMap (source : Prop) (target : Prop) :=
  source -> target

def AyURMPreprocessProjection
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURMConj
    (AyURMEquisat original preprocessed)
    (preprocessedUnsat -> originalUnsat)

def AyURMStreamingReplay
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) :=
  AyURMConj
    (AyURMMap preprocessed replayTrace)
    (AyURMMap replayTrace emptyClause)

def AyURMEmptyClauseSound
    (emptyClause : Prop) (preprocessedUnsat : Prop) :=
  emptyClause -> preprocessedUnsat

def AyURMUnsatReplayMinimal
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURMConj
    (AyURMPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat)
    (AyURMConj
      (AyURMStreamingReplay preprocessed replayTrace emptyClause)
      (AyURMEmptyClauseSound emptyClause preprocessedUnsat))

theorem ay_urm_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURMConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urm_conj_left
    (p : Prop) (q : Prop) :
    AyURMConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urm_disj_left
    (p : Prop) (q : Prop) :
    p -> AyURMDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_urm_disj_right
    (p : Prop) (q : Prop) :
    q -> AyURMDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_urm_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyURMEquisat before after := by
  intro forward
  intro backward
  exact ay_urm_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_urm_equisat_forward
    (before : Prop) (after : Prop) :
    AyURMEquisat before after ->
    before ->
    after := by
  intro certificate
  exact certificate (before -> after)
    (fun forward _backward => forward)

theorem ay_urm_equisat_backward
    (before : Prop) (after : Prop) :
    AyURMEquisat before after ->
    after ->
    before := by
  intro certificate
  exact certificate (after -> before)
    (fun _forward backward => backward)

theorem ay_urm_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyURMEquisat before middle ->
    AyURMEquisat middle after ->
    AyURMEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_urm_preprocess_projection_equisat
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat ->
    AyURMEquisat original preprocessed := by
  intro projection
  exact ay_urm_conj_left
    (AyURMEquisat original preprocessed)
    (preprocessedUnsat -> originalUnsat)
    projection

theorem ay_urm_preprocess_unsat_transport
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat ->
    preprocessedUnsat ->
    originalUnsat := by
  intro projection
  exact projection (preprocessedUnsat -> originalUnsat)
    (fun _equisat transport => transport)

theorem ay_urm_replay_trace_from_preprocessed
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) :
    AyURMStreamingReplay preprocessed replayTrace emptyClause ->
    preprocessed ->
    replayTrace := by
  intro replay
  exact replay (preprocessed -> replayTrace)
    (fun pre_to_trace _trace_to_empty => pre_to_trace)

theorem ay_urm_empty_clause_from_trace
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) :
    AyURMStreamingReplay preprocessed replayTrace emptyClause ->
    replayTrace ->
    emptyClause := by
  intro replay
  exact replay (replayTrace -> emptyClause)
    (fun _pre_to_trace trace_to_empty => trace_to_empty)

theorem ay_urm_empty_clause_from_preprocessed
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) :
    AyURMStreamingReplay preprocessed replayTrace emptyClause ->
    preprocessed ->
    emptyClause := by
  intro replay
  intro hpreprocessed
  exact ay_urm_empty_clause_from_trace preprocessed replayTrace emptyClause
    replay
    (ay_urm_replay_trace_from_preprocessed
      preprocessed replayTrace emptyClause replay hpreprocessed)

theorem ay_urm_preprocessed_unsat_from_empty
    (emptyClause : Prop) (preprocessedUnsat : Prop) :
    AyURMEmptyClauseSound emptyClause preprocessedUnsat ->
    emptyClause ->
    preprocessedUnsat := by
  intro sound
  exact sound

theorem ay_urm_minimal_projection
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURMPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat := by
  intro cert
  exact ay_urm_conj_left
    (AyURMPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat)
    (AyURMConj
      (AyURMStreamingReplay preprocessed replayTrace emptyClause)
      (AyURMEmptyClauseSound emptyClause preprocessedUnsat))
    cert

theorem ay_urm_minimal_streaming
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURMStreamingReplay preprocessed replayTrace emptyClause := by
  intro cert
  exact cert (AyURMStreamingReplay preprocessed replayTrace emptyClause)
    (fun _projection tail =>
      tail (AyURMStreamingReplay preprocessed replayTrace emptyClause)
        (fun streaming _empty_sound => streaming))

theorem ay_urm_minimal_empty_sound
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURMEmptyClauseSound emptyClause preprocessedUnsat := by
  intro cert
  exact cert (AyURMEmptyClauseSound emptyClause preprocessedUnsat)
    (fun _projection tail =>
      tail (AyURMEmptyClauseSound emptyClause preprocessedUnsat)
        (fun _streaming empty_sound => empty_sound))

theorem ay_urm_minimal_empty_from_original
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    emptyClause := by
  intro cert
  intro horiginal
  exact ay_urm_empty_clause_from_preprocessed preprocessed replayTrace emptyClause
    (ay_urm_minimal_streaming
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urm_equisat_forward original preprocessed
      (ay_urm_preprocess_projection_equisat original preprocessed
        preprocessedUnsat originalUnsat
        (ay_urm_minimal_projection
          original preprocessed replayTrace emptyClause
          preprocessedUnsat originalUnsat cert))
      horiginal)

theorem ay_urm_minimal_preprocessed_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    preprocessedUnsat := by
  intro cert
  intro horiginal
  exact ay_urm_preprocessed_unsat_from_empty emptyClause preprocessedUnsat
    (ay_urm_minimal_empty_sound
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urm_minimal_empty_from_original
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert horiginal)

theorem ay_urm_empty_clause_sound_for_original
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    emptyClause ->
    originalUnsat := by
  intro cert
  intro hempty
  exact ay_urm_preprocess_unsat_transport original preprocessed
    preprocessedUnsat originalUnsat
    (ay_urm_minimal_projection
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urm_preprocessed_unsat_from_empty emptyClause preprocessedUnsat
      (ay_urm_minimal_empty_sound
        original preprocessed replayTrace emptyClause
        preprocessedUnsat originalUnsat cert)
      hempty)

theorem ay_urm_minimal_unsat_replay_sound
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURMUnsatReplayMinimal original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro cert
  intro horiginal
  exact ay_urm_preprocess_unsat_transport original preprocessed
    preprocessedUnsat originalUnsat
    (ay_urm_minimal_projection
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urm_minimal_preprocessed_unsat
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert horiginal)
