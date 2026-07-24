-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact round-trip algebra for minimal UNSAT replay certificates. The
-- certificate transports formulas through preprocessing, replays an empty
-- clause on the preprocessed side, and transports UNSAT back to the original.

def AyURRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURRMap (source : Prop) (target : Prop) :=
  source -> target

def AyURREquisat (before : Prop) (after : Prop) :=
  AyURRConj (before -> after) (after -> before)

def AyURRProjection
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURRConj
    (AyURREquisat original preprocessed)
    (AyURRMap preprocessedUnsat originalUnsat)

def AyURRReplay
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) (preprocessedUnsat : Prop) :=
  AyURRConj
    (AyURRMap preprocessed replayTrace)
    (AyURRConj
      (AyURRMap replayTrace emptyClause)
      (AyURRMap emptyClause preprocessedUnsat))

def AyURRRoundtrip
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURRConj
    (AyURRProjection original preprocessed preprocessedUnsat originalUnsat)
    (AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat)

theorem ay_urr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urr_conj_left
    (p : Prop) (q : Prop) :
    AyURRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyURREquisat before after := by
  intro forward
  intro backward
  exact ay_urr_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_urr_equisat_forward
    (before : Prop) (after : Prop) :
    AyURREquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_urr_equisat_backward
    (before : Prop) (after : Prop) :
    AyURREquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_urr_projection_equisat
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRProjection original preprocessed preprocessedUnsat originalUnsat ->
    AyURREquisat original preprocessed := by
  intro projection
  exact ay_urr_conj_left
    (AyURREquisat original preprocessed)
    (AyURRMap preprocessedUnsat originalUnsat)
    projection

theorem ay_urr_projection_unsat_transport
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRProjection original preprocessed preprocessedUnsat originalUnsat ->
    preprocessedUnsat ->
    originalUnsat := by
  intro projection
  exact projection (preprocessedUnsat -> originalUnsat)
    (fun _equisat transport => transport)

theorem ay_urr_projection_roundtrip_to_preprocessed
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRProjection original preprocessed preprocessedUnsat originalUnsat ->
    original ->
    preprocessed := by
  intro projection
  exact ay_urr_equisat_forward original preprocessed
    (ay_urr_projection_equisat
      original preprocessed preprocessedUnsat originalUnsat projection)

theorem ay_urr_projection_roundtrip_to_original
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRProjection original preprocessed preprocessedUnsat originalUnsat ->
    preprocessed ->
    original := by
  intro projection
  exact ay_urr_equisat_backward original preprocessed
    (ay_urr_projection_equisat
      original preprocessed preprocessedUnsat originalUnsat projection)

theorem ay_urr_replay_trace
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) (preprocessedUnsat : Prop) :
    AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat ->
    preprocessed ->
    replayTrace := by
  intro replay
  exact replay (preprocessed -> replayTrace)
    (fun pre_to_trace _tail => pre_to_trace)

theorem ay_urr_replay_empty
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) (preprocessedUnsat : Prop) :
    AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat ->
    replayTrace ->
    emptyClause := by
  intro replay
  exact replay (replayTrace -> emptyClause)
    (fun _pre_to_trace tail =>
      tail (replayTrace -> emptyClause)
        (fun trace_to_empty _empty_to_unsat => trace_to_empty))

theorem ay_urr_replay_unsat
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) (preprocessedUnsat : Prop) :
    AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat ->
    emptyClause ->
    preprocessedUnsat := by
  intro replay
  exact replay (emptyClause -> preprocessedUnsat)
    (fun _pre_to_trace tail =>
      tail (emptyClause -> preprocessedUnsat)
        (fun _trace_to_empty empty_to_unsat => empty_to_unsat))

theorem ay_urr_replay_unsat_from_preprocessed
    (preprocessed : Prop) (replayTrace : Prop)
    (emptyClause : Prop) (preprocessedUnsat : Prop) :
    AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat ->
    preprocessed ->
    preprocessedUnsat := by
  intro replay
  intro hpreprocessed
  exact ay_urr_replay_unsat preprocessed replayTrace emptyClause preprocessedUnsat
    replay
    (ay_urr_replay_empty preprocessed replayTrace emptyClause preprocessedUnsat
      replay
      (ay_urr_replay_trace preprocessed replayTrace emptyClause
        preprocessedUnsat replay hpreprocessed))

theorem ay_urr_roundtrip_projection
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURRProjection original preprocessed preprocessedUnsat originalUnsat := by
  intro cert
  exact ay_urr_conj_left
    (AyURRProjection original preprocessed preprocessedUnsat originalUnsat)
    (AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat)
    cert

theorem ay_urr_roundtrip_replay
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat := by
  intro cert
  exact cert (AyURRReplay preprocessed replayTrace emptyClause preprocessedUnsat)
    (fun _projection replay => replay)

theorem ay_urr_roundtrip_preprocessed_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    preprocessedUnsat := by
  intro cert
  intro horiginal
  exact ay_urr_replay_unsat_from_preprocessed
    preprocessed replayTrace emptyClause preprocessedUnsat
    (ay_urr_roundtrip_replay
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urr_projection_roundtrip_to_preprocessed
      original preprocessed preprocessedUnsat originalUnsat
      (ay_urr_roundtrip_projection
        original preprocessed replayTrace emptyClause
        preprocessedUnsat originalUnsat cert)
      horiginal)

theorem ay_urr_roundtrip_original_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro cert
  intro horiginal
  exact ay_urr_projection_unsat_transport
    original preprocessed preprocessedUnsat originalUnsat
    (ay_urr_roundtrip_projection
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urr_roundtrip_preprocessed_unsat
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert horiginal)

theorem ay_urr_roundtrip_empty_to_original_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURRRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    emptyClause ->
    originalUnsat := by
  intro cert
  intro hempty
  exact ay_urr_projection_unsat_transport
    original preprocessed preprocessedUnsat originalUnsat
    (ay_urr_roundtrip_projection
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)
    (ay_urr_replay_unsat preprocessed replayTrace emptyClause preprocessedUnsat
      (ay_urr_roundtrip_replay
        original preprocessed replayTrace emptyClause
        preprocessedUnsat originalUnsat cert)
      hempty)
