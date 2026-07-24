-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact algebra combining UNSAT replay round-trips with compressed outcome
-- certificates. The compressed certificate keeps only preprocessing
-- projection, replay-to-empty, empty-clause soundness, and original UNSAT
-- transport.

def AyURCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyURCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyURCMap (source : Prop) (target : Prop) :=
  source -> target

def AyURCEquisat (before : Prop) (after : Prop) :=
  AyURCConj (before -> after) (after -> before)

def AyURCReplayRoundtrip
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURCConj
    (AyURCEquisat original preprocessed)
    (AyURCConj
      (AyURCMap preprocessed replayTrace)
      (AyURCConj
        (AyURCMap replayTrace emptyClause)
        (AyURCConj
          (AyURCMap emptyClause preprocessedUnsat)
          (AyURCMap preprocessedUnsat originalUnsat))))

def AyURCFullUnsatOutcome
    (metadata : Prop) (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURCConj metadata
    (AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat)

def AyURCCompressedUnsatOutcome
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat

def AyURCCompressedOutcome
    (satWitness : Prop) (unsatWitness : Prop) :=
  AyURCDisj satWitness unsatWitness

theorem ay_urc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyURCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_urc_conj_left
    (p : Prop) (q : Prop) :
    AyURCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_urc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyURCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_urc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyURCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_urc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyURCEquisat before after := by
  intro forward
  intro backward
  exact ay_urc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_urc_equisat_forward
    (before : Prop) (after : Prop) :
    AyURCEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_urc_equisat_backward
    (before : Prop) (after : Prop) :
    AyURCEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_urc_roundtrip_equisat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURCEquisat original preprocessed := by
  intro cert
  exact ay_urc_conj_left
    (AyURCEquisat original preprocessed)
    (AyURCConj
      (AyURCMap preprocessed replayTrace)
      (AyURCConj
        (AyURCMap replayTrace emptyClause)
        (AyURCConj
          (AyURCMap emptyClause preprocessedUnsat)
          (AyURCMap preprocessedUnsat originalUnsat))))
    cert

theorem ay_urc_roundtrip_replay_map
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURCMap preprocessed replayTrace := by
  intro cert
  exact cert (preprocessed -> replayTrace)
    (fun _equisat tail =>
      tail (preprocessed -> replayTrace)
        (fun pre_to_trace _tail => pre_to_trace))

theorem ay_urc_roundtrip_empty_map
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURCMap replayTrace emptyClause := by
  intro cert
  exact cert (replayTrace -> emptyClause)
    (fun _equisat tail =>
      tail (replayTrace -> emptyClause)
        (fun _pre_to_trace replay_tail =>
          replay_tail (replayTrace -> emptyClause)
            (fun trace_to_empty _unsat_tail => trace_to_empty)))

theorem ay_urc_roundtrip_preprocessed_unsat_map
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURCMap emptyClause preprocessedUnsat := by
  intro cert
  exact cert (emptyClause -> preprocessedUnsat)
    (fun _equisat tail =>
      tail (emptyClause -> preprocessedUnsat)
        (fun _pre_to_trace replay_tail =>
          replay_tail (emptyClause -> preprocessedUnsat)
            (fun _trace_to_empty unsat_tail =>
              unsat_tail (emptyClause -> preprocessedUnsat)
                (fun empty_to_unsat _original_transport => empty_to_unsat))))

theorem ay_urc_roundtrip_original_unsat_map
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    AyURCMap preprocessedUnsat originalUnsat := by
  intro cert
  exact cert (preprocessedUnsat -> originalUnsat)
    (fun _equisat tail =>
      tail (preprocessedUnsat -> originalUnsat)
        (fun _pre_to_trace replay_tail =>
          replay_tail (preprocessedUnsat -> originalUnsat)
            (fun _trace_to_empty unsat_tail =>
              unsat_tail (preprocessedUnsat -> originalUnsat)
                (fun _empty_to_unsat original_transport =>
                  original_transport))))

theorem ay_urc_roundtrip_to_preprocessed
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    preprocessed := by
  intro cert
  exact ay_urc_equisat_forward original preprocessed
    (ay_urc_roundtrip_equisat
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)

theorem ay_urc_roundtrip_to_original
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    preprocessed ->
    original := by
  intro cert
  exact ay_urc_equisat_backward original preprocessed
    (ay_urc_roundtrip_equisat
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert)

theorem ay_urc_roundtrip_empty_from_original
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    emptyClause := by
  intro cert
  intro horiginal
  exact ay_urc_roundtrip_empty_map
    original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat cert
    (ay_urc_roundtrip_replay_map
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert
      (ay_urc_roundtrip_to_preprocessed
        original preprocessed replayTrace emptyClause
        preprocessedUnsat originalUnsat cert horiginal))

theorem ay_urc_roundtrip_preprocessed_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    preprocessedUnsat := by
  intro cert
  intro horiginal
  exact ay_urc_roundtrip_preprocessed_unsat_map
    original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat cert
    (ay_urc_roundtrip_empty_from_original
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert horiginal)

theorem ay_urc_roundtrip_original_unsat
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro cert
  intro horiginal
  exact ay_urc_roundtrip_original_unsat_map
    original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat cert
    (ay_urc_roundtrip_preprocessed_unsat
      original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat cert horiginal)

theorem ay_urc_compress_unsat_outcome
    (metadata : Prop) (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCFullUnsatOutcome metadata original preprocessed replayTrace
      emptyClause preprocessedUnsat originalUnsat ->
    AyURCCompressedUnsatOutcome original preprocessed replayTrace
      emptyClause preprocessedUnsat originalUnsat := by
  intro full
  exact full
    (AyURCReplayRoundtrip original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat)
    (fun _metadata compressed => compressed)

theorem ay_urc_compressed_unsat_sound
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCCompressedUnsatOutcome original preprocessed replayTrace
      emptyClause preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro compressed
  exact ay_urc_roundtrip_original_unsat
    original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat compressed

theorem ay_urc_full_unsat_sound_after_compression
    (metadata : Prop) (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCFullUnsatOutcome metadata original preprocessed replayTrace
      emptyClause preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro full
  exact ay_urc_compressed_unsat_sound
    original preprocessed replayTrace emptyClause
    preprocessedUnsat originalUnsat
    (ay_urc_compress_unsat_outcome
      metadata original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat full)

theorem ay_urc_compressed_outcome_unsat_branch
    (satWitness : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyURCCompressedOutcome satWitness originalUnsat := by
  intro unsat
  exact ay_urc_disj_right satWitness originalUnsat unsat

theorem ay_urc_compressed_outcome_transport_unsat
    (satWitness : Prop) (unsatWitness : Prop)
    (originalUnsat : Prop) :
    AyURCCompressedOutcome satWitness unsatWitness ->
    (satWitness -> originalUnsat) ->
    (unsatWitness -> originalUnsat) ->
    originalUnsat := by
  intro outcome
  intro sat_to_unsat
  intro unsat_to_original
  exact outcome originalUnsat sat_to_unsat unsat_to_original

theorem ay_urc_roundtrip_compressed_outcome_sound
    (satWitness : Prop) (metadata : Prop)
    (original : Prop) (preprocessed : Prop)
    (replayTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyURCFullUnsatOutcome metadata original preprocessed replayTrace
      emptyClause preprocessedUnsat originalUnsat ->
    original ->
    AyURCCompressedOutcome satWitness originalUnsat := by
  intro full
  intro horiginal
  exact ay_urc_compressed_outcome_unsat_branch satWitness originalUnsat
    (ay_urc_full_unsat_sound_after_compression
      metadata original preprocessed replayTrace emptyClause
      preprocessedUnsat originalUnsat full horiginal)
