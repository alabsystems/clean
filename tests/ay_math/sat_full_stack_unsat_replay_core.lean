-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction for UNSAT proof replay through the SAT-COMP solver
-- stack. Propositions stand for formulas, clause databases, replay states,
-- final empty clauses, and original UNSAT claims; all connections are explicit
-- Church-encoded maps/certificates.

def AyFSURConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyFSURDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyFSUREquisat (before : Prop) (after : Prop) :=
  AyFSURConj (before -> after) (after -> before)

def AyFSURMap (source : Prop) (target : Prop) :=
  source -> target

def AyFSURPreprocessProjection
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyFSURConj
    (AyFSUREquisat original preprocessed)
    (preprocessedUnsat -> originalUnsat)

def AyFSURWatchedReplay
    (preprocessed : Prop) (watchedClauses : Prop)
    (learnedClauses : Prop) :=
  AyFSURConj
    (AyFSURMap preprocessed watchedClauses)
    (AyFSURMap watchedClauses learnedClauses)

def AyFSURStreamingReplay
    (learnedClauses : Prop) (replayState : Prop)
    (finalTrace : Prop) :=
  AyFSURConj
    (AyFSURMap learnedClauses replayState)
    (AyFSURMap replayState finalTrace)

def AyFSUREmptyClauseSound
    (finalTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) :=
  AyFSURConj
    (AyFSURMap finalTrace emptyClause)
    (emptyClause -> preprocessedUnsat)

def AyFSURUnsatReplayStack
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyFSURConj
    (AyFSURPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat)
    (AyFSURConj
      (AyFSURWatchedReplay preprocessed watchedClauses learnedClauses)
      (AyFSURConj
        (AyFSURStreamingReplay learnedClauses replayState finalTrace)
        (AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat)))

theorem ay_fsur_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyFSURConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_fsur_conj_left
    (p : Prop) (q : Prop) :
    AyFSURConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_fsur_disj_left
    (p : Prop) (q : Prop) :
    p -> AyFSURDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_fsur_disj_right
    (p : Prop) (q : Prop) :
    q -> AyFSURDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_fsur_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFSUREquisat before after := by
  intro forward
  intro backward
  exact ay_fsur_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_fsur_equisat_forward
    (before : Prop) (after : Prop) :
    AyFSUREquisat before after ->
    before ->
    after := by
  intro certificate
  exact certificate (before -> after)
    (fun forward _backward => forward)

theorem ay_fsur_equisat_backward
    (before : Prop) (after : Prop) :
    AyFSUREquisat before after ->
    after ->
    before := by
  intro certificate
  exact certificate (after -> before)
    (fun _forward backward => backward)

theorem ay_fsur_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyFSUREquisat before middle ->
    AyFSUREquisat middle after ->
    AyFSUREquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_fsur_preprocess_projection_equisat
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat ->
    AyFSUREquisat original preprocessed := by
  intro projection
  exact ay_fsur_conj_left
    (AyFSUREquisat original preprocessed)
    (preprocessedUnsat -> originalUnsat)
    projection

theorem ay_fsur_preprocess_unsat_lift
    (original : Prop) (preprocessed : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat ->
    preprocessedUnsat ->
    originalUnsat := by
  intro projection
  exact projection (preprocessedUnsat -> originalUnsat)
    (fun _equisat lift => lift)

theorem ay_fsur_watched_from_preprocessed
    (preprocessed : Prop) (watchedClauses : Prop)
    (learnedClauses : Prop) :
    AyFSURWatchedReplay preprocessed watchedClauses learnedClauses ->
    preprocessed ->
    watchedClauses := by
  intro watched
  exact watched (preprocessed -> watchedClauses)
    (fun pre_to_watch _watch_to_learned => pre_to_watch)

theorem ay_fsur_learned_from_watched
    (preprocessed : Prop) (watchedClauses : Prop)
    (learnedClauses : Prop) :
    AyFSURWatchedReplay preprocessed watchedClauses learnedClauses ->
    watchedClauses ->
    learnedClauses := by
  intro watched
  exact watched (watchedClauses -> learnedClauses)
    (fun _pre_to_watch watch_to_learned => watch_to_learned)

theorem ay_fsur_learned_from_preprocessed
    (preprocessed : Prop) (watchedClauses : Prop)
    (learnedClauses : Prop) :
    AyFSURWatchedReplay preprocessed watchedClauses learnedClauses ->
    preprocessed ->
    learnedClauses := by
  intro watched
  intro hpreprocessed
  exact ay_fsur_learned_from_watched
    preprocessed watchedClauses learnedClauses watched
    (ay_fsur_watched_from_preprocessed
      preprocessed watchedClauses learnedClauses watched hpreprocessed)

theorem ay_fsur_replay_state_from_learned
    (learnedClauses : Prop) (replayState : Prop)
    (finalTrace : Prop) :
    AyFSURStreamingReplay learnedClauses replayState finalTrace ->
    learnedClauses ->
    replayState := by
  intro stream
  exact stream (learnedClauses -> replayState)
    (fun learned_to_replay _replay_to_trace => learned_to_replay)

theorem ay_fsur_final_trace_from_replay
    (learnedClauses : Prop) (replayState : Prop)
    (finalTrace : Prop) :
    AyFSURStreamingReplay learnedClauses replayState finalTrace ->
    replayState ->
    finalTrace := by
  intro stream
  exact stream (replayState -> finalTrace)
    (fun _learned_to_replay replay_to_trace => replay_to_trace)

theorem ay_fsur_final_trace_from_learned
    (learnedClauses : Prop) (replayState : Prop)
    (finalTrace : Prop) :
    AyFSURStreamingReplay learnedClauses replayState finalTrace ->
    learnedClauses ->
    finalTrace := by
  intro stream
  intro hlearned
  exact ay_fsur_final_trace_from_replay
    learnedClauses replayState finalTrace stream
    (ay_fsur_replay_state_from_learned
      learnedClauses replayState finalTrace stream hlearned)

theorem ay_fsur_empty_clause_from_trace
    (finalTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) :
    AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat ->
    finalTrace ->
    emptyClause := by
  intro sound
  exact sound (finalTrace -> emptyClause)
    (fun trace_to_empty _empty_to_unsat => trace_to_empty)

theorem ay_fsur_preprocessed_unsat_from_empty
    (finalTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) :
    AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat ->
    emptyClause ->
    preprocessedUnsat := by
  intro sound
  exact sound (emptyClause -> preprocessedUnsat)
    (fun _trace_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_fsur_preprocessed_unsat_from_trace
    (finalTrace : Prop) (emptyClause : Prop)
    (preprocessedUnsat : Prop) :
    AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat ->
    finalTrace ->
    preprocessedUnsat := by
  intro sound
  intro htrace
  exact ay_fsur_preprocessed_unsat_from_empty
    finalTrace emptyClause preprocessedUnsat sound
    (ay_fsur_empty_clause_from_trace
      finalTrace emptyClause preprocessedUnsat sound htrace)

theorem ay_fsur_stack_projection
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    AyFSURPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat := by
  intro stack
  exact ay_fsur_conj_left
    (AyFSURPreprocessProjection original preprocessed
      preprocessedUnsat originalUnsat)
    (AyFSURConj
      (AyFSURWatchedReplay preprocessed watchedClauses learnedClauses)
      (AyFSURConj
        (AyFSURStreamingReplay learnedClauses replayState finalTrace)
        (AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat)))
    stack

theorem ay_fsur_stack_watched
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    AyFSURWatchedReplay preprocessed watchedClauses learnedClauses := by
  intro stack
  exact stack (AyFSURWatchedReplay preprocessed watchedClauses learnedClauses)
    (fun _projection rest =>
      rest (AyFSURWatchedReplay preprocessed watchedClauses learnedClauses)
        (fun watched _tail => watched))

theorem ay_fsur_stack_streaming
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    AyFSURStreamingReplay learnedClauses replayState finalTrace := by
  intro stack
  exact stack (AyFSURStreamingReplay learnedClauses replayState finalTrace)
    (fun _projection rest =>
      rest (AyFSURStreamingReplay learnedClauses replayState finalTrace)
        (fun _watched tail =>
          tail (AyFSURStreamingReplay learnedClauses replayState finalTrace)
            (fun streaming _empty_sound => streaming)))

theorem ay_fsur_stack_empty_sound
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat := by
  intro stack
  exact stack (AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat)
    (fun _projection rest =>
      rest (AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat)
        (fun _watched tail =>
          tail (AyFSUREmptyClauseSound finalTrace emptyClause preprocessedUnsat)
            (fun _streaming empty_sound => empty_sound)))

theorem ay_fsur_stack_final_trace_from_original
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    original ->
    finalTrace := by
  intro stack
  intro horiginal
  exact ay_fsur_final_trace_from_learned learnedClauses replayState finalTrace
    (ay_fsur_stack_streaming
      original preprocessed watchedClauses learnedClauses replayState
      finalTrace emptyClause preprocessedUnsat originalUnsat stack)
    (ay_fsur_learned_from_preprocessed preprocessed watchedClauses learnedClauses
      (ay_fsur_stack_watched
        original preprocessed watchedClauses learnedClauses replayState
        finalTrace emptyClause preprocessedUnsat originalUnsat stack)
      (ay_fsur_equisat_forward original preprocessed
        (ay_fsur_preprocess_projection_equisat original preprocessed
          preprocessedUnsat originalUnsat
          (ay_fsur_stack_projection
            original preprocessed watchedClauses learnedClauses replayState
            finalTrace emptyClause preprocessedUnsat originalUnsat stack))
        horiginal))

theorem ay_fsur_stack_preprocessed_unsat
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    finalTrace ->
    preprocessedUnsat := by
  intro stack
  intro htrace
  exact ay_fsur_preprocessed_unsat_from_trace
    finalTrace emptyClause preprocessedUnsat
    (ay_fsur_stack_empty_sound
      original preprocessed watchedClauses learnedClauses replayState
      finalTrace emptyClause preprocessedUnsat originalUnsat stack)
    htrace

theorem ay_fsur_stack_original_unsat_from_trace
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    finalTrace ->
    originalUnsat := by
  intro stack
  intro htrace
  exact ay_fsur_preprocess_unsat_lift original preprocessed
    preprocessedUnsat originalUnsat
    (ay_fsur_stack_projection
      original preprocessed watchedClauses learnedClauses replayState
      finalTrace emptyClause preprocessedUnsat originalUnsat stack)
    (ay_fsur_stack_preprocessed_unsat
      original preprocessed watchedClauses learnedClauses replayState
      finalTrace emptyClause preprocessedUnsat originalUnsat stack htrace)

theorem ay_fsur_empty_clause_sound_for_original
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    emptyClause ->
    originalUnsat := by
  intro stack
  intro hempty
  exact ay_fsur_preprocess_unsat_lift original preprocessed
    preprocessedUnsat originalUnsat
    (ay_fsur_stack_projection
      original preprocessed watchedClauses learnedClauses replayState
      finalTrace emptyClause preprocessedUnsat originalUnsat stack)
    (ay_fsur_preprocessed_unsat_from_empty
      finalTrace emptyClause preprocessedUnsat
      (ay_fsur_stack_empty_sound
        original preprocessed watchedClauses learnedClauses replayState
        finalTrace emptyClause preprocessedUnsat originalUnsat stack)
      hempty)

theorem ay_fsur_full_stack_unsat_replay_sound
    (original : Prop) (preprocessed : Prop)
    (watchedClauses : Prop) (learnedClauses : Prop)
    (replayState : Prop) (finalTrace : Prop)
    (emptyClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFSURUnsatReplayStack original preprocessed watchedClauses learnedClauses
      replayState finalTrace emptyClause preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro stack
  intro horiginal
  exact ay_fsur_stack_original_unsat_from_trace
    original preprocessed watchedClauses learnedClauses replayState finalTrace
    emptyClause preprocessedUnsat originalUnsat stack
    (ay_fsur_stack_final_trace_from_original
      original preprocessed watchedClauses learnedClauses replayState finalTrace
      emptyClause preprocessedUnsat originalUnsat stack horiginal)
