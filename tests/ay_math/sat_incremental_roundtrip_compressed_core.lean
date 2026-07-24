-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact checked round-trip theorem for incremental outcomes with compressed
-- certificates. A compressed certificate keeps only the boundary state and
-- final clause while preserving SAT/UNSAT transport through assumptions,
-- preprocessing, and replay.

def AyCompRtConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCompRtDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCompRtEquisat (before : Prop) (after : Prop) :=
  AyCompRtConj (before -> after) (after -> before)

def AyCompRtScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyCompRtState (formula : Prop) (assumptions : Prop) :=
  AyCompRtConj formula assumptions

def AyCompRtCompressed (state : Prop) (finalClause : Prop) :=
  AyCompRtConj state finalClause

def AyCompRtOutcome (model : Prop) (conflict : Prop) :=
  AyCompRtDisj model conflict

theorem ay_comp_rt_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCompRtConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_comp_rt_conj_left
    (left : Prop) (right : Prop) :
    AyCompRtConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_comp_rt_conj_right
    (left : Prop) (right : Prop) :
    AyCompRtConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_comp_rt_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCompRtDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_comp_rt_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCompRtDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_comp_rt_equisat_forward
    (before : Prop) (after : Prop) :
    AyCompRtEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_comp_rt_equisat_backward
    (before : Prop) (after : Prop) :
    AyCompRtEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_comp_rt_scope_push
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyCompRtScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_comp_rt_state_push
    (formula : Prop) (active : Prop) (pushed : Prop) :
    AyCompRtState formula active ->
    pushed ->
    AyCompRtState formula (AyCompRtScope active pushed) :=
  fun state pushedH =>
    ay_comp_rt_conj_intro formula (AyCompRtScope active pushed)
      (ay_comp_rt_conj_left formula active state)
      (ay_comp_rt_scope_push active pushed
        (ay_comp_rt_conj_right formula active state)
        pushedH)

theorem ay_comp_rt_preprocess_forward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyCompRtEquisat original preprocessed ->
    AyCompRtState original assumptions ->
    AyCompRtState preprocessed assumptions :=
  fun preprocess state =>
    ay_comp_rt_conj_intro preprocessed assumptions
      (ay_comp_rt_equisat_forward original preprocessed preprocess
        (ay_comp_rt_conj_left original assumptions state))
      (ay_comp_rt_conj_right original assumptions state)

theorem ay_comp_rt_preprocess_backward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyCompRtEquisat original preprocessed ->
    AyCompRtState preprocessed assumptions ->
    AyCompRtState original assumptions :=
  fun preprocess state =>
    ay_comp_rt_conj_intro original assumptions
      (ay_comp_rt_equisat_backward original preprocessed preprocess
        (ay_comp_rt_conj_left preprocessed assumptions state))
      (ay_comp_rt_conj_right preprocessed assumptions state)

theorem ay_comp_rt_replay_compress
    (start : Prop) (middle : Prop) (finish : Prop) (finalClause : Prop) :
    (start -> middle) ->
    (middle -> finish) ->
    (finish -> finalClause) ->
    start ->
    AyCompRtCompressed finish finalClause :=
  fun first second replay startH =>
    ay_comp_rt_conj_intro finish finalClause
      (second (first startH))
      (replay (second (first startH)))

theorem ay_comp_rt_compressed_state
    (state : Prop) (finalClause : Prop) :
    AyCompRtCompressed state finalClause -> state :=
  fun compressed =>
    ay_comp_rt_conj_left state finalClause compressed

theorem ay_comp_rt_compressed_final
    (state : Prop) (finalClause : Prop) :
    AyCompRtCompressed state finalClause -> finalClause :=
  fun compressed =>
    ay_comp_rt_conj_right state finalClause compressed

theorem ay_comp_rt_compressed_inflate
    (state : Prop) (finalClause : Prop) :
    AyCompRtCompressed state finalClause ->
    AyCompRtConj state finalClause :=
  fun compressed =>
    compressed

theorem ay_comp_rt_sat_transport
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyCompRtEquisat original preprocessed ->
    (preprocessed -> model) ->
    original ->
    model :=
  fun preprocess sat originalH =>
    sat
      (ay_comp_rt_equisat_forward original preprocessed
        preprocess originalH)

theorem ay_comp_rt_unsat_transport
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    (preprocessed -> conflict -> False) ->
    original -> conflict -> False :=
  fun preprocess unsat originalH conflictH =>
    unsat
      (ay_comp_rt_equisat_forward original preprocessed
        preprocess originalH)
      conflictH

theorem ay_comp_rt_sat_roundtrip_compressed
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyCompRtState original active ->
    model :=
  fun preprocess pushedH sat state =>
    ay_comp_rt_sat_transport original preprocessed model
      preprocess
      sat
      (ay_comp_rt_conj_left original (AyCompRtScope active pushed)
        (ay_comp_rt_state_push original active pushed state pushedH))

theorem ay_comp_rt_unsat_roundtrip_compressed
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (middle : Prop) (finish : Prop)
    (finalClause : Prop) (conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (AyCompRtState preprocessed (AyCompRtScope active pushed) -> middle) ->
    (middle -> finish) ->
    (finish -> finalClause) ->
    (finalClause -> conflict) ->
    AyCompRtState original active ->
    conflict :=
  fun preprocess pushedH first second replay clauseToConflict state =>
    clauseToConflict
      (ay_comp_rt_compressed_final finish finalClause
        (ay_comp_rt_replay_compress
          (AyCompRtState preprocessed (AyCompRtScope active pushed))
          middle
          finish
          finalClause
          first
          second
          replay
          (ay_comp_rt_preprocess_forward original preprocessed
            (AyCompRtScope active pushed)
            preprocess
            (ay_comp_rt_state_push original active pushed state pushedH))))

theorem ay_comp_rt_unsat_roundtrip_contradiction
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (middle : Prop) (finish : Prop)
    (finalClause : Prop) (conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (AyCompRtState preprocessed (AyCompRtScope active pushed) -> middle) ->
    (middle -> finish) ->
    (finish -> finalClause) ->
    (finalClause -> conflict) ->
    (original -> conflict -> False) ->
    AyCompRtState original active ->
    False :=
  fun preprocess pushedH first second replay clauseToConflict unsat state =>
    unsat
      (ay_comp_rt_conj_left original active state)
      (ay_comp_rt_unsat_roundtrip_compressed
        original preprocessed active pushed middle finish finalClause conflict
        preprocess pushedH first second replay clauseToConflict state)

theorem ay_comp_rt_sat_outcome_compressed
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyCompRtState original active ->
    AyCompRtOutcome model conflict :=
  fun preprocess pushedH sat state =>
    ay_comp_rt_disj_left model conflict
      (ay_comp_rt_sat_roundtrip_compressed
        original preprocessed active pushed model
        preprocess pushedH sat state)

theorem ay_comp_rt_unsat_outcome_compressed
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (middle : Prop) (finish : Prop)
    (finalClause : Prop) (model conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (AyCompRtState preprocessed (AyCompRtScope active pushed) -> middle) ->
    (middle -> finish) ->
    (finish -> finalClause) ->
    (finalClause -> conflict) ->
    AyCompRtState original active ->
    AyCompRtOutcome model conflict :=
  fun preprocess pushedH first second replay clauseToConflict state =>
    ay_comp_rt_disj_right model conflict
      (ay_comp_rt_unsat_roundtrip_compressed
        original preprocessed active pushed middle finish finalClause conflict
        preprocess pushedH first second replay clauseToConflict state)

theorem ay_comp_rt_full_compressed_roundtrip
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (middle : Prop) (finish : Prop)
    (finalClause : Prop) (model conflict : Prop) :
    AyCompRtEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    (AyCompRtState preprocessed (AyCompRtScope active pushed) -> middle) ->
    (middle -> finish) ->
    (finish -> finalClause) ->
    (finalClause -> conflict) ->
    AyCompRtState original active ->
    AyCompRtConj
      (AyCompRtOutcome model conflict)
      (AyCompRtOutcome model conflict) :=
  fun preprocess pushedH sat first second replay clauseToConflict state =>
    ay_comp_rt_conj_intro
      (AyCompRtOutcome model conflict)
      (AyCompRtOutcome model conflict)
      (ay_comp_rt_sat_outcome_compressed
        original preprocessed active pushed model conflict
        preprocess pushedH sat state)
      (ay_comp_rt_unsat_outcome_compressed
        original preprocessed active pushed middle finish finalClause
        model conflict preprocess pushedH first second replay
        clauseToConflict state)
