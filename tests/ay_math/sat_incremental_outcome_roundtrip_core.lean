-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Round-trip properties for the minimal incremental outcome certificate.
-- Theorems are compact Church-encoded maps showing SAT and UNSAT transports
-- compose through assumptions, preprocessing, CDCL/replay, and reconstruction.

def AyRoundConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRoundDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRoundEquisat (before : Prop) (after : Prop) :=
  AyRoundConj (before -> after) (after -> before)

def AyRoundScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyRoundState (formula : Prop) (assumptions : Prop) :=
  AyRoundConj formula assumptions

def AyRoundOutcome (model : Prop) (conflict : Prop) :=
  AyRoundDisj model conflict

theorem ay_round_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRoundConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_round_conj_left
    (left : Prop) (right : Prop) :
    AyRoundConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_round_conj_right
    (left : Prop) (right : Prop) :
    AyRoundConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_round_disj_left
    (left : Prop) (right : Prop) :
    left -> AyRoundDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_round_disj_right
    (left : Prop) (right : Prop) :
    right -> AyRoundDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_round_equisat_forward
    (before : Prop) (after : Prop) :
    AyRoundEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_round_equisat_backward
    (before : Prop) (after : Prop) :
    AyRoundEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_round_scope_push
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyRoundScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_round_state_push
    (formula : Prop) (active : Prop) (pushed : Prop) :
    AyRoundState formula active ->
    pushed ->
    AyRoundState formula (AyRoundScope active pushed) :=
  fun state pushedH =>
    ay_round_conj_intro formula (AyRoundScope active pushed)
      (ay_round_conj_left formula active state)
      (ay_round_scope_push active pushed
        (ay_round_conj_right formula active state)
        pushedH)

theorem ay_round_state_pop_with
    (formula : Prop) (active : Prop) (pushed : Prop) :
    (AyRoundScope active pushed -> active) ->
    AyRoundState formula (AyRoundScope active pushed) ->
    AyRoundState formula active :=
  fun popProjection state =>
    ay_round_conj_intro formula active
      (ay_round_conj_left formula (AyRoundScope active pushed) state)
      (popProjection
        (ay_round_conj_right formula (AyRoundScope active pushed) state))

theorem ay_round_preprocess_forward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyRoundEquisat original preprocessed ->
    AyRoundState original assumptions ->
    AyRoundState preprocessed assumptions :=
  fun preprocess state =>
    ay_round_conj_intro preprocessed assumptions
      (ay_round_equisat_forward original preprocessed preprocess
        (ay_round_conj_left original assumptions state))
      (ay_round_conj_right original assumptions state)

theorem ay_round_preprocess_backward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyRoundEquisat original preprocessed ->
    AyRoundState preprocessed assumptions ->
    AyRoundState original assumptions :=
  fun preprocess state =>
    ay_round_conj_intro original assumptions
      (ay_round_equisat_backward original preprocessed preprocess
        (ay_round_conj_left preprocessed assumptions state))
      (ay_round_conj_right preprocessed assumptions state)

theorem ay_round_sat_transport_forward
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyRoundEquisat original preprocessed ->
    (preprocessed -> model) ->
    original ->
    model :=
  fun preprocess sat originalH =>
    sat (ay_round_equisat_forward original preprocessed preprocess originalH)

theorem ay_round_sat_transport_backward
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyRoundEquisat original preprocessed ->
    (original -> model) ->
    preprocessed ->
    model :=
  fun preprocess sat preprocessedH =>
    sat (ay_round_equisat_backward original preprocessed preprocess
      preprocessedH)

theorem ay_round_unsat_transport_forward
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    (preprocessed -> conflict -> False) ->
    original -> conflict -> False :=
  fun preprocess unsat originalH conflictH =>
    unsat
      (ay_round_equisat_forward original preprocessed preprocess originalH)
      conflictH

theorem ay_round_unsat_transport_backward
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    (original -> conflict -> False) ->
    preprocessed -> conflict -> False :=
  fun preprocess unsat preprocessedH conflictH =>
    unsat
      (ay_round_equisat_backward original preprocessed preprocess
        preprocessedH)
      conflictH

theorem ay_round_replay_compose
    (state : Prop) (cdclState : Prop) (finalClause : Prop) :
    (state -> cdclState) ->
    (cdclState -> finalClause) ->
    state ->
    finalClause :=
  fun cdcl replay stateH =>
    replay (cdcl stateH)

theorem ay_round_sat_assumption_preprocess_roundtrip
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyRoundState original active ->
    model :=
  fun preprocess pushedH sat state =>
    ay_round_sat_transport_forward original preprocessed model
      preprocess
      sat
      (ay_round_conj_left original (AyRoundScope active pushed)
        (ay_round_state_push original active pushed state pushedH))

theorem ay_round_sat_preprocess_assumption_reconstruct
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) :
    (AyRoundScope active pushed -> active) ->
    AyRoundEquisat original preprocessed ->
    AyRoundState preprocessed (AyRoundScope active pushed) ->
    AyRoundState original active :=
  fun popProjection preprocess scoped =>
    ay_round_state_pop_with original active pushed popProjection
      (ay_round_preprocess_backward original preprocessed
        (AyRoundScope active pushed)
        preprocess
        scoped)

theorem ay_round_unsat_assumption_preprocess_replay
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop) (conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (AyRoundState preprocessed (AyRoundScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    AyRoundState original active ->
    conflict :=
  fun preprocess pushedH cdcl replay clauseToConflict state =>
    clauseToConflict
      (ay_round_replay_compose
        (AyRoundState preprocessed (AyRoundScope active pushed))
        cdclState
        finalClause
        cdcl
        replay
        (ay_round_preprocess_forward original preprocessed
          (AyRoundScope active pushed)
          preprocess
          (ay_round_state_push original active pushed state pushedH)))

theorem ay_round_unsat_conflict_roundtrip
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop) (conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (AyRoundState preprocessed (AyRoundScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    (original -> conflict -> False) ->
    AyRoundState original active ->
    False :=
  fun preprocess pushedH cdcl replay clauseToConflict unsatOriginal state =>
    unsatOriginal
      (ay_round_conj_left original active state)
      (ay_round_unsat_assumption_preprocess_replay
        original preprocessed active pushed cdclState finalClause conflict
        preprocess pushedH cdcl replay clauseToConflict state)

theorem ay_round_sat_outcome_roundtrip
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyRoundState original active ->
    AyRoundOutcome model conflict :=
  fun preprocess pushedH sat state =>
    ay_round_disj_left model conflict
      (ay_round_sat_assumption_preprocess_roundtrip
        original preprocessed active pushed model
        preprocess pushedH sat state)

theorem ay_round_unsat_outcome_roundtrip
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop) (model conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (AyRoundState preprocessed (AyRoundScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    AyRoundState original active ->
    AyRoundOutcome model conflict :=
  fun preprocess pushedH cdcl replay clauseToConflict state =>
    ay_round_disj_right model conflict
      (ay_round_unsat_assumption_preprocess_replay
        original preprocessed active pushed cdclState finalClause conflict
        preprocess pushedH cdcl replay clauseToConflict state)

theorem ay_round_full_outcome_roundtrip_pair
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop) (model conflict : Prop) :
    AyRoundEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    (AyRoundState preprocessed (AyRoundScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    AyRoundState original active ->
    AyRoundConj
      (AyRoundOutcome model conflict)
      (AyRoundOutcome model conflict) :=
  fun preprocess pushedH sat cdcl replay clauseToConflict state =>
    ay_round_conj_intro
      (AyRoundOutcome model conflict)
      (AyRoundOutcome model conflict)
      (ay_round_sat_outcome_roundtrip
        original preprocessed active pushed model conflict
        preprocess pushedH sat state)
      (ay_round_unsat_outcome_roundtrip
        original preprocessed active pushed cdclState finalClause
        model conflict preprocess pushedH cdcl replay clauseToConflict state)
