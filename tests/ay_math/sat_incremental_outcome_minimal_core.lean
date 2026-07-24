-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal checked SAT-COMP incremental outcome certificate.
-- This keeps only the Church encodings needed to preserve the full SAT/UNSAT
-- soundness theorem over assumptions, preprocessing, BCP, CDCL, and replay.

def AyMinConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMinDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMinEquisat (before : Prop) (after : Prop) :=
  AyMinConj (before -> after) (after -> before)

def AyMinScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyMinState (formula : Prop) (assumptions : Prop) :=
  AyMinConj formula assumptions

def AyMinOutcome (model : Prop) (conflict : Prop) :=
  AyMinDisj model conflict

theorem ay_min_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMinConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_min_conj_left
    (left : Prop) (right : Prop) :
    AyMinConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_min_conj_right
    (left : Prop) (right : Prop) :
    AyMinConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_min_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMinDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_min_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMinDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_min_equisat_forward
    (before : Prop) (after : Prop) :
    AyMinEquisat before after -> before -> after :=
  fun eqsat =>
    eqsat (before -> after)
      (fun forward _backward => forward)

theorem ay_min_equisat_backward
    (before : Prop) (after : Prop) :
    AyMinEquisat before after -> after -> before :=
  fun eqsat =>
    eqsat (after -> before)
      (fun _forward backward => backward)

theorem ay_min_scope_push
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyMinScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_min_state_push
    (formula : Prop) (active : Prop) (pushed : Prop) :
    AyMinState formula active ->
    pushed ->
    AyMinState formula (AyMinScope active pushed) :=
  fun state pushedH =>
    ay_min_conj_intro formula (AyMinScope active pushed)
      (ay_min_conj_left formula active state)
      (ay_min_scope_push active pushed
        (ay_min_conj_right formula active state)
        pushedH)

theorem ay_min_preprocess_state
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyMinEquisat original preprocessed ->
    AyMinState original assumptions ->
    AyMinState preprocessed assumptions :=
  fun preprocess state =>
    ay_min_conj_intro preprocessed assumptions
      (ay_min_equisat_forward original preprocessed preprocess
        (ay_min_conj_left original assumptions state))
      (ay_min_conj_right original assumptions state)

theorem ay_min_bcp_unit
    (state : Prop) (unit : Prop) :
    (state -> unit) -> state -> unit :=
  fun bcp stateH =>
    bcp stateH

theorem ay_min_cdcl_replay_clause
    (state : Prop) (cdclState : Prop) (finalClause : Prop) :
    (state -> cdclState) ->
    (cdclState -> finalClause) ->
    state ->
    finalClause :=
  fun cdcl replay stateH =>
    replay (cdcl stateH)

theorem ay_min_sat_transport
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyMinEquisat original preprocessed ->
    (preprocessed -> model) ->
    original ->
    model :=
  fun preprocess sat originalH =>
    sat (ay_min_equisat_forward original preprocessed preprocess originalH)

theorem ay_min_unsat_transport
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyMinEquisat original preprocessed ->
    (preprocessed -> conflict -> False) ->
    original -> conflict -> False :=
  fun preprocess unsat originalH conflictH =>
    unsat
      (ay_min_equisat_forward original preprocessed preprocess originalH)
      conflictH

theorem ay_min_sat_outcome
    (model : Prop) (conflict : Prop) :
    model -> AyMinOutcome model conflict :=
  fun modelH =>
    ay_min_disj_left model conflict modelH

theorem ay_min_unsat_outcome
    (model : Prop) (conflict : Prop) :
    conflict -> AyMinOutcome model conflict :=
  fun conflictH =>
    ay_min_disj_right model conflict conflictH

theorem ay_min_full_sat_sound
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (model : Prop) (conflict : Prop) :
    AyMinEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyMinState original active ->
    AyMinOutcome model conflict :=
  fun preprocess pushedH sat state =>
    ay_min_sat_outcome model conflict
      (ay_min_sat_transport original preprocessed model
        preprocess
        sat
        (ay_min_conj_left original (AyMinScope active pushed)
          (ay_min_state_push original active pushed state pushedH)))

theorem ay_min_full_unsat_sound
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop)
    (model : Prop) (conflict : Prop) :
    AyMinEquisat original preprocessed ->
    pushed ->
    (AyMinState preprocessed (AyMinScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    AyMinState original active ->
    AyMinOutcome model conflict :=
  fun preprocess pushedH cdcl replay clauseToConflict state =>
    ay_min_unsat_outcome model conflict
      (clauseToConflict
        (ay_min_cdcl_replay_clause
          (AyMinState preprocessed (AyMinScope active pushed))
          cdclState
          finalClause
          cdcl
          replay
          (ay_min_preprocess_state original preprocessed
            (AyMinScope active pushed)
            preprocess
            (ay_min_state_push original active pushed state pushedH))))

theorem ay_min_full_competition_sound
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (cdclState : Prop) (finalClause : Prop)
    (model : Prop) (conflict : Prop) :
    AyMinEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    (AyMinState preprocessed (AyMinScope active pushed) -> cdclState) ->
    (cdclState -> finalClause) ->
    (finalClause -> conflict) ->
    AyMinState original active ->
    AyMinConj
      (AyMinOutcome model conflict)
      (AyMinOutcome model conflict) :=
  fun preprocess pushedH sat cdcl replay clauseToConflict state =>
    ay_min_conj_intro
      (AyMinOutcome model conflict)
      (AyMinOutcome model conflict)
      (ay_min_full_sat_sound original preprocessed active pushed
        model conflict preprocess pushedH sat state)
      (ay_min_full_unsat_sound original preprocessed active pushed
        cdclState finalClause model conflict preprocess pushedH
        cdcl replay clauseToConflict state)
