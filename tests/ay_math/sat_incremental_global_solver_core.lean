-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for incremental global solver soundness.
-- Solver states, preprocessing maps, watched BCP, proof replay, SAT models,
-- and UNSAT conflicts are abstract propositions with explicit transport maps.

def AyGlobalConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyGlobalDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyGlobalEquisat (before : Prop) (after : Prop) :=
  AyGlobalConj (before -> after) (after -> before)

def AyGlobalScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyGlobalState (formula : Prop) (learned : Prop) (assumptions : Prop) :=
  forall result : Prop,
    (formula -> learned -> assumptions -> result) -> result

def AyGlobalPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyGlobalEquisat original preprocessed

def AyGlobalBcpUnit (state : Prop) (unit : Prop) :=
  state -> unit

def AyGlobalBcpConflict (state : Prop) (conflict : Prop) :=
  state -> conflict

def AyGlobalReplay (state : Prop) (finalClause : Prop) :=
  state -> finalClause

def AyGlobalSatOutcome (formula : Prop) (model : Prop) :=
  formula -> model

def AyGlobalUnsatOutcome (formula : Prop) (conflict : Prop) :=
  formula -> conflict -> False

def AyGlobalSolveResult (satModel : Prop) (unsatConflict : Prop) :=
  AyGlobalDisj satModel unsatConflict

theorem ay_global_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyGlobalConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_global_conj_left
    (left : Prop) (right : Prop) :
    AyGlobalConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_global_conj_right
    (left : Prop) (right : Prop) :
    AyGlobalConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_global_disj_left
    (left : Prop) (right : Prop) :
    left -> AyGlobalDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_global_disj_right
    (left : Prop) (right : Prop) :
    right -> AyGlobalDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_global_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyGlobalEquisat before after :=
  fun forward backward result keep =>
    keep forward backward

theorem ay_global_equisat_forward
    (before : Prop) (after : Prop) :
    AyGlobalEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_global_equisat_backward
    (before : Prop) (after : Prop) :
    AyGlobalEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_global_state_intro
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    formula -> learned -> assumptions ->
    AyGlobalState formula learned assumptions :=
  fun formulaH learnedH assumptionsH result build =>
    build formulaH learnedH assumptionsH

theorem ay_global_state_formula
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyGlobalState formula learned assumptions -> formula :=
  fun state =>
    state formula (fun formulaH _learnedH _assumptionsH => formulaH)

theorem ay_global_state_learned
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyGlobalState formula learned assumptions -> learned :=
  fun state =>
    state learned (fun _formulaH learnedH _assumptionsH => learnedH)

theorem ay_global_state_assumptions
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyGlobalState formula learned assumptions -> assumptions :=
  fun state =>
    state assumptions (fun _formulaH _learnedH assumptionsH => assumptionsH)

theorem ay_global_push_scope
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyGlobalScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_global_state_push_assumption
    (formula : Prop) (learned : Prop)
    (active : Prop) (pushed : Prop) :
    AyGlobalState formula learned active ->
    pushed ->
    AyGlobalState formula learned (AyGlobalScope active pushed) :=
  fun state pushedH =>
    ay_global_state_intro formula learned (AyGlobalScope active pushed)
      (ay_global_state_formula formula learned active state)
      (ay_global_state_learned formula learned active state)
      (ay_global_push_scope active pushed
        (ay_global_state_assumptions formula learned active state)
        pushedH)

theorem ay_global_state_pop_assumption
    (formula : Prop) (learned : Prop)
    (active : Prop) (pushed : Prop) :
    (AyGlobalScope active pushed -> active) ->
    AyGlobalState formula learned (AyGlobalScope active pushed) ->
    AyGlobalState formula learned active :=
  fun popProjection state =>
    ay_global_state_intro formula learned active
      (ay_global_state_formula
        formula learned (AyGlobalScope active pushed) state)
      (ay_global_state_learned
        formula learned (AyGlobalScope active pushed) state)
      (popProjection
        (ay_global_state_assumptions
          formula learned (AyGlobalScope active pushed) state))

theorem ay_global_preprocess_state_forward
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    AyGlobalState original learned assumptions ->
    AyGlobalState preprocessed learned assumptions :=
  fun preprocess state =>
    ay_global_state_intro preprocessed learned assumptions
      (ay_global_equisat_forward original preprocessed preprocess
        (ay_global_state_formula original learned assumptions state))
      (ay_global_state_learned original learned assumptions state)
      (ay_global_state_assumptions original learned assumptions state)

theorem ay_global_preprocess_state_backward
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    AyGlobalState preprocessed learned assumptions ->
    AyGlobalState original learned assumptions :=
  fun preprocess state =>
    ay_global_state_intro original learned assumptions
      (ay_global_equisat_backward original preprocessed preprocess
        (ay_global_state_formula preprocessed learned assumptions state))
      (ay_global_state_learned preprocessed learned assumptions state)
      (ay_global_state_assumptions preprocessed learned assumptions state)

theorem ay_global_preprocess_state_equisat
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    AyGlobalEquisat
      (AyGlobalState original learned assumptions)
      (AyGlobalState preprocessed learned assumptions) :=
  fun preprocess =>
    ay_global_equisat_intro
      (AyGlobalState original learned assumptions)
      (AyGlobalState preprocessed learned assumptions)
      (ay_global_preprocess_state_forward
        original preprocessed learned assumptions preprocess)
      (ay_global_preprocess_state_backward
        original preprocessed learned assumptions preprocess)

theorem ay_global_bcp_unit_extend_learned
    (formula : Prop) (learned : Prop) (assumptions : Prop)
    (unit : Prop) :
    AyGlobalBcpUnit
      (AyGlobalState formula learned assumptions)
      unit ->
    AyGlobalState formula learned assumptions ->
    AyGlobalState formula (AyGlobalConj learned unit) assumptions :=
  fun bcpUnit state =>
    ay_global_state_intro formula
      (AyGlobalConj learned unit)
      assumptions
      (ay_global_state_formula formula learned assumptions state)
      (ay_global_conj_intro learned unit
        (ay_global_state_learned formula learned assumptions state)
        (bcpUnit state))
      (ay_global_state_assumptions formula learned assumptions state)

theorem ay_global_bcp_conflict_sound
    (state : Prop) (conflict : Prop) :
    AyGlobalBcpConflict state conflict ->
    state ->
    conflict :=
  fun bcpConflict stateH =>
    bcpConflict stateH

theorem ay_global_replay_final_clause
    (state : Prop) (finalClause : Prop) :
    AyGlobalReplay state finalClause ->
    state ->
    finalClause :=
  fun replay stateH =>
    replay stateH

theorem ay_global_replay_after_bcp_unit
    (formula : Prop) (learned : Prop) (assumptions : Prop)
    (unit : Prop) (finalClause : Prop) :
    AyGlobalBcpUnit
      (AyGlobalState formula learned assumptions)
      unit ->
    AyGlobalReplay
      (AyGlobalState formula (AyGlobalConj learned unit) assumptions)
      finalClause ->
    AyGlobalState formula learned assumptions ->
    finalClause :=
  fun bcpUnit replay state =>
    replay
      (ay_global_bcp_unit_extend_learned
        formula learned assumptions unit bcpUnit state)

theorem ay_global_sat_model_transport_forward
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    AyGlobalSatOutcome preprocessed model ->
    original ->
    model :=
  fun preprocess satOutcome originalH =>
    satOutcome
      (ay_global_equisat_forward original preprocessed
        preprocess originalH)

theorem ay_global_sat_model_transport_backward
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    (original -> model) ->
    preprocessed ->
    model :=
  fun preprocess satOutcome preprocessedH =>
    satOutcome
      (ay_global_equisat_backward original preprocessed
        preprocess preprocessedH)

theorem ay_global_unsat_conflict_transport
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    AyGlobalUnsatOutcome preprocessed conflict ->
    AyGlobalUnsatOutcome original conflict :=
  fun preprocess unsatOutcome originalH conflictH =>
    unsatOutcome
      (ay_global_equisat_forward original preprocessed
        preprocess originalH)
      conflictH

theorem ay_global_unsat_from_bcp_conflict
    (formula : Prop) (learned : Prop) (assumptions : Prop)
    (conflict : Prop) :
    AyGlobalBcpConflict
      (AyGlobalState formula learned assumptions)
      conflict ->
    (formula -> assumptions -> conflict -> False) ->
    AyGlobalState formula learned assumptions ->
    False :=
  fun bcpConflict conflictContradicts state =>
    conflictContradicts
      (ay_global_state_formula formula learned assumptions state)
      (ay_global_state_assumptions formula learned assumptions state)
      (bcpConflict state)

theorem ay_global_unsat_from_replayed_clause
    (state : Prop) (finalClause : Prop) :
    AyGlobalReplay state finalClause ->
    (finalClause -> False) ->
    state ->
    False :=
  fun replay finalContradiction stateH =>
    finalContradiction (replay stateH)

theorem ay_global_sat_result_left
    (satModel : Prop) (unsatConflict : Prop) :
    satModel -> AyGlobalSolveResult satModel unsatConflict :=
  fun satH =>
    ay_global_disj_left satModel unsatConflict satH

theorem ay_global_unsat_result_right
    (satModel : Prop) (unsatConflict : Prop) :
    unsatConflict -> AyGlobalSolveResult satModel unsatConflict :=
  fun unsatH =>
    ay_global_disj_right satModel unsatConflict unsatH

theorem ay_global_incremental_sat_pipeline
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (model : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    pushed ->
    AyGlobalSatOutcome preprocessed model ->
    AyGlobalState original learned active ->
    model :=
  fun preprocess pushedH satOutcome state =>
    ay_global_sat_model_transport_forward original preprocessed model
      preprocess
      satOutcome
      (ay_global_state_formula original learned
        (AyGlobalScope active pushed)
        (ay_global_state_push_assumption
          original learned active pushed state pushedH))

theorem ay_global_incremental_unsat_pipeline
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (conflict : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    pushed ->
    (AyGlobalState
      preprocessed learned (AyGlobalScope active pushed) -> conflict) ->
    (preprocessed -> AyGlobalScope active pushed -> conflict -> False) ->
    AyGlobalState original learned active ->
    False :=
  fun preprocess pushedH replayConflict conflictContradicts state =>
    conflictContradicts
      (ay_global_state_formula preprocessed learned
        (AyGlobalScope active pushed)
        (ay_global_preprocess_state_forward original preprocessed learned
          (AyGlobalScope active pushed)
          preprocess
          (ay_global_state_push_assumption
            original learned active pushed state pushedH)))
      (ay_global_state_assumptions preprocessed learned
        (AyGlobalScope active pushed)
        (ay_global_preprocess_state_forward original preprocessed learned
          (AyGlobalScope active pushed)
          preprocess
          (ay_global_state_push_assumption
            original learned active pushed state pushedH)))
      (replayConflict
        (ay_global_preprocess_state_forward original preprocessed learned
          (AyGlobalScope active pushed)
          preprocess
          (ay_global_state_push_assumption
            original learned active pushed state pushedH)))

theorem ay_global_full_solver_sound
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (unit : Prop) (finalClause : Prop)
    (model : Prop) (conflict : Prop) :
    AyGlobalPreprocessMap original preprocessed ->
    pushed ->
    AyGlobalBcpUnit
      (AyGlobalState
        preprocessed learned (AyGlobalScope active pushed))
      unit ->
    AyGlobalReplay
      (AyGlobalState
        preprocessed (AyGlobalConj learned unit)
        (AyGlobalScope active pushed))
      finalClause ->
    (finalClause -> conflict) ->
    AyGlobalSatOutcome preprocessed model ->
    AyGlobalState original learned active ->
    AyGlobalSolveResult model conflict :=
  fun preprocess pushedH bcpUnit replay clauseToConflict satOutcome state =>
    ay_global_sat_result_left model conflict
      (ay_global_sat_model_transport_forward original preprocessed model
        preprocess
        satOutcome
        (ay_global_state_formula original learned active state))
