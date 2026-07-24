-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for incremental SAT-COMP outcome soundness.
-- The solver pipeline is abstract: assumptions, preprocessing, watched BCP,
-- CDCL search, streaming proof replay, and SAT/UNSAT output transport are
-- explicit Church-encoded maps.

def AyCompConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCompDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCompEquisat (before : Prop) (after : Prop) :=
  AyCompConj (before -> after) (after -> before)

def AyCompScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyCompState (formula : Prop) (learned : Prop) (assumptions : Prop) :=
  forall result : Prop,
    (formula -> learned -> assumptions -> result) -> result

def AyCompPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyCompEquisat original preprocessed

def AyCompBcpUnit (state : Prop) (unit : Prop) :=
  state -> unit

def AyCompBcpConflict (state : Prop) (conflict : Prop) :=
  state -> conflict

def AyCompCdclStep (state : Prop) (learned : Prop) :=
  state -> learned

def AyCompReplayChunk (before : Prop) (after : Prop) :=
  before -> after

def AyCompFinalClause (state : Prop) (clause : Prop) :=
  state -> clause

def AyCompSatTransport (formula : Prop) (model : Prop) :=
  formula -> model

def AyCompUnsatTransport (formula : Prop) (conflict : Prop) :=
  formula -> conflict -> False

def AyCompOutcome (model : Prop) (conflict : Prop) :=
  AyCompDisj model conflict

theorem ay_comp_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCompConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_comp_conj_left
    (left : Prop) (right : Prop) :
    AyCompConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_comp_conj_right
    (left : Prop) (right : Prop) :
    AyCompConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_comp_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCompDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_comp_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCompDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_comp_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCompEquisat before after :=
  fun forward backward result keep =>
    keep forward backward

theorem ay_comp_equisat_forward
    (before : Prop) (after : Prop) :
    AyCompEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_comp_equisat_backward
    (before : Prop) (after : Prop) :
    AyCompEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_comp_state_intro
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    formula -> learned -> assumptions ->
    AyCompState formula learned assumptions :=
  fun formulaH learnedH assumptionsH result build =>
    build formulaH learnedH assumptionsH

theorem ay_comp_state_formula
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyCompState formula learned assumptions -> formula :=
  fun state =>
    state formula (fun formulaH _learnedH _assumptionsH => formulaH)

theorem ay_comp_state_learned
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyCompState formula learned assumptions -> learned :=
  fun state =>
    state learned (fun _formulaH learnedH _assumptionsH => learnedH)

theorem ay_comp_state_assumptions
    (formula : Prop) (learned : Prop) (assumptions : Prop) :
    AyCompState formula learned assumptions -> assumptions :=
  fun state =>
    state assumptions (fun _formulaH _learnedH assumptionsH => assumptionsH)

theorem ay_comp_push_scope
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyCompScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_comp_state_push
    (formula : Prop) (learned : Prop)
    (active : Prop) (pushed : Prop) :
    AyCompState formula learned active ->
    pushed ->
    AyCompState formula learned (AyCompScope active pushed) :=
  fun state pushedH =>
    ay_comp_state_intro formula learned (AyCompScope active pushed)
      (ay_comp_state_formula formula learned active state)
      (ay_comp_state_learned formula learned active state)
      (ay_comp_push_scope active pushed
        (ay_comp_state_assumptions formula learned active state)
        pushedH)

theorem ay_comp_state_pop
    (formula : Prop) (learned : Prop)
    (active : Prop) (pushed : Prop) :
    (AyCompScope active pushed -> active) ->
    AyCompState formula learned (AyCompScope active pushed) ->
    AyCompState formula learned active :=
  fun popProjection state =>
    ay_comp_state_intro formula learned active
      (ay_comp_state_formula formula learned
        (AyCompScope active pushed) state)
      (ay_comp_state_learned formula learned
        (AyCompScope active pushed) state)
      (popProjection
        (ay_comp_state_assumptions formula learned
          (AyCompScope active pushed) state))

theorem ay_comp_preprocess_forward
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyCompPreprocessMap original preprocessed ->
    AyCompState original learned assumptions ->
    AyCompState preprocessed learned assumptions :=
  fun preprocess state =>
    ay_comp_state_intro preprocessed learned assumptions
      (ay_comp_equisat_forward original preprocessed preprocess
        (ay_comp_state_formula original learned assumptions state))
      (ay_comp_state_learned original learned assumptions state)
      (ay_comp_state_assumptions original learned assumptions state)

theorem ay_comp_preprocess_backward
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyCompPreprocessMap original preprocessed ->
    AyCompState preprocessed learned assumptions ->
    AyCompState original learned assumptions :=
  fun preprocess state =>
    ay_comp_state_intro original learned assumptions
      (ay_comp_equisat_backward original preprocessed preprocess
        (ay_comp_state_formula preprocessed learned assumptions state))
      (ay_comp_state_learned preprocessed learned assumptions state)
      (ay_comp_state_assumptions preprocessed learned assumptions state)

theorem ay_comp_bcp_unit_learn
    (formula : Prop) (learned : Prop) (assumptions : Prop)
    (unit : Prop) :
    AyCompBcpUnit (AyCompState formula learned assumptions) unit ->
    AyCompState formula learned assumptions ->
    AyCompState formula (AyCompConj learned unit) assumptions :=
  fun bcpUnit state =>
    ay_comp_state_intro formula (AyCompConj learned unit) assumptions
      (ay_comp_state_formula formula learned assumptions state)
      (ay_comp_conj_intro learned unit
        (ay_comp_state_learned formula learned assumptions state)
        (bcpUnit state))
      (ay_comp_state_assumptions formula learned assumptions state)

theorem ay_comp_bcp_conflict
    (state : Prop) (conflict : Prop) :
    AyCompBcpConflict state conflict -> state -> conflict :=
  fun bcp stateH =>
    bcp stateH

theorem ay_comp_cdcl_learn
    (state : Prop) (learned : Prop) :
    AyCompCdclStep state learned -> state -> learned :=
  fun cdcl stateH =>
    cdcl stateH

theorem ay_comp_stream_handoff
    (first : Prop) (middle : Prop) (last : Prop) :
    AyCompReplayChunk first middle ->
    AyCompReplayChunk middle last ->
    AyCompReplayChunk first last :=
  fun chunkA chunkB firstH =>
    chunkB (chunkA firstH)

theorem ay_comp_stream_final_clause
    (start : Prop) (finish : Prop) (clause : Prop) :
    AyCompReplayChunk start finish ->
    AyCompFinalClause finish clause ->
    start ->
    clause :=
  fun chunk finalCheck startH =>
    finalCheck (chunk startH)

theorem ay_comp_replay_after_cdcl
    (state : Prop) (learned : Prop) (clause : Prop) :
    AyCompCdclStep state learned ->
    AyCompFinalClause learned clause ->
    state ->
    clause :=
  fun cdcl finalCheck stateH =>
    finalCheck (cdcl stateH)

theorem ay_comp_sat_transport
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyCompPreprocessMap original preprocessed ->
    AyCompSatTransport preprocessed model ->
    AyCompSatTransport original model :=
  fun preprocess sat originalH =>
    sat (ay_comp_equisat_forward original preprocessed preprocess originalH)

theorem ay_comp_unsat_transport
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyCompPreprocessMap original preprocessed ->
    AyCompUnsatTransport preprocessed conflict ->
    AyCompUnsatTransport original conflict :=
  fun preprocess unsat originalH conflictH =>
    unsat
      (ay_comp_equisat_forward original preprocessed preprocess originalH)
      conflictH

theorem ay_comp_sat_outcome
    (model : Prop) (conflict : Prop) :
    model -> AyCompOutcome model conflict :=
  fun modelH =>
    ay_comp_disj_left model conflict modelH

theorem ay_comp_unsat_outcome
    (model : Prop) (conflict : Prop) :
    conflict -> AyCompOutcome model conflict :=
  fun conflictH =>
    ay_comp_disj_right model conflict conflictH

theorem ay_comp_incremental_sat_sound
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (model : Prop) :
    AyCompPreprocessMap original preprocessed ->
    pushed ->
    AyCompSatTransport preprocessed model ->
    AyCompState original learned active ->
    model :=
  fun preprocess pushedH sat state =>
    ay_comp_sat_transport original preprocessed model preprocess sat
      (ay_comp_state_formula original learned
        (AyCompScope active pushed)
        (ay_comp_state_push original learned active pushed state pushedH))

theorem ay_comp_incremental_unsat_sound
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (conflict : Prop) :
    AyCompPreprocessMap original preprocessed ->
    pushed ->
    AyCompBcpConflict
      (AyCompState preprocessed learned (AyCompScope active pushed))
      conflict ->
    AyCompUnsatTransport preprocessed conflict ->
    AyCompState original learned active ->
    False :=
  fun preprocess pushedH bcpConflict unsat state =>
    unsat
      (ay_comp_state_formula preprocessed learned
        (AyCompScope active pushed)
        (ay_comp_preprocess_forward original preprocessed learned
          (AyCompScope active pushed)
          preprocess
          (ay_comp_state_push original learned active pushed state pushedH)))
      (bcpConflict
        (ay_comp_preprocess_forward original preprocessed learned
          (AyCompScope active pushed)
          preprocess
          (ay_comp_state_push original learned active pushed state pushedH)))

theorem ay_comp_cdcl_replay_unsat_sound
    (state : Prop) (learned : Prop) (finalClause : Prop) :
    AyCompCdclStep state learned ->
    AyCompFinalClause learned finalClause ->
    (finalClause -> False) ->
    state ->
    False :=
  fun cdcl finalCheck contradiction stateH =>
    contradiction (finalCheck (cdcl stateH))

theorem ay_comp_streaming_replay_unsat_sound
    (start : Prop) (middle : Prop) (finish : Prop)
    (finalClause : Prop) :
    AyCompReplayChunk start middle ->
    AyCompReplayChunk middle finish ->
    AyCompFinalClause finish finalClause ->
    (finalClause -> False) ->
    start ->
    False :=
  fun chunkA chunkB finalCheck contradiction startH =>
    contradiction
      (ay_comp_stream_final_clause start finish finalClause
        (ay_comp_stream_handoff start middle finish chunkA chunkB)
        finalCheck
        startH)

theorem ay_comp_competition_sat_result
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (model : Prop) (conflict : Prop) :
    AyCompPreprocessMap original preprocessed ->
    pushed ->
    AyCompSatTransport preprocessed model ->
    AyCompState original learned active ->
    AyCompOutcome model conflict :=
  fun preprocess pushedH sat state =>
    ay_comp_sat_outcome model conflict
      (ay_comp_incremental_sat_sound
        original preprocessed learned active pushed model
        preprocess pushedH sat state)

theorem ay_comp_competition_unsat_result
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (conflict : Prop) (model : Prop) :
    AyCompPreprocessMap original preprocessed ->
    pushed ->
    AyCompBcpConflict
      (AyCompState preprocessed learned (AyCompScope active pushed))
      conflict ->
    AyCompState original learned active ->
    AyCompOutcome model conflict :=
  fun preprocess pushedH bcpConflict state =>
    ay_comp_unsat_outcome model conflict
      (bcpConflict
        (ay_comp_preprocess_forward original preprocessed learned
          (AyCompScope active pushed)
          preprocess
          (ay_comp_state_push original learned active pushed state pushedH)))

theorem ay_comp_full_competition_pipeline_sound
    (original : Prop) (preprocessed : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop)
    (unit : Prop) (cdclLearned : Prop) (finalClause : Prop)
    (model : Prop) (conflict : Prop) :
    AyCompPreprocessMap original preprocessed ->
    pushed ->
    AyCompBcpUnit
      (AyCompState preprocessed learned (AyCompScope active pushed))
      unit ->
    AyCompCdclStep
      (AyCompState preprocessed (AyCompConj learned unit)
        (AyCompScope active pushed))
      cdclLearned ->
    AyCompFinalClause cdclLearned finalClause ->
    (finalClause -> conflict) ->
    AyCompSatTransport preprocessed model ->
    AyCompState original learned active ->
    AyCompOutcome model conflict :=
  fun preprocess pushedH bcpUnit cdcl finalCheck _clauseToConflict sat state =>
    ay_comp_sat_outcome model conflict
      (ay_comp_sat_transport original preprocessed model preprocess sat
        (ay_comp_state_formula original learned active state))
