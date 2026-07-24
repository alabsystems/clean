-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton focused on visible-variable model
-- reconstruction through the SAT stack: preprocessing, incremental
-- assumptions, watched BCP, solver-loop SAT, and final original model output.

def AyFSVMConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFSVMDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFSVMEquisat (before : Prop) (after : Prop) :=
  AyFSVMConj (before -> after) (after -> before)

def AyFSVMVisibleMap (internal : Prop) (visible : Prop) :=
  AyFSVMConj (internal -> visible) (visible -> internal)

def AyFSVMPreprocessCertificate
    (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyFSVMConj
    (AyFSVMEquisat original preprocessed)
    (AyFSVMVisibleMap preprocessed visible)

def AyFSVMScope (active : Prop) (pushed : Prop) :=
  AyFSVMConj active pushed

def AyFSVMWatchedBcp (queue_model : Prop) (unit_model : Prop) :=
  queue_model -> unit_model

def AyFSVMSolverSat (formula_model : Prop) (visible_model : Prop) :=
  formula_model -> visible_model

def AyFSVMStackState
    (formula_model : Prop) (assumptions : Prop) (bcp_model : Prop) :=
  AyFSVMConj formula_model (AyFSVMConj assumptions bcp_model)

def AyFSVMSatOutcome (visible_model : Prop) (original_model : Prop) :=
  AyFSVMConj visible_model original_model

theorem ay_fsvm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFSVMConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_fsvm_conj_left
    (left : Prop) (right : Prop) :
    AyFSVMConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_fsvm_conj_right
    (left : Prop) (right : Prop) :
    AyFSVMConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_fsvm_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFSVMDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_fsvm_disj_right
    (left : Prop) (right : Prop) :
    right -> AyFSVMDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_fsvm_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFSVMEquisat before after := by
  intro forward
  intro backward
  exact ay_fsvm_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_fsvm_equisat_forward
    (before : Prop) (after : Prop) :
    AyFSVMEquisat before after -> before -> after := by
  intro certificate
  exact ay_fsvm_conj_left (before -> after) (after -> before) certificate

theorem ay_fsvm_equisat_backward
    (before : Prop) (after : Prop) :
    AyFSVMEquisat before after -> after -> before := by
  intro certificate
  exact ay_fsvm_conj_right (before -> after) (after -> before) certificate

theorem ay_fsvm_visible_map_intro
    (internal : Prop) (visible : Prop) :
    (internal -> visible) ->
    (visible -> internal) ->
    AyFSVMVisibleMap internal visible := by
  intro project
  intro reconstruct
  exact ay_fsvm_conj_intro
    (internal -> visible)
    (visible -> internal)
    project
    reconstruct

theorem ay_fsvm_visible_project
    (internal : Prop) (visible : Prop) :
    AyFSVMVisibleMap internal visible -> internal -> visible := by
  intro visible_map
  exact ay_fsvm_conj_left (internal -> visible) (visible -> internal)
    visible_map

theorem ay_fsvm_visible_reconstruct
    (internal : Prop) (visible : Prop) :
    AyFSVMVisibleMap internal visible -> visible -> internal := by
  intro visible_map
  exact ay_fsvm_conj_right (internal -> visible) (visible -> internal)
    visible_map

theorem ay_fsvm_preprocess_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    AyFSVMEquisat original preprocessed := by
  intro certificate
  exact ay_fsvm_conj_left
    (AyFSVMEquisat original preprocessed)
    (AyFSVMVisibleMap preprocessed visible)
    certificate

theorem ay_fsvm_preprocess_visible_map
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    AyFSVMVisibleMap preprocessed visible := by
  intro certificate
  exact ay_fsvm_conj_right
    (AyFSVMEquisat original preprocessed)
    (AyFSVMVisibleMap preprocessed visible)
    certificate

theorem ay_fsvm_preprocess_visible_from_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    original ->
    visible := by
  intro certificate
  intro horiginal
  exact ay_fsvm_visible_project preprocessed visible
    (ay_fsvm_preprocess_visible_map original preprocessed visible certificate)
    (ay_fsvm_equisat_forward original preprocessed
      (ay_fsvm_preprocess_equisat original preprocessed visible certificate)
      horiginal)

theorem ay_fsvm_original_from_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    visible ->
    original := by
  intro certificate
  intro hvisible
  exact ay_fsvm_equisat_backward original preprocessed
    (ay_fsvm_preprocess_equisat original preprocessed visible certificate)
    (ay_fsvm_visible_reconstruct preprocessed visible
      (ay_fsvm_preprocess_visible_map original preprocessed visible certificate)
      hvisible)

theorem ay_fsvm_scope_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyFSVMScope active pushed := by
  intro hactive
  intro hpushed
  exact ay_fsvm_conj_intro active pushed hactive hpushed

theorem ay_fsvm_scope_active
    (active : Prop) (pushed : Prop) :
    AyFSVMScope active pushed -> active := by
  intro hscope
  exact ay_fsvm_conj_left active pushed hscope

theorem ay_fsvm_stack_state_intro
    (formula_model : Prop) (assumptions : Prop) (bcp_model : Prop) :
    formula_model -> assumptions -> bcp_model ->
    AyFSVMStackState formula_model assumptions bcp_model := by
  intro hformula
  intro hassumptions
  intro hbcp
  exact ay_fsvm_conj_intro formula_model
    (AyFSVMConj assumptions bcp_model)
    hformula
    (ay_fsvm_conj_intro assumptions bcp_model hassumptions hbcp)

theorem ay_fsvm_stack_formula_model
    (formula_model : Prop) (assumptions : Prop) (bcp_model : Prop) :
    AyFSVMStackState formula_model assumptions bcp_model ->
    formula_model := by
  intro state
  exact ay_fsvm_conj_left formula_model
    (AyFSVMConj assumptions bcp_model)
    state

theorem ay_fsvm_stack_assumptions
    (formula_model : Prop) (assumptions : Prop) (bcp_model : Prop) :
    AyFSVMStackState formula_model assumptions bcp_model ->
    assumptions := by
  intro state
  exact ay_fsvm_conj_left assumptions bcp_model
    (ay_fsvm_conj_right formula_model
      (AyFSVMConj assumptions bcp_model)
      state)

theorem ay_fsvm_stack_bcp_model
    (formula_model : Prop) (assumptions : Prop) (bcp_model : Prop) :
    AyFSVMStackState formula_model assumptions bcp_model ->
    bcp_model := by
  intro state
  exact ay_fsvm_conj_right assumptions bcp_model
    (ay_fsvm_conj_right formula_model
      (AyFSVMConj assumptions bcp_model)
      state)

theorem ay_fsvm_watched_bcp_model
    (queue_model : Prop) (unit_model : Prop) :
    AyFSVMWatchedBcp queue_model unit_model ->
    queue_model ->
    unit_model := by
  intro watched
  intro hqueue
  exact watched hqueue

theorem ay_fsvm_stack_after_watched_bcp
    (formula_model : Prop) (assumptions : Prop)
    (queue_model : Prop) (unit_model : Prop) :
    AyFSVMWatchedBcp queue_model unit_model ->
    formula_model ->
    assumptions ->
    queue_model ->
    AyFSVMStackState formula_model assumptions unit_model := by
  intro watched
  intro hformula
  intro hassumptions
  intro hqueue
  exact ay_fsvm_stack_state_intro formula_model assumptions unit_model
    hformula
    hassumptions
    (ay_fsvm_watched_bcp_model queue_model unit_model watched hqueue)

theorem ay_fsvm_solver_sat_visible
    (formula_model : Prop) (visible_model : Prop) :
    AyFSVMSolverSat formula_model visible_model ->
    formula_model ->
    visible_model := by
  intro solver_sat
  intro hformula
  exact solver_sat hformula

theorem ay_fsvm_solver_sat_from_stack
    (formula_model : Prop) (assumptions : Prop)
    (bcp_model : Prop) (visible_model : Prop) :
    AyFSVMSolverSat formula_model visible_model ->
    AyFSVMStackState formula_model assumptions bcp_model ->
    visible_model := by
  intro solver_sat
  intro state
  exact solver_sat
    (ay_fsvm_stack_formula_model formula_model assumptions bcp_model state)

theorem ay_fsvm_sat_outcome_intro
    (visible_model : Prop) (original_model : Prop) :
    visible_model ->
    original_model ->
    AyFSVMSatOutcome visible_model original_model := by
  intro hvisible
  intro horiginal
  exact ay_fsvm_conj_intro visible_model original_model hvisible horiginal

theorem ay_fsvm_sat_outcome_visible
    (visible_model : Prop) (original_model : Prop) :
    AyFSVMSatOutcome visible_model original_model -> visible_model := by
  intro outcome
  exact ay_fsvm_conj_left visible_model original_model outcome

theorem ay_fsvm_sat_outcome_original
    (visible_model : Prop) (original_model : Prop) :
    AyFSVMSatOutcome visible_model original_model -> original_model := by
  intro outcome
  exact ay_fsvm_conj_right visible_model original_model outcome

theorem ay_fsvm_visible_model_reconstruct_through_stack
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop)
    (visible_model : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    AyFSVMWatchedBcp queue_model unit_model ->
    AyFSVMSolverSat preprocessed visible_model ->
    (visible_model -> visible) ->
    original ->
    active ->
    pushed ->
    queue_model ->
    AyFSVMSatOutcome visible_model original := by
  intro preprocess
  intro watched
  intro solver_sat
  intro visible_to_certificate_visible
  intro horiginal
  intro hactive
  intro hpushed
  intro hqueue
  have hpreprocessed : preprocessed :=
    ay_fsvm_equisat_forward original preprocessed
      (ay_fsvm_preprocess_equisat original preprocessed visible preprocess)
      horiginal
  have hstate :
      AyFSVMStackState preprocessed (AyFSVMScope active pushed) unit_model :=
    ay_fsvm_stack_after_watched_bcp preprocessed
      (AyFSVMScope active pushed)
      queue_model
      unit_model
      watched
      hpreprocessed
      (ay_fsvm_scope_intro active pushed hactive hpushed)
      hqueue
  have hvisible_model : visible_model :=
    ay_fsvm_solver_sat_from_stack preprocessed
      (AyFSVMScope active pushed)
      unit_model
      visible_model
      solver_sat
      hstate
  exact ay_fsvm_sat_outcome_intro visible_model original
    hvisible_model
    (ay_fsvm_original_from_visible original preprocessed visible
      preprocess
      (visible_to_certificate_visible hvisible_model))

theorem ay_fsvm_solver_visible_model_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop)
    (visible_model : Prop) :
    AyFSVMPreprocessCertificate original preprocessed visible ->
    AyFSVMWatchedBcp queue_model unit_model ->
    AyFSVMSolverSat preprocessed visible_model ->
    (visible_model -> visible) ->
    original ->
    active ->
    pushed ->
    queue_model ->
    original := by
  intro preprocess
  intro watched
  intro solver_sat
  intro visible_to_certificate_visible
  intro horiginal
  intro hactive
  intro hpushed
  intro hqueue
  exact ay_fsvm_sat_outcome_original visible_model original
    (ay_fsvm_visible_model_reconstruct_through_stack
      original preprocessed visible active pushed queue_model unit_model
      visible_model
      preprocess watched solver_sat visible_to_certificate_visible
      horiginal hactive hpushed hqueue)
