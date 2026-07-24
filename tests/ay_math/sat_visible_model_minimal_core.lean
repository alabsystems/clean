-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal checked visible-model reconstruction skeleton for the SAT branch.
-- The propositions stand for model predicates through preprocessing,
-- incremental assumptions, watched BCP, and solver SAT outcome maps.

def AyVMMConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVMMDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVMMEquisat (before : Prop) (after : Prop) :=
  AyVMMConj (before -> after) (after -> before)

def AyVMMVisibleReconstruction (visible_model : Prop) (original_model : Prop) :=
  visible_model -> original_model

def AyVMMPreprocessModelMap
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :=
  AyVMMConj
    (AyVMMEquisat original_model preprocessed_model)
    (preprocessed_model -> visible_model)

def AyVMMAssumptionScope (active : Prop) (pushed : Prop) :=
  AyVMMConj active pushed

def AyVMMWatchedBcpMap (queue_model : Prop) (unit_model : Prop) :=
  queue_model -> unit_model

def AyVMMSolverSatMap (preprocessed_model : Prop) (visible_model : Prop) :=
  preprocessed_model -> visible_model

def AyVMMMinimalSatOutcome
    (visible_model : Prop) (original_model : Prop) :=
  AyVMMConj
    visible_model
    (AyVMMVisibleReconstruction visible_model original_model)

theorem ay_vmm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVMMConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_vmm_conj_left
    (left : Prop) (right : Prop) :
    AyVMMConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vmm_conj_right
    (left : Prop) (right : Prop) :
    AyVMMConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vmm_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVMMDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_vmm_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVMMDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_vmm_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVMMEquisat before after := by
  intro forward
  intro backward
  exact ay_vmm_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_vmm_equisat_forward
    (before : Prop) (after : Prop) :
    AyVMMEquisat before after -> before -> after := by
  intro certificate
  exact ay_vmm_conj_left (before -> after) (after -> before) certificate

theorem ay_vmm_equisat_backward
    (before : Prop) (after : Prop) :
    AyVMMEquisat before after -> after -> before := by
  intro certificate
  exact ay_vmm_conj_right (before -> after) (after -> before) certificate

theorem ay_vmm_preprocess_equisat
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVMMPreprocessModelMap
      original_model preprocessed_model visible_model ->
    AyVMMEquisat original_model preprocessed_model := by
  intro preprocess
  exact ay_vmm_conj_left
    (AyVMMEquisat original_model preprocessed_model)
    (preprocessed_model -> visible_model)
    preprocess

theorem ay_vmm_preprocess_visible
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVMMPreprocessModelMap
      original_model preprocessed_model visible_model ->
    preprocessed_model ->
    visible_model := by
  intro preprocess
  exact ay_vmm_conj_right
    (AyVMMEquisat original_model preprocessed_model)
    (preprocessed_model -> visible_model)
    preprocess

theorem ay_vmm_reconstruct_original
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVMMPreprocessModelMap
      original_model preprocessed_model visible_model ->
    (visible_model -> preprocessed_model) ->
    AyVMMVisibleReconstruction visible_model original_model := by
  intro preprocess
  intro visible_to_preprocessed
  intro hvisible
  exact ay_vmm_equisat_backward original_model preprocessed_model
    (ay_vmm_preprocess_equisat
      original_model preprocessed_model visible_model preprocess)
    (visible_to_preprocessed hvisible)

theorem ay_vmm_scope_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyVMMAssumptionScope active pushed := by
  intro hactive
  intro hpushed
  exact ay_vmm_conj_intro active pushed hactive hpushed

theorem ay_vmm_scope_active
    (active : Prop) (pushed : Prop) :
    AyVMMAssumptionScope active pushed -> active := by
  intro hscope
  exact ay_vmm_conj_left active pushed hscope

theorem ay_vmm_watched_bcp_sound
    (queue_model : Prop) (unit_model : Prop) :
    AyVMMWatchedBcpMap queue_model unit_model ->
    queue_model ->
    unit_model := by
  intro watched
  intro hqueue
  exact watched hqueue

theorem ay_vmm_solver_sat_sound
    (preprocessed_model : Prop) (visible_model : Prop) :
    AyVMMSolverSatMap preprocessed_model visible_model ->
    preprocessed_model ->
    visible_model := by
  intro solver_sat
  intro hpreprocessed
  exact solver_sat hpreprocessed

theorem ay_vmm_minimal_sat_outcome_intro
    (visible_model : Prop) (original_model : Prop) :
    visible_model ->
    AyVMMVisibleReconstruction visible_model original_model ->
    AyVMMMinimalSatOutcome visible_model original_model := by
  intro hvisible
  intro reconstruct
  exact ay_vmm_conj_intro
    visible_model
    (AyVMMVisibleReconstruction visible_model original_model)
    hvisible
    reconstruct

theorem ay_vmm_minimal_sat_outcome_original
    (visible_model : Prop) (original_model : Prop) :
    AyVMMMinimalSatOutcome visible_model original_model ->
    original_model := by
  intro outcome
  exact outcome original_model
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_vmm_visible_model_through_stack
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop) :
    AyVMMPreprocessModelMap
      original_model preprocessed_model visible_model ->
    AyVMMWatchedBcpMap queue_model unit_model ->
    AyVMMSolverSatMap preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    (visible_model -> preprocessed_model) ->
    active ->
    pushed ->
    queue_model ->
    AyVMMMinimalSatOutcome visible_model original_model := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro visible_to_preprocessed
  intro _hactive
  intro _hpushed
  intro hqueue
  have hunit : unit_model :=
    ay_vmm_watched_bcp_sound queue_model unit_model watched hqueue
  have hvisible : visible_model :=
    ay_vmm_solver_sat_sound preprocessed_model visible_model
      solver_sat
      (unit_to_preprocessed hunit)
  exact ay_vmm_minimal_sat_outcome_intro visible_model original_model
    hvisible
    (ay_vmm_reconstruct_original original_model preprocessed_model
      visible_model preprocess visible_to_preprocessed)

theorem ay_vmm_visible_model_original_sound
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop) :
    AyVMMPreprocessModelMap
      original_model preprocessed_model visible_model ->
    AyVMMWatchedBcpMap queue_model unit_model ->
    AyVMMSolverSatMap preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    (visible_model -> preprocessed_model) ->
    active ->
    pushed ->
    queue_model ->
    original_model := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro visible_to_preprocessed
  intro hactive
  intro hpushed
  intro hqueue
  exact ay_vmm_minimal_sat_outcome_original visible_model original_model
    (ay_vmm_visible_model_through_stack
      original_model preprocessed_model visible_model active pushed
      queue_model unit_model
      preprocess watched solver_sat unit_to_preprocessed
      visible_to_preprocessed hactive hpushed hqueue)
