-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact checked visible-model roundtrip skeleton across preprocessing,
-- watched BCP, incremental assumptions, and solver SAT outcome.

def AyVMRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVMRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVMREquisat (before : Prop) (after : Prop) :=
  AyVMRConj (before -> after) (after -> before)

def AyVMRRoundtrip (before : Prop) (after : Prop) :=
  AyVMRConj (before -> after) (after -> before)

def AyVMRPreprocessRoundtrip
    (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyVMRConj
    (AyVMREquisat original preprocessed)
    (AyVMRRoundtrip preprocessed visible)

def AyVMRAssumptionScope (active : Prop) (pushed : Prop) :=
  AyVMRConj active pushed

def AyVMRWatchedBcp (queue_model : Prop) (unit_model : Prop) :=
  queue_model -> unit_model

def AyVMRSolverSat (preprocessed_model : Prop) (visible_model : Prop) :=
  preprocessed_model -> visible_model

def AyVMRSatRoundtripOutcome
    (original_model : Prop) (visible_model : Prop) :=
  AyVMRConj visible_model (visible_model -> original_model)

theorem ay_vmr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVMRConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_vmr_conj_left
    (left : Prop) (right : Prop) :
    AyVMRConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vmr_conj_right
    (left : Prop) (right : Prop) :
    AyVMRConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vmr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVMRDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_vmr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVMRDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_vmr_roundtrip_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVMRRoundtrip before after := by
  intro forward
  intro backward
  exact ay_vmr_conj_intro (before -> after) (after -> before)
    forward backward

theorem ay_vmr_roundtrip_forward
    (before : Prop) (after : Prop) :
    AyVMRRoundtrip before after -> before -> after := by
  intro roundtrip
  exact ay_vmr_conj_left (before -> after) (after -> before) roundtrip

theorem ay_vmr_roundtrip_backward
    (before : Prop) (after : Prop) :
    AyVMRRoundtrip before after -> after -> before := by
  intro roundtrip
  exact ay_vmr_conj_right (before -> after) (after -> before) roundtrip

theorem ay_vmr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVMREquisat before after := by
  intro forward
  intro backward
  exact ay_vmr_roundtrip_intro before after forward backward

theorem ay_vmr_equisat_forward
    (before : Prop) (after : Prop) :
    AyVMREquisat before after -> before -> after := by
  intro certificate
  exact ay_vmr_roundtrip_forward before after certificate

theorem ay_vmr_equisat_backward
    (before : Prop) (after : Prop) :
    AyVMREquisat before after -> after -> before := by
  intro certificate
  exact ay_vmr_roundtrip_backward before after certificate

theorem ay_vmr_preprocess_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVMRPreprocessRoundtrip original preprocessed visible ->
    AyVMREquisat original preprocessed := by
  intro cert
  exact ay_vmr_conj_left
    (AyVMREquisat original preprocessed)
    (AyVMRRoundtrip preprocessed visible)
    cert

theorem ay_vmr_preprocess_visible_roundtrip
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVMRPreprocessRoundtrip original preprocessed visible ->
    AyVMRRoundtrip preprocessed visible := by
  intro cert
  exact ay_vmr_conj_right
    (AyVMREquisat original preprocessed)
    (AyVMRRoundtrip preprocessed visible)
    cert

theorem ay_vmr_original_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVMRPreprocessRoundtrip original preprocessed visible ->
    original ->
    visible := by
  intro cert
  intro horiginal
  exact ay_vmr_roundtrip_forward preprocessed visible
    (ay_vmr_preprocess_visible_roundtrip original preprocessed visible cert)
    (ay_vmr_equisat_forward original preprocessed
      (ay_vmr_preprocess_equisat original preprocessed visible cert)
      horiginal)

theorem ay_vmr_visible_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVMRPreprocessRoundtrip original preprocessed visible ->
    visible ->
    original := by
  intro cert
  intro hvisible
  exact ay_vmr_equisat_backward original preprocessed
    (ay_vmr_preprocess_equisat original preprocessed visible cert)
    (ay_vmr_roundtrip_backward preprocessed visible
      (ay_vmr_preprocess_visible_roundtrip original preprocessed visible cert)
      hvisible)

theorem ay_vmr_scope_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyVMRAssumptionScope active pushed := by
  intro hactive
  intro hpushed
  exact ay_vmr_conj_intro active pushed hactive hpushed

theorem ay_vmr_scope_active
    (active : Prop) (pushed : Prop) :
    AyVMRAssumptionScope active pushed -> active := by
  intro hscope
  exact ay_vmr_conj_left active pushed hscope

theorem ay_vmr_watched_bcp_sound
    (queue_model : Prop) (unit_model : Prop) :
    AyVMRWatchedBcp queue_model unit_model ->
    queue_model ->
    unit_model := by
  intro watched
  intro hqueue
  exact watched hqueue

theorem ay_vmr_solver_sat_sound
    (preprocessed_model : Prop) (visible_model : Prop) :
    AyVMRSolverSat preprocessed_model visible_model ->
    preprocessed_model ->
    visible_model := by
  intro solver_sat
  intro hpreprocessed
  exact solver_sat hpreprocessed

theorem ay_vmr_sat_roundtrip_outcome_intro
    (original_model : Prop) (visible_model : Prop) :
    visible_model ->
    (visible_model -> original_model) ->
    AyVMRSatRoundtripOutcome original_model visible_model := by
  intro hvisible
  intro reconstruct
  exact ay_vmr_conj_intro visible_model
    (visible_model -> original_model)
    hvisible
    reconstruct

theorem ay_vmr_sat_roundtrip_original
    (original_model : Prop) (visible_model : Prop) :
    AyVMRSatRoundtripOutcome original_model visible_model ->
    original_model := by
  intro outcome
  exact outcome original_model
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_vmr_visible_roundtrip_through_stack
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop) :
    AyVMRPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVMRWatchedBcp queue_model unit_model ->
    AyVMRSolverSat preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    active ->
    pushed ->
    queue_model ->
    AyVMRSatRoundtripOutcome original_model visible_model := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro _hactive
  intro _hpushed
  intro hqueue
  have hpreprocessed : preprocessed_model :=
    unit_to_preprocessed
      (ay_vmr_watched_bcp_sound queue_model unit_model watched hqueue)
  have hvisible : visible_model :=
    ay_vmr_solver_sat_sound preprocessed_model visible_model
      solver_sat hpreprocessed
  exact ay_vmr_sat_roundtrip_outcome_intro original_model visible_model
    hvisible
    (ay_vmr_visible_to_original
      original_model preprocessed_model visible_model preprocess)

theorem ay_vmr_visible_roundtrip_original_sound
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (active : Prop) (pushed : Prop)
    (queue_model : Prop) (unit_model : Prop) :
    AyVMRPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVMRWatchedBcp queue_model unit_model ->
    AyVMRSolverSat preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    active ->
    pushed ->
    queue_model ->
    original_model := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro hactive
  intro hpushed
  intro hqueue
  exact ay_vmr_sat_roundtrip_original original_model visible_model
    (ay_vmr_visible_roundtrip_through_stack
      original_model preprocessed_model visible_model active pushed
      queue_model unit_model
      preprocess watched solver_sat unit_to_preprocessed
      hactive hpushed hqueue)
