-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact checked skeleton combining visible-model roundtrip with compressed
-- SAT outcome certificates. Full certificates may carry metadata; compressed
-- certificates retain only visible model plus reconstruction.

def AyVRCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVRCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVRCRoundtrip (before : Prop) (after : Prop) :=
  AyVRCConj (before -> after) (after -> before)

def AyVRCPreprocessRoundtrip
    (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyVRCConj
    (AyVRCRoundtrip original preprocessed)
    (AyVRCRoundtrip preprocessed visible)

def AyVRCWatchedBcp (queue_model : Prop) (unit_model : Prop) :=
  queue_model -> unit_model

def AyVRCSolverSat (preprocessed_model : Prop) (visible_model : Prop) :=
  preprocessed_model -> visible_model

def AyVRCFullSatCertificate
    (visible_model : Prop) (original_model : Prop) (metadata : Prop) :=
  AyVRCConj metadata
    (AyVRCConj visible_model (visible_model -> original_model))

def AyVRCCompressedSatCertificate
    (visible_model : Prop) (original_model : Prop) :=
  AyVRCConj visible_model (visible_model -> original_model)

theorem ay_vrc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVRCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_vrc_conj_left
    (left : Prop) (right : Prop) :
    AyVRCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vrc_conj_right
    (left : Prop) (right : Prop) :
    AyVRCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vrc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVRCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_vrc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVRCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_vrc_roundtrip_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVRCRoundtrip before after := by
  intro forward
  intro backward
  exact ay_vrc_conj_intro (before -> after) (after -> before)
    forward backward

theorem ay_vrc_roundtrip_forward
    (before : Prop) (after : Prop) :
    AyVRCRoundtrip before after -> before -> after := by
  intro roundtrip
  exact ay_vrc_conj_left (before -> after) (after -> before) roundtrip

theorem ay_vrc_roundtrip_backward
    (before : Prop) (after : Prop) :
    AyVRCRoundtrip before after -> after -> before := by
  intro roundtrip
  exact ay_vrc_conj_right (before -> after) (after -> before) roundtrip

theorem ay_vrc_preprocess_internal
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVRCPreprocessRoundtrip original preprocessed visible ->
    AyVRCRoundtrip original preprocessed := by
  intro cert
  exact ay_vrc_conj_left
    (AyVRCRoundtrip original preprocessed)
    (AyVRCRoundtrip preprocessed visible)
    cert

theorem ay_vrc_preprocess_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVRCPreprocessRoundtrip original preprocessed visible ->
    AyVRCRoundtrip preprocessed visible := by
  intro cert
  exact ay_vrc_conj_right
    (AyVRCRoundtrip original preprocessed)
    (AyVRCRoundtrip preprocessed visible)
    cert

theorem ay_vrc_original_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVRCPreprocessRoundtrip original preprocessed visible ->
    original ->
    visible := by
  intro cert
  intro horiginal
  exact ay_vrc_roundtrip_forward preprocessed visible
    (ay_vrc_preprocess_visible original preprocessed visible cert)
    (ay_vrc_roundtrip_forward original preprocessed
      (ay_vrc_preprocess_internal original preprocessed visible cert)
      horiginal)

theorem ay_vrc_visible_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyVRCPreprocessRoundtrip original preprocessed visible ->
    visible ->
    original := by
  intro cert
  intro hvisible
  exact ay_vrc_roundtrip_backward original preprocessed
    (ay_vrc_preprocess_internal original preprocessed visible cert)
    (ay_vrc_roundtrip_backward preprocessed visible
      (ay_vrc_preprocess_visible original preprocessed visible cert)
      hvisible)

theorem ay_vrc_watched_bcp_sound
    (queue_model : Prop) (unit_model : Prop) :
    AyVRCWatchedBcp queue_model unit_model ->
    queue_model ->
    unit_model := by
  intro watched
  intro hqueue
  exact watched hqueue

theorem ay_vrc_solver_sat_sound
    (preprocessed_model : Prop) (visible_model : Prop) :
    AyVRCSolverSat preprocessed_model visible_model ->
    preprocessed_model ->
    visible_model := by
  intro solver_sat
  intro hpreprocessed
  exact solver_sat hpreprocessed

theorem ay_vrc_full_sat_metadata
    (visible_model : Prop) (original_model : Prop) (metadata : Prop) :
    AyVRCFullSatCertificate visible_model original_model metadata ->
    metadata := by
  intro full
  exact ay_vrc_conj_left metadata
    (AyVRCConj visible_model (visible_model -> original_model))
    full

theorem ay_vrc_full_sat_visible
    (visible_model : Prop) (original_model : Prop) (metadata : Prop) :
    AyVRCFullSatCertificate visible_model original_model metadata ->
    visible_model := by
  intro full
  exact ay_vrc_conj_left visible_model
    (visible_model -> original_model)
    (ay_vrc_conj_right metadata
      (AyVRCConj visible_model (visible_model -> original_model))
      full)

theorem ay_vrc_full_sat_reconstruct
    (visible_model : Prop) (original_model : Prop) (metadata : Prop) :
    AyVRCFullSatCertificate visible_model original_model metadata ->
    visible_model -> original_model := by
  intro full
  exact ay_vrc_conj_right visible_model
    (visible_model -> original_model)
    (ay_vrc_conj_right metadata
      (AyVRCConj visible_model (visible_model -> original_model))
      full)

theorem ay_vrc_compress_sat_certificate
    (visible_model : Prop) (original_model : Prop) (metadata : Prop) :
    AyVRCFullSatCertificate visible_model original_model metadata ->
    AyVRCCompressedSatCertificate visible_model original_model := by
  intro full
  exact ay_vrc_conj_intro visible_model
    (visible_model -> original_model)
    (ay_vrc_full_sat_visible visible_model original_model metadata full)
    (ay_vrc_full_sat_reconstruct visible_model original_model metadata full)

theorem ay_vrc_compressed_sat_original
    (visible_model : Prop) (original_model : Prop) :
    AyVRCCompressedSatCertificate visible_model original_model ->
    original_model := by
  intro compressed
  exact compressed original_model
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_vrc_build_full_sat_from_roundtrip
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (queue_model : Prop) (unit_model : Prop)
    (metadata : Prop) :
    AyVRCPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVRCWatchedBcp queue_model unit_model ->
    AyVRCSolverSat preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    metadata ->
    queue_model ->
    AyVRCFullSatCertificate visible_model original_model metadata := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro hmetadata
  intro hqueue
  have hvisible : visible_model :=
    ay_vrc_solver_sat_sound preprocessed_model visible_model
      solver_sat
      (unit_to_preprocessed
        (ay_vrc_watched_bcp_sound queue_model unit_model watched hqueue))
  exact ay_vrc_conj_intro metadata
    (AyVRCConj visible_model (visible_model -> original_model))
    hmetadata
    (ay_vrc_conj_intro visible_model
      (visible_model -> original_model)
      hvisible
      (ay_vrc_visible_to_original
        original_model preprocessed_model visible_model preprocess))

theorem ay_vrc_compressed_roundtrip_original_sound
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) (queue_model : Prop) (unit_model : Prop)
    (metadata : Prop) :
    AyVRCPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVRCWatchedBcp queue_model unit_model ->
    AyVRCSolverSat preprocessed_model visible_model ->
    (unit_model -> preprocessed_model) ->
    metadata ->
    queue_model ->
    original_model := by
  intro preprocess
  intro watched
  intro solver_sat
  intro unit_to_preprocessed
  intro hmetadata
  intro hqueue
  exact ay_vrc_compressed_sat_original visible_model original_model
    (ay_vrc_compress_sat_certificate visible_model original_model metadata
      (ay_vrc_build_full_sat_from_roundtrip
        original_model preprocessed_model visible_model
        queue_model unit_model metadata
        preprocess watched solver_sat unit_to_preprocessed
        hmetadata hqueue))
