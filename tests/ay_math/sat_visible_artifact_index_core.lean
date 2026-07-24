-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific artifact-index skeleton for visible model certificates.
-- Index ids, lookups, stored artifacts, preprocessing roundtrips, and
-- compressed SAT certificates are represented propositionally.

def AyVAIConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVAIDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVAIRoundtrip (before : Prop) (after : Prop) :=
  AyVAIConj (before -> after) (after -> before)

def AyVAIPreprocessRoundtrip
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :=
  AyVAIConj
    (AyVAIRoundtrip original_model preprocessed_model)
    (AyVAIRoundtrip preprocessed_model visible_model)

def AyVAIArtifactLookup (index_id : Prop) (artifact : Prop) :=
  index_id -> artifact

def AyVAIArtifactProjection
    (artifact : Prop) (visible_model : Prop) :=
  artifact -> visible_model

def AyVAIArtifactReconstruction
    (visible_model : Prop) (original_model : Prop) :=
  visible_model -> original_model

def AyVAIVisibleArtifactIndex
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :=
  AyVAIConj
    (AyVAIArtifactLookup index_id artifact)
    (AyVAIConj
      (AyVAIArtifactProjection artifact visible_model)
      (AyVAIArtifactReconstruction visible_model original_model))

def AyVAICompressedVisibleCertificate
    (index_id : Prop) (visible_model : Prop) (original_model : Prop) :=
  AyVAIConj index_id
    (AyVAIConj visible_model
      (AyVAIArtifactReconstruction visible_model original_model))

theorem ay_vai_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVAIConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_vai_conj_left
    (left : Prop) (right : Prop) :
    AyVAIConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vai_conj_right
    (left : Prop) (right : Prop) :
    AyVAIConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vai_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVAIDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_vai_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVAIDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_vai_roundtrip_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVAIRoundtrip before after := by
  intro forward
  intro backward
  exact ay_vai_conj_intro (before -> after) (after -> before)
    forward backward

theorem ay_vai_roundtrip_forward
    (before : Prop) (after : Prop) :
    AyVAIRoundtrip before after -> before -> after := by
  intro roundtrip
  exact ay_vai_conj_left (before -> after) (after -> before) roundtrip

theorem ay_vai_roundtrip_backward
    (before : Prop) (after : Prop) :
    AyVAIRoundtrip before after -> after -> before := by
  intro roundtrip
  exact ay_vai_conj_right (before -> after) (after -> before) roundtrip

theorem ay_vai_preprocess_internal_roundtrip
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVAIPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVAIRoundtrip original_model preprocessed_model := by
  intro preprocess
  exact ay_vai_conj_left
    (AyVAIRoundtrip original_model preprocessed_model)
    (AyVAIRoundtrip preprocessed_model visible_model)
    preprocess

theorem ay_vai_preprocess_visible_roundtrip
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVAIPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVAIRoundtrip preprocessed_model visible_model := by
  intro preprocess
  exact ay_vai_conj_right
    (AyVAIRoundtrip original_model preprocessed_model)
    (AyVAIRoundtrip preprocessed_model visible_model)
    preprocess

theorem ay_vai_visible_to_original_from_preprocess
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVAIPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    visible_model ->
    original_model := by
  intro preprocess
  intro hvisible
  exact ay_vai_roundtrip_backward original_model preprocessed_model
    (ay_vai_preprocess_internal_roundtrip
      original_model preprocessed_model visible_model preprocess)
    (ay_vai_roundtrip_backward preprocessed_model visible_model
      (ay_vai_preprocess_visible_roundtrip
        original_model preprocessed_model visible_model preprocess)
      hvisible)

theorem ay_vai_index_lookup
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    AyVAIArtifactLookup index_id artifact := by
  intro index
  exact ay_vai_conj_left
    (AyVAIArtifactLookup index_id artifact)
    (AyVAIConj
      (AyVAIArtifactProjection artifact visible_model)
      (AyVAIArtifactReconstruction visible_model original_model))
    index

theorem ay_vai_index_projection
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    AyVAIArtifactProjection artifact visible_model := by
  intro index
  exact ay_vai_conj_left
    (AyVAIArtifactProjection artifact visible_model)
    (AyVAIArtifactReconstruction visible_model original_model)
    (ay_vai_conj_right
      (AyVAIArtifactLookup index_id artifact)
      (AyVAIConj
        (AyVAIArtifactProjection artifact visible_model)
        (AyVAIArtifactReconstruction visible_model original_model))
      index)

theorem ay_vai_index_reconstruction
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    AyVAIArtifactReconstruction visible_model original_model := by
  intro index
  exact ay_vai_conj_right
    (AyVAIArtifactProjection artifact visible_model)
    (AyVAIArtifactReconstruction visible_model original_model)
    (ay_vai_conj_right
      (AyVAIArtifactLookup index_id artifact)
      (AyVAIConj
        (AyVAIArtifactProjection artifact visible_model)
        (AyVAIArtifactReconstruction visible_model original_model))
      index)

theorem ay_vai_lookup_projects_visible
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    index_id ->
    visible_model := by
  intro index
  intro hid
  exact ay_vai_index_projection
    index_id artifact visible_model original_model index
    (ay_vai_index_lookup
      index_id artifact visible_model original_model index hid)

theorem ay_vai_indexed_artifact_reconstructs_original
    (index_id : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    index_id ->
    original_model := by
  intro index
  intro hid
  exact ay_vai_index_reconstruction
    index_id artifact visible_model original_model index
    (ay_vai_lookup_projects_visible
      index_id artifact visible_model original_model index hid)

theorem ay_vai_compressed_certificate_intro
    (index_id : Prop) (visible_model : Prop) (original_model : Prop) :
    index_id ->
    visible_model ->
    AyVAIArtifactReconstruction visible_model original_model ->
    AyVAICompressedVisibleCertificate
      index_id visible_model original_model := by
  intro hid
  intro hvisible
  intro reconstruct
  exact ay_vai_conj_intro index_id
    (AyVAIConj visible_model
      (AyVAIArtifactReconstruction visible_model original_model))
    hid
    (ay_vai_conj_intro visible_model
      (AyVAIArtifactReconstruction visible_model original_model)
      hvisible
      reconstruct)

theorem ay_vai_compressed_certificate_visible
    (index_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVAICompressedVisibleCertificate
      index_id visible_model original_model ->
    visible_model := by
  intro cert
  exact ay_vai_conj_left visible_model
    (AyVAIArtifactReconstruction visible_model original_model)
    (ay_vai_conj_right index_id
      (AyVAIConj visible_model
        (AyVAIArtifactReconstruction visible_model original_model))
      cert)

theorem ay_vai_compressed_certificate_reconstruction
    (index_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVAICompressedVisibleCertificate
      index_id visible_model original_model ->
    AyVAIArtifactReconstruction visible_model original_model := by
  intro cert
  exact ay_vai_conj_right visible_model
    (AyVAIArtifactReconstruction visible_model original_model)
    (ay_vai_conj_right index_id
      (AyVAIConj visible_model
        (AyVAIArtifactReconstruction visible_model original_model))
      cert)

theorem ay_vai_compressed_certificate_original
    (index_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVAICompressedVisibleCertificate
      index_id visible_model original_model ->
    original_model := by
  intro cert
  exact ay_vai_compressed_certificate_reconstruction
    index_id visible_model original_model cert
    (ay_vai_compressed_certificate_visible
      index_id visible_model original_model cert)

theorem ay_vai_indexed_compressed_certificate
    (index_id : Prop) (artifact : Prop)
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVAIPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    index_id ->
    AyVAICompressedVisibleCertificate
      index_id visible_model original_model := by
  intro preprocess
  intro index
  intro hid
  have hvisible : visible_model :=
    ay_vai_lookup_projects_visible
      index_id artifact visible_model original_model index hid
  exact ay_vai_compressed_certificate_intro
    index_id visible_model original_model
    hid
    hvisible
    (ay_vai_visible_to_original_from_preprocess
      original_model preprocessed_model visible_model preprocess)

theorem ay_vai_indexed_compressed_reconstructs_original
    (index_id : Prop) (artifact : Prop)
    (original_model : Prop) (preprocessed_model : Prop)
    (visible_model : Prop) :
    AyVAIPreprocessRoundtrip
      original_model preprocessed_model visible_model ->
    AyVAIVisibleArtifactIndex
      index_id artifact visible_model original_model ->
    index_id ->
    original_model := by
  intro preprocess
  intro index
  intro hid
  exact ay_vai_compressed_certificate_original
    index_id visible_model original_model
    (ay_vai_indexed_compressed_certificate
      index_id artifact original_model preprocessed_model visible_model
      preprocess index hid)
