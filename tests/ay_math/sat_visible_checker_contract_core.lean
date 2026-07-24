-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific contract for visible model certificates emitted by ay.
-- Assignment artifacts, visible-CNF checker acceptance, indexed preprocessing
-- reconstruction, and compressed public SAT certificates are propositions.

def AyVCCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVCCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVCCEquisat (before : Prop) (after : Prop) :=
  AyVCCConj (before -> after) (after -> before)

def AyVCCAssignmentProjection
    (assignment_artifact : Prop) (visible_model : Prop) :=
  assignment_artifact -> visible_model

def AyVCCCheckerValidation
    (visible_cnf : Prop) (visible_model : Prop) :=
  visible_cnf -> visible_model

def AyVCCPreprocessArtifact
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :=
  AyVCCConj artifact_id (visible_model -> original_model)

def AyVCCIndexedReconstruction
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :=
  artifact_id -> visible_model -> original_model

def AyVCCCompressedSatCertificate
    (visible_model : Prop) (original_model : Prop) :=
  AyVCCConj visible_model (visible_model -> original_model)

def AyVCCCheckerAcceptance
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (visible_model : Prop) :=
  AyVCCConj
    (AyVCCAssignmentProjection assignment_artifact visible_model)
    (AyVCCCheckerValidation visible_cnf visible_model)

def AyVCCPublicSatAnswer (original_model : Prop) :=
  original_model

theorem ay_vcc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVCCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_vcc_conj_left
    (left : Prop) (right : Prop) :
    AyVCCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_vcc_conj_right
    (left : Prop) (right : Prop) :
    AyVCCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_vcc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVCCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_vcc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVCCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_vcc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVCCEquisat before after := by
  intro forward
  intro backward
  exact ay_vcc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_vcc_equisat_forward
    (before : Prop) (after : Prop) :
    AyVCCEquisat before after -> before -> after := by
  intro certificate
  exact ay_vcc_conj_left (before -> after) (after -> before) certificate

theorem ay_vcc_equisat_backward
    (before : Prop) (after : Prop) :
    AyVCCEquisat before after -> after -> before := by
  intro certificate
  exact ay_vcc_conj_right (before -> after) (after -> before) certificate

theorem ay_vcc_assignment_projects_visible
    (assignment_artifact : Prop) (visible_model : Prop) :
    AyVCCAssignmentProjection assignment_artifact visible_model ->
    assignment_artifact ->
    visible_model := by
  intro project
  intro hartifact
  exact project hartifact

theorem ay_vcc_checker_accepts_visible
    (visible_cnf : Prop) (visible_model : Prop) :
    AyVCCCheckerValidation visible_cnf visible_model ->
    visible_cnf ->
    visible_model := by
  intro validate
  intro hvisible_cnf
  exact validate hvisible_cnf

theorem ay_vcc_checker_acceptance_projection
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (visible_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    AyVCCAssignmentProjection assignment_artifact visible_model := by
  intro acceptance
  exact ay_vcc_conj_left
    (AyVCCAssignmentProjection assignment_artifact visible_model)
    (AyVCCCheckerValidation visible_cnf visible_model)
    acceptance

theorem ay_vcc_checker_acceptance_validation
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (visible_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    AyVCCCheckerValidation visible_cnf visible_model := by
  intro acceptance
  exact ay_vcc_conj_right
    (AyVCCAssignmentProjection assignment_artifact visible_model)
    (AyVCCCheckerValidation visible_cnf visible_model)
    acceptance

theorem ay_vcc_checker_acceptance_roundtrip
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (visible_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    (visible_model -> assignment_artifact) ->
    AyVCCEquisat assignment_artifact visible_model := by
  intro acceptance
  intro reconstruct_assignment
  exact ay_vcc_equisat_intro assignment_artifact visible_model
    (ay_vcc_checker_acceptance_projection
      assignment_artifact visible_cnf visible_model acceptance)
    reconstruct_assignment

theorem ay_vcc_preprocess_artifact_id
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCPreprocessArtifact artifact_id visible_model original_model ->
    artifact_id := by
  intro artifact
  exact ay_vcc_conj_left artifact_id
    (visible_model -> original_model)
    artifact

theorem ay_vcc_preprocess_artifact_reconstruct
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCPreprocessArtifact artifact_id visible_model original_model ->
    visible_model ->
    original_model := by
  intro artifact
  exact ay_vcc_conj_right artifact_id
    (visible_model -> original_model)
    artifact

theorem ay_vcc_indexed_reconstruction_from_artifact
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCPreprocessArtifact artifact_id visible_model original_model ->
    AyVCCIndexedReconstruction
      artifact_id visible_model original_model := by
  intro artifact
  intro _hid
  exact ay_vcc_preprocess_artifact_reconstruct
    artifact_id visible_model original_model artifact

theorem ay_vcc_reconstruct_original_from_index
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCIndexedReconstruction
      artifact_id visible_model original_model ->
    artifact_id ->
    visible_model ->
    original_model := by
  intro reconstruct
  intro hid
  intro hvisible
  exact reconstruct hid hvisible

theorem ay_vcc_compressed_certificate_intro
    (visible_model : Prop) (original_model : Prop) :
    visible_model ->
    (visible_model -> original_model) ->
    AyVCCCompressedSatCertificate visible_model original_model := by
  intro hvisible
  intro reconstruct
  exact ay_vcc_conj_intro visible_model
    (visible_model -> original_model)
    hvisible
    reconstruct

theorem ay_vcc_compressed_certificate_visible
    (visible_model : Prop) (original_model : Prop) :
    AyVCCCompressedSatCertificate visible_model original_model ->
    visible_model := by
  intro cert
  exact ay_vcc_conj_left visible_model
    (visible_model -> original_model)
    cert

theorem ay_vcc_compressed_certificate_reconstruction
    (visible_model : Prop) (original_model : Prop) :
    AyVCCCompressedSatCertificate visible_model original_model ->
    visible_model -> original_model := by
  intro cert
  exact ay_vcc_conj_right visible_model
    (visible_model -> original_model)
    cert

theorem ay_vcc_compressed_certificate_original
    (visible_model : Prop) (original_model : Prop) :
    AyVCCCompressedSatCertificate visible_model original_model ->
    original_model := by
  intro cert
  exact ay_vcc_compressed_certificate_reconstruction
    visible_model original_model cert
    (ay_vcc_compressed_certificate_visible visible_model original_model cert)

theorem ay_vcc_checker_builds_compressed_certificate
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    AyVCCIndexedReconstruction
      artifact_id visible_model original_model ->
    assignment_artifact ->
    artifact_id ->
    AyVCCCompressedSatCertificate visible_model original_model := by
  intro acceptance
  intro reconstruct
  intro hartifact
  intro hid
  have hvisible : visible_model :=
    ay_vcc_assignment_projects_visible assignment_artifact visible_model
      (ay_vcc_checker_acceptance_projection
        assignment_artifact visible_cnf visible_model acceptance)
      hartifact
  exact ay_vcc_compressed_certificate_intro visible_model original_model
    hvisible
    (ay_vcc_reconstruct_original_from_index
      artifact_id visible_model original_model reconstruct hid)

theorem ay_vcc_public_sat_answer_sound
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    AyVCCPreprocessArtifact artifact_id visible_model original_model ->
    assignment_artifact ->
    AyVCCPublicSatAnswer original_model := by
  intro acceptance
  intro artifact
  intro hartifact
  exact ay_vcc_compressed_certificate_original visible_model original_model
    (ay_vcc_checker_builds_compressed_certificate
      assignment_artifact visible_cnf artifact_id visible_model original_model
      acceptance
      (ay_vcc_indexed_reconstruction_from_artifact
        artifact_id visible_model original_model artifact)
      hartifact
      (ay_vcc_preprocess_artifact_id
        artifact_id visible_model original_model artifact))

theorem ay_vcc_checker_validation_public_sat
    (assignment_artifact : Prop) (visible_cnf : Prop)
    (artifact_id : Prop) (visible_model : Prop) (original_model : Prop) :
    AyVCCCheckerAcceptance
      assignment_artifact visible_cnf visible_model ->
    AyVCCPreprocessArtifact artifact_id visible_model original_model ->
    visible_cnf ->
    artifact_id ->
    AyVCCPublicSatAnswer original_model := by
  intro acceptance
  intro artifact
  intro hvisible_cnf
  intro _hid
  exact ay_vcc_preprocess_artifact_reconstruct
    artifact_id visible_model original_model artifact
    (ay_vcc_checker_accepts_visible visible_cnf visible_model
      (ay_vcc_checker_acceptance_validation
        assignment_artifact visible_cnf visible_model acceptance)
      hvisible_cnf)
