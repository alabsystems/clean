-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific model-projection checker contract. Internal solver
-- assignments are projected to visible CNF variables, checked against the
-- visible CNF, then reconstructed to the original CNF through indexed
-- preprocessing artifacts and compressed model artifacts.

def AyMPCkConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMPCkDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMPCkEquisat (before : Prop) (after : Prop) :=
  AyMPCkConj (before -> after) (after -> before)

def AyMPCkAssignmentProjection
    (internal_assignment : Prop) (visible_assignment : Prop) :=
  internal_assignment -> visible_assignment

def AyMPCkVisibleChecker
    (visible_cnf : Prop) (visible_assignment : Prop) :=
  visible_cnf -> visible_assignment

def AyMPCkPreprocessArtifact
    (artifact_id : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :=
  AyMPCkConj artifact_id (visible_assignment -> original_assignment)

def AyMPCkArtifactLookup
    (artifact_id : Prop) (compressed_artifact : Prop) :=
  artifact_id -> compressed_artifact

def AyMPCkCompressedModelArtifact
    (visible_assignment : Prop) (original_assignment : Prop) :=
  AyMPCkConj visible_assignment
    (visible_assignment -> original_assignment)

def AyMPCkProjectionCheckerAcceptance
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :=
  AyMPCkConj
    (AyMPCkAssignmentProjection
      internal_assignment visible_assignment)
    (AyMPCkVisibleChecker visible_cnf visible_assignment)

def AyMPCkPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_mpck_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMPCkConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mpck_conj_left
    (left : Prop) (right : Prop) :
    AyMPCkConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mpck_conj_right
    (left : Prop) (right : Prop) :
    AyMPCkConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mpck_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMPCkDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mpck_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMPCkDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mpck_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMPCkEquisat before after := by
  intro forward
  intro backward
  exact ay_mpck_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_mpck_equisat_forward
    (before : Prop) (after : Prop) :
    AyMPCkEquisat before after -> before -> after := by
  intro certificate
  exact ay_mpck_conj_left (before -> after) (after -> before) certificate

theorem ay_mpck_equisat_backward
    (before : Prop) (after : Prop) :
    AyMPCkEquisat before after -> after -> before := by
  intro certificate
  exact ay_mpck_conj_right (before -> after) (after -> before) certificate

theorem ay_mpck_project_assignment
    (internal_assignment : Prop) (visible_assignment : Prop) :
    AyMPCkAssignmentProjection
      internal_assignment visible_assignment ->
    internal_assignment ->
    visible_assignment := by
  intro project
  intro hinternal
  exact project hinternal

theorem ay_mpck_visible_checker_accepts
    (visible_cnf : Prop) (visible_assignment : Prop) :
    AyMPCkVisibleChecker visible_cnf visible_assignment ->
    visible_cnf ->
    visible_assignment := by
  intro checker
  intro hvisible_cnf
  exact checker hvisible_cnf

theorem ay_mpck_acceptance_projection
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    AyMPCkAssignmentProjection
      internal_assignment visible_assignment := by
  intro acceptance
  exact ay_mpck_conj_left
    (AyMPCkAssignmentProjection
      internal_assignment visible_assignment)
    (AyMPCkVisibleChecker visible_cnf visible_assignment)
    acceptance

theorem ay_mpck_acceptance_checker
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    AyMPCkVisibleChecker visible_cnf visible_assignment := by
  intro acceptance
  exact ay_mpck_conj_right
    (AyMPCkAssignmentProjection
      internal_assignment visible_assignment)
    (AyMPCkVisibleChecker visible_cnf visible_assignment)
    acceptance

theorem ay_mpck_preprocess_artifact_id
    (artifact_id : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMPCkPreprocessArtifact
      artifact_id visible_assignment original_assignment ->
    artifact_id := by
  intro artifact
  exact ay_mpck_conj_left artifact_id
    (visible_assignment -> original_assignment)
    artifact

theorem ay_mpck_preprocess_reconstruction
    (artifact_id : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMPCkPreprocessArtifact
      artifact_id visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro artifact
  exact ay_mpck_conj_right artifact_id
    (visible_assignment -> original_assignment)
    artifact

theorem ay_mpck_lookup_artifact
    (artifact_id : Prop) (compressed_artifact : Prop) :
    AyMPCkArtifactLookup artifact_id compressed_artifact ->
    artifact_id ->
    compressed_artifact := by
  intro lookup
  intro hid
  exact lookup hid

theorem ay_mpck_compressed_artifact_intro
    (visible_assignment : Prop) (original_assignment : Prop) :
    visible_assignment ->
    (visible_assignment -> original_assignment) ->
    AyMPCkCompressedModelArtifact
      visible_assignment original_assignment := by
  intro hvisible
  intro reconstruct
  exact ay_mpck_conj_intro visible_assignment
    (visible_assignment -> original_assignment)
    hvisible
    reconstruct

theorem ay_mpck_compressed_artifact_visible
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMPCkCompressedModelArtifact
      visible_assignment original_assignment ->
    visible_assignment := by
  intro artifact
  exact ay_mpck_conj_left visible_assignment
    (visible_assignment -> original_assignment)
    artifact

theorem ay_mpck_compressed_artifact_reconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMPCkCompressedModelArtifact
      visible_assignment original_assignment ->
    visible_assignment -> original_assignment := by
  intro artifact
  exact ay_mpck_conj_right visible_assignment
    (visible_assignment -> original_assignment)
    artifact

theorem ay_mpck_compressed_artifact_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMPCkCompressedModelArtifact
      visible_assignment original_assignment ->
    original_assignment := by
  intro artifact
  exact ay_mpck_compressed_artifact_reconstruction
    visible_assignment original_assignment artifact
    (ay_mpck_compressed_artifact_visible
      visible_assignment original_assignment artifact)

theorem ay_mpck_build_compressed_artifact
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) (artifact_id : Prop)
    (original_assignment : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    AyMPCkPreprocessArtifact
      artifact_id visible_assignment original_assignment ->
    internal_assignment ->
    AyMPCkCompressedModelArtifact
      visible_assignment original_assignment := by
  intro acceptance
  intro preprocess
  intro hinternal
  have hvisible : visible_assignment :=
    ay_mpck_project_assignment
      internal_assignment visible_assignment
      (ay_mpck_acceptance_projection
        internal_assignment visible_cnf visible_assignment acceptance)
      hinternal
  exact ay_mpck_compressed_artifact_intro
    visible_assignment original_assignment
    hvisible
    (ay_mpck_preprocess_reconstruction
      artifact_id visible_assignment original_assignment preprocess)

theorem ay_mpck_projection_checker_public_sat
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) (artifact_id : Prop)
    (original_assignment : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    AyMPCkPreprocessArtifact
      artifact_id visible_assignment original_assignment ->
    internal_assignment ->
    AyMPCkPublicSatAnswer original_assignment := by
  intro acceptance
  intro preprocess
  intro hinternal
  exact ay_mpck_compressed_artifact_original
    visible_assignment original_assignment
    (ay_mpck_build_compressed_artifact
      internal_assignment visible_cnf visible_assignment artifact_id
      original_assignment acceptance preprocess hinternal)

theorem ay_mpck_projection_checker_acceptance_roundtrip
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    (visible_assignment -> internal_assignment) ->
    AyMPCkEquisat internal_assignment visible_assignment := by
  intro acceptance
  intro reconstruct_internal
  exact ay_mpck_equisat_intro internal_assignment visible_assignment
    (ay_mpck_acceptance_projection
      internal_assignment visible_cnf visible_assignment acceptance)
    reconstruct_internal

theorem ay_mpck_lookup_public_sat
    (internal_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) (artifact_id : Prop)
    (original_assignment : Prop)
    (compressed_artifact : Prop) :
    AyMPCkProjectionCheckerAcceptance
      internal_assignment visible_cnf visible_assignment ->
    AyMPCkPreprocessArtifact
      artifact_id visible_assignment original_assignment ->
    AyMPCkArtifactLookup artifact_id compressed_artifact ->
    (compressed_artifact ->
      AyMPCkCompressedModelArtifact
        visible_assignment original_assignment) ->
    internal_assignment ->
    AyMPCkPublicSatAnswer original_assignment := by
  intro acceptance
  intro preprocess
  intro lookup
  intro decode
  intro hinternal
  have hid : artifact_id :=
    ay_mpck_preprocess_artifact_id
      artifact_id visible_assignment original_assignment preprocess
  exact ay_mpck_compressed_artifact_original
    visible_assignment original_assignment
    (decode (ay_mpck_lookup_artifact artifact_id compressed_artifact
      lookup hid))
