-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for compressed model witnesses. Sparse and
-- bitset witnesses expand to full internal assignments, project to visible
-- assignments, pass visible-CNF checking, and reconstruct original models
-- through preprocessing artifacts.

def AyMWCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMWCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMWCEquisat (before : Prop) (after : Prop) :=
  AyMWCConj (before -> after) (after -> before)

def AyMWCExpansion (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyMWCSparseWitness (sparse_store : Prop) (full_assignment : Prop) :=
  AyMWCExpansion sparse_store full_assignment

def AyMWCBitsetWitness (bitset_store : Prop) (full_assignment : Prop) :=
  AyMWCExpansion bitset_store full_assignment

def AyMWCProjection (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyMWCVisibleChecker
    (visible_cnf : Prop) (visible_assignment : Prop) :=
  visible_cnf -> visible_assignment

def AyMWCPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyMWCCompressedModelCertificate
    (visible_assignment : Prop) (original_assignment : Prop) :=
  AyMWCConj visible_assignment
    (AyMWCPreprocessReconstruction
      visible_assignment original_assignment)

def AyMWCProjectionCheckerContract
    (full_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :=
  AyMWCConj
    (AyMWCProjection full_assignment visible_assignment)
    (AyMWCVisibleChecker visible_cnf visible_assignment)

def AyMWCPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_mwc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMWCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mwc_conj_left
    (left : Prop) (right : Prop) :
    AyMWCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mwc_conj_right
    (left : Prop) (right : Prop) :
    AyMWCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mwc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMWCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mwc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMWCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mwc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMWCEquisat before after := by
  intro forward
  intro backward
  exact ay_mwc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_mwc_equisat_forward
    (before : Prop) (after : Prop) :
    AyMWCEquisat before after -> before -> after := by
  intro certificate
  exact ay_mwc_conj_left (before -> after) (after -> before) certificate

theorem ay_mwc_equisat_backward
    (before : Prop) (after : Prop) :
    AyMWCEquisat before after -> after -> before := by
  intro certificate
  exact ay_mwc_conj_right (before -> after) (after -> before) certificate

theorem ay_mwc_expand_sparse
    (sparse_store : Prop) (full_assignment : Prop) :
    AyMWCSparseWitness sparse_store full_assignment ->
    sparse_store ->
    full_assignment := by
  intro expand
  intro hsparse
  exact expand hsparse

theorem ay_mwc_expand_bitset
    (bitset_store : Prop) (full_assignment : Prop) :
    AyMWCBitsetWitness bitset_store full_assignment ->
    bitset_store ->
    full_assignment := by
  intro expand
  intro hbitset
  exact expand hbitset

theorem ay_mwc_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyMWCProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_mwc_checker_accepts_visible
    (visible_cnf : Prop) (visible_assignment : Prop) :
    AyMWCVisibleChecker visible_cnf visible_assignment ->
    visible_cnf ->
    visible_assignment := by
  intro checker
  intro hvisible_cnf
  exact checker hvisible_cnf

theorem ay_mwc_contract_projection
    (full_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCProjection full_assignment visible_assignment := by
  intro contract
  exact ay_mwc_conj_left
    (AyMWCProjection full_assignment visible_assignment)
    (AyMWCVisibleChecker visible_cnf visible_assignment)
    contract

theorem ay_mwc_contract_checker
    (full_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCVisibleChecker visible_cnf visible_assignment := by
  intro contract
  exact ay_mwc_conj_right
    (AyMWCProjection full_assignment visible_assignment)
    (AyMWCVisibleChecker visible_cnf visible_assignment)
    contract

theorem ay_mwc_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mwc_compressed_certificate_intro
    (visible_assignment : Prop) (original_assignment : Prop) :
    visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment := by
  intro hvisible
  intro reconstruct
  exact ay_mwc_conj_intro visible_assignment
    (AyMWCPreprocessReconstruction
      visible_assignment original_assignment)
    hvisible
    reconstruct

theorem ay_mwc_compressed_certificate_visible
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment ->
    visible_assignment := by
  intro certificate
  exact ay_mwc_conj_left visible_assignment
    (AyMWCPreprocessReconstruction
      visible_assignment original_assignment)
    certificate

theorem ay_mwc_compressed_certificate_reconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment := by
  intro certificate
  exact ay_mwc_conj_right visible_assignment
    (AyMWCPreprocessReconstruction
      visible_assignment original_assignment)
    certificate

theorem ay_mwc_compressed_certificate_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment ->
    original_assignment := by
  intro certificate
  exact ay_mwc_compressed_certificate_reconstruction
    visible_assignment original_assignment certificate
    (ay_mwc_compressed_certificate_visible
      visible_assignment original_assignment certificate)

theorem ay_mwc_sparse_projection_visible
    (sparse_store : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyMWCSparseWitness sparse_store full_assignment ->
    AyMWCProjection full_assignment visible_assignment ->
    sparse_store ->
    visible_assignment := by
  intro expand
  intro project
  intro hsparse
  exact project (expand hsparse)

theorem ay_mwc_bitset_projection_visible
    (bitset_store : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyMWCBitsetWitness bitset_store full_assignment ->
    AyMWCProjection full_assignment visible_assignment ->
    bitset_store ->
    visible_assignment := by
  intro expand
  intro project
  intro hbitset
  exact project (expand hbitset)

theorem ay_mwc_sparse_public_sat_sound
    (sparse_store : Prop) (full_assignment : Prop)
    (visible_cnf : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMWCSparseWitness sparse_store full_assignment ->
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    sparse_store ->
    AyMWCPublicSatAnswer original_assignment := by
  intro expand
  intro contract
  intro reconstruct
  intro hsparse
  exact reconstruct
    (ay_mwc_sparse_projection_visible
      sparse_store full_assignment visible_assignment
      expand
      (ay_mwc_contract_projection
        full_assignment visible_cnf visible_assignment contract)
      hsparse)

theorem ay_mwc_bitset_public_sat_sound
    (bitset_store : Prop) (full_assignment : Prop)
    (visible_cnf : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMWCBitsetWitness bitset_store full_assignment ->
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    bitset_store ->
    AyMWCPublicSatAnswer original_assignment := by
  intro expand
  intro contract
  intro reconstruct
  intro hbitset
  exact reconstruct
    (ay_mwc_bitset_projection_visible
      bitset_store full_assignment visible_assignment
      expand
      (ay_mwc_contract_projection
        full_assignment visible_cnf visible_assignment contract)
      hbitset)

theorem ay_mwc_sparse_compressed_certificate
    (sparse_store : Prop) (full_assignment : Prop)
    (visible_cnf : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMWCSparseWitness sparse_store full_assignment ->
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    sparse_store ->
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment := by
  intro expand
  intro contract
  intro reconstruct
  intro hsparse
  exact ay_mwc_compressed_certificate_intro
    visible_assignment original_assignment
    (ay_mwc_sparse_projection_visible
      sparse_store full_assignment visible_assignment
      expand
      (ay_mwc_contract_projection
        full_assignment visible_cnf visible_assignment contract)
      hsparse)
    reconstruct

theorem ay_mwc_bitset_compressed_certificate
    (bitset_store : Prop) (full_assignment : Prop)
    (visible_cnf : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMWCBitsetWitness bitset_store full_assignment ->
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    bitset_store ->
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment := by
  intro expand
  intro contract
  intro reconstruct
  intro hbitset
  exact ay_mwc_compressed_certificate_intro
    visible_assignment original_assignment
    (ay_mwc_bitset_projection_visible
      bitset_store full_assignment visible_assignment
      expand
      (ay_mwc_contract_projection
        full_assignment visible_cnf visible_assignment contract)
      hbitset)
    reconstruct

theorem ay_mwc_checker_acceptance_from_projection
    (full_assignment : Prop) (visible_cnf : Prop)
    (visible_assignment : Prop) :
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    full_assignment ->
    visible_cnf ->
    AyMWCConj visible_assignment visible_assignment := by
  intro contract
  intro hfull
  intro hvisible_cnf
  exact ay_mwc_conj_intro visible_assignment visible_assignment
    (ay_mwc_project_visible full_assignment visible_assignment
      (ay_mwc_contract_projection
        full_assignment visible_cnf visible_assignment contract)
      hfull)
    (ay_mwc_checker_accepts_visible visible_cnf visible_assignment
      (ay_mwc_contract_checker
        full_assignment visible_cnf visible_assignment contract)
      hvisible_cnf)

theorem ay_mwc_agrees_with_projection_checker
    (sparse_store : Prop) (full_assignment : Prop)
    (visible_cnf : Prop) (visible_assignment : Prop)
    (original_assignment : Prop) :
    AyMWCSparseWitness sparse_store full_assignment ->
    AyMWCProjectionCheckerContract
      full_assignment visible_cnf visible_assignment ->
    AyMWCPreprocessReconstruction
      visible_assignment original_assignment ->
    sparse_store ->
    AyMWCCompressedModelCertificate
      visible_assignment original_assignment ->
    original_assignment := by
  intro _expand
  intro _contract
  intro _reconstruct
  intro _hsparse
  intro certificate
  exact ay_mwc_compressed_certificate_original
    visible_assignment original_assignment certificate
