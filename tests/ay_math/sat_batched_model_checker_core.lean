-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for batched model checking. Clause batches are
-- validated against a visible assignment, accumulated into full visible-CNF
-- satisfaction, then reconstructed to an original-formula SAT certificate.

def AyBMCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBMCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBMCEquisat (before : Prop) (after : Prop) :=
  AyBMCConj (before -> after) (after -> before)

def AyBMCWitnessExpansion
    (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyBMCAssignmentProjection
    (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyBMCBatchValidation
    (batch : Prop) (visible_assignment : Prop) :=
  visible_assignment -> batch

def AyBMCBatchAccumulator (accepted : Prop) (batch : Prop) :=
  AyBMCConj accepted batch

def AyBMCFullVisibleCnf (batch_a : Prop) (batch_b : Prop) :=
  AyBMCConj batch_a batch_b

def AyBMCPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyBMCPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_bmc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBMCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_bmc_conj_left
    (left : Prop) (right : Prop) :
    AyBMCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bmc_conj_right
    (left : Prop) (right : Prop) :
    AyBMCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bmc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBMCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_bmc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBMCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_bmc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBMCEquisat before after := by
  intro forward
  intro backward
  exact ay_bmc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_bmc_equisat_forward
    (before : Prop) (after : Prop) :
    AyBMCEquisat before after -> before -> after := by
  intro certificate
  exact ay_bmc_conj_left (before -> after) (after -> before) certificate

theorem ay_bmc_equisat_backward
    (before : Prop) (after : Prop) :
    AyBMCEquisat before after -> after -> before := by
  intro certificate
  exact ay_bmc_conj_right (before -> after) (after -> before) certificate

theorem ay_bmc_expand_witness
    (compressed_witness : Prop) (full_assignment : Prop) :
    AyBMCWitnessExpansion compressed_witness full_assignment ->
    compressed_witness ->
    full_assignment := by
  intro expand
  intro hcompressed
  exact expand hcompressed

theorem ay_bmc_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyBMCAssignmentProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_bmc_batch_accepts
    (batch : Prop) (visible_assignment : Prop) :
    AyBMCBatchValidation batch visible_assignment ->
    visible_assignment ->
    batch := by
  intro validate
  intro hvisible
  exact validate hvisible

theorem ay_bmc_accumulator_intro
    (accepted : Prop) (batch : Prop) :
    accepted -> batch -> AyBMCBatchAccumulator accepted batch := by
  intro haccepted
  intro hbatch
  exact ay_bmc_conj_intro accepted batch haccepted hbatch

theorem ay_bmc_accumulator_previous
    (accepted : Prop) (batch : Prop) :
    AyBMCBatchAccumulator accepted batch -> accepted := by
  intro accumulator
  exact ay_bmc_conj_left accepted batch accumulator

theorem ay_bmc_accumulator_batch
    (accepted : Prop) (batch : Prop) :
    AyBMCBatchAccumulator accepted batch -> batch := by
  intro accumulator
  exact ay_bmc_conj_right accepted batch accumulator

theorem ay_bmc_first_batch_accumulator
    (batch_a : Prop) (visible_assignment : Prop) :
    AyBMCBatchValidation batch_a visible_assignment ->
    visible_assignment ->
    AyBMCBatchAccumulator visible_assignment batch_a := by
  intro validate_a
  intro hvisible
  exact ay_bmc_accumulator_intro visible_assignment batch_a
    hvisible
    (validate_a hvisible)

theorem ay_bmc_second_batch_accumulator
    (batch_a : Prop) (batch_b : Prop) :
    AyBMCBatchAccumulator batch_a batch_b ->
    AyBMCFullVisibleCnf batch_a batch_b := by
  intro accumulator
  exact ay_bmc_conj_intro batch_a batch_b
    (ay_bmc_accumulator_previous batch_a batch_b accumulator)
    (ay_bmc_accumulator_batch batch_a batch_b accumulator)

theorem ay_bmc_batches_full_visible_cnf
    (batch_a : Prop) (batch_b : Prop)
    (visible_assignment : Prop) :
    AyBMCBatchValidation batch_a visible_assignment ->
    AyBMCBatchValidation batch_b visible_assignment ->
    visible_assignment ->
    AyBMCFullVisibleCnf batch_a batch_b := by
  intro validate_a
  intro validate_b
  intro hvisible
  exact ay_bmc_conj_intro batch_a batch_b
    (validate_a hvisible)
    (validate_b hvisible)

theorem ay_bmc_compressed_witness_visible
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyBMCWitnessExpansion compressed_witness full_assignment ->
    AyBMCAssignmentProjection full_assignment visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro expand
  intro project
  intro hcompressed
  exact project (expand hcompressed)

theorem ay_bmc_batched_checker_acceptance
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (batch_a : Prop) (batch_b : Prop) :
    AyBMCWitnessExpansion compressed_witness full_assignment ->
    AyBMCAssignmentProjection full_assignment visible_assignment ->
    AyBMCBatchValidation batch_a visible_assignment ->
    AyBMCBatchValidation batch_b visible_assignment ->
    compressed_witness ->
    AyBMCConj visible_assignment
      (AyBMCFullVisibleCnf batch_a batch_b) := by
  intro expand
  intro project
  intro validate_a
  intro validate_b
  intro hcompressed
  have hvisible : visible_assignment :=
    ay_bmc_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed
  exact ay_bmc_conj_intro visible_assignment
    (AyBMCFullVisibleCnf batch_a batch_b)
    hvisible
    (ay_bmc_batches_full_visible_cnf
      batch_a batch_b visible_assignment
      validate_a validate_b hvisible)

theorem ay_bmc_acceptance_visible_assignment
    (visible_assignment : Prop) (batch_a : Prop) (batch_b : Prop) :
    AyBMCConj visible_assignment
      (AyBMCFullVisibleCnf batch_a batch_b) ->
    visible_assignment := by
  intro acceptance
  exact ay_bmc_conj_left visible_assignment
    (AyBMCFullVisibleCnf batch_a batch_b)
    acceptance

theorem ay_bmc_acceptance_full_visible_cnf
    (visible_assignment : Prop) (batch_a : Prop) (batch_b : Prop) :
    AyBMCConj visible_assignment
      (AyBMCFullVisibleCnf batch_a batch_b) ->
    AyBMCFullVisibleCnf batch_a batch_b := by
  intro acceptance
  exact ay_bmc_conj_right visible_assignment
    (AyBMCFullVisibleCnf batch_a batch_b)
    acceptance

theorem ay_bmc_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyBMCPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_bmc_batched_public_sat_sound
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (batch_a : Prop) (batch_b : Prop)
    (original_assignment : Prop) :
    AyBMCWitnessExpansion compressed_witness full_assignment ->
    AyBMCAssignmentProjection full_assignment visible_assignment ->
    AyBMCBatchValidation batch_a visible_assignment ->
    AyBMCBatchValidation batch_b visible_assignment ->
    AyBMCPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyBMCPublicSatAnswer original_assignment := by
  intro expand
  intro project
  intro validate_a
  intro validate_b
  intro reconstruct
  intro hcompressed
  exact reconstruct
    (ay_bmc_acceptance_visible_assignment
      visible_assignment batch_a batch_b
      (ay_bmc_batched_checker_acceptance
        compressed_witness full_assignment visible_assignment
        batch_a batch_b
        expand project validate_a validate_b hcompressed))

theorem ay_bmc_batched_soundness_certificate
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (batch_a : Prop) (batch_b : Prop)
    (original_assignment : Prop) :
    AyBMCWitnessExpansion compressed_witness full_assignment ->
    AyBMCAssignmentProjection full_assignment visible_assignment ->
    AyBMCBatchValidation batch_a visible_assignment ->
    AyBMCBatchValidation batch_b visible_assignment ->
    AyBMCPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyBMCConj
      (AyBMCFullVisibleCnf batch_a batch_b)
      original_assignment := by
  intro expand
  intro project
  intro validate_a
  intro validate_b
  intro reconstruct
  intro hcompressed
  have acceptance :
      AyBMCConj visible_assignment
        (AyBMCFullVisibleCnf batch_a batch_b) :=
    ay_bmc_batched_checker_acceptance
      compressed_witness full_assignment visible_assignment
      batch_a batch_b
      expand project validate_a validate_b hcompressed
  exact ay_bmc_conj_intro
    (AyBMCFullVisibleCnf batch_a batch_b)
    original_assignment
    (ay_bmc_acceptance_full_visible_cnf
      visible_assignment batch_a batch_b acceptance)
    (reconstruct
      (ay_bmc_acceptance_visible_assignment
        visible_assignment batch_a batch_b acceptance))
