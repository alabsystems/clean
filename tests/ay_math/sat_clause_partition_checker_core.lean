-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for clause-partition model checking. A visible
-- CNF is split into checked blocks, folded through an accumulator, and then
-- transported through compressed witness expansion and preprocessing
-- reconstruction to a public SAT answer.

def AyCPCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCPCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCPCEquisat (before : Prop) (after : Prop) :=
  AyCPCConj (before -> after) (after -> before)

def AyCPCWitnessExpansion
    (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyCPCProjection
    (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyCPCBlockCheck (block : Prop) (visible_assignment : Prop) :=
  visible_assignment -> block

def AyCPCPartition (block_a : Prop) (block_b : Prop) :=
  AyCPCConj block_a block_b

def AyCPCAccumulator (accepted : Prop) (next_block : Prop) :=
  AyCPCConj accepted next_block

def AyCPCFullVisibleCheck
    (visible_cnf : Prop) (visible_assignment : Prop) :=
  visible_assignment -> visible_cnf

def AyCPCPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyCPCPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_cpc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCPCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_cpc_conj_left
    (left : Prop) (right : Prop) :
    AyCPCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cpc_conj_right
    (left : Prop) (right : Prop) :
    AyCPCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cpc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCPCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_cpc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCPCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_cpc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCPCEquisat before after := by
  intro forward
  intro backward
  exact ay_cpc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_cpc_equisat_forward
    (before : Prop) (after : Prop) :
    AyCPCEquisat before after -> before -> after := by
  intro certificate
  exact ay_cpc_conj_left (before -> after) (after -> before) certificate

theorem ay_cpc_equisat_backward
    (before : Prop) (after : Prop) :
    AyCPCEquisat before after -> after -> before := by
  intro certificate
  exact ay_cpc_conj_right (before -> after) (after -> before) certificate

theorem ay_cpc_expand_witness
    (compressed_witness : Prop) (full_assignment : Prop) :
    AyCPCWitnessExpansion compressed_witness full_assignment ->
    compressed_witness ->
    full_assignment := by
  intro expand
  intro hcompressed
  exact expand hcompressed

theorem ay_cpc_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyCPCProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_cpc_block_accepts
    (block : Prop) (visible_assignment : Prop) :
    AyCPCBlockCheck block visible_assignment ->
    visible_assignment ->
    block := by
  intro check
  intro hvisible
  exact check hvisible

theorem ay_cpc_partition_intro
    (block_a : Prop) (block_b : Prop) :
    block_a -> block_b -> AyCPCPartition block_a block_b := by
  intro ha
  intro hb
  exact ay_cpc_conj_intro block_a block_b ha hb

theorem ay_cpc_partition_left
    (block_a : Prop) (block_b : Prop) :
    AyCPCPartition block_a block_b -> block_a := by
  intro partition
  exact ay_cpc_conj_left block_a block_b partition

theorem ay_cpc_partition_right
    (block_a : Prop) (block_b : Prop) :
    AyCPCPartition block_a block_b -> block_b := by
  intro partition
  exact ay_cpc_conj_right block_a block_b partition

theorem ay_cpc_accumulator_intro
    (accepted : Prop) (next_block : Prop) :
    accepted -> next_block -> AyCPCAccumulator accepted next_block := by
  intro haccepted
  intro hnext
  exact ay_cpc_conj_intro accepted next_block haccepted hnext

theorem ay_cpc_accumulator_accepted
    (accepted : Prop) (next_block : Prop) :
    AyCPCAccumulator accepted next_block -> accepted := by
  intro accumulator
  exact ay_cpc_conj_left accepted next_block accumulator

theorem ay_cpc_accumulator_next
    (accepted : Prop) (next_block : Prop) :
    AyCPCAccumulator accepted next_block -> next_block := by
  intro accumulator
  exact ay_cpc_conj_right accepted next_block accumulator

theorem ay_cpc_fold_two_blocks
    (block_a : Prop) (block_b : Prop)
    (visible_assignment : Prop) :
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    visible_assignment ->
    AyCPCAccumulator block_a block_b := by
  intro check_a
  intro check_b
  intro hvisible
  exact ay_cpc_accumulator_intro block_a block_b
    (check_a hvisible)
    (check_b hvisible)

theorem ay_cpc_fold_to_partition
    (block_a : Prop) (block_b : Prop) :
    AyCPCAccumulator block_a block_b ->
    AyCPCPartition block_a block_b := by
  intro accumulator
  exact ay_cpc_partition_intro block_a block_b
    (ay_cpc_accumulator_accepted block_a block_b accumulator)
    (ay_cpc_accumulator_next block_a block_b accumulator)

theorem ay_cpc_partitioned_visible_check
    (block_a : Prop) (block_b : Prop)
    (visible_assignment : Prop) :
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    visible_assignment ->
    AyCPCPartition block_a block_b := by
  intro check_a
  intro check_b
  intro hvisible
  exact ay_cpc_fold_to_partition block_a block_b
    (ay_cpc_fold_two_blocks block_a block_b visible_assignment
      check_a check_b hvisible)

theorem ay_cpc_full_check_from_partition
    (visible_cnf : Prop) (block_a : Prop) (block_b : Prop)
    (visible_assignment : Prop) :
    (AyCPCPartition block_a block_b -> visible_cnf) ->
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    AyCPCFullVisibleCheck visible_cnf visible_assignment := by
  intro assemble
  intro check_a
  intro check_b
  intro hvisible
  exact assemble
    (ay_cpc_partitioned_visible_check
      block_a block_b visible_assignment check_a check_b hvisible)

theorem ay_cpc_partition_from_full_check
    (visible_cnf : Prop) (block_a : Prop) (block_b : Prop)
    (visible_assignment : Prop) :
    (visible_cnf -> AyCPCPartition block_a block_b) ->
    AyCPCFullVisibleCheck visible_cnf visible_assignment ->
    visible_assignment ->
    AyCPCPartition block_a block_b := by
  intro cnf_to_partition
  intro full_check
  intro hvisible
  exact cnf_to_partition (full_check hvisible)

theorem ay_cpc_partition_full_equiv
    (visible_cnf : Prop) (block_a : Prop) (block_b : Prop)
    (visible_assignment : Prop) :
    (AyCPCPartition block_a block_b -> visible_cnf) ->
    (visible_cnf -> AyCPCPartition block_a block_b) ->
    AyCPCEquisat
      (AyCPCPartition block_a block_b)
      visible_cnf := by
  intro assemble
  intro cnf_to_partition
  exact ay_cpc_equisat_intro
    (AyCPCPartition block_a block_b)
    visible_cnf
    assemble
    cnf_to_partition

theorem ay_cpc_compressed_witness_visible
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyCPCWitnessExpansion compressed_witness full_assignment ->
    AyCPCProjection full_assignment visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro expand
  intro project
  intro hcompressed
  exact project (expand hcompressed)

theorem ay_cpc_partitioned_full_visible_cnf
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop)
    (visible_cnf : Prop) (block_a : Prop) (block_b : Prop) :
    AyCPCWitnessExpansion compressed_witness full_assignment ->
    AyCPCProjection full_assignment visible_assignment ->
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    (AyCPCPartition block_a block_b -> visible_cnf) ->
    compressed_witness ->
    visible_cnf := by
  intro expand
  intro project
  intro check_a
  intro check_b
  intro assemble
  intro hcompressed
  exact ay_cpc_full_check_from_partition
    visible_cnf block_a block_b visible_assignment
    assemble check_a check_b
    (ay_cpc_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed)

theorem ay_cpc_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyCPCPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_cpc_partition_public_sat_sound
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (block_a : Prop) (block_b : Prop) (original_assignment : Prop) :
    AyCPCWitnessExpansion compressed_witness full_assignment ->
    AyCPCProjection full_assignment visible_assignment ->
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    (AyCPCPartition block_a block_b -> visible_cnf) ->
    AyCPCPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyCPCPublicSatAnswer original_assignment := by
  intro expand
  intro project
  intro _check_a
  intro _check_b
  intro _assemble
  intro reconstruct
  intro hcompressed
  exact reconstruct
    (ay_cpc_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed)

theorem ay_cpc_partition_soundness_certificate
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (block_a : Prop) (block_b : Prop) (original_assignment : Prop) :
    AyCPCWitnessExpansion compressed_witness full_assignment ->
    AyCPCProjection full_assignment visible_assignment ->
    AyCPCBlockCheck block_a visible_assignment ->
    AyCPCBlockCheck block_b visible_assignment ->
    (AyCPCPartition block_a block_b -> visible_cnf) ->
    AyCPCPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyCPCConj visible_cnf original_assignment := by
  intro expand
  intro project
  intro check_a
  intro check_b
  intro assemble
  intro reconstruct
  intro hcompressed
  have hvisible : visible_assignment :=
    ay_cpc_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed
  exact ay_cpc_conj_intro visible_cnf original_assignment
    (ay_cpc_full_check_from_partition
      visible_cnf block_a block_b visible_assignment
      assemble check_a check_b hvisible)
    (reconstruct hvisible)
