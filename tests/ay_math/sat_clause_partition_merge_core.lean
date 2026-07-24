-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for merging accepted visible-CNF clause
-- partitions. Two checked partitions are folded into a merged partition,
-- shown equivalent to full visible-CNF checking, and transported through
-- compressed witness reuse plus preprocessing reconstruction.

def AyCPMConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCPMDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCPMEquisat (before : Prop) (after : Prop) :=
  AyCPMConj (before -> after) (after -> before)

def AyCPMWitnessExpansion
    (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyCPMProjection
    (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyCPMBlockCheck (block : Prop) (visible_assignment : Prop) :=
  visible_assignment -> block

def AyCPMPartition (left_block : Prop) (right_block : Prop) :=
  AyCPMConj left_block right_block

def AyCPMMergedPartition
    (left_partition : Prop) (right_partition : Prop) :=
  AyCPMConj left_partition right_partition

def AyCPMAccumulator (accepted : Prop) (next : Prop) :=
  AyCPMConj accepted next

def AyCPMFullVisibleCheck
    (visible_cnf : Prop) (visible_assignment : Prop) :=
  visible_assignment -> visible_cnf

def AyCPMPreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyCPMPublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_cpm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCPMConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_cpm_conj_left
    (left : Prop) (right : Prop) :
    AyCPMConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cpm_conj_right
    (left : Prop) (right : Prop) :
    AyCPMConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cpm_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCPMDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_cpm_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCPMDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_cpm_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCPMEquisat before after := by
  intro forward
  intro backward
  exact ay_cpm_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_cpm_equisat_forward
    (before : Prop) (after : Prop) :
    AyCPMEquisat before after -> before -> after := by
  intro certificate
  exact ay_cpm_conj_left (before -> after) (after -> before) certificate

theorem ay_cpm_equisat_backward
    (before : Prop) (after : Prop) :
    AyCPMEquisat before after -> after -> before := by
  intro certificate
  exact ay_cpm_conj_right (before -> after) (after -> before) certificate

theorem ay_cpm_expand_witness
    (compressed_witness : Prop) (full_assignment : Prop) :
    AyCPMWitnessExpansion compressed_witness full_assignment ->
    compressed_witness ->
    full_assignment := by
  intro expand
  intro hcompressed
  exact expand hcompressed

theorem ay_cpm_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyCPMProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_cpm_block_accepts
    (block : Prop) (visible_assignment : Prop) :
    AyCPMBlockCheck block visible_assignment ->
    visible_assignment ->
    block := by
  intro check
  intro hvisible
  exact check hvisible

theorem ay_cpm_partition_intro
    (left_block : Prop) (right_block : Prop) :
    left_block ->
    right_block ->
    AyCPMPartition left_block right_block := by
  intro hleft
  intro hright
  exact ay_cpm_conj_intro left_block right_block hleft hright

theorem ay_cpm_partition_left
    (left_block : Prop) (right_block : Prop) :
    AyCPMPartition left_block right_block -> left_block := by
  intro partition
  exact ay_cpm_conj_left left_block right_block partition

theorem ay_cpm_partition_right
    (left_block : Prop) (right_block : Prop) :
    AyCPMPartition left_block right_block -> right_block := by
  intro partition
  exact ay_cpm_conj_right left_block right_block partition

theorem ay_cpm_partition_checked
    (left_block : Prop) (right_block : Prop)
    (visible_assignment : Prop) :
    AyCPMBlockCheck left_block visible_assignment ->
    AyCPMBlockCheck right_block visible_assignment ->
    visible_assignment ->
    AyCPMPartition left_block right_block := by
  intro check_left
  intro check_right
  intro hvisible
  exact ay_cpm_partition_intro left_block right_block
    (check_left hvisible)
    (check_right hvisible)

theorem ay_cpm_merge_partitions
    (partition_a : Prop) (partition_b : Prop) :
    partition_a ->
    partition_b ->
    AyCPMMergedPartition partition_a partition_b := by
  intro hpartition_a
  intro hpartition_b
  exact ay_cpm_conj_intro partition_a partition_b
    hpartition_a hpartition_b

theorem ay_cpm_merged_left
    (partition_a : Prop) (partition_b : Prop) :
    AyCPMMergedPartition partition_a partition_b -> partition_a := by
  intro merged
  exact ay_cpm_conj_left partition_a partition_b merged

theorem ay_cpm_merged_right
    (partition_a : Prop) (partition_b : Prop) :
    AyCPMMergedPartition partition_a partition_b -> partition_b := by
  intro merged
  exact ay_cpm_conj_right partition_a partition_b merged

theorem ay_cpm_accumulator_intro
    (accepted : Prop) (next : Prop) :
    accepted -> next -> AyCPMAccumulator accepted next := by
  intro haccepted
  intro hnext
  exact ay_cpm_conj_intro accepted next haccepted hnext

theorem ay_cpm_accumulator_compatible
    (partition_a : Prop) (partition_b : Prop) :
    AyCPMAccumulator partition_a partition_b ->
    AyCPMMergedPartition partition_a partition_b := by
  intro accumulator
  exact ay_cpm_merge_partitions partition_a partition_b
    (ay_cpm_conj_left partition_a partition_b accumulator)
    (ay_cpm_conj_right partition_a partition_b accumulator)

theorem ay_cpm_checked_partitions_merge
    (block_a : Prop) (block_b : Prop)
    (block_c : Prop) (block_d : Prop)
    (visible_assignment : Prop) :
    AyCPMBlockCheck block_a visible_assignment ->
    AyCPMBlockCheck block_b visible_assignment ->
    AyCPMBlockCheck block_c visible_assignment ->
    AyCPMBlockCheck block_d visible_assignment ->
    visible_assignment ->
    AyCPMMergedPartition
      (AyCPMPartition block_a block_b)
      (AyCPMPartition block_c block_d) := by
  intro check_a
  intro check_b
  intro check_c
  intro check_d
  intro hvisible
  exact ay_cpm_merge_partitions
    (AyCPMPartition block_a block_b)
    (AyCPMPartition block_c block_d)
    (ay_cpm_partition_checked
      block_a block_b visible_assignment check_a check_b hvisible)
    (ay_cpm_partition_checked
      block_c block_d visible_assignment check_c check_d hvisible)

theorem ay_cpm_merge_to_full_visible
    (visible_cnf : Prop)
    (partition_a : Prop) (partition_b : Prop) :
    (AyCPMMergedPartition partition_a partition_b -> visible_cnf) ->
    AyCPMMergedPartition partition_a partition_b ->
    visible_cnf := by
  intro assemble
  intro merged
  exact assemble merged

theorem ay_cpm_full_visible_to_merge
    (visible_cnf : Prop)
    (partition_a : Prop) (partition_b : Prop) :
    (visible_cnf -> AyCPMMergedPartition partition_a partition_b) ->
    visible_cnf ->
    AyCPMMergedPartition partition_a partition_b := by
  intro decompose
  intro hvisible_cnf
  exact decompose hvisible_cnf

theorem ay_cpm_merge_full_equiv
    (visible_cnf : Prop)
    (partition_a : Prop) (partition_b : Prop) :
    (AyCPMMergedPartition partition_a partition_b -> visible_cnf) ->
    (visible_cnf -> AyCPMMergedPartition partition_a partition_b) ->
    AyCPMEquisat
      (AyCPMMergedPartition partition_a partition_b)
      visible_cnf := by
  intro assemble
  intro decompose
  exact ay_cpm_equisat_intro
    (AyCPMMergedPartition partition_a partition_b)
    visible_cnf
    assemble
    decompose

theorem ay_cpm_compressed_witness_visible
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyCPMWitnessExpansion compressed_witness full_assignment ->
    AyCPMProjection full_assignment visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro expand
  intro project
  intro hcompressed
  exact project (expand hcompressed)

theorem ay_cpm_merged_visible_cnf_checked
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (block_a : Prop) (block_b : Prop)
    (block_c : Prop) (block_d : Prop) :
    AyCPMWitnessExpansion compressed_witness full_assignment ->
    AyCPMProjection full_assignment visible_assignment ->
    AyCPMBlockCheck block_a visible_assignment ->
    AyCPMBlockCheck block_b visible_assignment ->
    AyCPMBlockCheck block_c visible_assignment ->
    AyCPMBlockCheck block_d visible_assignment ->
    (AyCPMMergedPartition
      (AyCPMPartition block_a block_b)
      (AyCPMPartition block_c block_d) -> visible_cnf) ->
    compressed_witness ->
    visible_cnf := by
  intro expand
  intro project
  intro check_a
  intro check_b
  intro check_c
  intro check_d
  intro assemble
  intro hcompressed
  exact assemble
    (ay_cpm_checked_partitions_merge
      block_a block_b block_c block_d visible_assignment
      check_a check_b check_c check_d
      (ay_cpm_compressed_witness_visible
        compressed_witness full_assignment visible_assignment
        expand project hcompressed))

theorem ay_cpm_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyCPMPreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_cpm_merge_public_sat_sound
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (block_a : Prop) (block_b : Prop)
    (block_c : Prop) (block_d : Prop)
    (original_assignment : Prop) :
    AyCPMWitnessExpansion compressed_witness full_assignment ->
    AyCPMProjection full_assignment visible_assignment ->
    AyCPMBlockCheck block_a visible_assignment ->
    AyCPMBlockCheck block_b visible_assignment ->
    AyCPMBlockCheck block_c visible_assignment ->
    AyCPMBlockCheck block_d visible_assignment ->
    (AyCPMMergedPartition
      (AyCPMPartition block_a block_b)
      (AyCPMPartition block_c block_d) -> visible_cnf) ->
    AyCPMPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyCPMPublicSatAnswer original_assignment := by
  intro expand
  intro project
  intro _check_a
  intro _check_b
  intro _check_c
  intro _check_d
  intro _assemble
  intro reconstruct
  intro hcompressed
  exact reconstruct
    (ay_cpm_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed)

theorem ay_cpm_merge_soundness_certificate
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (block_a : Prop) (block_b : Prop)
    (block_c : Prop) (block_d : Prop)
    (original_assignment : Prop) :
    AyCPMWitnessExpansion compressed_witness full_assignment ->
    AyCPMProjection full_assignment visible_assignment ->
    AyCPMBlockCheck block_a visible_assignment ->
    AyCPMBlockCheck block_b visible_assignment ->
    AyCPMBlockCheck block_c visible_assignment ->
    AyCPMBlockCheck block_d visible_assignment ->
    (AyCPMMergedPartition
      (AyCPMPartition block_a block_b)
      (AyCPMPartition block_c block_d) -> visible_cnf) ->
    AyCPMPreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    AyCPMConj visible_cnf original_assignment := by
  intro expand
  intro project
  intro check_a
  intro check_b
  intro check_c
  intro check_d
  intro assemble
  intro reconstruct
  intro hcompressed
  have hvisible : visible_assignment :=
    ay_cpm_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed
  exact ay_cpm_conj_intro visible_cnf original_assignment
    (assemble
      (ay_cpm_checked_partitions_merge
        block_a block_b block_c block_d visible_assignment
        check_a check_b check_c check_d hvisible))
    (reconstruct hvisible)
