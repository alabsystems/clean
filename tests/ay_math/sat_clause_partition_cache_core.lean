-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for caching accepted clause partitions. Cached
-- partition reuse is guarded by a cache key plus a witness/partition identity
-- guard; only matching guards expose the accepted partition facts.

def AyCPCacheConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCPCacheDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCPCacheEquisat (before : Prop) (after : Prop) :=
  AyCPCacheConj (before -> after) (after -> before)

def AyCPCacheWitnessExpansion
    (compressed_witness : Prop) (full_assignment : Prop) :=
  compressed_witness -> full_assignment

def AyCPCacheProjection
    (full_assignment : Prop) (visible_assignment : Prop) :=
  full_assignment -> visible_assignment

def AyCPCacheBlockCheck (block : Prop) (visible_assignment : Prop) :=
  visible_assignment -> block

def AyCPCachePartition (left_block : Prop) (right_block : Prop) :=
  AyCPCacheConj left_block right_block

def AyCPCacheMergedPartition
    (left_partition : Prop) (right_partition : Prop) :=
  AyCPCacheConj left_partition right_partition

def AyCPCacheGuard (cache_key : Prop) (witness_id : Prop) :=
  AyCPCacheConj cache_key witness_id

def AyCPCacheEntry (guard : Prop) (partition : Prop) :=
  guard -> partition

def AyCPCacheAccumulator (accepted : Prop) (cached : Prop) :=
  AyCPCacheConj accepted cached

def AyCPCachePreprocessReconstruction
    (visible_assignment : Prop) (original_assignment : Prop) :=
  visible_assignment -> original_assignment

def AyCPCachePublicSatAnswer (original_assignment : Prop) :=
  original_assignment

theorem ay_cpcache_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCPCacheConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_cpcache_conj_left
    (left : Prop) (right : Prop) :
    AyCPCacheConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cpcache_conj_right
    (left : Prop) (right : Prop) :
    AyCPCacheConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cpcache_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCPCacheDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_cpcache_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCPCacheDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_cpcache_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCPCacheEquisat before after := by
  intro forward
  intro backward
  exact ay_cpcache_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_cpcache_equisat_forward
    (before : Prop) (after : Prop) :
    AyCPCacheEquisat before after -> before -> after := by
  intro certificate
  exact ay_cpcache_conj_left
    (before -> after) (after -> before) certificate

theorem ay_cpcache_equisat_backward
    (before : Prop) (after : Prop) :
    AyCPCacheEquisat before after -> after -> before := by
  intro certificate
  exact ay_cpcache_conj_right
    (before -> after) (after -> before) certificate

theorem ay_cpcache_expand_witness
    (compressed_witness : Prop) (full_assignment : Prop) :
    AyCPCacheWitnessExpansion compressed_witness full_assignment ->
    compressed_witness ->
    full_assignment := by
  intro expand
  intro hcompressed
  exact expand hcompressed

theorem ay_cpcache_project_visible
    (full_assignment : Prop) (visible_assignment : Prop) :
    AyCPCacheProjection full_assignment visible_assignment ->
    full_assignment ->
    visible_assignment := by
  intro project
  intro hfull
  exact project hfull

theorem ay_cpcache_block_accepts
    (block : Prop) (visible_assignment : Prop) :
    AyCPCacheBlockCheck block visible_assignment ->
    visible_assignment ->
    block := by
  intro check
  intro hvisible
  exact check hvisible

theorem ay_cpcache_partition_intro
    (left_block : Prop) (right_block : Prop) :
    left_block ->
    right_block ->
    AyCPCachePartition left_block right_block := by
  intro hleft
  intro hright
  exact ay_cpcache_conj_intro left_block right_block hleft hright

theorem ay_cpcache_partition_left
    (left_block : Prop) (right_block : Prop) :
    AyCPCachePartition left_block right_block -> left_block := by
  intro partition
  exact ay_cpcache_conj_left left_block right_block partition

theorem ay_cpcache_partition_right
    (left_block : Prop) (right_block : Prop) :
    AyCPCachePartition left_block right_block -> right_block := by
  intro partition
  exact ay_cpcache_conj_right left_block right_block partition

theorem ay_cpcache_checked_partition
    (left_block : Prop) (right_block : Prop)
    (visible_assignment : Prop) :
    AyCPCacheBlockCheck left_block visible_assignment ->
    AyCPCacheBlockCheck right_block visible_assignment ->
    visible_assignment ->
    AyCPCachePartition left_block right_block := by
  intro check_left
  intro check_right
  intro hvisible
  exact ay_cpcache_partition_intro left_block right_block
    (check_left hvisible)
    (check_right hvisible)

theorem ay_cpcache_guard_intro
    (cache_key : Prop) (witness_id : Prop) :
    cache_key ->
    witness_id ->
    AyCPCacheGuard cache_key witness_id := by
  intro hkey
  intro hwitness
  exact ay_cpcache_conj_intro cache_key witness_id hkey hwitness

theorem ay_cpcache_guard_key
    (cache_key : Prop) (witness_id : Prop) :
    AyCPCacheGuard cache_key witness_id -> cache_key := by
  intro guard
  exact ay_cpcache_conj_left cache_key witness_id guard

theorem ay_cpcache_guard_witness
    (cache_key : Prop) (witness_id : Prop) :
    AyCPCacheGuard cache_key witness_id -> witness_id := by
  intro guard
  exact ay_cpcache_conj_right cache_key witness_id guard

theorem ay_cpcache_entry_lookup
    (guard : Prop) (partition : Prop) :
    AyCPCacheEntry guard partition ->
    guard ->
    partition := by
  intro entry
  intro hguard
  exact entry hguard

theorem ay_cpcache_reuse_partition
    (cache_key : Prop) (witness_id : Prop)
    (partition : Prop) :
    AyCPCacheEntry
      (AyCPCacheGuard cache_key witness_id)
      partition ->
    cache_key ->
    witness_id ->
    partition := by
  intro entry
  intro hkey
  intro hwitness
  exact entry
    (ay_cpcache_guard_intro cache_key witness_id hkey hwitness)

theorem ay_cpcache_merge_partitions
    (left_partition : Prop) (right_partition : Prop) :
    left_partition ->
    right_partition ->
    AyCPCacheMergedPartition left_partition right_partition := by
  intro hleft
  intro hright
  exact ay_cpcache_conj_intro left_partition right_partition
    hleft hright

theorem ay_cpcache_merged_left
    (left_partition : Prop) (right_partition : Prop) :
    AyCPCacheMergedPartition left_partition right_partition ->
    left_partition := by
  intro merged
  exact ay_cpcache_conj_left left_partition right_partition merged

theorem ay_cpcache_merged_right
    (left_partition : Prop) (right_partition : Prop) :
    AyCPCacheMergedPartition left_partition right_partition ->
    right_partition := by
  intro merged
  exact ay_cpcache_conj_right left_partition right_partition merged

theorem ay_cpcache_accumulator_intro
    (accepted : Prop) (cached : Prop) :
    accepted -> cached -> AyCPCacheAccumulator accepted cached := by
  intro haccepted
  intro hcached
  exact ay_cpcache_conj_intro accepted cached haccepted hcached

theorem ay_cpcache_accumulator_compatible
    (accepted : Prop) (cached : Prop) :
    AyCPCacheAccumulator accepted cached ->
    AyCPCacheMergedPartition accepted cached := by
  intro accumulator
  exact ay_cpcache_merge_partitions accepted cached
    (ay_cpcache_conj_left accepted cached accumulator)
    (ay_cpcache_conj_right accepted cached accumulator)

theorem ay_cpcache_merge_checked_and_cached
    (accepted_partition : Prop) (cached_partition : Prop)
    (cache_key : Prop) (witness_id : Prop) :
    accepted_partition ->
    AyCPCacheEntry
      (AyCPCacheGuard cache_key witness_id)
      cached_partition ->
    cache_key ->
    witness_id ->
    AyCPCacheMergedPartition
      accepted_partition cached_partition := by
  intro haccepted
  intro entry
  intro hkey
  intro hwitness
  exact ay_cpcache_merge_partitions
    accepted_partition cached_partition
    haccepted
    (ay_cpcache_reuse_partition
      cache_key witness_id cached_partition entry hkey hwitness)

theorem ay_cpcache_merge_full_equiv
    (visible_cnf : Prop)
    (accepted_partition : Prop) (cached_partition : Prop) :
    (AyCPCacheMergedPartition
      accepted_partition cached_partition -> visible_cnf) ->
    (visible_cnf ->
      AyCPCacheMergedPartition accepted_partition cached_partition) ->
    AyCPCacheEquisat
      (AyCPCacheMergedPartition accepted_partition cached_partition)
      visible_cnf := by
  intro assemble
  intro decompose
  exact ay_cpcache_equisat_intro
    (AyCPCacheMergedPartition accepted_partition cached_partition)
    visible_cnf
    assemble
    decompose

theorem ay_cpcache_compressed_witness_visible
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) :
    AyCPCacheWitnessExpansion compressed_witness full_assignment ->
    AyCPCacheProjection full_assignment visible_assignment ->
    compressed_witness ->
    visible_assignment := by
  intro expand
  intro project
  intro hcompressed
  exact project (expand hcompressed)

theorem ay_cpcache_reconstruct_original
    (visible_assignment : Prop) (original_assignment : Prop) :
    AyCPCachePreprocessReconstruction
      visible_assignment original_assignment ->
    visible_assignment ->
    original_assignment := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_cpcache_cached_full_visible_check
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (accepted_partition : Prop) (cached_partition : Prop)
    (cache_key : Prop) (witness_id : Prop) :
    AyCPCacheWitnessExpansion compressed_witness full_assignment ->
    AyCPCacheProjection full_assignment visible_assignment ->
    accepted_partition ->
    AyCPCacheEntry
      (AyCPCacheGuard cache_key witness_id)
      cached_partition ->
    (AyCPCacheMergedPartition
      accepted_partition cached_partition -> visible_cnf) ->
    compressed_witness ->
    cache_key ->
    witness_id ->
    visible_cnf := by
  intro _expand
  intro _project
  intro haccepted
  intro entry
  intro assemble
  intro _hcompressed
  intro hkey
  intro hwitness
  exact assemble
    (ay_cpcache_merge_checked_and_cached
      accepted_partition cached_partition cache_key witness_id
      haccepted entry hkey hwitness)

theorem ay_cpcache_cached_public_sat_sound
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (accepted_partition : Prop) (cached_partition : Prop)
    (cache_key : Prop) (witness_id : Prop)
    (original_assignment : Prop) :
    AyCPCacheWitnessExpansion compressed_witness full_assignment ->
    AyCPCacheProjection full_assignment visible_assignment ->
    accepted_partition ->
    AyCPCacheEntry
      (AyCPCacheGuard cache_key witness_id)
      cached_partition ->
    (AyCPCacheMergedPartition
      accepted_partition cached_partition -> visible_cnf) ->
    AyCPCachePreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    cache_key ->
    witness_id ->
    AyCPCachePublicSatAnswer original_assignment := by
  intro expand
  intro project
  intro _haccepted
  intro _entry
  intro _assemble
  intro reconstruct
  intro hcompressed
  intro _hkey
  intro _hwitness
  exact reconstruct
    (ay_cpcache_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed)

theorem ay_cpcache_cached_soundness_certificate
    (compressed_witness : Prop) (full_assignment : Prop)
    (visible_assignment : Prop) (visible_cnf : Prop)
    (accepted_partition : Prop) (cached_partition : Prop)
    (cache_key : Prop) (witness_id : Prop)
    (original_assignment : Prop) :
    AyCPCacheWitnessExpansion compressed_witness full_assignment ->
    AyCPCacheProjection full_assignment visible_assignment ->
    accepted_partition ->
    AyCPCacheEntry
      (AyCPCacheGuard cache_key witness_id)
      cached_partition ->
    (AyCPCacheMergedPartition
      accepted_partition cached_partition -> visible_cnf) ->
    AyCPCachePreprocessReconstruction
      visible_assignment original_assignment ->
    compressed_witness ->
    cache_key ->
    witness_id ->
    AyCPCacheConj visible_cnf original_assignment := by
  intro expand
  intro project
  intro haccepted
  intro entry
  intro assemble
  intro reconstruct
  intro hcompressed
  intro hkey
  intro hwitness
  have hvisible : visible_assignment :=
    ay_cpcache_compressed_witness_visible
      compressed_witness full_assignment visible_assignment
      expand project hcompressed
  exact ay_cpcache_conj_intro visible_cnf original_assignment
    (assemble
      (ay_cpcache_merge_checked_and_cached
        accepted_partition cached_partition cache_key witness_id
        haccepted entry hkey hwitness))
    (reconstruct hvisible)
