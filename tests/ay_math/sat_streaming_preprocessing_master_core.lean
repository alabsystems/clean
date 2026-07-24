-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton composing streaming certificate replay with
-- the master preprocessing certificate pipeline. Formula states, visible-model
-- maps, proof chunks, and final UNSAT replay are abstract checker facts.

def AySPMConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AySPMDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AySPMEquisat (before : Prop) (after : Prop) :=
  AySPMConj (before -> after) (after -> before)

def AySPMForwardMap (before : Prop) (after : Prop) :=
  before -> after

def AySPMBackwardMap (before : Prop) (after : Prop) :=
  after -> before

def AySPMVisibleMap (internal : Prop) (visible : Prop) :=
  AySPMConj (internal -> visible) (visible -> internal)

def AySPMPreprocessCertificate
    (before : Prop) (after : Prop) (visible_before : Prop)
    (visible_after : Prop) :=
  AySPMConj
    (AySPMEquisat before after)
    (AySPMConj
      (AySPMVisibleMap before visible_before)
      (AySPMVisibleMap after visible_after))

def AySPMChunkReplay (before_state : Prop) (chunk : Prop)
    (after_state : Prop) :=
  before_state -> chunk -> after_state

def AySPMChunkPair (first_chunk : Prop) (second_chunk : Prop) :=
  AySPMConj first_chunk second_chunk

def AySPMFinalUnsatReplay (state : Prop) (unsat : Prop) :=
  state -> unsat

def AySPMStreamingCertificate (state : Prop) (visible : Prop) (unsat : Prop) :=
  AySPMConj (AySPMVisibleMap state visible) unsat

theorem ay_spm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AySPMConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_spm_conj_left
    (left : Prop) (right : Prop) :
    AySPMConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_spm_conj_right
    (left : Prop) (right : Prop) :
    AySPMConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_spm_disj_left
    (left : Prop) (right : Prop) :
    left -> AySPMDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_spm_disj_right
    (left : Prop) (right : Prop) :
    right -> AySPMDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_spm_equisat_intro
    (before : Prop) (after : Prop) :
    AySPMForwardMap before after ->
    AySPMBackwardMap before after ->
    AySPMEquisat before after := by
  intro forward
  intro backward
  exact ay_spm_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_spm_equisat_forward
    (before : Prop) (after : Prop) :
    AySPMEquisat before after -> AySPMForwardMap before after := by
  intro certificate
  exact ay_spm_conj_left (before -> after) (after -> before) certificate

theorem ay_spm_equisat_backward
    (before : Prop) (after : Prop) :
    AySPMEquisat before after -> AySPMBackwardMap before after := by
  intro certificate
  exact ay_spm_conj_right (before -> after) (after -> before) certificate

theorem ay_spm_equisat_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AySPMEquisat a b ->
    AySPMEquisat b c ->
    AySPMEquisat a c := by
  intro ab
  intro bc
  exact ay_spm_equisat_intro a c
    (fun ha => ay_spm_equisat_forward b c bc
      (ay_spm_equisat_forward a b ab ha))
    (fun hc => ay_spm_equisat_backward a b ab
      (ay_spm_equisat_backward b c bc hc))

theorem ay_spm_visible_map_intro
    (internal : Prop) (visible : Prop) :
    (internal -> visible) ->
    (visible -> internal) ->
    AySPMVisibleMap internal visible := by
  intro project
  intro reconstruct
  exact ay_spm_conj_intro
    (internal -> visible)
    (visible -> internal)
    project
    reconstruct

theorem ay_spm_visible_project
    (internal : Prop) (visible : Prop) :
    AySPMVisibleMap internal visible -> internal -> visible := by
  intro visible_map
  exact ay_spm_conj_left (internal -> visible) (visible -> internal)
    visible_map

theorem ay_spm_visible_reconstruct
    (internal : Prop) (visible : Prop) :
    AySPMVisibleMap internal visible -> visible -> internal := by
  intro visible_map
  exact ay_spm_conj_right (internal -> visible) (visible -> internal)
    visible_map

theorem ay_spm_visible_map_transport_forward
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMEquisat before after ->
    AySPMVisibleMap before visible_before ->
    AySPMVisibleMap after visible_after ->
    (visible_before -> visible_after) := by
  intro stage
  intro before_visible
  intro after_visible
  intro hvisible_before
  exact ay_spm_visible_project after visible_after after_visible
    (ay_spm_equisat_forward before after stage
      (ay_spm_visible_reconstruct before visible_before before_visible
        hvisible_before))

theorem ay_spm_visible_map_transport_backward
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMEquisat before after ->
    AySPMVisibleMap before visible_before ->
    AySPMVisibleMap after visible_after ->
    (visible_after -> visible_before) := by
  intro stage
  intro before_visible
  intro after_visible
  intro hvisible_after
  exact ay_spm_visible_project before visible_before before_visible
    (ay_spm_equisat_backward before after stage
      (ay_spm_visible_reconstruct after visible_after after_visible
        hvisible_after))

theorem ay_spm_preprocess_certificate_stage
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMPreprocessCertificate
      before after visible_before visible_after ->
    AySPMEquisat before after := by
  intro certificate
  exact ay_spm_conj_left
    (AySPMEquisat before after)
    (AySPMConj
      (AySPMVisibleMap before visible_before)
      (AySPMVisibleMap after visible_after))
    certificate

theorem ay_spm_preprocess_visible_before
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMPreprocessCertificate
      before after visible_before visible_after ->
    AySPMVisibleMap before visible_before := by
  intro certificate
  exact ay_spm_conj_left
    (AySPMVisibleMap before visible_before)
    (AySPMVisibleMap after visible_after)
    (ay_spm_conj_right
      (AySPMEquisat before after)
      (AySPMConj
        (AySPMVisibleMap before visible_before)
        (AySPMVisibleMap after visible_after))
      certificate)

theorem ay_spm_preprocess_visible_after
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMPreprocessCertificate
      before after visible_before visible_after ->
    AySPMVisibleMap after visible_after := by
  intro certificate
  exact ay_spm_conj_right
    (AySPMVisibleMap before visible_before)
    (AySPMVisibleMap after visible_after)
    (ay_spm_conj_right
      (AySPMEquisat before after)
      (AySPMConj
        (AySPMVisibleMap before visible_before)
        (AySPMVisibleMap after visible_after))
      certificate)

theorem ay_spm_preprocess_visible_transport
    (before : Prop) (after : Prop)
    (visible_before : Prop) (visible_after : Prop) :
    AySPMPreprocessCertificate
      before after visible_before visible_after ->
    AySPMEquisat visible_before visible_after := by
  intro certificate
  exact ay_spm_equisat_intro visible_before visible_after
    (ay_spm_visible_map_transport_forward before after
      visible_before visible_after
      (ay_spm_preprocess_certificate_stage before after
        visible_before visible_after certificate)
      (ay_spm_preprocess_visible_before before after
        visible_before visible_after certificate)
      (ay_spm_preprocess_visible_after before after
        visible_before visible_after certificate))
    (ay_spm_visible_map_transport_backward before after
      visible_before visible_after
      (ay_spm_preprocess_certificate_stage before after
        visible_before visible_after certificate)
      (ay_spm_preprocess_visible_before before after
        visible_before visible_after certificate)
      (ay_spm_preprocess_visible_after before after
        visible_before visible_after certificate))

theorem ay_spm_two_preprocess_visible_transport
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop)
    (visible0 : Prop) (visible1 : Prop) (visible2 : Prop) :
    AySPMPreprocessCertificate stage0 stage1 visible0 visible1 ->
    AySPMPreprocessCertificate stage1 stage2 visible1 visible2 ->
    AySPMEquisat visible0 visible2 := by
  intro first_cert
  intro second_cert
  exact ay_spm_equisat_intro visible0 visible2
    (fun hvisible0 =>
      ay_spm_equisat_forward visible1 visible2
        (ay_spm_preprocess_visible_transport stage1 stage2
          visible1 visible2 second_cert)
        (ay_spm_equisat_forward visible0 visible1
          (ay_spm_preprocess_visible_transport stage0 stage1
            visible0 visible1 first_cert)
          hvisible0))
    (fun hvisible2 =>
      ay_spm_equisat_backward visible0 visible1
        (ay_spm_preprocess_visible_transport stage0 stage1
          visible0 visible1 first_cert)
        (ay_spm_equisat_backward visible1 visible2
          (ay_spm_preprocess_visible_transport stage1 stage2
            visible1 visible2 second_cert)
          hvisible2))

theorem ay_spm_chunk_pair_intro
    (first_chunk : Prop) (second_chunk : Prop) :
    first_chunk ->
    second_chunk ->
    AySPMChunkPair first_chunk second_chunk := by
  intro hfirst
  intro hsecond
  exact ay_spm_conj_intro first_chunk second_chunk hfirst hsecond

theorem ay_spm_chunk_pair_first
    (first_chunk : Prop) (second_chunk : Prop) :
    AySPMChunkPair first_chunk second_chunk -> first_chunk := by
  intro chunks
  exact ay_spm_conj_left first_chunk second_chunk chunks

theorem ay_spm_chunk_pair_second
    (first_chunk : Prop) (second_chunk : Prop) :
    AySPMChunkPair first_chunk second_chunk -> second_chunk := by
  intro chunks
  exact ay_spm_conj_right first_chunk second_chunk chunks

theorem ay_spm_chunk_handoff
    (state0 : Prop) (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) :
    AySPMChunkReplay state0 chunk0 state1 ->
    AySPMChunkReplay state1 chunk1 state2 ->
    state0 ->
    AySPMChunkPair chunk0 chunk1 ->
    state2 := by
  intro first_replay
  intro second_replay
  intro hstate0
  intro chunks
  exact second_replay
    (first_replay hstate0
      (ay_spm_chunk_pair_first chunk0 chunk1 chunks))
    (ay_spm_chunk_pair_second chunk0 chunk1 chunks)

theorem ay_spm_chunked_unsat_replay
    (state0 : Prop) (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (unsat : Prop) :
    AySPMChunkReplay state0 chunk0 state1 ->
    AySPMChunkReplay state1 chunk1 state2 ->
    AySPMFinalUnsatReplay state2 unsat ->
    state0 ->
    AySPMChunkPair chunk0 chunk1 ->
    unsat := by
  intro first_replay
  intro second_replay
  intro final_replay
  intro hstate0
  intro chunks
  exact final_replay
    (ay_spm_chunk_handoff state0 state1 state2 chunk0 chunk1
      first_replay second_replay hstate0 chunks)

theorem ay_spm_streaming_certificate_intro
    (state : Prop) (visible : Prop) (unsat : Prop) :
    AySPMVisibleMap state visible ->
    unsat ->
    AySPMStreamingCertificate state visible unsat := by
  intro visible_map
  intro hunsat
  exact ay_spm_conj_intro (AySPMVisibleMap state visible) unsat
    visible_map
    hunsat

theorem ay_spm_streaming_certificate_unsat
    (state : Prop) (visible : Prop) (unsat : Prop) :
    AySPMStreamingCertificate state visible unsat -> unsat := by
  intro certificate
  exact ay_spm_conj_right (AySPMVisibleMap state visible) unsat
    certificate

theorem ay_spm_streaming_preprocess_unsat_sound
    (original : Prop) (preprocessed : Prop)
    (visible_original : Prop) (visible_preprocessed : Prop)
    (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (unsat : Prop) :
    AySPMPreprocessCertificate
      original preprocessed visible_original visible_preprocessed ->
    AySPMChunkReplay preprocessed chunk0 state1 ->
    AySPMChunkReplay state1 chunk1 state2 ->
    AySPMFinalUnsatReplay state2 unsat ->
    original ->
    AySPMChunkPair chunk0 chunk1 ->
    unsat := by
  intro preprocess
  intro first_replay
  intro second_replay
  intro final_replay
  intro horiginal
  intro chunks
  exact ay_spm_chunked_unsat_replay
    preprocessed state1 state2 chunk0 chunk1 unsat
    first_replay
    second_replay
    final_replay
    (ay_spm_equisat_forward original preprocessed
      (ay_spm_preprocess_certificate_stage original preprocessed
        visible_original visible_preprocessed preprocess)
      horiginal)
    chunks

theorem ay_spm_streaming_preprocess_certificate
    (original : Prop) (preprocessed : Prop)
    (visible_original : Prop) (visible_preprocessed : Prop)
    (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (unsat : Prop) :
    AySPMPreprocessCertificate
      original preprocessed visible_original visible_preprocessed ->
    AySPMChunkReplay preprocessed chunk0 state1 ->
    AySPMChunkReplay state1 chunk1 state2 ->
    AySPMFinalUnsatReplay state2 unsat ->
    original ->
    AySPMChunkPair chunk0 chunk1 ->
    AySPMStreamingCertificate preprocessed visible_preprocessed unsat := by
  intro preprocess
  intro first_replay
  intro second_replay
  intro final_replay
  intro horiginal
  intro chunks
  exact ay_spm_streaming_certificate_intro
    preprocessed
    visible_preprocessed
    unsat
    (ay_spm_preprocess_visible_after original preprocessed
      visible_original visible_preprocessed preprocess)
    (ay_spm_streaming_preprocess_unsat_sound
      original preprocessed visible_original visible_preprocessed
      state1 state2 chunk0 chunk1 unsat
      preprocess first_replay second_replay final_replay
      horiginal chunks)

theorem ay_spm_master_pipeline_visible_and_unsat
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop)
    (visible0 : Prop) (visible1 : Prop) (visible2 : Prop)
    (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (unsat : Prop) :
    AySPMPreprocessCertificate stage0 stage1 visible0 visible1 ->
    AySPMPreprocessCertificate stage1 stage2 visible1 visible2 ->
    AySPMChunkReplay stage2 chunk0 state1 ->
    AySPMChunkReplay state1 chunk1 state2 ->
    AySPMFinalUnsatReplay state2 unsat ->
    stage0 ->
    AySPMChunkPair chunk0 chunk1 ->
    AySPMConj (AySPMEquisat visible0 visible2) unsat := by
  intro first_preprocess
  intro second_preprocess
  intro first_replay
  intro second_replay
  intro final_replay
  intro hstage0
  intro chunks
  exact ay_spm_conj_intro
    (AySPMEquisat visible0 visible2)
    unsat
    (ay_spm_two_preprocess_visible_transport
      stage0 stage1 stage2 visible0 visible1 visible2
      first_preprocess second_preprocess)
    (ay_spm_chunked_unsat_replay
      stage2 state1 state2 chunk0 chunk1 unsat
      first_replay second_replay final_replay
      (ay_spm_equisat_forward stage1 stage2
        (ay_spm_preprocess_certificate_stage stage1 stage2
          visible1 visible2 second_preprocess)
        (ay_spm_equisat_forward stage0 stage1
          (ay_spm_preprocess_certificate_stage stage0 stage1
            visible0 visible1 first_preprocess)
          hstage0))
      chunks)
