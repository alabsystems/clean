-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for streaming certificate replay. Chunk
-- states, proof-log chunks, GC transitions, and monolithic replay are abstract
-- checker facts connected by explicit state handoff maps.

def AyStreamConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyStreamDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyStreamEquisat (before : Prop) (after : Prop) :=
  AyStreamConj (before -> after) (after -> before)

def AyStreamChunkReplay (before_state : Prop) (chunk : Prop)
    (after_state : Prop) :=
  before_state -> chunk -> after_state

def AyStreamStateHandoff (from_state : Prop) (to_state : Prop) :=
  from_state -> to_state

def AyStreamGcStep (before_state : Prop) (after_state : Prop) :=
  before_state -> after_state

def AyStreamFinalReplay (state : Prop) (final_clause : Prop) :=
  state -> final_clause

def AyStreamMonolithicReplay
    (initial_state : Prop) (full_log : Prop) (final_clause : Prop) :=
  initial_state -> full_log -> final_clause

def AyStreamChunkPair (left_chunk : Prop) (right_chunk : Prop) :=
  AyStreamConj left_chunk right_chunk

def AyStreamReplayTrace (state : Prop) (final_clause : Prop) :=
  AyStreamConj state final_clause

theorem ay_stream_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyStreamConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_stream_conj_left
    (left : Prop) (right : Prop) :
    AyStreamConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_stream_conj_right
    (left : Prop) (right : Prop) :
    AyStreamConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_stream_disj_left
    (left : Prop) (right : Prop) :
    left -> AyStreamDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_stream_disj_right
    (left : Prop) (right : Prop) :
    right -> AyStreamDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_stream_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyStreamEquisat before after := by
  intro forward
  intro backward
  exact ay_stream_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_stream_equisat_forward
    (before : Prop) (after : Prop) :
    AyStreamEquisat before after -> before -> after := by
  intro certificate
  exact ay_stream_conj_left (before -> after) (after -> before) certificate

theorem ay_stream_equisat_backward
    (before : Prop) (after : Prop) :
    AyStreamEquisat before after -> after -> before := by
  intro certificate
  exact ay_stream_conj_right (before -> after) (after -> before) certificate

theorem ay_stream_chunk_pair_intro
    (left_chunk : Prop) (right_chunk : Prop) :
    left_chunk ->
    right_chunk ->
    AyStreamChunkPair left_chunk right_chunk := by
  intro hleft
  intro hright
  exact ay_stream_conj_intro left_chunk right_chunk hleft hright

theorem ay_stream_chunk_pair_left
    (left_chunk : Prop) (right_chunk : Prop) :
    AyStreamChunkPair left_chunk right_chunk -> left_chunk := by
  intro chunks
  exact ay_stream_conj_left left_chunk right_chunk chunks

theorem ay_stream_chunk_pair_right
    (left_chunk : Prop) (right_chunk : Prop) :
    AyStreamChunkPair left_chunk right_chunk -> right_chunk := by
  intro chunks
  exact ay_stream_conj_right left_chunk right_chunk chunks

theorem ay_stream_chunk_replay_sound
    (before_state : Prop) (chunk : Prop) (after_state : Prop) :
    AyStreamChunkReplay before_state chunk after_state ->
    before_state ->
    chunk ->
    after_state := by
  intro replay
  intro hbefore
  intro hchunk
  exact replay hbefore hchunk

theorem ay_stream_state_handoff_sound
    (from_state : Prop) (to_state : Prop) :
    AyStreamStateHandoff from_state to_state ->
    from_state ->
    to_state := by
  intro handoff
  intro hfrom
  exact handoff hfrom

theorem ay_stream_two_chunk_handoff
    (initial_state : Prop) (middle_state : Prop)
    (handoff_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop) :
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamStateHandoff middle_state handoff_state ->
    AyStreamChunkReplay handoff_state second_chunk final_state ->
    initial_state ->
    AyStreamChunkPair first_chunk second_chunk ->
    final_state := by
  intro first_replay
  intro handoff
  intro second_replay
  intro hinitial
  intro chunks
  exact second_replay
    (handoff (first_replay hinitial
      (ay_stream_chunk_pair_left first_chunk second_chunk chunks)))
    (ay_stream_chunk_pair_right first_chunk second_chunk chunks)

theorem ay_stream_gc_between_chunks
    (initial_state : Prop) (middle_state : Prop)
    (after_gc_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop) :
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamGcStep middle_state after_gc_state ->
    AyStreamChunkReplay after_gc_state second_chunk final_state ->
    initial_state ->
    AyStreamChunkPair first_chunk second_chunk ->
    final_state := by
  intro first_replay
  intro gc_step
  intro second_replay
  exact ay_stream_two_chunk_handoff
    initial_state middle_state after_gc_state final_state
    first_chunk second_chunk
    first_replay
    gc_step
    second_replay

theorem ay_stream_gc_equisat
    (before_state : Prop) (after_state : Prop) :
    AyStreamGcStep before_state after_state ->
    (after_state -> before_state) ->
    AyStreamEquisat before_state after_state := by
  intro gc_step
  intro gc_reconstruct
  exact ay_stream_equisat_intro before_state after_state
    gc_step
    gc_reconstruct

theorem ay_stream_final_clause_preserved
    (state : Prop) (final_clause : Prop) :
    AyStreamFinalReplay state final_clause ->
    state ->
    AyStreamReplayTrace state final_clause := by
  intro final_replay
  intro hstate
  exact ay_stream_conj_intro state final_clause
    hstate
    (final_replay hstate)

theorem ay_stream_final_clause_sound
    (state : Prop) (final_clause : Prop) :
    AyStreamFinalReplay state final_clause ->
    state ->
    final_clause := by
  intro final_replay
  intro hstate
  exact ay_stream_conj_right state final_clause
    (ay_stream_final_clause_preserved state final_clause
      final_replay hstate)

theorem ay_stream_two_chunk_final_sound
    (initial_state : Prop) (middle_state : Prop)
    (handoff_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop)
    (final_clause : Prop) :
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamStateHandoff middle_state handoff_state ->
    AyStreamChunkReplay handoff_state second_chunk final_state ->
    AyStreamFinalReplay final_state final_clause ->
    initial_state ->
    AyStreamChunkPair first_chunk second_chunk ->
    final_clause := by
  intro first_replay
  intro handoff
  intro second_replay
  intro final_replay
  intro hinitial
  intro chunks
  exact final_replay
    (ay_stream_two_chunk_handoff
      initial_state middle_state handoff_state final_state
      first_chunk second_chunk
      first_replay handoff second_replay hinitial chunks)

theorem ay_stream_gc_two_chunk_final_sound
    (initial_state : Prop) (middle_state : Prop)
    (after_gc_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop)
    (final_clause : Prop) :
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamGcStep middle_state after_gc_state ->
    AyStreamChunkReplay after_gc_state second_chunk final_state ->
    AyStreamFinalReplay final_state final_clause ->
    initial_state ->
    AyStreamChunkPair first_chunk second_chunk ->
    final_clause := by
  intro first_replay
  intro gc_step
  intro second_replay
  exact ay_stream_two_chunk_final_sound
    initial_state middle_state after_gc_state final_state
    first_chunk second_chunk final_clause
    first_replay gc_step second_replay

theorem ay_stream_chunked_to_monolithic
    (initial_state : Prop) (middle_state : Prop)
    (handoff_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop)
    (full_log : Prop) (final_clause : Prop) :
    (full_log -> AyStreamChunkPair first_chunk second_chunk) ->
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamStateHandoff middle_state handoff_state ->
    AyStreamChunkReplay handoff_state second_chunk final_state ->
    AyStreamFinalReplay final_state final_clause ->
    AyStreamMonolithicReplay initial_state full_log final_clause := by
  intro split_log
  intro first_replay
  intro handoff
  intro second_replay
  intro final_replay
  intro hinitial
  intro hfull
  exact ay_stream_two_chunk_final_sound
    initial_state middle_state handoff_state final_state
    first_chunk second_chunk final_clause
    first_replay handoff second_replay final_replay
    hinitial
    (split_log hfull)

theorem ay_stream_monolithic_to_chunked_final
    (initial_state : Prop) (first_chunk : Prop)
    (second_chunk : Prop) (full_log : Prop) (final_clause : Prop) :
    (AyStreamChunkPair first_chunk second_chunk -> full_log) ->
    AyStreamMonolithicReplay initial_state full_log final_clause ->
    initial_state ->
    AyStreamChunkPair first_chunk second_chunk ->
    final_clause := by
  intro join_log
  intro monolithic
  intro hinitial
  intro chunks
  exact monolithic hinitial (join_log chunks)

theorem ay_stream_chunked_monolithic_equiv
    (initial_state : Prop) (middle_state : Prop)
    (handoff_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop)
    (full_log : Prop) (final_clause : Prop) :
    (full_log -> AyStreamChunkPair first_chunk second_chunk) ->
    (AyStreamChunkPair first_chunk second_chunk -> full_log) ->
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamStateHandoff middle_state handoff_state ->
    AyStreamChunkReplay handoff_state second_chunk final_state ->
    AyStreamFinalReplay final_state final_clause ->
    AyStreamEquisat
      (AyStreamConj initial_state full_log)
      (AyStreamConj initial_state
        (AyStreamChunkPair first_chunk second_chunk)) := by
  intro split_log
  intro join_log
  intro _first_replay
  intro _handoff
  intro _second_replay
  intro _final_replay
  exact ay_stream_equisat_intro
    (AyStreamConj initial_state full_log)
    (AyStreamConj initial_state
      (AyStreamChunkPair first_chunk second_chunk))
    (fun monolithic_input =>
      ay_stream_conj_intro initial_state
        (AyStreamChunkPair first_chunk second_chunk)
        (ay_stream_conj_left initial_state full_log monolithic_input)
        (split_log
          (ay_stream_conj_right initial_state full_log monolithic_input)))
    (fun chunked_input =>
      ay_stream_conj_intro initial_state full_log
        (ay_stream_conj_left initial_state
          (AyStreamChunkPair first_chunk second_chunk)
          chunked_input)
        (join_log
          (ay_stream_conj_right initial_state
            (AyStreamChunkPair first_chunk second_chunk)
            chunked_input)))

theorem ay_stream_gc_chunked_monolithic_final_sound
    (initial_state : Prop) (middle_state : Prop)
    (after_gc_state : Prop) (final_state : Prop)
    (first_chunk : Prop) (second_chunk : Prop)
    (full_log : Prop) (final_clause : Prop) :
    (full_log -> AyStreamChunkPair first_chunk second_chunk) ->
    AyStreamChunkReplay initial_state first_chunk middle_state ->
    AyStreamGcStep middle_state after_gc_state ->
    AyStreamChunkReplay after_gc_state second_chunk final_state ->
    AyStreamFinalReplay final_state final_clause ->
    initial_state ->
    full_log ->
    final_clause := by
  intro split_log
  intro first_replay
  intro gc_step
  intro second_replay
  intro final_replay
  intro hinitial
  intro hfull
  exact ay_stream_gc_two_chunk_final_sound
    initial_state middle_state after_gc_state final_state
    first_chunk second_chunk final_clause
    first_replay gc_step second_replay final_replay
    hinitial
    (split_log hfull)
