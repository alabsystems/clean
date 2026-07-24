-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton composing streaming proof replay,
-- incremental assumptions, and clause database GC. Chunk states, assumption
-- scopes, inactive clauses, hints, conflicts, and cores are abstract checker
-- facts connected by explicit maps.

def AySRIGConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AySRIGDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AySRIGEquisat (before : Prop) (after : Prop) :=
  AySRIGConj (before -> after) (after -> before)

def AySRIGScope (active : Prop) (pushed : Prop) :=
  AySRIGConj active pushed

def AySRIGDb (active : Prop) (inactive : Prop) :=
  AySRIGConj active inactive

def AySRIGState (database : Prop) (assumptions : Prop) (log_state : Prop) :=
  AySRIGConj (AySRIGConj database assumptions) log_state

def AySRIGChunkReplay
    (before_state : Prop) (chunk : Prop) (after_state : Prop) :=
  before_state -> chunk -> after_state

def AySRIGHandoff (before_state : Prop) (after_state : Prop) :=
  before_state -> after_state

def AySRIGGcStep (before_database : Prop) (after_database : Prop) :=
  before_database -> after_database

def AySRIGHintProjection (full_hints : Prop) (active_hints : Prop) :=
  full_hints -> active_hints

def AySRIGReplayStep (database : Prop) (hints : Prop) (derived : Prop) :=
  database -> hints -> derived

def AySRIGFinalReplay (state : Prop) (final_clause : Prop) :=
  state -> final_clause

def AySRIGCoreCertificate
    (formula : Prop) (active_assumptions : Prop) (core_assumptions : Prop) :=
  AySRIGConj
    (active_assumptions -> core_assumptions)
    (formula -> core_assumptions -> False)

theorem ay_srig_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AySRIGConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_srig_conj_left
    (left : Prop) (right : Prop) :
    AySRIGConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_srig_conj_right
    (left : Prop) (right : Prop) :
    AySRIGConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_srig_disj_left
    (left : Prop) (right : Prop) :
    left -> AySRIGDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_srig_disj_right
    (left : Prop) (right : Prop) :
    right -> AySRIGDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_srig_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AySRIGEquisat before after := by
  intro forward
  intro backward
  exact ay_srig_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_srig_equisat_forward
    (before : Prop) (after : Prop) :
    AySRIGEquisat before after -> before -> after := by
  intro certificate
  exact ay_srig_conj_left (before -> after) (after -> before) certificate

theorem ay_srig_equisat_backward
    (before : Prop) (after : Prop) :
    AySRIGEquisat before after -> after -> before := by
  intro certificate
  exact ay_srig_conj_right (before -> after) (after -> before) certificate

theorem ay_srig_scope_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AySRIGScope active pushed := by
  intro hactive
  intro hpushed
  exact ay_srig_conj_intro active pushed hactive hpushed

theorem ay_srig_scope_pop
    (active : Prop) (pushed : Prop) :
    AySRIGScope active pushed -> active := by
  intro hscope
  exact ay_srig_conj_left active pushed hscope

theorem ay_srig_state_intro
    (database : Prop) (assumptions : Prop) (log_state : Prop) :
    database -> assumptions -> log_state ->
    AySRIGState database assumptions log_state := by
  intro hdatabase
  intro hassumptions
  intro hlog
  exact ay_srig_conj_intro
    (AySRIGConj database assumptions)
    log_state
    (ay_srig_conj_intro database assumptions hdatabase hassumptions)
    hlog

theorem ay_srig_state_database
    (database : Prop) (assumptions : Prop) (log_state : Prop) :
    AySRIGState database assumptions log_state -> database := by
  intro state
  exact ay_srig_conj_left database assumptions
    (ay_srig_conj_left
      (AySRIGConj database assumptions)
      log_state
      state)

theorem ay_srig_state_assumptions
    (database : Prop) (assumptions : Prop) (log_state : Prop) :
    AySRIGState database assumptions log_state -> assumptions := by
  intro state
  exact ay_srig_conj_right database assumptions
    (ay_srig_conj_left
      (AySRIGConj database assumptions)
      log_state
      state)

theorem ay_srig_state_log
    (database : Prop) (assumptions : Prop) (log_state : Prop) :
    AySRIGState database assumptions log_state -> log_state := by
  intro state
  exact ay_srig_conj_right
    (AySRIGConj database assumptions)
    log_state
    state

theorem ay_srig_chunk_handoff_under_scope
    (database : Prop) (active : Prop) (pushed : Prop)
    (log_a : Prop) (log_b : Prop) (log_c : Prop)
    (chunk_a : Prop) (chunk_b : Prop) :
    AySRIGChunkReplay
      (AySRIGState database (AySRIGScope active pushed) log_a)
      chunk_a
      (AySRIGState database (AySRIGScope active pushed) log_b) ->
    AySRIGHandoff
      (AySRIGState database (AySRIGScope active pushed) log_b)
      (AySRIGState database (AySRIGScope active pushed) log_b) ->
    AySRIGChunkReplay
      (AySRIGState database (AySRIGScope active pushed) log_b)
      chunk_b
      (AySRIGState database (AySRIGScope active pushed) log_c) ->
    AySRIGState database (AySRIGScope active pushed) log_a ->
    AySRIGConj chunk_a chunk_b ->
    AySRIGState database (AySRIGScope active pushed) log_c := by
  intro replay_a
  intro handoff
  intro replay_b
  intro state_a
  intro chunks
  exact replay_b
    (handoff
      (replay_a state_a
        (ay_srig_conj_left chunk_a chunk_b chunks)))
    (ay_srig_conj_right chunk_a chunk_b chunks)

theorem ay_srig_gc_database_under_scope
    (before_database : Prop) (after_database : Prop)
    (assumptions : Prop) (log_state : Prop) :
    AySRIGGcStep before_database after_database ->
    AySRIGState before_database assumptions log_state ->
    AySRIGState after_database assumptions log_state := by
  intro gc_step
  intro state
  exact ay_srig_state_intro after_database assumptions log_state
    (gc_step
      (ay_srig_state_database before_database assumptions log_state state))
    (ay_srig_state_assumptions before_database assumptions log_state state)
    (ay_srig_state_log before_database assumptions log_state state)

theorem ay_srig_chunk_handoff_scope_with_gc
    (before_database : Prop) (after_database : Prop)
    (active : Prop) (pushed : Prop)
    (log_a : Prop) (log_b : Prop) (log_c : Prop)
    (chunk_a : Prop) (chunk_b : Prop) :
    AySRIGChunkReplay
      (AySRIGState before_database (AySRIGScope active pushed) log_a)
      chunk_a
      (AySRIGState before_database (AySRIGScope active pushed) log_b) ->
    AySRIGGcStep before_database after_database ->
    AySRIGChunkReplay
      (AySRIGState after_database (AySRIGScope active pushed) log_b)
      chunk_b
      (AySRIGState after_database (AySRIGScope active pushed) log_c) ->
    AySRIGState before_database (AySRIGScope active pushed) log_a ->
    AySRIGConj chunk_a chunk_b ->
    AySRIGState after_database (AySRIGScope active pushed) log_c := by
  intro replay_a
  intro gc_step
  intro replay_b
  intro state_a
  intro chunks
  exact replay_b
    (ay_srig_gc_database_under_scope before_database after_database
      (AySRIGScope active pushed)
      log_b
      gc_step
      (replay_a state_a
        (ay_srig_conj_left chunk_a chunk_b chunks)))
    (ay_srig_conj_right chunk_a chunk_b chunks)

theorem ay_srig_hint_projection_through_inactive
    (active : Prop) (inactive : Prop)
    (full_hints : Prop) (active_hints : Prop) (derived : Prop) :
    AySRIGHintProjection full_hints active_hints ->
    AySRIGReplayStep active active_hints derived ->
    AySRIGDb active inactive ->
    full_hints ->
    derived := by
  intro project
  intro replay
  intro database
  intro hfull
  exact replay
    (ay_srig_conj_left active inactive database)
    (project hfull)

theorem ay_srig_final_clause_preserved
    (state : Prop) (final_clause : Prop) :
    AySRIGFinalReplay state final_clause ->
    state ->
    AySRIGConj state final_clause := by
  intro final_replay
  intro hstate
  exact ay_srig_conj_intro state final_clause
    hstate
    (final_replay hstate)

theorem ay_srig_final_clause_sound
    (state : Prop) (final_clause : Prop) :
    AySRIGFinalReplay state final_clause ->
    state ->
    final_clause := by
  intro final_replay
  intro hstate
  exact ay_srig_conj_right state final_clause
    (ay_srig_final_clause_preserved state final_clause
      final_replay hstate)

theorem ay_srig_streaming_gc_final_sound
    (before_database : Prop) (after_database : Prop)
    (active : Prop) (pushed : Prop)
    (log_a : Prop) (log_b : Prop) (log_c : Prop)
    (chunk_a : Prop) (chunk_b : Prop) (final_clause : Prop) :
    AySRIGChunkReplay
      (AySRIGState before_database (AySRIGScope active pushed) log_a)
      chunk_a
      (AySRIGState before_database (AySRIGScope active pushed) log_b) ->
    AySRIGGcStep before_database after_database ->
    AySRIGChunkReplay
      (AySRIGState after_database (AySRIGScope active pushed) log_b)
      chunk_b
      (AySRIGState after_database (AySRIGScope active pushed) log_c) ->
    AySRIGFinalReplay
      (AySRIGState after_database (AySRIGScope active pushed) log_c)
      final_clause ->
    AySRIGState before_database (AySRIGScope active pushed) log_a ->
    AySRIGConj chunk_a chunk_b ->
    final_clause := by
  intro replay_a
  intro gc_step
  intro replay_b
  intro final_replay
  intro state_a
  intro chunks
  exact final_replay
    (ay_srig_chunk_handoff_scope_with_gc
      before_database after_database active pushed
      log_a log_b log_c chunk_a chunk_b
      replay_a gc_step replay_b state_a chunks)

theorem ay_srig_core_projection
    (formula : Prop) (active_assumptions : Prop)
    (core_assumptions : Prop) :
    AySRIGCoreCertificate formula active_assumptions core_assumptions ->
    active_assumptions ->
    core_assumptions := by
  intro certificate
  exact ay_srig_conj_left
    (active_assumptions -> core_assumptions)
    (formula -> core_assumptions -> False)
    certificate

theorem ay_srig_core_conflict
    (formula : Prop) (active_assumptions : Prop)
    (core_assumptions : Prop) :
    AySRIGCoreCertificate formula active_assumptions core_assumptions ->
    formula ->
    core_assumptions ->
    False := by
  intro certificate
  exact ay_srig_conj_right
    (active_assumptions -> core_assumptions)
    (formula -> core_assumptions -> False)
    certificate

theorem ay_srig_core_transport_pop_scope
    (formula : Prop) (active : Prop) (pushed : Prop)
    (core_assumptions : Prop) :
    AySRIGCoreCertificate formula active core_assumptions ->
    AySRIGScope active pushed ->
    core_assumptions := by
  intro certificate
  intro hscope
  exact ay_srig_core_projection formula active core_assumptions
    certificate
    (ay_srig_scope_pop active pushed hscope)

theorem ay_srig_conflict_transport_pop_scope
    (formula : Prop) (active : Prop) (pushed : Prop)
    (core_assumptions : Prop) :
    AySRIGCoreCertificate formula active core_assumptions ->
    formula ->
    AySRIGScope active pushed ->
    False := by
  intro certificate
  intro hformula
  intro hscope
  exact ay_srig_core_conflict formula active core_assumptions
    certificate
    hformula
    (ay_srig_core_transport_pop_scope formula active pushed
      core_assumptions certificate hscope)

theorem ay_srig_core_transport_through_gc_equisat
    (before_formula : Prop) (after_formula : Prop)
    (active : Prop) (core_assumptions : Prop) :
    AySRIGEquisat before_formula after_formula ->
    AySRIGCoreCertificate after_formula active core_assumptions ->
    active ->
    core_assumptions := by
  intro _formula_map
  intro certificate
  intro hactive
  exact ay_srig_core_projection after_formula active core_assumptions
    certificate
    hactive

theorem ay_srig_conflict_transport_through_gc_equisat
    (before_formula : Prop) (after_formula : Prop)
    (active : Prop) (core_assumptions : Prop) :
    AySRIGEquisat before_formula after_formula ->
    AySRIGCoreCertificate after_formula active core_assumptions ->
    before_formula ->
    active ->
    False := by
  intro formula_map
  intro certificate
  intro hbefore
  intro hactive
  exact ay_srig_core_conflict after_formula active core_assumptions
    certificate
    (ay_srig_equisat_forward before_formula after_formula
      formula_map hbefore)
    (ay_srig_core_projection after_formula active core_assumptions
      certificate hactive)

theorem ay_srig_streaming_incremental_gc_conflict_sound
    (before_formula : Prop) (after_formula : Prop)
    (before_database : Prop) (after_database : Prop)
    (active : Prop) (pushed : Prop)
    (log_a : Prop) (log_b : Prop) (log_c : Prop)
    (chunk_a : Prop) (chunk_b : Prop)
    (core_assumptions : Prop) :
    AySRIGEquisat before_formula after_formula ->
    AySRIGChunkReplay
      (AySRIGState before_database (AySRIGScope active pushed) log_a)
      chunk_a
      (AySRIGState before_database (AySRIGScope active pushed) log_b) ->
    AySRIGGcStep before_database after_database ->
    AySRIGChunkReplay
      (AySRIGState after_database (AySRIGScope active pushed) log_b)
      chunk_b
      (AySRIGState after_database (AySRIGScope active pushed) log_c) ->
    AySRIGCoreCertificate after_formula active core_assumptions ->
    before_formula ->
    AySRIGState before_database (AySRIGScope active pushed) log_a ->
    AySRIGConj chunk_a chunk_b ->
    False := by
  intro formula_map
  intro replay_a
  intro gc_step
  intro replay_b
  intro certificate
  intro hbefore_formula
  intro state_a
  intro chunks
  have final_state :
      AySRIGState after_database (AySRIGScope active pushed) log_c :=
    ay_srig_chunk_handoff_scope_with_gc
      before_database after_database active pushed
      log_a log_b log_c chunk_a chunk_b
      replay_a gc_step replay_b state_a chunks
  exact ay_srig_conflict_transport_through_gc_equisat
    before_formula after_formula active core_assumptions
    formula_map
    certificate
    hbefore_formula
    (ay_srig_scope_pop active pushed
      (ay_srig_state_assumptions after_database
        (AySRIGScope active pushed)
        log_c
        final_state))
