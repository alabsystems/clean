-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton integrating proof-log replay with clause
-- database garbage collection. Active clauses, inactive clauses, projected
-- hints, compressed logs, and final clauses are abstract checker facts.

def AyPRGCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyPRGCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPRGCEquisat (before : Prop) (after : Prop) :=
  AyPRGCConj (before -> after) (after -> before)

def AyPRGCDatabase (active : Prop) (inactive : Prop) :=
  AyPRGCConj active inactive

def AyPRGCActiveReplay (active : Prop) (hints : Prop) (derived : Prop) :=
  active -> hints -> derived

def AyPRGCHintProjection (full_hints : Prop) (active_hints : Prop) :=
  full_hints -> active_hints

def AyPRGCDeleteStep (before : Prop) (after : Prop) :=
  before -> after

def AyPRGCReaddStep (after_delete : Prop) (after_readd : Prop) :=
  after_delete -> after_readd

def AyPRGCCompressedLog (active : Prop) (final_clause : Prop) :=
  AyPRGCConj active final_clause

def AyPRGCReplayThenDelete
    (active : Prop) (derived : Prop) (after_gc : Prop) :=
  AyPRGCConj (AyPRGCConj active derived) after_gc

def AyPRGCDeleteThenReplay
    (after_gc : Prop) (derived : Prop) :=
  AyPRGCConj after_gc derived

theorem ay_prgc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyPRGCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_prgc_conj_left
    (left : Prop) (right : Prop) :
    AyPRGCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_prgc_conj_right
    (left : Prop) (right : Prop) :
    AyPRGCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_prgc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyPRGCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_prgc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyPRGCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_prgc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyPRGCEquisat before after := by
  intro forward
  intro backward
  exact ay_prgc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_prgc_equisat_forward
    (before : Prop) (after : Prop) :
    AyPRGCEquisat before after -> before -> after := by
  intro certificate
  exact ay_prgc_conj_left (before -> after) (after -> before) certificate

theorem ay_prgc_equisat_backward
    (before : Prop) (after : Prop) :
    AyPRGCEquisat before after -> after -> before := by
  intro certificate
  exact ay_prgc_conj_right (before -> after) (after -> before) certificate

theorem ay_prgc_database_active
    (active : Prop) (inactive : Prop) :
    AyPRGCDatabase active inactive -> active := by
  intro database
  exact ay_prgc_conj_left active inactive database

theorem ay_prgc_database_inactive
    (active : Prop) (inactive : Prop) :
    AyPRGCDatabase active inactive -> inactive := by
  intro database
  exact ay_prgc_conj_right active inactive database

theorem ay_prgc_hint_projection_sound
    (full_hints : Prop) (active_hints : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    full_hints ->
    active_hints := by
  intro project
  intro hfull
  exact project hfull

theorem ay_prgc_replay_with_projected_hints
    (active : Prop) (full_hints : Prop)
    (active_hints : Prop) (derived : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay active active_hints derived ->
    AyPRGCActiveReplay active full_hints derived := by
  intro project
  intro replay
  intro hactive
  intro hfull
  exact replay hactive (project hfull)

theorem ay_prgc_hint_projection_through_inactive_clauses
    (active : Prop) (inactive : Prop)
    (full_hints : Prop) (active_hints : Prop) (derived : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay active active_hints derived ->
    AyPRGCDatabase active inactive ->
    full_hints ->
    derived := by
  intro project
  intro replay
  intro database
  intro hfull
  exact replay
    (ay_prgc_database_active active inactive database)
    (project hfull)

theorem ay_prgc_replay_after_deletion
    (before_gc : Prop) (after_gc : Prop)
    (hints : Prop) (derived : Prop) :
    AyPRGCDeleteStep before_gc after_gc ->
    AyPRGCActiveReplay after_gc hints derived ->
    before_gc ->
    hints ->
    AyPRGCDeleteThenReplay after_gc derived := by
  intro delete_step
  intro replay
  intro hbefore
  intro hhints
  have hafter : after_gc := delete_step hbefore
  exact ay_prgc_conj_intro after_gc derived
    hafter
    (replay hafter hhints)

theorem ay_prgc_replay_after_deletion_final_sound
    (before_gc : Prop) (after_gc : Prop)
    (hints : Prop) (derived : Prop) :
    AyPRGCDeleteStep before_gc after_gc ->
    AyPRGCActiveReplay after_gc hints derived ->
    before_gc ->
    hints ->
    derived := by
  intro delete_step
  intro replay
  intro hbefore
  intro hhints
  exact ay_prgc_conj_right after_gc derived
    (ay_prgc_replay_after_deletion before_gc after_gc hints derived
      delete_step replay hbefore hhints)

theorem ay_prgc_deletion_after_replay
    (active : Prop) (hints : Prop)
    (derived : Prop) (after_gc : Prop) :
    AyPRGCActiveReplay active hints derived ->
    AyPRGCDeleteStep active after_gc ->
    active ->
    hints ->
    AyPRGCReplayThenDelete active derived after_gc := by
  intro replay
  intro delete_step
  intro hactive
  intro hhints
  exact ay_prgc_conj_intro
    (AyPRGCConj active derived)
    after_gc
    (ay_prgc_conj_intro active derived
      hactive
      (replay hactive hhints))
    (delete_step hactive)

theorem ay_prgc_deletion_after_replay_final_sound
    (active : Prop) (hints : Prop)
    (derived : Prop) (after_gc : Prop) :
    AyPRGCActiveReplay active hints derived ->
    AyPRGCDeleteStep active after_gc ->
    active ->
    hints ->
    derived := by
  intro replay
  intro delete_step
  intro hactive
  intro hhints
  exact ay_prgc_conj_right active derived
    (ay_prgc_conj_left
      (AyPRGCConj active derived)
      after_gc
      (ay_prgc_deletion_after_replay active hints derived after_gc
        replay delete_step hactive hhints))

theorem ay_prgc_delete_readd_equisat
    (before_gc : Prop) (after_gc : Prop) (after_readd : Prop) :
    AyPRGCDeleteStep before_gc after_gc ->
    AyPRGCReaddStep after_gc after_readd ->
    (after_readd -> before_gc) ->
    AyPRGCEquisat before_gc after_readd := by
  intro delete_step
  intro readd_step
  intro project_back
  exact ay_prgc_equisat_intro before_gc after_readd
    (fun hbefore => readd_step (delete_step hbefore))
    project_back

theorem ay_prgc_compressed_log_intro
    (active : Prop) (final_clause : Prop) :
    active -> final_clause -> AyPRGCCompressedLog active final_clause := by
  intro hactive
  intro hfinal
  exact ay_prgc_conj_intro active final_clause hactive hfinal

theorem ay_prgc_compressed_log_active
    (active : Prop) (final_clause : Prop) :
    AyPRGCCompressedLog active final_clause -> active := by
  intro log
  exact ay_prgc_conj_left active final_clause log

theorem ay_prgc_compressed_log_final
    (active : Prop) (final_clause : Prop) :
    AyPRGCCompressedLog active final_clause -> final_clause := by
  intro log
  exact ay_prgc_conj_right active final_clause log

theorem ay_prgc_compressed_log_sound
    (active : Prop) (full_hints : Prop)
    (active_hints : Prop) (final_clause : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay active active_hints final_clause ->
    active ->
    full_hints ->
    AyPRGCCompressedLog active final_clause := by
  intro project
  intro replay
  intro hactive
  intro hfull
  exact ay_prgc_compressed_log_intro active final_clause
    hactive
    (replay hactive (project hfull))

theorem ay_prgc_compressed_log_final_sound
    (active : Prop) (full_hints : Prop)
    (active_hints : Prop) (final_clause : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay active active_hints final_clause ->
    active ->
    full_hints ->
    final_clause := by
  intro project
  intro replay
  intro hactive
  intro hfull
  exact ay_prgc_compressed_log_final active final_clause
    (ay_prgc_compressed_log_sound active full_hints active_hints final_clause
      project replay hactive hfull)

theorem ay_prgc_replay_gc_compressed_pipeline_sound
    (before_gc : Prop) (after_gc : Prop)
    (full_hints : Prop) (active_hints : Prop) (final_clause : Prop) :
    AyPRGCDeleteStep before_gc after_gc ->
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay after_gc active_hints final_clause ->
    before_gc ->
    full_hints ->
    AyPRGCCompressedLog after_gc final_clause := by
  intro delete_step
  intro project
  intro replay
  intro hbefore
  intro hfull
  have hafter : after_gc := delete_step hbefore
  exact ay_prgc_compressed_log_intro after_gc final_clause
    hafter
    (replay hafter (project hfull))

theorem ay_prgc_replay_gc_compressed_final_sound
    (before_gc : Prop) (after_gc : Prop)
    (full_hints : Prop) (active_hints : Prop) (final_clause : Prop) :
    AyPRGCDeleteStep before_gc after_gc ->
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay after_gc active_hints final_clause ->
    before_gc ->
    full_hints ->
    final_clause := by
  intro delete_step
  intro project
  intro replay
  intro hbefore
  intro hfull
  exact ay_prgc_compressed_log_final after_gc final_clause
    (ay_prgc_replay_gc_compressed_pipeline_sound
      before_gc after_gc full_hints active_hints final_clause
      delete_step project replay hbefore hfull)

theorem ay_prgc_compressed_log_equisat
    (active : Prop) (full_hints : Prop)
    (active_hints : Prop) (final_clause : Prop) :
    AyPRGCHintProjection full_hints active_hints ->
    AyPRGCActiveReplay active active_hints final_clause ->
    full_hints ->
    AyPRGCEquisat active (AyPRGCCompressedLog active final_clause) := by
  intro project
  intro replay
  intro hfull
  exact ay_prgc_equisat_intro
    active
    (AyPRGCCompressedLog active final_clause)
    (fun hactive =>
      ay_prgc_compressed_log_sound active full_hints active_hints final_clause
        project replay hactive hfull)
    (ay_prgc_compressed_log_active active final_clause)
