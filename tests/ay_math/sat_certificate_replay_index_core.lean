-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for certificate replay index and renumbering
-- soundness. Clause-id maps, hint projection, deletion/readdition, and
-- LRAT/RAT replay are abstract propositions standing for checker facts.

def AyCRIConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCRIDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCRIEquisat (before : Prop) (after : Prop) :=
  AyCRIConj (before -> after) (after -> before)

def AyCRIClauseRenaming (old_id : Prop) (new_id : Prop) :=
  old_id -> new_id

def AyCRIClauseUnrenaming (old_id : Prop) (new_id : Prop) :=
  new_id -> old_id

def AyCRIHintProjection (full_hints : Prop) (projected_hints : Prop) :=
  full_hints -> projected_hints

def AyCRIReplayStep (database : Prop) (hints : Prop) (derived : Prop) :=
  database -> hints -> derived

def AyCRIIndexedClause (database : Prop) (clause : Prop) :=
  AyCRIConj database clause

def AyCRIReplayAfterDelete (database : Prop) (deleted : Prop) :=
  database -> deleted

def AyCRIReplayAfterReadd (deleted : Prop) (readded : Prop) :=
  deleted -> readded

def AyCRIReplayTrace (database : Prop) (final_clause : Prop) :=
  AyCRIConj database final_clause

theorem ay_cri_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCRIConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_cri_conj_left
    (left : Prop) (right : Prop) :
    AyCRIConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cri_conj_right
    (left : Prop) (right : Prop) :
    AyCRIConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cri_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCRIDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_cri_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCRIDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_cri_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCRIEquisat before after := by
  intro forward
  intro backward
  exact ay_cri_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_cri_equisat_forward
    (before : Prop) (after : Prop) :
    AyCRIEquisat before after -> before -> after := by
  intro certificate
  exact ay_cri_conj_left (before -> after) (after -> before) certificate

theorem ay_cri_equisat_backward
    (before : Prop) (after : Prop) :
    AyCRIEquisat before after -> after -> before := by
  intro certificate
  exact ay_cri_conj_right (before -> after) (after -> before) certificate

theorem ay_cri_clause_id_rename_sound
    (old_id : Prop) (new_id : Prop) :
    AyCRIClauseRenaming old_id new_id ->
    old_id ->
    new_id := by
  intro rename
  intro hold
  exact rename hold

theorem ay_cri_clause_id_renaming_equisat
    (old_id : Prop) (new_id : Prop) :
    AyCRIClauseRenaming old_id new_id ->
    AyCRIClauseUnrenaming old_id new_id ->
    AyCRIEquisat old_id new_id := by
  intro rename
  intro unrename
  exact ay_cri_equisat_intro old_id new_id rename unrename

theorem ay_cri_hint_list_projection_sound
    (full_hints : Prop) (projected_hints : Prop) :
    AyCRIHintProjection full_hints projected_hints ->
    full_hints ->
    projected_hints := by
  intro project
  intro hfull
  exact project hfull

theorem ay_cri_lrat_replay_with_projected_hints
    (database : Prop) (full_hints : Prop)
    (projected_hints : Prop) (derived : Prop) :
    AyCRIHintProjection full_hints projected_hints ->
    AyCRIReplayStep database projected_hints derived ->
    AyCRIReplayStep database full_hints derived := by
  intro project
  intro replay
  intro hdatabase
  intro hfull
  exact replay hdatabase (project hfull)

theorem ay_cri_renamed_replay_step_sound
    (old_database : Prop) (new_database : Prop)
    (old_clause : Prop) (new_clause : Prop) (hints : Prop) :
    AyCRIClauseRenaming old_database new_database ->
    AyCRIClauseUnrenaming old_clause new_clause ->
    AyCRIReplayStep new_database hints new_clause ->
    AyCRIReplayStep old_database hints old_clause := by
  intro rename_database
  intro unrename_clause
  intro replay
  intro old_db
  intro hhints
  exact unrename_clause (replay (rename_database old_db) hhints)

theorem ay_cri_indexed_clause_intro
    (database : Prop) (clause : Prop) :
    database -> clause -> AyCRIIndexedClause database clause := by
  intro hdatabase
  intro hclause
  exact ay_cri_conj_intro database clause hdatabase hclause

theorem ay_cri_indexed_clause_database
    (database : Prop) (clause : Prop) :
    AyCRIIndexedClause database clause -> database := by
  intro indexed
  exact ay_cri_conj_left database clause indexed

theorem ay_cri_indexed_clause_value
    (database : Prop) (clause : Prop) :
    AyCRIIndexedClause database clause -> clause := by
  intro indexed
  exact ay_cri_conj_right database clause indexed

theorem ay_cri_deletion_readdition_replay
    (database : Prop) (deleted : Prop) (readded : Prop) :
    AyCRIReplayAfterDelete database deleted ->
    AyCRIReplayAfterReadd deleted readded ->
    database ->
    readded := by
  intro delete_step
  intro readd_step
  intro hdatabase
  exact readd_step (delete_step hdatabase)

theorem ay_cri_deletion_readdition_equisat
    (database : Prop) (deleted : Prop) (readded : Prop) :
    AyCRIReplayAfterDelete database deleted ->
    AyCRIReplayAfterReadd deleted readded ->
    (readded -> database) ->
    AyCRIEquisat database readded := by
  intro delete_step
  intro readd_step
  intro project_back
  exact ay_cri_equisat_intro database readded
    (ay_cri_deletion_readdition_replay database deleted readded
      delete_step readd_step)
    project_back

theorem ay_cri_lrat_replay_trace_intro
    (database : Prop) (hints : Prop) (final_clause : Prop) :
    AyCRIReplayStep database hints final_clause ->
    database ->
    hints ->
    AyCRIReplayTrace database final_clause := by
  intro replay
  intro hdatabase
  intro hhints
  exact ay_cri_conj_intro database final_clause
    hdatabase
    (replay hdatabase hhints)

theorem ay_cri_lrat_replay_final_sound
    (database : Prop) (hints : Prop) (final_clause : Prop) :
    AyCRIReplayStep database hints final_clause ->
    database ->
    hints ->
    final_clause := by
  intro replay
  intro hdatabase
  intro hhints
  exact ay_cri_conj_right database final_clause
    (ay_cri_lrat_replay_trace_intro database hints final_clause
      replay hdatabase hhints)

theorem ay_cri_rat_replay_refines_to_lrat
    (database : Prop) (rat_hints : Prop)
    (lrat_hints : Prop) (final_clause : Prop) :
    AyCRIHintProjection lrat_hints rat_hints ->
    AyCRIReplayStep database rat_hints final_clause ->
    AyCRIReplayStep database lrat_hints final_clause := by
  intro project
  intro rat_replay
  exact ay_cri_lrat_replay_with_projected_hints
    database lrat_hints rat_hints final_clause project rat_replay

theorem ay_cri_rat_lrat_replay_preserves_final
    (database : Prop) (rat_hints : Prop)
    (lrat_hints : Prop) (final_clause : Prop) :
    AyCRIHintProjection lrat_hints rat_hints ->
    AyCRIReplayStep database rat_hints final_clause ->
    database ->
    lrat_hints ->
    final_clause := by
  intro project
  intro rat_replay
  exact ay_cri_lrat_replay_final_sound database lrat_hints final_clause
    (ay_cri_rat_replay_refines_to_lrat
      database rat_hints lrat_hints final_clause project rat_replay)

theorem ay_cri_renumbered_rat_lrat_replay_preserves_final
    (old_database : Prop) (new_database : Prop)
    (old_final : Prop) (new_final : Prop)
    (rat_hints : Prop) (lrat_hints : Prop) :
    AyCRIClauseRenaming old_database new_database ->
    AyCRIClauseUnrenaming old_final new_final ->
    AyCRIHintProjection lrat_hints rat_hints ->
    AyCRIReplayStep new_database rat_hints new_final ->
    old_database ->
    lrat_hints ->
    old_final := by
  intro rename_database
  intro unrename_final
  intro project
  intro replay
  exact ay_cri_lrat_replay_final_sound old_database lrat_hints old_final
    (ay_cri_renamed_replay_step_sound
      old_database new_database old_final new_final lrat_hints
      rename_database
      unrename_final
      (ay_cri_rat_replay_refines_to_lrat
        new_database rat_hints lrat_hints new_final project replay))

theorem ay_cri_replay_index_pipeline_equisat
    (database : Prop) (deleted : Prop)
    (readded : Prop) (final_clause : Prop) :
    AyCRIReplayAfterDelete database deleted ->
    AyCRIReplayAfterReadd deleted readded ->
    (readded -> database) ->
    (readded -> final_clause) ->
    AyCRIEquisat
      database
      (AyCRIReplayTrace database final_clause) := by
  intro delete_step
  intro readd_step
  intro project_back
  intro final_step
  exact ay_cri_equisat_intro
    database
    (AyCRIReplayTrace database final_clause)
    (fun hdatabase =>
      ay_cri_conj_intro database final_clause
        hdatabase
        (final_step
          (ay_cri_deletion_readdition_replay database deleted readded
            delete_step readd_step hdatabase)))
    (fun trace =>
      project_back
        (ay_cri_deletion_readdition_replay database deleted readded
          delete_step readd_step
          (ay_cri_conj_left database final_clause trace)))
