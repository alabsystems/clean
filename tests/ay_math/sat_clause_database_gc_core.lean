-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for clause database deletion / garbage collection
-- certificate soundness. Active and inactive clause sets are propositions
-- representing satisfiability witnesses for those abstract database views.

def AyGcDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyGcConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyGcEquisat (before : Prop) (after : Prop) :=
  AyGcConj (before -> after) (after -> before)

def AyGcDatabase (active : Prop) (inactive : Prop) :=
  AyGcConj active inactive

def AyGcDeletedDatabase (active : Prop) (inactive : Prop) :=
  AyGcConj active inactive

def AyGcWithClause (active : Prop) (clause : Prop) :=
  AyGcConj active clause

def AyGcRatAdded (active : Prop) (candidate : Prop) :=
  AyGcConj active candidate

def AyGcRatAddedThenDerived
    (active : Prop) (candidate : Prop) (derived : Prop) :=
  AyGcConj (AyGcRatAdded active candidate) derived

def AyGcAfterTrace (active : Prop) (derived : Prop) :=
  AyGcConj active derived

def AyGcRedundantClause (active : Prop) (clause : Prop) :=
  active -> clause

def AyGcRatWitness (active : Prop) (candidate : Prop) :=
  active -> candidate

def AyGcUnusedClause (active : Prop) (clause : Prop) :=
  AyGcEquisat (AyGcWithClause active clause) active

theorem ay_gc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyGcConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_gc_conj_left
    (left : Prop) (right : Prop) :
    AyGcConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_gc_conj_right
    (left : Prop) (right : Prop) :
    AyGcConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_gc_equisat_forward
    (before : Prop) (after : Prop) :
    AyGcEquisat before after -> before -> after := by
  intro eqsat
  exact eqsat (before -> after)
    (fun forward _backward => forward)

theorem ay_gc_equisat_backward
    (before : Prop) (after : Prop) :
    AyGcEquisat before after -> after -> before := by
  intro eqsat
  exact eqsat (after -> before)
    (fun _forward backward => backward)

theorem ay_gc_delete_projection
    (active : Prop) (clause : Prop) :
    AyGcWithClause active clause -> active := by
  intro database
  exact ay_gc_conj_left active clause database

theorem ay_gc_delete_reconstruct_redundant
    (active : Prop) (clause : Prop) :
    AyGcRedundantClause active clause ->
    active ->
    AyGcWithClause active clause := by
  intro redundant
  intro hactive
  exact ay_gc_conj_intro active clause
    hactive
    (redundant hactive)

theorem ay_gc_delete_redundant_equisat
    (active : Prop) (clause : Prop) :
    AyGcRedundantClause active clause ->
    AyGcEquisat (AyGcWithClause active clause) active := by
  intro redundant
  exact ay_gc_conj_intro
    (AyGcWithClause active clause -> active)
    (active -> AyGcWithClause active clause)
    (ay_gc_delete_projection active clause)
    (ay_gc_delete_reconstruct_redundant active clause redundant)

theorem ay_gc_delete_unused_equisat
    (active : Prop) (clause : Prop) :
    AyGcUnusedClause active clause ->
    AyGcEquisat (AyGcWithClause active clause) active := by
  intro unused
  exact unused

theorem ay_gc_database_delete_to_inactive_forward
    (active : Prop) (inactive : Prop) (clause : Prop) :
    AyGcDatabase (AyGcWithClause active clause) inactive ->
    AyGcDeletedDatabase active (AyGcConj inactive clause) := by
  intro database
  exact ay_gc_conj_intro active (AyGcConj inactive clause)
    (ay_gc_delete_projection active clause
      (ay_gc_conj_left (AyGcWithClause active clause) inactive database))
    (ay_gc_conj_intro inactive clause
      (ay_gc_conj_right (AyGcWithClause active clause) inactive database)
      (ay_gc_conj_right active clause
        (ay_gc_conj_left (AyGcWithClause active clause) inactive database)))

theorem ay_gc_database_delete_to_inactive_backward
    (active : Prop) (inactive : Prop) (clause : Prop) :
    AyGcRedundantClause active clause ->
    AyGcDeletedDatabase active (AyGcConj inactive clause) ->
    AyGcDatabase (AyGcWithClause active clause) inactive := by
  intro redundant
  intro deleted
  exact ay_gc_conj_intro (AyGcWithClause active clause) inactive
    (ay_gc_delete_reconstruct_redundant active clause
      redundant
      (ay_gc_conj_left active (AyGcConj inactive clause) deleted))
    (ay_gc_conj_left inactive clause
      (ay_gc_conj_right active (AyGcConj inactive clause) deleted))

theorem ay_gc_database_delete_to_inactive_equisat
    (active : Prop) (inactive : Prop) (clause : Prop) :
    AyGcRedundantClause active clause ->
    AyGcEquisat
      (AyGcDatabase (AyGcWithClause active clause) inactive)
      (AyGcDeletedDatabase active (AyGcConj inactive clause)) := by
  intro redundant
  exact ay_gc_conj_intro
    (AyGcDatabase (AyGcWithClause active clause) inactive ->
      AyGcDeletedDatabase active (AyGcConj inactive clause))
    (AyGcDeletedDatabase active (AyGcConj inactive clause) ->
      AyGcDatabase (AyGcWithClause active clause) inactive)
    (ay_gc_database_delete_to_inactive_forward active inactive clause)
    (ay_gc_database_delete_to_inactive_backward
      active inactive clause redundant)

theorem ay_gc_rat_clause_add
    (active : Prop) (candidate : Prop) :
    AyGcRatWitness active candidate ->
    active ->
    AyGcRatAdded active candidate := by
  intro witness
  intro hactive
  exact ay_gc_conj_intro active candidate
    hactive
    (witness hactive)

theorem ay_gc_rat_clause_add_equisat
    (active : Prop) (candidate : Prop) :
    AyGcRatWitness active candidate ->
    AyGcEquisat active (AyGcRatAdded active candidate) := by
  intro witness
  exact ay_gc_conj_intro
    (active -> AyGcRatAdded active candidate)
    (AyGcRatAdded active candidate -> active)
    (ay_gc_rat_clause_add active candidate witness)
    (ay_gc_conj_left active candidate)

theorem ay_gc_lrat_trace_step_after_add
    (active : Prop) (candidate : Prop) (derived : Prop) :
    (AyGcRatAdded active candidate -> derived) ->
    AyGcRatAdded active candidate ->
    AyGcRatAddedThenDerived active candidate derived := by
  intro trace_step
  intro added
  exact ay_gc_conj_intro
    (AyGcRatAdded active candidate)
    derived
    added
    (trace_step added)

theorem ay_gc_delete_added_clause_after_trace
    (active : Prop) (candidate : Prop) (derived : Prop) :
    AyGcRatAddedThenDerived active candidate derived ->
    AyGcAfterTrace active derived := by
  intro added_then_derived
  exact ay_gc_conj_intro active derived
    (ay_gc_conj_left active candidate
      (ay_gc_conj_left
        (AyGcRatAdded active candidate)
        derived
        added_then_derived))
    (ay_gc_conj_right
      (AyGcRatAdded active candidate)
      derived
      added_then_derived)

theorem ay_gc_rat_lrat_trace_with_gc_forward
    (active : Prop) (candidate : Prop) (derived : Prop) :
    AyGcRatWitness active candidate ->
    (AyGcRatAdded active candidate -> derived) ->
    active ->
    AyGcAfterTrace active derived := by
  intro witness
  intro trace_step
  intro hactive
  exact ay_gc_delete_added_clause_after_trace active candidate derived
    (ay_gc_lrat_trace_step_after_add active candidate derived
      trace_step
      (ay_gc_rat_clause_add active candidate witness hactive))

theorem ay_gc_rat_lrat_trace_with_gc_backward
    (active : Prop) (derived : Prop) :
    AyGcAfterTrace active derived -> active := by
  intro after_trace
  exact ay_gc_conj_left active derived after_trace

theorem ay_gc_rat_lrat_trace_with_gc_equisat
    (active : Prop) (candidate : Prop) (derived : Prop) :
    AyGcRatWitness active candidate ->
    (AyGcRatAdded active candidate -> derived) ->
    AyGcEquisat active (AyGcAfterTrace active derived) := by
  intro witness
  intro trace_step
  exact ay_gc_conj_intro
    (active -> AyGcAfterTrace active derived)
    (AyGcAfterTrace active derived -> active)
    (ay_gc_rat_lrat_trace_with_gc_forward
      active candidate derived witness trace_step)
    (ay_gc_rat_lrat_trace_with_gc_backward active derived)

theorem ay_gc_compose_deletion_after_trace
    (active : Prop) (candidate : Prop) (derived : Prop)
    (final : Prop) :
    AyGcRatWitness active candidate ->
    (AyGcRatAdded active candidate -> derived) ->
    AyGcRedundantClause active final ->
    active ->
    AyGcAfterTrace active derived := by
  intro witness
  intro trace_step
  intro _final_redundant
  exact ay_gc_rat_lrat_trace_with_gc_forward
    active candidate derived witness trace_step

theorem ay_gc_two_deletions_compose
    (active : Prop) (firstClause : Prop) (secondClause : Prop) :
    AyGcRedundantClause active firstClause ->
    AyGcRedundantClause active secondClause ->
    AyGcEquisat
      (AyGcWithClause (AyGcWithClause active firstClause) secondClause)
      active := by
  intro first_redundant
  intro second_redundant
  exact ay_gc_conj_intro
    (AyGcWithClause (AyGcWithClause active firstClause) secondClause ->
      active)
    (active ->
      AyGcWithClause (AyGcWithClause active firstClause) secondClause)
    (fun full =>
      ay_gc_conj_left active firstClause
        (ay_gc_conj_left
          (AyGcWithClause active firstClause)
          secondClause
          full))
    (fun hactive =>
      ay_gc_conj_intro
        (AyGcWithClause active firstClause)
        secondClause
        (ay_gc_delete_reconstruct_redundant
          active firstClause first_redundant hactive)
        (second_redundant hactive))

theorem ay_gc_active_inactive_projection
    (active : Prop) (inactive : Prop) :
    AyGcDatabase active inactive -> active := by
  intro database
  exact ay_gc_conj_left active inactive database

theorem ay_gc_active_inactive_reconstruct
    (active : Prop) (inactive : Prop) :
    inactive ->
    active ->
    AyGcDatabase active inactive := by
  intro hinactive
  intro hactive
  exact ay_gc_conj_intro active inactive hactive hinactive
