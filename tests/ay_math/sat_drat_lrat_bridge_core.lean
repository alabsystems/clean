-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for a DRAT/RAT-to-LRAT bridge.
-- A RAT addition with explicit witness hints is refined into LRAT-style
-- parent hints, then spliced into a later checked trace. All objects are
-- abstract propositions standing for formula or clause validity facts.

def AyDratLratDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyDratLratConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDratLratEquisat (before : Prop) (after : Prop) :=
  AyDratLratConj (before -> after) (after -> before)

def AyDratRatWitness (available : Prop) (candidate : Prop) :=
  available -> candidate

def AyLratParentHints (available : Prop) (candidate : Prop) :=
  available -> candidate

def AyDratLratAdded (available : Prop) (candidate : Prop) :=
  AyDratLratConj available candidate

def AyDratLratAddedThenFinal
    (available : Prop) (candidate : Prop) (final : Prop) :=
  AyDratLratConj (AyDratLratAdded available candidate) final

def AyDratLratDeletedAfterUse
    (available : Prop) (final : Prop) :=
  AyDratLratConj available final

def AyDratLratStep (available : Prop) (derived : Prop) :=
  available -> derived

theorem ay_drat_lrat_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDratLratDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_drat_lrat_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDratLratDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_drat_lrat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyDratLratConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_drat_lrat_conj_left
    (left : Prop) (right : Prop) :
    AyDratLratConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_drat_lrat_conj_right
    (left : Prop) (right : Prop) :
    AyDratLratConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_drat_lrat_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyDratLratEquisat before after := by
  intro forward
  intro backward
  exact ay_drat_lrat_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_drat_rat_witness_refines_to_lrat_parents
    (available : Prop) (candidate : Prop) :
    AyDratRatWitness available candidate ->
    AyLratParentHints available candidate := by
  intro rat_witness
  exact rat_witness

theorem ay_lrat_parent_hints_derive_candidate
    (available : Prop) (candidate : Prop) :
    AyLratParentHints available candidate ->
    AyDratLratStep available candidate := by
  intro parents
  exact parents

theorem ay_drat_lrat_clause_add
    (available : Prop) (candidate : Prop) :
    AyLratParentHints available candidate ->
    AyDratLratStep
      available
      (AyDratLratAdded available candidate) := by
  intro parents
  intro available_sat
  exact ay_drat_lrat_conj_intro available candidate
    available_sat
    (parents available_sat)

theorem ay_drat_lrat_clause_add_projection
    (available : Prop) (candidate : Prop) :
    AyDratLratAdded available candidate -> available := by
  intro added
  exact ay_drat_lrat_conj_left available candidate added

theorem ay_drat_lrat_clause_add_candidate
    (available : Prop) (candidate : Prop) :
    AyDratLratAdded available candidate -> candidate := by
  intro added
  exact ay_drat_lrat_conj_right available candidate added

theorem ay_drat_lrat_clause_add_equisat
    (available : Prop) (candidate : Prop) :
    AyLratParentHints available candidate ->
    AyDratLratEquisat
      available
      (AyDratLratAdded available candidate) := by
  intro parents
  exact ay_drat_lrat_equisat_intro
    available
    (AyDratLratAdded available candidate)
    (ay_drat_lrat_clause_add available candidate parents)
    (ay_drat_lrat_clause_add_projection available candidate)

theorem ay_drat_rat_add_refined_equisat
    (available : Prop) (candidate : Prop) :
    AyDratRatWitness available candidate ->
    AyDratLratEquisat
      available
      (AyDratLratAdded available candidate) := by
  intro rat_witness
  exact ay_drat_lrat_clause_add_equisat available candidate
    (ay_drat_rat_witness_refines_to_lrat_parents
      available candidate rat_witness)

theorem ay_drat_lrat_later_trace_intro
    (available : Prop) (candidate : Prop) (final : Prop) :
    (AyDratLratAdded available candidate -> final) ->
    AyDratLratAdded available candidate ->
    AyDratLratAddedThenFinal available candidate final := by
  intro final_step
  intro added
  exact ay_drat_lrat_conj_intro
    (AyDratLratAdded available candidate)
    final
    added
    (final_step added)

theorem ay_drat_lrat_delete_added_after_final
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyDratLratAddedThenFinal available candidate final ->
    AyDratLratDeletedAfterUse available final := by
  intro trace
  exact ay_drat_lrat_conj_intro available final
    (ay_drat_lrat_clause_add_projection available candidate
      (ay_drat_lrat_conj_left
        (AyDratLratAdded available candidate)
        final
        trace))
    (ay_drat_lrat_conj_right
      (AyDratLratAdded available candidate)
      final
      trace)

theorem ay_drat_lrat_splice_add_then_trace
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyLratParentHints available candidate ->
    (AyDratLratAdded available candidate -> final) ->
    AyDratLratStep
      available
      (AyDratLratDeletedAfterUse available final) := by
  intro parents
  intro final_step
  intro available_sat
  exact ay_drat_lrat_delete_added_after_final available candidate final
    (ay_drat_lrat_later_trace_intro available candidate final
      final_step
      (ay_drat_lrat_clause_add available candidate parents available_sat))

theorem ay_drat_rat_spliced_final_sound
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyDratRatWitness available candidate ->
    (AyDratLratAdded available candidate -> final) ->
    available ->
    final := by
  intro rat_witness
  intro final_step
  intro available_sat
  exact ay_drat_lrat_conj_right available final
    (ay_drat_lrat_splice_add_then_trace available candidate final
      (ay_drat_rat_witness_refines_to_lrat_parents
        available candidate rat_witness)
      final_step
      available_sat)

theorem ay_drat_rat_spliced_trace_equisat
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyDratRatWitness available candidate ->
    (AyDratLratAdded available candidate -> final) ->
    AyDratLratEquisat
      available
      (AyDratLratDeletedAfterUse available final) := by
  intro rat_witness
  intro final_step
  exact ay_drat_lrat_equisat_intro
    available
    (AyDratLratDeletedAfterUse available final)
    (ay_drat_lrat_splice_add_then_trace available candidate final
      (ay_drat_rat_witness_refines_to_lrat_parents
        available candidate rat_witness)
      final_step)
    (ay_drat_lrat_conj_left available final)

