-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for handing a hyper-binary derived clause to a
-- RAT/RUP-style add/use/delete skeleton.

def AyHbrRatDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrRatConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrRatBinaryImp (source : Prop) (target : Prop) :=
  AyHbrRatDisj (Not source) target

def AyHbrRatParents
    (first : Prop) (second : Prop) (third : Prop) :=
  AyHbrRatConj
    (AyHbrRatBinaryImp first second)
    (AyHbrRatBinaryImp second third)

def AyHbrRatAddedFormula (existing : Prop) (candidate : Prop) :=
  AyHbrRatConj existing candidate

def AyHbrRatAddedThenUsed
    (existing : Prop) (candidate : Prop) (used : Prop) :=
  AyHbrRatConj (AyHbrRatAddedFormula existing candidate) used

def AyHbrRatDeletedAfterUse (existing : Prop) (used : Prop) :=
  AyHbrRatConj existing used

def AyHbrRatEquisat (before : Prop) (after : Prop) :=
  AyHbrRatConj (before -> after) (after -> before)

def AyHbrRatWitness (existing : Prop) (candidate : Prop) :=
  existing -> candidate

theorem ay_hbr_rat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrRatConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_rat_conj_left
    (left : Prop) (right : Prop) :
    AyHbrRatConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_rat_conj_right
    (left : Prop) (right : Prop) :
    AyHbrRatConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hbr_rat_binary_to_implication
    (source : Prop) (target : Prop) :
    AyHbrRatBinaryImp source target ->
    source ->
    target := by
  intro clause
  intro hsource
  exact clause target
    (fun not_source => False.elim (not_source hsource))
    (fun htarget => htarget)

theorem ay_hbr_rat_binary_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrRatBinaryImp source middle ->
    AyHbrRatBinaryImp middle target ->
    AyHbrRatBinaryImp source target := by
  intro first_clause
  intro second_clause
  intro result
  intro not_source_case
  intro target_case
  exact first_clause result
    not_source_case
    (fun hmiddle =>
      second_clause result
        (fun not_middle => False.elim (not_middle hmiddle))
        target_case)

theorem ay_hbr_rat_derive_candidate
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatParents first second third ->
    AyHbrRatBinaryImp first third := by
  intro parents
  exact parents (AyHbrRatBinaryImp first third)
    (fun first_second second_third =>
      ay_hbr_rat_binary_transitive
        first second third first_second second_third)

theorem ay_hbr_rat_derivation_is_rat_witness
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatWitness
      (AyHbrRatParents first second third)
      (AyHbrRatBinaryImp first third) := by
  exact ay_hbr_rat_derive_candidate first second third

theorem ay_hbr_rat_clause_add_projection
    (existing : Prop) (candidate : Prop) :
    AyHbrRatAddedFormula existing candidate -> existing := by
  intro added
  exact ay_hbr_rat_conj_left existing candidate added

theorem ay_hbr_rat_clause_add_reconstruct
    (existing : Prop) (candidate : Prop) :
    AyHbrRatWitness existing candidate ->
    existing ->
    AyHbrRatAddedFormula existing candidate := by
  intro witness
  intro existing_sat
  exact ay_hbr_rat_conj_intro existing candidate
    existing_sat
    (witness existing_sat)

theorem ay_hbr_rat_clause_add_equisat
    (existing : Prop) (candidate : Prop) :
    AyHbrRatWitness existing candidate ->
    AyHbrRatEquisat existing (AyHbrRatAddedFormula existing candidate) := by
  intro witness
  exact ay_hbr_rat_conj_intro
    (existing -> AyHbrRatAddedFormula existing candidate)
    (AyHbrRatAddedFormula existing candidate -> existing)
    (ay_hbr_rat_clause_add_reconstruct existing candidate witness)
    (ay_hbr_rat_clause_add_projection existing candidate)

theorem ay_hbr_rat_add_derived_clause_forward
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatParents first second third ->
    AyHbrRatAddedFormula
      (AyHbrRatParents first second third)
      (AyHbrRatBinaryImp first third) := by
  intro parents
  exact ay_hbr_rat_clause_add_reconstruct
    (AyHbrRatParents first second third)
    (AyHbrRatBinaryImp first third)
    (ay_hbr_rat_derivation_is_rat_witness first second third)
    parents

theorem ay_hbr_rat_add_derived_clause_equisat
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatEquisat
      (AyHbrRatParents first second third)
      (AyHbrRatAddedFormula
        (AyHbrRatParents first second third)
        (AyHbrRatBinaryImp first third)) := by
  exact ay_hbr_rat_clause_add_equisat
    (AyHbrRatParents first second third)
    (AyHbrRatBinaryImp first third)
    (ay_hbr_rat_derivation_is_rat_witness first second third)

theorem ay_hbr_rat_use_added_clause
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatAddedFormula
      (AyHbrRatParents first second third)
      (AyHbrRatBinaryImp first third) ->
    first ->
    third := by
  intro added
  intro hfirst
  exact ay_hbr_rat_binary_to_implication first third
    (ay_hbr_rat_conj_right
      (AyHbrRatParents first second third)
      (AyHbrRatBinaryImp first third)
      added)
    hfirst

theorem ay_hbr_rat_later_used_intro
    (existing : Prop) (candidate : Prop) (used : Prop) :
    (AyHbrRatAddedFormula existing candidate -> used) ->
    AyHbrRatAddedFormula existing candidate ->
    AyHbrRatAddedThenUsed existing candidate used := by
  intro use_candidate
  intro added
  exact ay_hbr_rat_conj_intro
    (AyHbrRatAddedFormula existing candidate)
    used
    added
    (use_candidate added)

theorem ay_hbr_rat_delete_candidate_after_use
    (existing : Prop) (candidate : Prop) (used : Prop) :
    AyHbrRatAddedThenUsed existing candidate used ->
    AyHbrRatDeletedAfterUse existing used := by
  intro added_then_used
  exact ay_hbr_rat_conj_intro existing used
    (ay_hbr_rat_clause_add_projection existing candidate
      (ay_hbr_rat_conj_left
        (AyHbrRatAddedFormula existing candidate)
        used
        added_then_used))
    (ay_hbr_rat_conj_right
      (AyHbrRatAddedFormula existing candidate)
      used
      added_then_used)

theorem ay_hbr_rat_add_use_delete_forward
    (existing : Prop) (candidate : Prop) (used : Prop) :
    AyHbrRatWitness existing candidate ->
    (AyHbrRatAddedFormula existing candidate -> used) ->
    existing ->
    AyHbrRatDeletedAfterUse existing used := by
  intro witness
  intro use_candidate
  intro existing_sat
  exact ay_hbr_rat_delete_candidate_after_use existing candidate used
    (ay_hbr_rat_later_used_intro existing candidate used
      use_candidate
      (ay_hbr_rat_clause_add_reconstruct
        existing candidate witness existing_sat))

theorem ay_hbr_rat_add_use_delete_backward
    (existing : Prop) (used : Prop) :
    AyHbrRatDeletedAfterUse existing used ->
    existing := by
  intro deleted
  exact ay_hbr_rat_conj_left existing used deleted

theorem ay_hbr_rat_add_use_delete_equisat
    (existing : Prop) (candidate : Prop) (used : Prop) :
    AyHbrRatWitness existing candidate ->
    (AyHbrRatAddedFormula existing candidate -> used) ->
    AyHbrRatEquisat existing (AyHbrRatDeletedAfterUse existing used) := by
  intro witness
  intro use_candidate
  exact ay_hbr_rat_conj_intro
    (existing -> AyHbrRatDeletedAfterUse existing used)
    (AyHbrRatDeletedAfterUse existing used -> existing)
    (ay_hbr_rat_add_use_delete_forward
      existing candidate used witness use_candidate)
    (ay_hbr_rat_add_use_delete_backward existing used)

theorem ay_hbr_rat_handoff_equisat
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatEquisat
      (AyHbrRatParents first second third)
      (AyHbrRatDeletedAfterUse
        (AyHbrRatParents first second third)
        (first -> third)) := by
  exact ay_hbr_rat_add_use_delete_equisat
    (AyHbrRatParents first second third)
    (AyHbrRatBinaryImp first third)
    (first -> third)
    (ay_hbr_rat_derivation_is_rat_witness first second third)
    (fun added =>
      ay_hbr_rat_use_added_clause first second third added)
