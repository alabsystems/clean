-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for hyper-binary resolution / transitive
-- implication at the propositional abstraction level.

def AyHbrDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrBinaryImp (source : Prop) (target : Prop) :=
  AyHbrDisj (Not source) target

def AyHbrTransitiveParents
    (source : Prop) (middle : Prop) (target : Prop) :=
  AyHbrConj
    (AyHbrBinaryImp source middle)
    (AyHbrBinaryImp middle target)

def AyHbrWithDerived (context : Prop) (derived : Prop) :=
  AyHbrConj context derived

def AyHbrEquisat (before : Prop) (after : Prop) :=
  AyHbrConj (before -> after) (after -> before)

theorem ay_hbr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_conj_left
    (left : Prop) (right : Prop) :
    AyHbrConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_conj_right
    (left : Prop) (right : Prop) :
    AyHbrConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hbr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyHbrDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_hbr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyHbrDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_hbr_binary_clause_to_implication
    (source : Prop) (target : Prop) :
    AyHbrBinaryImp source target ->
    source ->
    target := by
  intro clause
  intro hsource
  exact clause target
    (fun not_source => False.elim (not_source hsource))
    (fun htarget => htarget)

theorem ay_hbr_implication_trans
    (source : Prop) (middle : Prop) (target : Prop) :
    (source -> middle) ->
    (middle -> target) ->
    source ->
    target := by
  intro source_to_middle
  intro middle_to_target
  intro hsource
  exact middle_to_target (source_to_middle hsource)

theorem ay_hbr_binary_implication_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrBinaryImp source middle ->
    AyHbrBinaryImp middle target ->
    AyHbrBinaryImp source target := by
  intro source_to_middle_clause
  intro middle_to_target_clause
  intro result
  intro not_source_case
  intro target_case
  exact source_to_middle_clause result
    not_source_case
    (fun hmiddle =>
      middle_to_target_clause result
        (fun not_middle => False.elim (not_middle hmiddle))
        target_case)

theorem ay_hbr_transitive_parents_derive_binary
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrTransitiveParents source middle target ->
    AyHbrBinaryImp source target := by
  intro parents
  exact parents (AyHbrBinaryImp source target)
    (fun source_to_middle_clause middle_to_target_clause =>
      ay_hbr_binary_implication_transitive
        source middle target
        source_to_middle_clause
        middle_to_target_clause)

theorem ay_hbr_transitive_parents_derive_implication
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrTransitiveParents source middle target ->
    source ->
    target := by
  intro parents
  exact ay_hbr_binary_clause_to_implication source target
    (ay_hbr_transitive_parents_derive_binary source middle target parents)

theorem ay_hbr_add_derived_forward
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    context ->
    AyHbrWithDerived context derived := by
  intro derive
  intro hcontext
  exact ay_hbr_conj_intro context derived
    hcontext
    (derive hcontext)

theorem ay_hbr_add_derived_backward
    (context : Prop) (derived : Prop) :
    AyHbrWithDerived context derived ->
    context := by
  intro with_derived
  exact ay_hbr_conj_left context derived with_derived

theorem ay_hbr_add_derived_equisat
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    AyHbrEquisat context (AyHbrWithDerived context derived) := by
  intro derive
  exact ay_hbr_conj_intro
    (context -> AyHbrWithDerived context derived)
    (AyHbrWithDerived context derived -> context)
    (ay_hbr_add_derived_forward context derived derive)
    (ay_hbr_add_derived_backward context derived)

theorem ay_hbr_add_transitive_binary_forward
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrTransitiveParents source middle target ->
    AyHbrWithDerived
      (AyHbrTransitiveParents source middle target)
      (AyHbrBinaryImp source target) := by
  intro parents
  exact ay_hbr_add_derived_forward
    (AyHbrTransitiveParents source middle target)
    (AyHbrBinaryImp source target)
    (ay_hbr_transitive_parents_derive_binary source middle target)
    parents

theorem ay_hbr_add_transitive_binary_backward
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrWithDerived
      (AyHbrTransitiveParents source middle target)
      (AyHbrBinaryImp source target) ->
    AyHbrTransitiveParents source middle target := by
  intro with_derived
  exact ay_hbr_add_derived_backward
    (AyHbrTransitiveParents source middle target)
    (AyHbrBinaryImp source target)
    with_derived

theorem ay_hbr_add_transitive_binary_equisat
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrEquisat
      (AyHbrTransitiveParents source middle target)
      (AyHbrWithDerived
        (AyHbrTransitiveParents source middle target)
        (AyHbrBinaryImp source target)) := by
  exact ay_hbr_add_derived_equisat
    (AyHbrTransitiveParents source middle target)
    (AyHbrBinaryImp source target)
    (ay_hbr_transitive_parents_derive_binary source middle target)

theorem ay_hbr_three_step_binary_implication
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrBinaryImp first second ->
    AyHbrBinaryImp second third ->
    AyHbrBinaryImp third fourth ->
    AyHbrBinaryImp first fourth := by
  intro first_second
  intro second_third
  intro third_fourth
  exact ay_hbr_binary_implication_transitive first third fourth
    (ay_hbr_binary_implication_transitive
      first second third first_second second_third)
    third_fourth
