-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for hyper-binary resolution chain compression.
-- Binary implications are represented as clauses of the form Not source OR target.

def AyHbrChainDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrChainConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrChainBinaryImp (source : Prop) (target : Prop) :=
  AyHbrChainDisj (Not source) target

def AyHbrChainParents
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :=
  AyHbrChainConj
    (AyHbrChainBinaryImp first second)
    (AyHbrChainConj
      (AyHbrChainBinaryImp second third)
      (AyHbrChainBinaryImp third fourth))

def AyHbrChainWithDerived (context : Prop) (derived : Prop) :=
  AyHbrChainConj context derived

def AyHbrChainEquisat (before : Prop) (after : Prop) :=
  AyHbrChainConj (before -> after) (after -> before)

theorem ay_hbr_chain_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrChainConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_chain_conj_left
    (left : Prop) (right : Prop) :
    AyHbrChainConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_chain_conj_right
    (left : Prop) (right : Prop) :
    AyHbrChainConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hbr_chain_binary_to_implication
    (source : Prop) (target : Prop) :
    AyHbrChainBinaryImp source target ->
    source ->
    target := by
  intro clause
  intro hsource
  exact clause target
    (fun not_source => False.elim (not_source hsource))
    (fun htarget => htarget)

theorem ay_hbr_chain_binary_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrChainBinaryImp source middle ->
    AyHbrChainBinaryImp middle target ->
    AyHbrChainBinaryImp source target := by
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

theorem ay_hbr_chain_three_implications_compress
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainBinaryImp first second ->
    AyHbrChainBinaryImp second third ->
    AyHbrChainBinaryImp third fourth ->
    AyHbrChainBinaryImp first fourth := by
  intro first_second
  intro second_third
  intro third_fourth
  exact ay_hbr_chain_binary_transitive first third fourth
    (ay_hbr_chain_binary_transitive
      first second third first_second second_third)
    third_fourth

theorem ay_hbr_chain_parents_derive_binary
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainParents first second third fourth ->
    AyHbrChainBinaryImp first fourth := by
  intro parents
  exact parents (AyHbrChainBinaryImp first fourth)
    (fun first_second tail =>
      tail (AyHbrChainBinaryImp first fourth)
        (fun second_third third_fourth =>
          ay_hbr_chain_three_implications_compress
            first second third fourth
            first_second second_third third_fourth))

theorem ay_hbr_chain_parents_derive_implication
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainParents first second third fourth ->
    first ->
    fourth := by
  intro parents
  exact ay_hbr_chain_binary_to_implication first fourth
    (ay_hbr_chain_parents_derive_binary
      first second third fourth parents)

theorem ay_hbr_chain_add_derived_forward
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    context ->
    AyHbrChainWithDerived context derived := by
  intro derive
  intro hcontext
  exact ay_hbr_chain_conj_intro context derived
    hcontext
    (derive hcontext)

theorem ay_hbr_chain_add_derived_backward
    (context : Prop) (derived : Prop) :
    AyHbrChainWithDerived context derived ->
    context := by
  intro with_derived
  exact ay_hbr_chain_conj_left context derived with_derived

theorem ay_hbr_chain_add_derived_equisat
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    AyHbrChainEquisat context (AyHbrChainWithDerived context derived) := by
  intro derive
  exact ay_hbr_chain_conj_intro
    (context -> AyHbrChainWithDerived context derived)
    (AyHbrChainWithDerived context derived -> context)
    (ay_hbr_chain_add_derived_forward context derived derive)
    (ay_hbr_chain_add_derived_backward context derived)

theorem ay_hbr_chain_add_compressed_binary_forward
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainParents first second third fourth ->
    AyHbrChainWithDerived
      (AyHbrChainParents first second third fourth)
      (AyHbrChainBinaryImp first fourth) := by
  intro parents
  exact ay_hbr_chain_add_derived_forward
    (AyHbrChainParents first second third fourth)
    (AyHbrChainBinaryImp first fourth)
    (ay_hbr_chain_parents_derive_binary first second third fourth)
    parents

theorem ay_hbr_chain_add_compressed_binary_backward
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainWithDerived
      (AyHbrChainParents first second third fourth)
      (AyHbrChainBinaryImp first fourth) ->
    AyHbrChainParents first second third fourth := by
  intro with_derived
  exact ay_hbr_chain_add_derived_backward
    (AyHbrChainParents first second third fourth)
    (AyHbrChainBinaryImp first fourth)
    with_derived

theorem ay_hbr_chain_add_compressed_binary_equisat
    (first : Prop) (second : Prop) (third : Prop) (fourth : Prop) :
    AyHbrChainEquisat
      (AyHbrChainParents first second third fourth)
      (AyHbrChainWithDerived
        (AyHbrChainParents first second third fourth)
        (AyHbrChainBinaryImp first fourth)) := by
  exact ay_hbr_chain_add_derived_equisat
    (AyHbrChainParents first second third fourth)
    (AyHbrChainBinaryImp first fourth)
    (ay_hbr_chain_parents_derive_binary first second third fourth)
