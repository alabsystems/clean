-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for interaction between hyper-binary resolution
-- and equivalence substitution at the propositional abstraction level.

def AyHbrEqDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrEqConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrEqEquiv (left : Prop) (right : Prop) :=
  AyHbrEqConj (left -> right) (right -> left)

def AyHbrEqBinaryImp (source : Prop) (target : Prop) :=
  AyHbrEqDisj (Not source) target

def AyHbrEqTransitiveParents
    (source : Prop) (middle : Prop) (target : Prop) :=
  AyHbrEqConj
    (AyHbrEqBinaryImp source middle)
    (AyHbrEqBinaryImp middle target)

def AyHbrEqWithDerived (context : Prop) (derived : Prop) :=
  AyHbrEqConj context derived

def AyHbrEqEquisat (before : Prop) (after : Prop) :=
  AyHbrEqConj (before -> after) (after -> before)

def AyHbrEqTargetSubstContext
    (source : Prop) (middle : Prop)
    (oldTarget : Prop) (newTarget : Prop) :=
  AyHbrEqConj
    (AyHbrEqEquiv oldTarget newTarget)
    (AyHbrEqTransitiveParents source middle oldTarget)

theorem ay_hbr_equiv_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrEqConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_equiv_conj_left
    (left : Prop) (right : Prop) :
    AyHbrEqConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_equiv_disj_left
    (left : Prop) (right : Prop) :
    left -> AyHbrEqDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_hbr_equiv_disj_right
    (left : Prop) (right : Prop) :
    right -> AyHbrEqDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_hbr_equiv_forward
    (left : Prop) (right : Prop) :
    AyHbrEqEquiv left right -> left -> right := by
  intro equiv
  exact equiv (left -> right) (fun forward _backward => forward)

theorem ay_hbr_equiv_backward
    (left : Prop) (right : Prop) :
    AyHbrEqEquiv left right -> right -> left := by
  intro equiv
  exact equiv (right -> left) (fun _forward backward => backward)

theorem ay_hbr_equiv_not_forward
    (left : Prop) (right : Prop) :
    AyHbrEqEquiv left right -> Not left -> Not right := by
  intro equiv
  intro not_left
  intro hright
  exact not_left (ay_hbr_equiv_backward left right equiv hright)

theorem ay_hbr_equiv_not_backward
    (left : Prop) (right : Prop) :
    AyHbrEqEquiv left right -> Not right -> Not left := by
  intro equiv
  intro not_right
  intro hleft
  exact not_right (ay_hbr_equiv_forward left right equiv hleft)

theorem ay_hbr_equiv_binary_implication_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrEqBinaryImp source middle ->
    AyHbrEqBinaryImp middle target ->
    AyHbrEqBinaryImp source target := by
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

theorem ay_hbr_equiv_derive_binary
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrEqTransitiveParents source middle target ->
    AyHbrEqBinaryImp source target := by
  intro parents
  exact parents (AyHbrEqBinaryImp source target)
    (fun first_clause second_clause =>
      ay_hbr_equiv_binary_implication_transitive
        source middle target first_clause second_clause)

theorem ay_hbr_equiv_substitute_source_forward
    (oldSource : Prop) (newSource : Prop) (target : Prop) :
    AyHbrEqEquiv oldSource newSource ->
    AyHbrEqBinaryImp oldSource target ->
    AyHbrEqBinaryImp newSource target := by
  intro equiv
  intro old_clause
  intro result
  intro not_new_source_case
  intro target_case
  exact old_clause result
    (fun not_old_source =>
      not_new_source_case
        (ay_hbr_equiv_not_forward oldSource newSource equiv
          not_old_source))
    target_case

theorem ay_hbr_equiv_substitute_source_backward
    (oldSource : Prop) (newSource : Prop) (target : Prop) :
    AyHbrEqEquiv oldSource newSource ->
    AyHbrEqBinaryImp newSource target ->
    AyHbrEqBinaryImp oldSource target := by
  intro equiv
  intro new_clause
  intro result
  intro not_old_source_case
  intro target_case
  exact new_clause result
    (fun not_new_source =>
      not_old_source_case
        (ay_hbr_equiv_not_backward oldSource newSource equiv
          not_new_source))
    target_case

theorem ay_hbr_equiv_substitute_target_forward
    (source : Prop) (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqEquiv oldTarget newTarget ->
    AyHbrEqBinaryImp source oldTarget ->
    AyHbrEqBinaryImp source newTarget := by
  intro equiv
  intro old_clause
  intro result
  intro not_source_case
  intro new_target_case
  exact old_clause result
    not_source_case
    (fun old_target =>
      new_target_case
        (ay_hbr_equiv_forward oldTarget newTarget equiv old_target))

theorem ay_hbr_equiv_substitute_target_backward
    (source : Prop) (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqEquiv oldTarget newTarget ->
    AyHbrEqBinaryImp source newTarget ->
    AyHbrEqBinaryImp source oldTarget := by
  intro equiv
  intro new_clause
  intro result
  intro not_source_case
  intro old_target_case
  exact new_clause result
    not_source_case
    (fun new_target =>
      old_target_case
        (ay_hbr_equiv_backward oldTarget newTarget equiv new_target))

theorem ay_hbr_equiv_substitute_binary_equisat
    (source : Prop) (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqEquiv oldTarget newTarget ->
    AyHbrEqEquisat
      (AyHbrEqBinaryImp source oldTarget)
      (AyHbrEqBinaryImp source newTarget) := by
  intro equiv
  exact ay_hbr_equiv_conj_intro
    (AyHbrEqBinaryImp source oldTarget ->
      AyHbrEqBinaryImp source newTarget)
    (AyHbrEqBinaryImp source newTarget ->
      AyHbrEqBinaryImp source oldTarget)
    (ay_hbr_equiv_substitute_target_forward
      source oldTarget newTarget equiv)
    (ay_hbr_equiv_substitute_target_backward
      source oldTarget newTarget equiv)

theorem ay_hbr_equiv_context_derive_substituted_target
    (source : Prop) (middle : Prop)
    (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqTargetSubstContext source middle oldTarget newTarget ->
    AyHbrEqBinaryImp source newTarget := by
  intro context
  exact context (AyHbrEqBinaryImp source newTarget)
    (fun target_equiv parents =>
      ay_hbr_equiv_substitute_target_forward
        source oldTarget newTarget
        target_equiv
        (ay_hbr_equiv_derive_binary source middle oldTarget parents))

theorem ay_hbr_equiv_add_substituted_forward
    (source : Prop) (middle : Prop)
    (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqTargetSubstContext source middle oldTarget newTarget ->
    AyHbrEqWithDerived
      (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
      (AyHbrEqBinaryImp source newTarget) := by
  intro context
  exact ay_hbr_equiv_conj_intro
    (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
    (AyHbrEqBinaryImp source newTarget)
    context
    (ay_hbr_equiv_context_derive_substituted_target
      source middle oldTarget newTarget context)

theorem ay_hbr_equiv_add_substituted_backward
    (source : Prop) (middle : Prop)
    (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqWithDerived
      (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
      (AyHbrEqBinaryImp source newTarget) ->
    AyHbrEqTargetSubstContext source middle oldTarget newTarget := by
  intro with_derived
  exact ay_hbr_equiv_conj_left
    (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
    (AyHbrEqBinaryImp source newTarget)
    with_derived

theorem ay_hbr_equiv_add_substituted_equisat
    (source : Prop) (middle : Prop)
    (oldTarget : Prop) (newTarget : Prop) :
    AyHbrEqEquisat
      (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
      (AyHbrEqWithDerived
        (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
        (AyHbrEqBinaryImp source newTarget)) := by
  exact ay_hbr_equiv_conj_intro
    (AyHbrEqTargetSubstContext source middle oldTarget newTarget ->
      AyHbrEqWithDerived
        (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
        (AyHbrEqBinaryImp source newTarget))
    (AyHbrEqWithDerived
      (AyHbrEqTargetSubstContext source middle oldTarget newTarget)
      (AyHbrEqBinaryImp source newTarget) ->
      AyHbrEqTargetSubstContext source middle oldTarget newTarget)
    (ay_hbr_equiv_add_substituted_forward
      source middle oldTarget newTarget)
    (ay_hbr_equiv_add_substituted_backward
      source middle oldTarget newTarget)
