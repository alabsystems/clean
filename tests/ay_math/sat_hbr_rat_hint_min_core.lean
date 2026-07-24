-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for HBR/RAT/LRAT hint minimization.
-- Hints are abstracted propositionally: a minimized hint set remains valid
-- when it can reconstruct the removed redundant hints needed by the original
-- checked HBR-derived RAT clause-add witness.

def AyHbrHintDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrHintConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrHintStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyHbrHintBinaryImp (source : Prop) (target : Prop) :=
  AyHbrHintDisj (Not source) target

def AyHbrHintParents (first : Prop) (second : Prop) (third : Prop) :=
  AyHbrHintConj
    (AyHbrHintBinaryImp first second)
    (AyHbrHintBinaryImp second third)

def AyHbrHintRatAdded (available : Prop) (candidate : Prop) :=
  AyHbrHintConj available candidate

def AyHbrHintWithFinal (available : Prop) (final : Prop) :=
  AyHbrHintConj available final

def AyHbrHintEquisat (before : Prop) (after : Prop) :=
  AyHbrHintConj (before -> after) (after -> before)

def AyHbrHintRedundant (keptHints : Prop) (removedHints : Prop) :=
  keptHints -> removedHints

def AyHbrHintFullHints (keptHints : Prop) (removedHints : Prop) :=
  AyHbrHintConj keptHints removedHints

theorem ay_hbr_hint_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrHintConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_hint_conj_left
    (left : Prop) (right : Prop) :
    AyHbrHintConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_hint_conj_right
    (left : Prop) (right : Prop) :
    AyHbrHintConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hbr_hint_binary_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrHintBinaryImp source middle ->
    AyHbrHintBinaryImp middle target ->
    AyHbrHintBinaryImp source target := by
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

theorem ay_hbr_hint_derive_candidate
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrHintParents first second third ->
    AyHbrHintBinaryImp first third := by
  intro parents
  exact parents (AyHbrHintBinaryImp first third)
    (fun first_second second_third =>
      ay_hbr_hint_binary_transitive
        first second third first_second second_third)

theorem ay_hbr_hint_rat_add_candidate
    (available : Prop) (candidate : Prop) :
    AyHbrHintStep available candidate ->
    AyHbrHintStep
      available
      (AyHbrHintRatAdded available candidate) := by
  intro witness
  intro available_sat
  exact ay_hbr_hint_conj_intro available candidate
    available_sat
    (witness available_sat)

theorem ay_hbr_hint_rat_added_candidate
    (available : Prop) (candidate : Prop) :
    AyHbrHintRatAdded available candidate -> candidate := by
  intro added
  exact ay_hbr_hint_conj_right available candidate added

theorem ay_hbr_hint_full_reconstruct
    (keptHints : Prop) (removedHints : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    keptHints ->
    AyHbrHintFullHints keptHints removedHints := by
  intro redundancy
  intro kept
  exact ay_hbr_hint_conj_intro keptHints removedHints
    kept
    (redundancy kept)

theorem ay_hbr_hint_full_projection
    (keptHints : Prop) (removedHints : Prop) :
    AyHbrHintFullHints keptHints removedHints -> keptHints := by
  intro full
  exact ay_hbr_hint_conj_left keptHints removedHints full

theorem ay_hbr_hint_minimize_step
    (keptHints : Prop) (removedHints : Prop) (derived : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      derived ->
    AyHbrHintStep keptHints derived := by
  intro redundancy
  intro original_step
  intro kept
  exact original_step
    (ay_hbr_hint_full_reconstruct
      keptHints removedHints redundancy kept)

theorem ay_hbr_hint_hbr_derivation_from_full_hints
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintBinaryImp first third) := by
  intro parents_from_full
  intro full
  exact ay_hbr_hint_derive_candidate first second third
    (parents_from_full full)

theorem ay_hbr_hint_hbr_derivation_from_minimized_hints
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep keptHints (AyHbrHintBinaryImp first third) := by
  intro redundancy
  intro parents_from_full
  exact ay_hbr_hint_minimize_step
    keptHints
    removedHints
    (AyHbrHintBinaryImp first third)
    redundancy
    (ay_hbr_hint_hbr_derivation_from_full_hints
      keptHints removedHints first second third parents_from_full)

theorem ay_hbr_hint_rat_add_from_minimized_hints
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      keptHints
      (AyHbrHintRatAdded
        keptHints
        (AyHbrHintBinaryImp first third)) := by
  intro redundancy
  intro parents_from_full
  exact ay_hbr_hint_rat_add_candidate
    keptHints
    (AyHbrHintBinaryImp first third)
    (ay_hbr_hint_hbr_derivation_from_minimized_hints
      keptHints removedHints first second third
      redundancy parents_from_full)

theorem ay_hbr_hint_rat_added_use_candidate
    (keptHints : Prop)
    (first : Prop) (third : Prop) :
    AyHbrHintRatAdded keptHints (AyHbrHintBinaryImp first third) ->
    AyHbrHintBinaryImp first third := by
  intro added
  exact ay_hbr_hint_rat_added_candidate
    keptHints
    (AyHbrHintBinaryImp first third)
    added

theorem ay_hbr_hint_compress_rat_add_trace
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      (AyHbrHintRatAdded
        keptHints
        (AyHbrHintBinaryImp first third))
      final ->
    AyHbrHintStep keptHints final := by
  intro redundancy
  intro parents_from_full
  intro final_from_added
  intro kept
  exact final_from_added
    (ay_hbr_hint_rat_add_from_minimized_hints
      keptHints removedHints first second third
      redundancy parents_from_full kept)

theorem ay_hbr_hint_compressed_trace_projection
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      (AyHbrHintRatAdded
        keptHints
        (AyHbrHintBinaryImp first third))
      final ->
    keptHints ->
    final := by
  intro redundancy
  intro parents_from_full
  intro final_from_added
  exact ay_hbr_hint_compress_rat_add_trace
    keptHints removedHints first second third final
    redundancy parents_from_full final_from_added

theorem ay_hbr_hint_with_final_intro
    (keptHints : Prop) (final : Prop) :
    AyHbrHintStep keptHints final ->
    keptHints ->
    AyHbrHintWithFinal keptHints final := by
  intro final_step
  intro kept
  exact ay_hbr_hint_conj_intro keptHints final
    kept
    (final_step kept)

theorem ay_hbr_hint_with_final_projection
    (keptHints : Prop) (final : Prop) :
    AyHbrHintWithFinal keptHints final -> keptHints := by
  intro with_final
  exact ay_hbr_hint_conj_left keptHints final with_final

theorem ay_hbr_hint_compressed_trace_forward
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      (AyHbrHintRatAdded
        keptHints
        (AyHbrHintBinaryImp first third))
      final ->
    keptHints ->
    AyHbrHintWithFinal keptHints final := by
  intro redundancy
  intro parents_from_full
  intro final_from_added
  exact ay_hbr_hint_with_final_intro keptHints final
    (ay_hbr_hint_compress_rat_add_trace
      keptHints removedHints first second third final
      redundancy parents_from_full final_from_added)

theorem ay_hbr_hint_compressed_trace_backward
    (keptHints : Prop) (final : Prop) :
    AyHbrHintWithFinal keptHints final ->
    keptHints := by
  intro with_final
  exact ay_hbr_hint_with_final_projection keptHints final with_final

theorem ay_hbr_hint_compressed_trace_equisat
    (keptHints : Prop) (removedHints : Prop)
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrHintRedundant keptHints removedHints ->
    AyHbrHintStep
      (AyHbrHintFullHints keptHints removedHints)
      (AyHbrHintParents first second third) ->
    AyHbrHintStep
      (AyHbrHintRatAdded
        keptHints
        (AyHbrHintBinaryImp first third))
      final ->
    AyHbrHintEquisat keptHints (AyHbrHintWithFinal keptHints final) := by
  intro redundancy
  intro parents_from_full
  intro final_from_added
  exact ay_hbr_hint_conj_intro
    (keptHints -> AyHbrHintWithFinal keptHints final)
    (AyHbrHintWithFinal keptHints final -> keptHints)
    (ay_hbr_hint_compressed_trace_forward
      keptHints removedHints first second third final
      redundancy parents_from_full final_from_added)
    (ay_hbr_hint_compressed_trace_backward keptHints final)
