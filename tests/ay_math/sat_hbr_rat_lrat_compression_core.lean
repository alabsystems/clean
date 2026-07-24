-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for compressing an HBR-derived RAT/RUP clause-add
-- trace while preserving final derived-clause soundness.

def AyHbrRatLratDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHbrRatLratConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHbrRatLratStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyHbrRatLratBinaryImp (source : Prop) (target : Prop) :=
  AyHbrRatLratDisj (Not source) target

def AyHbrRatLratParents
    (first : Prop) (second : Prop) (third : Prop) :=
  AyHbrRatLratConj
    (AyHbrRatLratBinaryImp first second)
    (AyHbrRatLratBinaryImp second third)

def AyHbrRatLratRatAdded (available : Prop) (candidate : Prop) :=
  AyHbrRatLratConj available candidate

def AyHbrRatLratWithFinal (available : Prop) (final : Prop) :=
  AyHbrRatLratConj available final

def AyHbrRatLratEquisat (before : Prop) (after : Prop) :=
  AyHbrRatLratConj (before -> after) (after -> before)

theorem ay_hbr_rat_lrat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHbrRatLratConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hbr_rat_lrat_conj_left
    (left : Prop) (right : Prop) :
    AyHbrRatLratConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hbr_rat_lrat_conj_right
    (left : Prop) (right : Prop) :
    AyHbrRatLratConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hbr_rat_lrat_binary_to_implication
    (source : Prop) (target : Prop) :
    AyHbrRatLratBinaryImp source target ->
    source ->
    target := by
  intro clause
  intro hsource
  exact clause target
    (fun not_source => False.elim (not_source hsource))
    (fun htarget => htarget)

theorem ay_hbr_rat_lrat_binary_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrRatLratBinaryImp source middle ->
    AyHbrRatLratBinaryImp middle target ->
    AyHbrRatLratBinaryImp source target := by
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

theorem ay_hbr_rat_lrat_derive_candidate
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatLratParents first second third ->
    AyHbrRatLratBinaryImp first third := by
  intro parents
  exact parents (AyHbrRatLratBinaryImp first third)
    (fun first_second second_third =>
      ay_hbr_rat_lrat_binary_transitive
        first second third first_second second_third)

theorem ay_hbr_rat_lrat_rat_add_candidate
    (available : Prop) (candidate : Prop) :
    AyHbrRatLratStep available candidate ->
    AyHbrRatLratStep
      available
      (AyHbrRatLratRatAdded available candidate) := by
  intro witness
  intro available_sat
  exact ay_hbr_rat_lrat_conj_intro available candidate
    available_sat
    (witness available_sat)

theorem ay_hbr_rat_lrat_rat_added_projection
    (available : Prop) (candidate : Prop) :
    AyHbrRatLratRatAdded available candidate -> available := by
  intro added
  exact ay_hbr_rat_lrat_conj_left available candidate added

theorem ay_hbr_rat_lrat_rat_added_candidate
    (available : Prop) (candidate : Prop) :
    AyHbrRatLratRatAdded available candidate -> candidate := by
  intro added
  exact ay_hbr_rat_lrat_conj_right available candidate added

theorem ay_hbr_rat_lrat_add_then_derive
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyHbrRatLratStep available candidate ->
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded available candidate)
      final ->
    AyHbrRatLratStep available final := by
  intro add_candidate
  intro derive_final
  intro available_sat
  exact derive_final
    (ay_hbr_rat_lrat_rat_add_candidate available candidate
      add_candidate
      available_sat)

theorem ay_hbr_rat_lrat_hbr_add_trace
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratParents first second third)
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third)) := by
  exact ay_hbr_rat_lrat_rat_add_candidate
    (AyHbrRatLratParents first second third)
    (AyHbrRatLratBinaryImp first third)
    (ay_hbr_rat_lrat_derive_candidate first second third)

theorem ay_hbr_rat_lrat_compress_add_trace
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third))
      final ->
    AyHbrRatLratStep
      (AyHbrRatLratParents first second third)
      final := by
  intro final_from_added
  exact ay_hbr_rat_lrat_add_then_derive
    (AyHbrRatLratParents first second third)
    (AyHbrRatLratBinaryImp first third)
    final
    (ay_hbr_rat_lrat_derive_candidate first second third)
    final_from_added

theorem ay_hbr_rat_lrat_compressed_final_sound
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third))
      final ->
    AyHbrRatLratParents first second third ->
    final := by
  intro final_from_added
  exact ay_hbr_rat_lrat_compress_add_trace
    first second third final final_from_added

theorem ay_hbr_rat_lrat_with_final_intro
    (available : Prop) (final : Prop) :
    AyHbrRatLratStep available final ->
    available ->
    AyHbrRatLratWithFinal available final := by
  intro final_step
  intro available_sat
  exact ay_hbr_rat_lrat_conj_intro available final
    available_sat
    (final_step available_sat)

theorem ay_hbr_rat_lrat_with_final_projection
    (available : Prop) (final : Prop) :
    AyHbrRatLratWithFinal available final -> available := by
  intro with_final
  exact ay_hbr_rat_lrat_conj_left available final with_final

theorem ay_hbr_rat_lrat_compressed_with_final_forward
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third))
      final ->
    AyHbrRatLratParents first second third ->
    AyHbrRatLratWithFinal
      (AyHbrRatLratParents first second third)
      final := by
  intro final_from_added
  exact ay_hbr_rat_lrat_with_final_intro
    (AyHbrRatLratParents first second third)
    final
    (ay_hbr_rat_lrat_compress_add_trace
      first second third final final_from_added)

theorem ay_hbr_rat_lrat_compressed_with_final_backward
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrRatLratWithFinal
      (AyHbrRatLratParents first second third)
      final ->
    AyHbrRatLratParents first second third := by
  intro with_final
  exact ay_hbr_rat_lrat_with_final_projection
    (AyHbrRatLratParents first second third)
    final
    with_final

theorem ay_hbr_rat_lrat_compressed_trace_equisat
    (first : Prop) (second : Prop) (third : Prop) (final : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third))
      final ->
    AyHbrRatLratEquisat
      (AyHbrRatLratParents first second third)
      (AyHbrRatLratWithFinal
        (AyHbrRatLratParents first second third)
        final) := by
  intro final_from_added
  exact ay_hbr_rat_lrat_conj_intro
    (AyHbrRatLratParents first second third ->
      AyHbrRatLratWithFinal
        (AyHbrRatLratParents first second third)
        final)
    (AyHbrRatLratWithFinal
      (AyHbrRatLratParents first second third)
      final ->
      AyHbrRatLratParents first second third)
    (ay_hbr_rat_lrat_compressed_with_final_forward
      first second third final final_from_added)
    (ay_hbr_rat_lrat_compressed_with_final_backward
      first second third final)

theorem ay_hbr_rat_lrat_use_candidate_final
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratRatAdded
        (AyHbrRatLratParents first second third)
        (AyHbrRatLratBinaryImp first third))
      (first -> third) := by
  intro added
  intro hfirst
  exact ay_hbr_rat_lrat_binary_to_implication first third
    (ay_hbr_rat_lrat_rat_added_candidate
      (AyHbrRatLratParents first second third)
      (AyHbrRatLratBinaryImp first third)
      added)
    hfirst

theorem ay_hbr_rat_lrat_compress_use_candidate
    (first : Prop) (second : Prop) (third : Prop) :
    AyHbrRatLratStep
      (AyHbrRatLratParents first second third)
      (first -> third) := by
  exact ay_hbr_rat_lrat_compress_add_trace
    first second third
    (first -> third)
    (ay_hbr_rat_lrat_use_candidate_final first second third)
