-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for LRAT trace splicing.
-- Two independently checked traces can be spliced when the final clause of
-- the first trace is the intermediate clause consumed by the second trace.

def AyLratSpliceDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLratSpliceConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLratSpliceStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyLratSpliceWithDerived (available : Prop) (derived : Prop) :=
  AyLratSpliceConj available derived

def AyLratSpliceRatAdded (available : Prop) (candidate : Prop) :=
  AyLratSpliceConj available candidate

theorem ay_lrat_splice_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLratSpliceConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_lrat_splice_conj_left
    (left : Prop) (right : Prop) :
    AyLratSpliceConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_lrat_splice_conj_right
    (left : Prop) (right : Prop) :
    AyLratSpliceConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_lrat_splice_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLratSpliceDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_lrat_splice_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLratSpliceDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_lrat_splice_resolution_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLratSpliceDisj left pivot ->
    AyLratSpliceDisj right (Not pivot) ->
    AyLratSpliceDisj left right := by
  intro left_or_pivot
  intro right_or_not_pivot
  intro result
  intro left_to_result
  intro right_to_result
  exact left_or_pivot result left_to_result
    (fun pivot_sat =>
      right_or_not_pivot result right_to_result
        (fun pivot_unsat => False.elim (pivot_unsat pivot_sat)))

theorem ay_lrat_splice_matching_traces
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratSpliceStep available intermediate ->
    AyLratSpliceStep intermediate final ->
    AyLratSpliceStep available final := by
  intro firstTrace
  intro secondTrace
  intro available_sat
  exact secondTrace (firstTrace available_sat)

theorem ay_lrat_splice_with_context
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratSpliceStep available intermediate ->
    (AyLratSpliceWithDerived available intermediate -> final) ->
    AyLratSpliceStep available final := by
  intro firstTrace
  intro secondTrace
  intro available_sat
  exact secondTrace
    (ay_lrat_splice_conj_intro available intermediate
      available_sat
      (firstTrace available_sat))

theorem ay_lrat_splice_keeps_intermediate
    (available : Prop) (intermediate : Prop) :
    AyLratSpliceStep
      available
      (AyLratSpliceWithDerived available intermediate) ->
    AyLratSpliceStep available intermediate := by
  intro traced
  intro available_sat
  exact ay_lrat_splice_conj_right available intermediate
    (traced available_sat)

def AyLratSpliceResolutionParents
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyLratSpliceConj
    (AyLratSpliceDisj left pivot)
    (AyLratSpliceDisj right (Not pivot))

theorem ay_lrat_splice_resolution_trace
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLratSpliceStep
      (AyLratSpliceResolutionParents left right pivot)
      (AyLratSpliceDisj left right) := by
  intro parents
  exact ay_lrat_splice_resolution_sound left right pivot
    (ay_lrat_splice_conj_left
      (AyLratSpliceDisj left pivot)
      (AyLratSpliceDisj right (Not pivot))
      parents)
    (ay_lrat_splice_conj_right
      (AyLratSpliceDisj left pivot)
      (AyLratSpliceDisj right (Not pivot))
      parents)

theorem ay_lrat_splice_rat_add_candidate
    (available : Prop) (candidate : Prop) :
    AyLratSpliceStep available candidate ->
    AyLratSpliceStep
      available
      (AyLratSpliceRatAdded available candidate) := by
  intro witness
  intro available_sat
  exact ay_lrat_splice_conj_intro available candidate
    available_sat
    (witness available_sat)

theorem ay_lrat_splice_rat_added_projection
    (available : Prop) (candidate : Prop) :
    AyLratSpliceRatAdded available candidate -> available := by
  intro added
  exact ay_lrat_splice_conj_left available candidate added

theorem ay_lrat_splice_rat_added_candidate
    (available : Prop) (candidate : Prop) :
    AyLratSpliceRatAdded available candidate -> candidate := by
  intro added
  exact ay_lrat_splice_conj_right available candidate added

theorem ay_lrat_splice_rat_add_then_derive
    (available : Prop) (candidate : Prop) (final : Prop) :
    AyLratSpliceStep available candidate ->
    AyLratSpliceStep (AyLratSpliceRatAdded available candidate) final ->
    AyLratSpliceStep available final := by
  intro addCandidate
  intro deriveFinal
  intro available_sat
  exact deriveFinal
    (ay_lrat_splice_rat_add_candidate available candidate
      addCandidate
      available_sat)

theorem ay_lrat_splice_resolution_then_rat_add
    (left : Prop) (right : Prop) (pivot : Prop) (final : Prop) :
    AyLratSpliceStep
      (AyLratSpliceRatAdded
        (AyLratSpliceResolutionParents left right pivot)
        (AyLratSpliceDisj left right))
      final ->
    AyLratSpliceStep
      (AyLratSpliceResolutionParents left right pivot)
      final := by
  intro ratAddTrace
  exact ay_lrat_splice_rat_add_then_derive
    (AyLratSpliceResolutionParents left right pivot)
    (AyLratSpliceDisj left right)
    final
    (ay_lrat_splice_resolution_trace left right pivot)
    ratAddTrace

theorem ay_lrat_splice_resolution_then_rat_add_at_parents
    (left : Prop) (right : Prop) (pivot : Prop) (final : Prop) :
    AyLratSpliceStep
      (AyLratSpliceRatAdded
        (AyLratSpliceResolutionParents left right pivot)
        (AyLratSpliceDisj left right))
      final ->
    AyLratSpliceResolutionParents left right pivot ->
    final := by
  intro ratAddTrace
  exact ay_lrat_splice_resolution_then_rat_add
    left right pivot final ratAddTrace

