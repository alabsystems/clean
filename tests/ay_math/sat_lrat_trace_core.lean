-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for LRAT/RUP-style proof trace composition.
-- A trace step is represented as a soundness certificate from available
-- clauses to a derived clause. The two-resolution theorem models the common
-- LRAT pattern where a derived resolvent is immediately used by a later step.

def AyLratDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLratConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLratStep (available : Prop) (derived : Prop) :=
  available -> derived

theorem ay_lrat_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLratDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_lrat_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLratDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_lrat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLratConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_lrat_conj_left
    (left : Prop) (right : Prop) :
    AyLratConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_lrat_conj_right
    (left : Prop) (right : Prop) :
    AyLratConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_lrat_resolution_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLratDisj left pivot ->
    AyLratDisj right (Not pivot) ->
    AyLratDisj left right := by
  intro left_or_pivot
  intro right_or_not_pivot
  intro result
  intro left_to_result
  intro right_to_result
  exact left_or_pivot result left_to_result
    (fun pivot_sat =>
      right_or_not_pivot result right_to_result
        (fun pivot_unsat => False.elim (pivot_unsat pivot_sat)))

theorem ay_lrat_trace_compose
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratStep available intermediate ->
    AyLratStep intermediate final ->
    AyLratStep available final := by
  intro step_a
  intro step_b
  intro available_sat
  exact step_b (step_a available_sat)

theorem ay_lrat_trace_compose_with_context
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratStep available intermediate ->
    (AyLratConj available intermediate -> final) ->
    AyLratStep available final := by
  intro step_a
  intro step_b
  intro available_sat
  exact step_b
    (ay_lrat_conj_intro available intermediate
      available_sat
      (step_a available_sat))

def AyTwoResolutionParents
    (left middle final pivot : Prop) :=
  AyLratConj
    (AyLratDisj left pivot)
    (AyLratConj
      (AyLratDisj middle (Not pivot))
      (AyLratDisj final (Not middle)))

theorem ay_lrat_first_resolution_step
    (left middle final pivot : Prop) :
    AyLratStep
      (AyTwoResolutionParents left middle final pivot)
      (AyLratDisj left middle) := by
  intro parents
  exact ay_lrat_resolution_sound left middle pivot
    (ay_lrat_conj_left
      (AyLratDisj left pivot)
      (AyLratConj
        (AyLratDisj middle (Not pivot))
        (AyLratDisj final (Not middle)))
      parents)
    (ay_lrat_conj_left
      (AyLratDisj middle (Not pivot))
      (AyLratDisj final (Not middle))
      (ay_lrat_conj_right
        (AyLratDisj left pivot)
        (AyLratConj
          (AyLratDisj middle (Not pivot))
          (AyLratDisj final (Not middle)))
        parents))

theorem ay_lrat_second_resolution_step
    (left middle final pivot : Prop) :
    AyLratConj
      (AyTwoResolutionParents left middle final pivot)
      (AyLratDisj left middle) ->
    AyLratDisj left final := by
  intro trace_state
  exact ay_lrat_resolution_sound left final middle
    (ay_lrat_conj_right
      (AyTwoResolutionParents left middle final pivot)
      (AyLratDisj left middle)
      trace_state)
    (ay_lrat_conj_right
      (AyLratDisj middle (Not pivot))
      (AyLratDisj final (Not middle))
      (ay_lrat_conj_right
        (AyLratDisj left pivot)
        (AyLratConj
          (AyLratDisj middle (Not pivot))
          (AyLratDisj final (Not middle)))
        (ay_lrat_conj_left
          (AyTwoResolutionParents left middle final pivot)
          (AyLratDisj left middle)
          trace_state)))

theorem ay_lrat_two_resolution_trace
    (left middle final pivot : Prop) :
    AyLratStep
      (AyTwoResolutionParents left middle final pivot)
      (AyLratDisj left final) := by
  exact ay_lrat_trace_compose_with_context
    (AyTwoResolutionParents left middle final pivot)
    (AyLratDisj left middle)
    (AyLratDisj left final)
    (ay_lrat_first_resolution_step left middle final pivot)
    (ay_lrat_second_resolution_step left middle final pivot)

theorem ay_lrat_two_resolution_trace_at_parents
    (left middle final pivot : Prop) :
    AyTwoResolutionParents left middle final pivot ->
    AyLratDisj left final := by
  intro parents
  exact ay_lrat_two_resolution_trace left middle final pivot parents

