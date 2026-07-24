-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for LRAT/RUP-style unit propagation.
-- Clauses are represented by Church-encoded binary disjunctions. The
-- `residual` proposition stands for the remaining literals in a clause after
-- deleting the falsified complement of a propagated unit.

def AyUnitDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyUnitConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

theorem ay_unit_disj_left
    (left : Prop) (right : Prop) :
    left -> AyUnitDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_unit_disj_right
    (left : Prop) (right : Prop) :
    right -> AyUnitDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_unit_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyUnitConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_unit_propagate_negative_complement
    (pivot : Prop) (residual : Prop) :
    pivot ->
    AyUnitDisj (Not pivot) residual ->
    residual := by
  intro pivot_unit
  intro clause
  exact clause residual
    (fun neg_pivot => False.elim (neg_pivot pivot_unit))
    (fun residual_sat => residual_sat)

theorem ay_unit_propagate_positive_complement
    (pivot : Prop) (residual : Prop) :
    Not pivot ->
    AyUnitDisj pivot residual ->
    residual := by
  intro neg_pivot_unit
  intro clause
  exact clause residual
    (fun pivot_sat => False.elim (neg_pivot_unit pivot_sat))
    (fun residual_sat => residual_sat)

theorem ay_unit_clause_conflict
    (pivot : Prop) :
    pivot -> Not pivot -> False := by
  intro pivot_unit
  intro neg_pivot_unit
  exact neg_pivot_unit pivot_unit

theorem ay_unit_propagate_to_unit_clause
    (pivot : Prop) (next : Prop) :
    pivot ->
    AyUnitDisj (Not pivot) next ->
    next := by
  intro pivot_unit
  intro clause
  exact ay_unit_propagate_negative_complement pivot next pivot_unit clause

theorem ay_two_step_unit_propagation
    (first second third : Prop) :
    first ->
    AyUnitDisj (Not first) second ->
    AyUnitDisj (Not second) third ->
    third := by
  intro first_unit
  intro first_clause
  intro second_clause
  exact ay_unit_propagate_negative_complement second third
    (ay_unit_propagate_negative_complement first second first_unit first_clause)
    second_clause

theorem ay_two_step_unit_propagation_with_trace
    (first second third : Prop) :
    first ->
    AyUnitDisj (Not first) second ->
    AyUnitDisj (Not second) third ->
    AyUnitConj second third := by
  intro first_unit
  intro first_clause
  intro second_clause
  exact ay_unit_conj_intro second third
    (ay_unit_propagate_negative_complement first second first_unit first_clause)
    (ay_two_step_unit_propagation first second third
      first_unit first_clause second_clause)

theorem ay_two_step_unit_propagation_conflict
    (first second : Prop) :
    first ->
    AyUnitDisj (Not first) second ->
    AyUnitDisj (Not second) False ->
    False := by
  intro first_unit
  intro first_clause
  intro conflict_clause
  exact ay_two_step_unit_propagation first second False
    first_unit first_clause conflict_clause

