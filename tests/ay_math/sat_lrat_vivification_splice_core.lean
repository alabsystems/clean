-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for splicing a resolution LRAT trace into a
-- vivification/RAT handoff trace. The first trace derives an intermediate
-- clause; the second uses that intermediate clause as available context for a
-- checked RAT/RUP vivification witness.

def AyLratVivDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLratVivConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLratVivStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyLratVivWithDerived (available : Prop) (derived : Prop) :=
  AyLratVivConj available derived

def AyLratVivRatAdded (current : Prop) (candidate : Prop) :=
  AyLratVivConj current candidate

def AyLratVivRatReplacement (current : Prop) (candidate : Prop) :=
  AyLratVivConj candidate current

theorem ay_lrat_viv_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLratVivConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_lrat_viv_conj_left
    (left : Prop) (right : Prop) :
    AyLratVivConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_lrat_viv_conj_right
    (left : Prop) (right : Prop) :
    AyLratVivConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_lrat_viv_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLratVivDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_lrat_viv_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLratVivDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_lrat_viv_resolution_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLratVivDisj left pivot ->
    AyLratVivDisj right (Not pivot) ->
    AyLratVivDisj left right := by
  intro left_or_pivot
  intro right_or_not_pivot
  intro result
  intro left_to_result
  intro right_to_result
  exact left_or_pivot result left_to_result
    (fun pivot_sat =>
      right_or_not_pivot result right_to_result
        (fun pivot_unsat => False.elim (pivot_unsat pivot_sat)))

theorem ay_lrat_viv_splice_with_context
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratVivStep available intermediate ->
    (AyLratVivWithDerived available intermediate -> final) ->
    AyLratVivStep available final := by
  intro firstTrace
  intro secondTrace
  intro available_sat
  exact secondTrace
    (ay_lrat_viv_conj_intro available intermediate
      available_sat
      (firstTrace available_sat))

def AyLratVivResolutionParents
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyLratVivConj
    (AyLratVivDisj left pivot)
    (AyLratVivDisj right (Not pivot))

theorem ay_lrat_viv_resolution_trace
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLratVivStep
      (AyLratVivResolutionParents left right pivot)
      (AyLratVivDisj left right) := by
  intro parents
  exact ay_lrat_viv_resolution_sound left right pivot
    (ay_lrat_viv_conj_left
      (AyLratVivDisj left pivot)
      (AyLratVivDisj right (Not pivot))
      parents)
    (ay_lrat_viv_conj_right
      (AyLratVivDisj left pivot)
      (AyLratVivDisj right (Not pivot))
      parents)

theorem ay_lrat_viv_rat_add_candidate
    (current : Prop) (candidate : Prop) :
    AyLratVivStep current candidate ->
    AyLratVivStep current (AyLratVivRatAdded current candidate) := by
  intro witness
  intro current_sat
  exact ay_lrat_viv_conj_intro current candidate
    current_sat
    (witness current_sat)

theorem ay_lrat_viv_rat_delete_after_add
    (current : Prop) (candidate : Prop) :
    AyLratVivRatAdded current candidate ->
    AyLratVivRatReplacement current candidate := by
  intro added
  exact ay_lrat_viv_conj_intro candidate current
    (ay_lrat_viv_conj_right current candidate added)
    (ay_lrat_viv_conj_left current candidate added)

theorem ay_lrat_viv_rat_handoff_trace
    (current : Prop) (candidate : Prop) :
    AyLratVivStep current candidate ->
    AyLratVivStep current (AyLratVivRatReplacement current candidate) := by
  intro witness
  intro current_sat
  exact ay_lrat_viv_rat_delete_after_add current candidate
    (ay_lrat_viv_rat_add_candidate current candidate witness current_sat)

theorem ay_lrat_viv_rat_handoff_candidate
    (current : Prop) (candidate : Prop) :
    AyLratVivRatReplacement current candidate -> candidate := by
  intro replacement
  exact ay_lrat_viv_conj_left candidate current replacement

theorem ay_lrat_viv_rat_handoff_context
    (current : Prop) (candidate : Prop) :
    AyLratVivRatReplacement current candidate -> current := by
  intro replacement
  exact ay_lrat_viv_conj_right candidate current replacement

theorem ay_lrat_viv_splice_resolution_then_viv_rat
    (left : Prop)
    (right : Prop)
    (pivot : Prop)
    (candidate : Prop) :
    AyLratVivStep
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate ->
    AyLratVivStep
      (AyLratVivResolutionParents left right pivot)
      (AyLratVivRatReplacement
        (AyLratVivWithDerived
          (AyLratVivResolutionParents left right pivot)
          (AyLratVivDisj left right))
        candidate) := by
  intro vivWitness
  exact ay_lrat_viv_splice_with_context
    (AyLratVivResolutionParents left right pivot)
    (AyLratVivDisj left right)
    (AyLratVivRatReplacement
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate)
    (ay_lrat_viv_resolution_trace left right pivot)
    (ay_lrat_viv_rat_handoff_trace
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate
      vivWitness)

theorem ay_lrat_viv_spliced_final_clause_sound
    (left : Prop)
    (right : Prop)
    (pivot : Prop)
    (candidate : Prop) :
    AyLratVivStep
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate ->
    AyLratVivResolutionParents left right pivot ->
    candidate := by
  intro vivWitness
  intro parents
  exact ay_lrat_viv_rat_handoff_candidate
    (AyLratVivWithDerived
      (AyLratVivResolutionParents left right pivot)
      (AyLratVivDisj left right))
    candidate
    (ay_lrat_viv_splice_resolution_then_viv_rat
      left right pivot candidate vivWitness parents)

theorem ay_lrat_viv_spliced_resolution_context_sound
    (left : Prop)
    (right : Prop)
    (pivot : Prop)
    (candidate : Prop) :
    AyLratVivStep
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate ->
    AyLratVivResolutionParents left right pivot ->
    AyLratVivDisj left right := by
  intro vivWitness
  intro parents
  exact ay_lrat_viv_conj_right
    (AyLratVivResolutionParents left right pivot)
    (AyLratVivDisj left right)
    (ay_lrat_viv_rat_handoff_context
      (AyLratVivWithDerived
        (AyLratVivResolutionParents left right pivot)
        (AyLratVivDisj left right))
      candidate
      (ay_lrat_viv_splice_resolution_then_viv_rat
        left right pivot candidate vivWitness parents))

