-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for LRAT hint minimization feeding a
-- RAT/RUP clause-add handoff. A minimized LRAT/RUP step is an implication from
-- the remaining checked hints to the candidate clause, which is exactly the
-- witness needed to add that clause and later delete it after use.

def AyHintRatConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHintRatEquisat (before : Prop) (after : Prop) :=
  AyHintRatConj (before -> after) (after -> before)

def AyHintRatStep (hints : Prop) (derived : Prop) :=
  hints -> derived

def AyHintRatRedundantHint (keptHints : Prop) (redundantHint : Prop) :=
  keptHints -> redundantHint

def AyHintRatWithRedundantHint
    (keptHints : Prop) (redundantHint : Prop) :=
  AyHintRatConj keptHints redundantHint

def AyHintRatAddedFormula (existing : Prop) (candidate : Prop) :=
  AyHintRatConj existing candidate

def AyHintRatAddedThenUsed
    (existing : Prop) (candidate : Prop) (used : Prop) :=
  AyHintRatConj (AyHintRatAddedFormula existing candidate) used

def AyHintRatDeletedAfterUse (existing : Prop) (used : Prop) :=
  AyHintRatConj existing used

theorem ay_hint_rat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHintRatConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hint_rat_conj_left
    (left : Prop) (right : Prop) :
    AyHintRatConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hint_rat_conj_right
    (left : Prop) (right : Prop) :
    AyHintRatConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hint_rat_reconstruct_hint
    (keptHints : Prop) (redundantHint : Prop) :
    AyHintRatRedundantHint keptHints redundantHint ->
    keptHints ->
    AyHintRatWithRedundantHint keptHints redundantHint := by
  intro redundancy
  intro kept
  exact ay_hint_rat_conj_intro keptHints redundantHint
    kept
    (redundancy kept)

theorem ay_hint_rat_minimize_lrat_step
    (keptHints : Prop) (redundantHint : Prop) (candidate : Prop) :
    AyHintRatRedundantHint keptHints redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint keptHints redundantHint)
      candidate ->
    AyHintRatStep keptHints candidate := by
  intro redundancy
  intro originalStep
  intro kept
  exact originalStep
    (ay_hint_rat_reconstruct_hint keptHints redundantHint redundancy kept)

theorem ay_hint_rat_minimized_step_is_rat_witness
    (existing : Prop) (redundantHint : Prop) (candidate : Prop) :
    AyHintRatRedundantHint existing redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint existing redundantHint)
      candidate ->
    existing ->
    candidate := by
  intro redundancy
  intro originalStep
  exact ay_hint_rat_minimize_lrat_step
    existing redundantHint candidate redundancy originalStep

theorem ay_hint_rat_clause_add_reconstruct
    (existing : Prop) (candidate : Prop) :
    (existing -> candidate) ->
    existing ->
    AyHintRatAddedFormula existing candidate := by
  intro witness
  intro existing_sat
  exact ay_hint_rat_conj_intro existing candidate
    existing_sat
    (witness existing_sat)

theorem ay_hint_rat_clause_add_projection
    (existing : Prop) (candidate : Prop) :
    AyHintRatAddedFormula existing candidate -> existing := by
  intro added
  exact ay_hint_rat_conj_left existing candidate added

theorem ay_hint_rat_clause_add_candidate
    (existing : Prop) (candidate : Prop) :
    AyHintRatAddedFormula existing candidate -> candidate := by
  intro added
  exact ay_hint_rat_conj_right existing candidate added

theorem ay_hint_rat_minimized_lrat_clause_add
    (existing : Prop) (redundantHint : Prop) (candidate : Prop) :
    AyHintRatRedundantHint existing redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint existing redundantHint)
      candidate ->
    existing ->
    AyHintRatAddedFormula existing candidate := by
  intro redundancy
  intro originalStep
  exact ay_hint_rat_clause_add_reconstruct existing candidate
    (ay_hint_rat_minimized_step_is_rat_witness
      existing redundantHint candidate redundancy originalStep)

theorem ay_hint_rat_minimized_lrat_clause_add_equisat
    (existing : Prop) (redundantHint : Prop) (candidate : Prop) :
    AyHintRatRedundantHint existing redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint existing redundantHint)
      candidate ->
    AyHintRatEquisat existing (AyHintRatAddedFormula existing candidate) := by
  intro redundancy
  intro originalStep
  exact ay_hint_rat_conj_intro
    (existing -> AyHintRatAddedFormula existing candidate)
    (AyHintRatAddedFormula existing candidate -> existing)
    (ay_hint_rat_minimized_lrat_clause_add
      existing redundantHint candidate redundancy originalStep)
    (ay_hint_rat_clause_add_projection existing candidate)

theorem ay_hint_rat_later_use_intro
    (existing : Prop) (candidate : Prop) (used : Prop) :
    (AyHintRatAddedFormula existing candidate -> used) ->
    AyHintRatAddedFormula existing candidate ->
    AyHintRatAddedThenUsed existing candidate used := by
  intro useCandidate
  intro added
  exact ay_hint_rat_conj_intro
    (AyHintRatAddedFormula existing candidate)
    used
    added
    (useCandidate added)

theorem ay_hint_rat_delete_candidate_after_use
    (existing : Prop) (candidate : Prop) (used : Prop) :
    AyHintRatAddedThenUsed existing candidate used ->
    AyHintRatDeletedAfterUse existing used := by
  intro addedThenUsed
  exact ay_hint_rat_conj_intro existing used
    (ay_hint_rat_clause_add_projection existing candidate
      (ay_hint_rat_conj_left
        (AyHintRatAddedFormula existing candidate)
        used
        addedThenUsed))
    (ay_hint_rat_conj_right
      (AyHintRatAddedFormula existing candidate)
      used
      addedThenUsed)

theorem ay_hint_rat_minimized_lrat_handoff
    (existing : Prop)
    (redundantHint : Prop)
    (candidate : Prop)
    (used : Prop) :
    AyHintRatRedundantHint existing redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint existing redundantHint)
      candidate ->
    (AyHintRatAddedFormula existing candidate -> used) ->
    existing ->
    AyHintRatDeletedAfterUse existing used := by
  intro redundancy
  intro originalStep
  intro useCandidate
  intro existing_sat
  exact ay_hint_rat_delete_candidate_after_use existing candidate used
    (ay_hint_rat_later_use_intro existing candidate used
      useCandidate
      (ay_hint_rat_minimized_lrat_clause_add
        existing redundantHint candidate
        redundancy
        originalStep
        existing_sat))

theorem ay_hint_rat_minimized_lrat_handoff_candidate
    (existing : Prop)
    (redundantHint : Prop)
    (candidate : Prop)
    (used : Prop) :
    AyHintRatRedundantHint existing redundantHint ->
    AyHintRatStep
      (AyHintRatWithRedundantHint existing redundantHint)
      candidate ->
    (AyHintRatAddedFormula existing candidate -> used) ->
    existing ->
    used := by
  intro redundancy
  intro originalStep
  intro useCandidate
  intro existing_sat
  exact ay_hint_rat_conj_right existing used
    (ay_hint_rat_minimized_lrat_handoff
      existing redundantHint candidate used
      redundancy
      originalStep
      useCandidate
      existing_sat)

