-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for RAT/RUP-style clause addition.
-- A checked RUP/RAT witness is abstracted as an implication from the current
-- clause database semantics to the candidate clause. Adding the candidate is
-- therefore satisfiability-preserving by projection, and deletion later drops
-- the candidate while keeping any independently recorded derived clause.

def AyRatConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRatEquisat (original : Prop) (transformed : Prop) :=
  AyRatConj (original -> transformed) (transformed -> original)

def AyRupWitness (existing : Prop) (candidate : Prop) :=
  existing -> candidate

def AyRatWitness (existing : Prop) (candidate : Prop) :=
  existing -> candidate

def AyRatAddedFormula (existing : Prop) (candidate : Prop) :=
  AyRatConj existing candidate

def AyRatAddedThenDerived
    (existing : Prop) (candidate : Prop) (derived : Prop) :=
  AyRatConj (AyRatAddedFormula existing candidate) derived

def AyRatDeletedAfterUse
    (existing : Prop) (derived : Prop) :=
  AyRatConj existing derived

theorem ay_rat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRatConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_rat_conj_left
    (left : Prop) (right : Prop) :
    AyRatConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_rat_conj_right
    (left : Prop) (right : Prop) :
    AyRatConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_rup_witness_to_rat_witness
    (existing : Prop) (candidate : Prop) :
    AyRupWitness existing candidate ->
    AyRatWitness existing candidate := by
  intro witness
  exact witness

theorem ay_rat_clause_add_projection
    (existing : Prop) (candidate : Prop) :
    AyRatAddedFormula existing candidate -> existing := by
  intro added
  exact ay_rat_conj_left existing candidate added

theorem ay_rat_clause_add_candidate
    (existing : Prop) (candidate : Prop) :
    AyRatAddedFormula existing candidate -> candidate := by
  intro added
  exact ay_rat_conj_right existing candidate added

theorem ay_rat_clause_add_reconstruct
    (existing : Prop) (candidate : Prop) :
    AyRatWitness existing candidate ->
    existing ->
    AyRatAddedFormula existing candidate := by
  intro witness
  intro existing_sat
  exact ay_rat_conj_intro existing candidate
    existing_sat
    (witness existing_sat)

theorem ay_rup_clause_add_reconstruct
    (existing : Prop) (candidate : Prop) :
    AyRupWitness existing candidate ->
    existing ->
    AyRatAddedFormula existing candidate := by
  intro witness
  exact ay_rat_clause_add_reconstruct existing candidate
    (ay_rup_witness_to_rat_witness existing candidate witness)

theorem ay_rat_clause_add_equisat
    (existing : Prop) (candidate : Prop) :
    AyRatWitness existing candidate ->
    AyRatEquisat existing (AyRatAddedFormula existing candidate) := by
  intro witness
  exact ay_rat_conj_intro
    (existing -> AyRatAddedFormula existing candidate)
    (AyRatAddedFormula existing candidate -> existing)
    (ay_rat_clause_add_reconstruct existing candidate witness)
    (ay_rat_clause_add_projection existing candidate)

theorem ay_rup_clause_add_equisat
    (existing : Prop) (candidate : Prop) :
    AyRupWitness existing candidate ->
    AyRatEquisat existing (AyRatAddedFormula existing candidate) := by
  intro witness
  exact ay_rat_clause_add_equisat existing candidate
    (ay_rup_witness_to_rat_witness existing candidate witness)

theorem ay_rat_clause_delete_after_add_projection
    (existing : Prop) (candidate : Prop) :
    AyRatAddedFormula existing candidate -> existing := by
  intro added
  exact ay_rat_clause_add_projection existing candidate added

theorem ay_rat_later_derived_clause_intro
    (existing : Prop) (candidate : Prop) (derived : Prop) :
    (AyRatAddedFormula existing candidate -> derived) ->
    AyRatAddedFormula existing candidate ->
    AyRatAddedThenDerived existing candidate derived := by
  intro derive
  intro added
  exact ay_rat_conj_intro
    (AyRatAddedFormula existing candidate)
    derived
    added
    (derive added)

theorem ay_rat_delete_candidate_after_derived
    (existing : Prop) (candidate : Prop) (derived : Prop) :
    AyRatAddedThenDerived existing candidate derived ->
    AyRatDeletedAfterUse existing derived := by
  intro added_then_derived
  exact ay_rat_conj_intro existing derived
    (ay_rat_clause_add_projection existing candidate
      (ay_rat_conj_left
        (AyRatAddedFormula existing candidate)
        derived
        added_then_derived))
    (ay_rat_conj_right
      (AyRatAddedFormula existing candidate)
      derived
      added_then_derived)

theorem ay_rat_add_derive_delete_projection
    (existing : Prop) (candidate : Prop) (derived : Prop) :
    AyRatWitness existing candidate ->
    (AyRatAddedFormula existing candidate -> derived) ->
    existing ->
    AyRatDeletedAfterUse existing derived := by
  intro witness
  intro derive
  intro existing_sat
  exact ay_rat_delete_candidate_after_derived existing candidate derived
    (ay_rat_later_derived_clause_intro existing candidate derived
      derive
      (ay_rat_clause_add_reconstruct existing candidate witness existing_sat))

