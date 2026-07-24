-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for learned-clause cuts in SAT proof/certificate
-- pipelines. A learned clause is represented by an explicit derivation
-- witness from current premises; adding it, using it as a cut, and deleting it
-- preserves the satisfiability witness interface.

def AyCutDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCutConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCutEquisat (before : Prop) (after : Prop) :=
  AyCutConj (before -> after) (after -> before)

def AyCutPremises (leftPremise : Prop) (rightPremise : Prop) :=
  AyCutConj leftPremise rightPremise

def AyLearnedWitness (premises : Prop) (learned : Prop) :=
  premises -> learned

def AyCutAdded (premises : Prop) (learned : Prop) :=
  AyCutConj premises learned

def AyCutAddedThenUsed
    (premises : Prop) (learned : Prop) (final : Prop) :=
  AyCutConj (AyCutAdded premises learned) final

def AyCutDeletedAfterUse (premises : Prop) (final : Prop) :=
  AyCutConj premises final

theorem ay_cut_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCutConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_cut_conj_left
    (left : Prop) (right : Prop) :
    AyCutConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cut_conj_right
    (left : Prop) (right : Prop) :
    AyCutConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cut_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCutDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_cut_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCutDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_cut_resolution_learned_clause
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyCutDisj left pivot ->
    AyCutDisj right (Not pivot) ->
    AyCutDisj left right := by
  intro positive_parent
  intro negative_parent
  intro result
  intro left_case
  intro right_case
  exact positive_parent result left_case
    (fun pivot_sat =>
      negative_parent result right_case
        (fun pivot_unsat => False.elim (pivot_unsat pivot_sat)))

theorem ay_cut_premises_resolution_witness
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyLearnedWitness
      (AyCutPremises
        (AyCutDisj left pivot)
        (AyCutDisj right (Not pivot)))
      (AyCutDisj left right) := by
  intro premises
  exact ay_cut_resolution_learned_clause left right pivot
    (ay_cut_conj_left
      (AyCutDisj left pivot)
      (AyCutDisj right (Not pivot))
      premises)
    (ay_cut_conj_right
      (AyCutDisj left pivot)
      (AyCutDisj right (Not pivot))
      premises)

theorem ay_cut_learned_add_projection
    (premises : Prop) (learned : Prop) :
    AyCutAdded premises learned -> premises := by
  intro added
  exact ay_cut_conj_left premises learned added

theorem ay_cut_learned_add_candidate
    (premises : Prop) (learned : Prop) :
    AyCutAdded premises learned -> learned := by
  intro added
  exact ay_cut_conj_right premises learned added

theorem ay_cut_learned_add_reconstruct
    (premises : Prop) (learned : Prop) :
    AyLearnedWitness premises learned ->
    premises ->
    AyCutAdded premises learned := by
  intro witness
  intro hpremises
  exact ay_cut_conj_intro premises learned
    hpremises
    (witness hpremises)

theorem ay_cut_learned_add_equisat
    (premises : Prop) (learned : Prop) :
    AyLearnedWitness premises learned ->
    AyCutEquisat premises (AyCutAdded premises learned) := by
  intro witness
  exact ay_cut_conj_intro
    (premises -> AyCutAdded premises learned)
    (AyCutAdded premises learned -> premises)
    (ay_cut_learned_add_reconstruct premises learned witness)
    (ay_cut_learned_add_projection premises learned)

theorem ay_cut_use_added_learned
    (premises : Prop) (learned : Prop) (final : Prop) :
    (AyCutAdded premises learned -> final) ->
    AyCutAdded premises learned ->
    AyCutAddedThenUsed premises learned final := by
  intro use_cut
  intro added
  exact ay_cut_conj_intro
    (AyCutAdded premises learned)
    final
    added
    (use_cut added)

theorem ay_cut_delete_learned_after_use
    (premises : Prop) (learned : Prop) (final : Prop) :
    AyCutAddedThenUsed premises learned final ->
    AyCutDeletedAfterUse premises final := by
  intro added_then_used
  exact ay_cut_conj_intro premises final
    (ay_cut_learned_add_projection premises learned
      (ay_cut_conj_left
        (AyCutAdded premises learned)
        final
        added_then_used))
    (ay_cut_conj_right
      (AyCutAdded premises learned)
      final
      added_then_used)

theorem ay_cut_add_use_delete_forward
    (premises : Prop) (learned : Prop) (final : Prop) :
    AyLearnedWitness premises learned ->
    (AyCutAdded premises learned -> final) ->
    premises ->
    AyCutDeletedAfterUse premises final := by
  intro witness
  intro use_cut
  intro hpremises
  exact ay_cut_delete_learned_after_use premises learned final
    (ay_cut_use_added_learned premises learned final
      use_cut
      (ay_cut_learned_add_reconstruct
        premises learned witness hpremises))

theorem ay_cut_add_use_delete_backward
    (premises : Prop) (final : Prop) :
    AyCutDeletedAfterUse premises final ->
    premises := by
  intro deleted
  exact ay_cut_conj_left premises final deleted

theorem ay_cut_add_use_delete_equisat
    (premises : Prop) (learned : Prop) (final : Prop) :
    AyLearnedWitness premises learned ->
    (AyCutAdded premises learned -> final) ->
    AyCutEquisat premises (AyCutDeletedAfterUse premises final) := by
  intro witness
  intro use_cut
  exact ay_cut_conj_intro
    (premises -> AyCutDeletedAfterUse premises final)
    (AyCutDeletedAfterUse premises final -> premises)
    (ay_cut_add_use_delete_forward premises learned final witness use_cut)
    (ay_cut_add_use_delete_backward premises final)

theorem ay_cut_compressed_final_sound
    (premises : Prop) (learned : Prop) (final : Prop) :
    AyLearnedWitness premises learned ->
    (AyCutAdded premises learned -> final) ->
    premises ->
    final := by
  intro witness
  intro use_cut
  intro hpremises
  exact ay_cut_conj_right premises final
    (ay_cut_add_use_delete_forward
      premises learned final witness use_cut hpremises)

theorem ay_cut_resolution_add_use_delete_equisat
    (left : Prop) (right : Prop) (pivot : Prop) (final : Prop) :
    (AyCutAdded
      (AyCutPremises
        (AyCutDisj left pivot)
        (AyCutDisj right (Not pivot)))
      (AyCutDisj left right) ->
      final) ->
    AyCutEquisat
      (AyCutPremises
        (AyCutDisj left pivot)
        (AyCutDisj right (Not pivot)))
      (AyCutDeletedAfterUse
        (AyCutPremises
          (AyCutDisj left pivot)
          (AyCutDisj right (Not pivot)))
        final) := by
  intro use_cut
  exact ay_cut_add_use_delete_equisat
    (AyCutPremises
      (AyCutDisj left pivot)
      (AyCutDisj right (Not pivot)))
    (AyCutDisj left right)
    final
    (ay_cut_premises_resolution_witness left right pivot)
    use_cut

theorem ay_cut_resolution_compressed_final_sound
    (left : Prop) (right : Prop) (pivot : Prop) (final : Prop) :
    (AyCutAdded
      (AyCutPremises
        (AyCutDisj left pivot)
        (AyCutDisj right (Not pivot)))
      (AyCutDisj left right) ->
      final) ->
    AyCutPremises
      (AyCutDisj left pivot)
      (AyCutDisj right (Not pivot)) ->
    final := by
  intro use_cut
  exact ay_cut_compressed_final_sound
    (AyCutPremises
      (AyCutDisj left pivot)
      (AyCutDisj right (Not pivot)))
    (AyCutDisj left right)
    final
    (ay_cut_premises_resolution_witness left right pivot)
    use_cut
