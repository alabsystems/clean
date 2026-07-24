-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for vivification plus RAT/RUP certificate
-- handoff. The shorter vivified clause is first justified by a checked
-- witness from the current formula, then it can replace the original longer
-- clause while preserving satisfiability in both directions.

def AyVivRatDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVivRatConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVivRatEquisat (original : Prop) (transformed : Prop) :=
  AyVivRatConj (original -> transformed) (transformed -> original)

def AyVivRatOriginal
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :=
  AyVivRatConj (AyVivRatDisj droppedLit shorterClause) rest

def AyVivRatReplacement
    (shorterClause : Prop) (rest : Prop) :=
  AyVivRatConj shorterClause rest

def AyVivRatWitness (currentFormula : Prop) (candidateClause : Prop) :=
  currentFormula -> candidateClause

def AyVivRupWitness (currentFormula : Prop) (candidateClause : Prop) :=
  currentFormula -> candidateClause

def AyVivRatAddedCandidate
    (currentFormula : Prop) (candidateClause : Prop) :=
  AyVivRatConj currentFormula candidateClause

theorem ay_viv_rat_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVivRatDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_viv_rat_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVivRatConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_viv_rat_conj_left
    (left : Prop) (right : Prop) :
    AyVivRatConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_viv_rat_conj_right
    (left : Prop) (right : Prop) :
    AyVivRatConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_viv_rup_witness_to_rat_witness
    (currentFormula : Prop) (candidateClause : Prop) :
    AyVivRupWitness currentFormula candidateClause ->
    AyVivRatWitness currentFormula candidateClause := by
  intro witness
  exact witness

theorem ay_viv_rat_original_rest
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatOriginal droppedLit shorterClause rest -> rest := by
  intro original
  exact ay_viv_rat_conj_right
    (AyVivRatDisj droppedLit shorterClause)
    rest
    original

theorem ay_viv_rat_replacement_backward
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatReplacement shorterClause rest ->
    AyVivRatOriginal droppedLit shorterClause rest := by
  intro replacement
  exact ay_viv_rat_conj_intro
    (AyVivRatDisj droppedLit shorterClause)
    rest
    (ay_viv_rat_disj_right droppedLit shorterClause
      (ay_viv_rat_conj_left shorterClause rest replacement))
    (ay_viv_rat_conj_right shorterClause rest replacement)

theorem ay_viv_rat_replacement_forward
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatOriginal droppedLit shorterClause rest ->
    AyVivRatReplacement shorterClause rest := by
  intro witness
  intro original
  exact ay_viv_rat_conj_intro shorterClause rest
    (witness original)
    (ay_viv_rat_original_rest droppedLit shorterClause rest original)

theorem ay_viv_rup_replacement_forward
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRupWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatOriginal droppedLit shorterClause rest ->
    AyVivRatReplacement shorterClause rest := by
  intro witness
  exact ay_viv_rat_replacement_forward droppedLit shorterClause rest
    (ay_viv_rup_witness_to_rat_witness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause
      witness)

theorem ay_viv_rat_replacement_equisat
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatEquisat
      (AyVivRatOriginal droppedLit shorterClause rest)
      (AyVivRatReplacement shorterClause rest) := by
  intro witness
  exact ay_viv_rat_conj_intro
    (AyVivRatOriginal droppedLit shorterClause rest ->
      AyVivRatReplacement shorterClause rest)
    (AyVivRatReplacement shorterClause rest ->
      AyVivRatOriginal droppedLit shorterClause rest)
    (ay_viv_rat_replacement_forward droppedLit shorterClause rest witness)
    (ay_viv_rat_replacement_backward droppedLit shorterClause rest)

theorem ay_viv_rup_replacement_equisat
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRupWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatEquisat
      (AyVivRatOriginal droppedLit shorterClause rest)
      (AyVivRatReplacement shorterClause rest) := by
  intro witness
  exact ay_viv_rat_replacement_equisat droppedLit shorterClause rest
    (ay_viv_rup_witness_to_rat_witness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause
      witness)

theorem ay_viv_rat_add_candidate
    (currentFormula : Prop) (candidateClause : Prop) :
    AyVivRatWitness currentFormula candidateClause ->
    currentFormula ->
    AyVivRatAddedCandidate currentFormula candidateClause := by
  intro witness
  intro current
  exact ay_viv_rat_conj_intro currentFormula candidateClause
    current
    (witness current)

theorem ay_viv_rat_delete_original_after_add
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatAddedCandidate
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatReplacement shorterClause rest := by
  intro added
  exact ay_viv_rat_conj_intro shorterClause rest
    (ay_viv_rat_conj_right
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause
      added)
    (ay_viv_rat_original_rest droppedLit shorterClause rest
      (ay_viv_rat_conj_left
        (AyVivRatOriginal droppedLit shorterClause rest)
        shorterClause
        added))

theorem ay_viv_rat_add_delete_handoff_forward
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatOriginal droppedLit shorterClause rest ->
    AyVivRatReplacement shorterClause rest := by
  intro witness
  intro original
  exact ay_viv_rat_delete_original_after_add droppedLit shorterClause rest
    (ay_viv_rat_add_candidate
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause
      witness
      original)

theorem ay_viv_rat_add_delete_handoff_equisat
    (droppedLit : Prop) (shorterClause : Prop) (rest : Prop) :
    AyVivRatWitness
      (AyVivRatOriginal droppedLit shorterClause rest)
      shorterClause ->
    AyVivRatEquisat
      (AyVivRatOriginal droppedLit shorterClause rest)
      (AyVivRatReplacement shorterClause rest) := by
  intro witness
  exact ay_viv_rat_conj_intro
    (AyVivRatOriginal droppedLit shorterClause rest ->
      AyVivRatReplacement shorterClause rest)
    (AyVivRatReplacement shorterClause rest ->
      AyVivRatOriginal droppedLit shorterClause rest)
    (ay_viv_rat_add_delete_handoff_forward droppedLit shorterClause rest witness)
    (ay_viv_rat_replacement_backward droppedLit shorterClause rest)

