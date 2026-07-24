-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for equivalence substitution interacting with
-- vivification/strengthening. Formulas are propositions standing for the
-- existence of a satisfying assignment; equisatisfiability is represented by
-- explicit forward and backward model maps.

def AyEqVivConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyEqVivDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEqVivEquiv (left : Prop) (right : Prop) :=
  AyEqVivConj (left -> right) (right -> left)

def AyEqVivEquisat (before : Prop) (after : Prop) :=
  AyEqVivConj (before -> after) (after -> before)

def AyEqVivSatisfiable (formula : Prop) :=
  formula

def AyEqVivOriginalClause
    (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyEqVivConj (AyEqVivDisj lit shorter) rest

def AyEqVivVivifiedClause
    (shorter : Prop) (rest : Prop) :=
  AyEqVivConj shorter rest

def AyEqVivSideCondition
    (lit : Prop) (shorter : Prop) (rest : Prop) :=
  lit -> rest -> shorter

theorem ay_eq_viv_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyEqVivConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_eq_viv_disj_left
    (left : Prop) (right : Prop) :
    left -> AyEqVivDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_eq_viv_disj_right
    (left : Prop) (right : Prop) :
    right -> AyEqVivDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_eq_viv_equiv_forward
    (oldLit : Prop) (newLit : Prop) :
    AyEqVivEquiv oldLit newLit -> oldLit -> newLit := by
  intro litEquiv
  exact litEquiv (oldLit -> newLit)
    (fun forward _backward => forward)

theorem ay_eq_viv_equiv_backward
    (oldLit : Prop) (newLit : Prop) :
    AyEqVivEquiv oldLit newLit -> newLit -> oldLit := by
  intro litEquiv
  exact litEquiv (newLit -> oldLit)
    (fun _forward backward => backward)

theorem ay_eq_viv_substitute_disj_forward
    (oldLit : Prop) (newLit : Prop) (shorter : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivDisj oldLit shorter ->
    AyEqVivDisj newLit shorter := by
  intro litEquiv
  intro clause
  intro result
  intro newCase
  intro shorterCase
  exact clause result
    (fun oldH =>
      newCase (ay_eq_viv_equiv_forward oldLit newLit litEquiv oldH))
    shorterCase

theorem ay_eq_viv_substitute_disj_backward
    (oldLit : Prop) (newLit : Prop) (shorter : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivDisj newLit shorter ->
    AyEqVivDisj oldLit shorter := by
  intro litEquiv
  intro clause
  intro result
  intro oldCase
  intro shorterCase
  exact clause result
    (fun newH =>
      oldCase (ay_eq_viv_equiv_backward oldLit newLit litEquiv newH))
    shorterCase

theorem ay_eq_viv_substitution_forward
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivOriginalClause oldLit shorter rest ->
    AyEqVivOriginalClause newLit shorter rest := by
  intro litEquiv
  intro original
  exact original (AyEqVivOriginalClause newLit shorter rest)
    (fun clause restH =>
      ay_eq_viv_conj_intro
        (AyEqVivDisj newLit shorter)
        rest
        (ay_eq_viv_substitute_disj_forward
          oldLit newLit shorter litEquiv clause)
        restH)

theorem ay_eq_viv_substitution_backward
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivOriginalClause newLit shorter rest ->
    AyEqVivOriginalClause oldLit shorter rest := by
  intro litEquiv
  intro substituted
  exact substituted (AyEqVivOriginalClause oldLit shorter rest)
    (fun clause restH =>
      ay_eq_viv_conj_intro
        (AyEqVivDisj oldLit shorter)
        rest
        (ay_eq_viv_substitute_disj_backward
          oldLit newLit shorter litEquiv clause)
        restH)

theorem ay_eq_viv_substitution_equisat
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivEquisat
      (AyEqVivOriginalClause oldLit shorter rest)
      (AyEqVivOriginalClause newLit shorter rest) :=
  fun litEquiv result keep =>
    keep
      (ay_eq_viv_substitution_forward
        oldLit newLit shorter rest litEquiv)
      (ay_eq_viv_substitution_backward
        oldLit newLit shorter rest litEquiv)

theorem ay_eq_viv_side_condition_lift_forward
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition oldLit shorter rest ->
    AyEqVivSideCondition newLit shorter rest :=
  fun litEquiv oldSide newH restH =>
    oldSide
      (ay_eq_viv_equiv_backward oldLit newLit litEquiv newH)
      restH

theorem ay_eq_viv_side_condition_lift_backward
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition newLit shorter rest ->
    AyEqVivSideCondition oldLit shorter rest :=
  fun litEquiv newSide oldH restH =>
    newSide
      (ay_eq_viv_equiv_forward oldLit newLit litEquiv oldH)
      restH

theorem ay_eq_viv_forward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyEqVivSideCondition lit shorter rest ->
    AyEqVivOriginalClause lit shorter rest ->
    AyEqVivVivifiedClause shorter rest := by
  intro side
  intro original
  exact original (AyEqVivVivifiedClause shorter rest)
    (fun clause restH =>
      clause (AyEqVivVivifiedClause shorter rest)
        (fun litH =>
          ay_eq_viv_conj_intro shorter rest
            (side litH restH)
            restH)
        (fun shorterH =>
          ay_eq_viv_conj_intro shorter rest shorterH restH))

theorem ay_eq_viv_backward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyEqVivVivifiedClause shorter rest ->
    AyEqVivOriginalClause lit shorter rest := by
  intro vivified
  exact vivified (AyEqVivOriginalClause lit shorter rest)
    (fun shorterH restH =>
      ay_eq_viv_conj_intro
        (AyEqVivDisj lit shorter)
        rest
        (ay_eq_viv_disj_right lit shorter shorterH)
        restH)

theorem ay_eq_viv_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyEqVivSideCondition lit shorter rest ->
    AyEqVivEquisat
      (AyEqVivOriginalClause lit shorter rest)
      (AyEqVivVivifiedClause shorter rest) :=
  fun side result keep =>
    keep
      (ay_eq_viv_forward lit shorter rest side)
      (ay_eq_viv_backward lit shorter rest)

theorem ay_eq_viv_substituted_strengthening_forward
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition oldLit shorter rest ->
    AyEqVivOriginalClause oldLit shorter rest ->
    AyEqVivVivifiedClause shorter rest :=
  fun litEquiv oldSide original =>
    ay_eq_viv_forward newLit shorter rest
      (ay_eq_viv_side_condition_lift_forward
        oldLit newLit shorter rest litEquiv oldSide)
      (ay_eq_viv_substitution_forward
        oldLit newLit shorter rest litEquiv original)

theorem ay_eq_viv_substituted_strengthening_backward
    (oldLit : Prop) (shorter : Prop) (rest : Prop) :
    AyEqVivVivifiedClause shorter rest ->
    AyEqVivOriginalClause oldLit shorter rest :=
  fun vivified =>
    ay_eq_viv_backward oldLit shorter rest vivified

theorem ay_eq_viv_substituted_strengthening_equisat
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition oldLit shorter rest ->
    AyEqVivEquisat
      (AyEqVivOriginalClause oldLit shorter rest)
      (AyEqVivVivifiedClause shorter rest) :=
  fun litEquiv oldSide result keep =>
    keep
      (ay_eq_viv_substituted_strengthening_forward
        oldLit newLit shorter rest litEquiv oldSide)
      (ay_eq_viv_substituted_strengthening_backward
        oldLit shorter rest)

theorem ay_eq_viv_equisat_satisfiable_forward
    (before : Prop) (after : Prop) :
    AyEqVivEquisat before after ->
    AyEqVivSatisfiable before ->
    AyEqVivSatisfiable after :=
  fun equisat =>
    equisat (AyEqVivSatisfiable before -> AyEqVivSatisfiable after)
      (fun forward _backward => forward)

theorem ay_eq_viv_equisat_satisfiable_backward
    (before : Prop) (after : Prop) :
    AyEqVivEquisat before after ->
    AyEqVivSatisfiable after ->
    AyEqVivSatisfiable before :=
  fun equisat =>
    equisat (AyEqVivSatisfiable after -> AyEqVivSatisfiable before)
      (fun _forward backward => backward)

theorem ay_eq_viv_substituted_strengthening_preserves_sat
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition oldLit shorter rest ->
    AyEqVivSatisfiable (AyEqVivOriginalClause oldLit shorter rest) ->
    AyEqVivSatisfiable (AyEqVivVivifiedClause shorter rest) :=
  fun litEquiv oldSide satOriginal =>
    ay_eq_viv_equisat_satisfiable_forward
      (AyEqVivOriginalClause oldLit shorter rest)
      (AyEqVivVivifiedClause shorter rest)
      (ay_eq_viv_substituted_strengthening_equisat
        oldLit newLit shorter rest litEquiv oldSide)
      satOriginal

theorem ay_eq_viv_substituted_reconstruction_preserves_sat
    (oldLit : Prop) (newLit : Prop)
    (shorter : Prop) (rest : Prop) :
    AyEqVivEquiv oldLit newLit ->
    AyEqVivSideCondition oldLit shorter rest ->
    AyEqVivSatisfiable (AyEqVivVivifiedClause shorter rest) ->
    AyEqVivSatisfiable (AyEqVivOriginalClause oldLit shorter rest) :=
  fun litEquiv oldSide satVivified =>
    ay_eq_viv_equisat_satisfiable_backward
      (AyEqVivOriginalClause oldLit shorter rest)
      (AyEqVivVivifiedClause shorter rest)
      (ay_eq_viv_substituted_strengthening_equisat
        oldLit newLit shorter rest litEquiv oldSide)
      satVivified
