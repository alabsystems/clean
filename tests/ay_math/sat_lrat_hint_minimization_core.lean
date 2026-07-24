-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for LRAT hint minimization.
-- A proof step witness is an implication from supporting hints to the derived
-- clause. If a hint is redundant, removing it preserves the witness.

def AyLratHintConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLratHintEquiv (before : Prop) (after : Prop) :=
  AyLratHintConj (before -> after) (after -> before)

def AyLratHintStep (hints : Prop) (derived : Prop) :=
  hints -> derived

def AyLratRedundantHint (keptHints : Prop) (redundantHint : Prop) :=
  keptHints -> redundantHint

def AyLratWithRedundantHint
    (keptHints : Prop) (redundantHint : Prop) :=
  AyLratHintConj keptHints redundantHint

def AyLratWithTwoRedundantHints
    (keptHints : Prop) (redundantOne : Prop) (redundantTwo : Prop) :=
  AyLratHintConj
    (AyLratWithRedundantHint keptHints redundantOne)
    redundantTwo

theorem ay_lrat_hint_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLratHintConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_lrat_hint_conj_left
    (left : Prop) (right : Prop) :
    AyLratHintConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_lrat_hint_conj_right
    (left : Prop) (right : Prop) :
    AyLratHintConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_lrat_hint_remove_projection
    (keptHints : Prop) (redundantHint : Prop) :
    AyLratWithRedundantHint keptHints redundantHint -> keptHints := by
  intro fullHints
  exact ay_lrat_hint_conj_left keptHints redundantHint fullHints

theorem ay_lrat_hint_remove_reconstruct
    (keptHints : Prop) (redundantHint : Prop) :
    AyLratRedundantHint keptHints redundantHint ->
    keptHints ->
    AyLratWithRedundantHint keptHints redundantHint := by
  intro redundancy
  intro kept
  exact ay_lrat_hint_conj_intro keptHints redundantHint
    kept
    (redundancy kept)

theorem ay_lrat_hint_remove_equiv
    (keptHints : Prop) (redundantHint : Prop) :
    AyLratRedundantHint keptHints redundantHint ->
    AyLratHintEquiv
      (AyLratWithRedundantHint keptHints redundantHint)
      keptHints := by
  intro redundancy
  exact ay_lrat_hint_conj_intro
    (AyLratWithRedundantHint keptHints redundantHint -> keptHints)
    (keptHints -> AyLratWithRedundantHint keptHints redundantHint)
    (ay_lrat_hint_remove_projection keptHints redundantHint)
    (ay_lrat_hint_remove_reconstruct keptHints redundantHint redundancy)

theorem ay_lrat_hint_minimize_step
    (keptHints : Prop) (redundantHint : Prop) (derived : Prop) :
    AyLratRedundantHint keptHints redundantHint ->
    AyLratHintStep
      (AyLratWithRedundantHint keptHints redundantHint)
      derived ->
    AyLratHintStep keptHints derived := by
  intro redundancy
  intro originalStep
  intro kept
  exact originalStep
    (ay_lrat_hint_remove_reconstruct keptHints redundantHint redundancy kept)

theorem ay_lrat_hint_minimize_step_at_hints
    (keptHints : Prop) (redundantHint : Prop) (derived : Prop) :
    AyLratRedundantHint keptHints redundantHint ->
    AyLratHintStep
      (AyLratWithRedundantHint keptHints redundantHint)
      derived ->
    keptHints ->
    derived := by
  intro redundancy
  intro originalStep
  exact ay_lrat_hint_minimize_step
    keptHints redundantHint derived redundancy originalStep

theorem ay_lrat_two_hint_projection
    (keptHints : Prop) (redundantOne : Prop) (redundantTwo : Prop) :
    AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo ->
    keptHints := by
  intro fullHints
  exact ay_lrat_hint_conj_left keptHints redundantOne
    (ay_lrat_hint_conj_left
      (AyLratWithRedundantHint keptHints redundantOne)
      redundantTwo
      fullHints)

theorem ay_lrat_two_hint_reconstruct
    (keptHints : Prop) (redundantOne : Prop) (redundantTwo : Prop) :
    AyLratRedundantHint keptHints redundantOne ->
    AyLratRedundantHint keptHints redundantTwo ->
    keptHints ->
    AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo := by
  intro redundancyOne
  intro redundancyTwo
  intro kept
  exact ay_lrat_hint_conj_intro
    (AyLratWithRedundantHint keptHints redundantOne)
    redundantTwo
    (ay_lrat_hint_remove_reconstruct
      keptHints redundantOne redundancyOne kept)
    (redundancyTwo kept)

theorem ay_lrat_two_hint_remove_equiv
    (keptHints : Prop) (redundantOne : Prop) (redundantTwo : Prop) :
    AyLratRedundantHint keptHints redundantOne ->
    AyLratRedundantHint keptHints redundantTwo ->
    AyLratHintEquiv
      (AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo)
      keptHints := by
  intro redundancyOne
  intro redundancyTwo
  exact ay_lrat_hint_conj_intro
    (AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo ->
      keptHints)
    (keptHints ->
      AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo)
    (ay_lrat_two_hint_projection keptHints redundantOne redundantTwo)
    (ay_lrat_two_hint_reconstruct
      keptHints redundantOne redundantTwo redundancyOne redundancyTwo)

theorem ay_lrat_two_hint_minimize_step
    (keptHints : Prop)
    (redundantOne : Prop)
    (redundantTwo : Prop)
    (derived : Prop) :
    AyLratRedundantHint keptHints redundantOne ->
    AyLratRedundantHint keptHints redundantTwo ->
    AyLratHintStep
      (AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo)
      derived ->
    AyLratHintStep keptHints derived := by
  intro redundancyOne
  intro redundancyTwo
  intro originalStep
  intro kept
  exact originalStep
    (ay_lrat_two_hint_reconstruct
      keptHints redundantOne redundantTwo redundancyOne redundancyTwo kept)

theorem ay_lrat_hint_remove_then_remove
    (keptHints : Prop)
    (redundantOne : Prop)
    (redundantTwo : Prop)
    (derived : Prop) :
    AyLratRedundantHint keptHints redundantOne ->
    AyLratRedundantHint keptHints redundantTwo ->
    AyLratHintStep
      (AyLratWithTwoRedundantHints keptHints redundantOne redundantTwo)
      derived ->
    keptHints ->
    derived := by
  intro redundancyOne
  intro redundancyTwo
  intro originalStep
  exact ay_lrat_two_hint_minimize_step
    keptHints redundantOne redundantTwo derived
    redundancyOne
    redundancyTwo
    originalStep

