-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for pure-literal/autarky-style SAT simplification.
-- We mirror the Church-encoded style from sat_comp_transform_core.lean so this
-- file stays in the clean checker fragment that handles variable propositions.

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyAutarkyOriginal
    (removedClauses : Prop)
    (residualFormula : Prop) :=
  AyConj removedClauses residualFormula

def AyAutarkyReduced
    (residualFormula : Prop) :=
  residualFormula

def AyAutarkyExtension
    (residualFormula : Prop)
    (removedClauses : Prop) :=
  residualFormula -> removedClauses

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_autarky_delete_forward
    (removedClauses : Prop)
    (residualFormula : Prop) :
    AyAutarkyOriginal removedClauses residualFormula ->
    AyAutarkyReduced residualFormula := by
  intro original
  exact original residualFormula
    (fun _removedSat residualSat => residualSat)

theorem ay_autarky_extension_builds_original
    (removedClauses : Prop)
    (residualFormula : Prop) :
    AyAutarkyExtension residualFormula removedClauses ->
    AyAutarkyReduced residualFormula ->
    AyAutarkyOriginal removedClauses residualFormula := by
  intro extension
  intro residualSat
  exact ay_conj_intro removedClauses residualFormula
    (extension residualSat)
    residualSat

theorem ay_autarky_delete_equisat
    (removedClauses : Prop)
    (residualFormula : Prop) :
    AyAutarkyExtension residualFormula removedClauses ->
    AyEquisat
      (AyAutarkyOriginal removedClauses residualFormula)
      (AyAutarkyReduced residualFormula) := by
  intro extension
  exact ay_conj_intro
    (AyAutarkyOriginal removedClauses residualFormula ->
      AyAutarkyReduced residualFormula)
    (AyAutarkyReduced residualFormula ->
      AyAutarkyOriginal removedClauses residualFormula)
    (ay_autarky_delete_forward removedClauses residualFormula)
    (ay_autarky_extension_builds_original
      removedClauses residualFormula extension)

theorem ay_pure_literal_delete_equisat
    (pureSatisfiedClauses : Prop)
    (residualFormula : Prop) :
    (residualFormula -> pureSatisfiedClauses) ->
    AyEquisat
      (AyAutarkyOriginal pureSatisfiedClauses residualFormula)
      (AyAutarkyReduced residualFormula) := by
  intro pureLiteralExtension
  exact ay_autarky_delete_equisat
    pureSatisfiedClauses residualFormula pureLiteralExtension
