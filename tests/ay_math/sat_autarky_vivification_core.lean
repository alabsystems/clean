-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for composing autarky deletion with vivification.
-- This file is self-contained and uses the Church-encoded conjunction,
-- disjunction, and equisat pattern used by the SAT-COMP math packages.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyAutarkyOriginal
    (removedBlock : Prop) (residual : Prop) :=
  AyConj removedBlock residual

def AyAutarkyExtension
    (residual : Prop) (removedBlock : Prop) :=
  residual -> removedBlock

def AyVivificationOriginal
    (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyConj (AyDisj lit shorter) rest

def AyVivificationPruned
    (shorter : Prop) (rest : Prop) :=
  AyConj shorter rest

def AyVivificationSideCondition
    (lit : Prop) (shorter : Prop) (rest : Prop) :=
  lit -> rest -> shorter

def AyAutarkyVivificationOriginal
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyAutarkyOriginal removedBlock
    (AyVivificationOriginal lit shorter rest)

def AyAutarkyVivificationReduced
    (shorter : Prop) (rest : Prop) :=
  AyVivificationPruned shorter rest

def AyVisibleWitnesses
    (removedBlock : Prop) (shorter : Prop) (rest : Prop) :=
  AyConj removedBlock (AyConj shorter rest)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyEquisat original transformed := by
  intro forward
  intro backward
  exact ay_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_autarky_delete_forward
    (removedBlock : Prop) (residual : Prop) :
    AyAutarkyOriginal removedBlock residual ->
    residual := by
  intro original
  exact original residual
    (fun _removedSat residualSat => residualSat)

theorem ay_autarky_delete_backward
    (removedBlock : Prop) (residual : Prop) :
    AyAutarkyExtension residual removedBlock ->
    residual ->
    AyAutarkyOriginal removedBlock residual := by
  intro extension
  intro residualSat
  exact ay_conj_intro removedBlock residual
    (extension residualSat)
    residualSat

theorem ay_autarky_delete_equisat
    (removedBlock : Prop) (residual : Prop) :
    AyAutarkyExtension residual removedBlock ->
    AyEquisat
      (AyAutarkyOriginal removedBlock residual)
      residual := by
  intro extension
  exact ay_equisat_intro
    (AyAutarkyOriginal removedBlock residual)
    residual
    (ay_autarky_delete_forward removedBlock residual)
    (ay_autarky_delete_backward removedBlock residual extension)

theorem ay_vivification_forward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyVivificationOriginal lit shorter rest ->
    AyVivificationPruned shorter rest := by
  intro side
  intro original
  intro result
  intro build
  exact original result
    (fun clause hrest =>
      clause result
        (fun hlit => build (side hlit hrest) hrest)
        (fun hshorter => build hshorter hrest))

theorem ay_vivification_backward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationPruned shorter rest ->
    AyVivificationOriginal lit shorter rest := by
  intro pruned
  intro result
  intro build
  exact pruned result
    (fun hshorter hrest =>
      build
        (ay_disj_right lit shorter hshorter)
        hrest)

theorem ay_vivification_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyVivificationPruned shorter rest) := by
  intro side
  exact ay_equisat_intro
    (AyVivificationOriginal lit shorter rest)
    (AyVivificationPruned shorter rest)
    (ay_vivification_forward lit shorter rest side)
    (ay_vivification_backward lit shorter rest)

theorem ay_autarky_then_vivification_forward
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyAutarkyVivificationOriginal removedBlock lit shorter rest ->
    AyAutarkyVivificationReduced shorter rest := by
  intro side
  intro original
  exact ay_vivification_forward lit shorter rest side
    (ay_autarky_delete_forward
      removedBlock
      (AyVivificationOriginal lit shorter rest)
      original)

theorem ay_autarky_then_vivification_backward
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyAutarkyExtension
      (AyVivificationOriginal lit shorter rest)
      removedBlock ->
    AyAutarkyVivificationReduced shorter rest ->
    AyAutarkyVivificationOriginal removedBlock lit shorter rest := by
  intro extension
  intro reduced
  exact ay_autarky_delete_backward
    removedBlock
    (AyVivificationOriginal lit shorter rest)
    extension
    (ay_vivification_backward lit shorter rest reduced)

theorem ay_autarky_then_vivification_equisat
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyAutarkyExtension
      (AyVivificationOriginal lit shorter rest)
      removedBlock ->
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyAutarkyVivificationOriginal removedBlock lit shorter rest)
      (AyAutarkyVivificationReduced shorter rest) := by
  intro extension
  intro side
  exact ay_equisat_intro
    (AyAutarkyVivificationOriginal removedBlock lit shorter rest)
    (AyAutarkyVivificationReduced shorter rest)
    (ay_autarky_then_vivification_forward
      removedBlock lit shorter rest side)
    (ay_autarky_then_vivification_backward
      removedBlock lit shorter rest extension)

theorem ay_visible_witnesses_project_removed
    (removedBlock : Prop) (shorter : Prop) (rest : Prop) :
    AyVisibleWitnesses removedBlock shorter rest ->
    removedBlock := by
  intro witnesses
  exact witnesses removedBlock
    (fun hremoved _tail => hremoved)

theorem ay_visible_witnesses_project_pruned
    (removedBlock : Prop) (shorter : Prop) (rest : Prop) :
    AyVisibleWitnesses removedBlock shorter rest ->
    AyVivificationPruned shorter rest := by
  intro witnesses
  exact witnesses (AyVivificationPruned shorter rest)
    (fun _hremoved tail => tail)

theorem ay_visible_witnesses_reconstruct
    (removedBlock : Prop) (shorter : Prop) (rest : Prop) :
    removedBlock ->
    AyVivificationPruned shorter rest ->
    AyVisibleWitnesses removedBlock shorter rest := by
  intro hremoved
  intro pruned
  exact pruned (AyVisibleWitnesses removedBlock shorter rest)
    (fun hshorter hrest =>
      ay_conj_intro removedBlock (AyConj shorter rest)
        hremoved
        (ay_conj_intro shorter rest hshorter hrest))

theorem ay_autarky_vivification_visible_forward
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyAutarkyExtension
      (AyVivificationOriginal lit shorter rest)
      removedBlock ->
    AyVivificationSideCondition lit shorter rest ->
    AyAutarkyVivificationOriginal removedBlock lit shorter rest ->
    AyVisibleWitnesses removedBlock shorter rest := by
  intro extension
  intro side
  intro original
  let reduced :=
    ay_autarky_then_vivification_forward
      removedBlock lit shorter rest side original
  exact ay_visible_witnesses_reconstruct
    removedBlock shorter rest
    (extension
      (ay_autarky_delete_forward
        removedBlock
        (AyVivificationOriginal lit shorter rest)
        original))
    reduced

theorem ay_autarky_vivification_visible_backward
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVisibleWitnesses removedBlock shorter rest ->
    AyAutarkyVivificationOriginal removedBlock lit shorter rest := by
  intro witnesses
  exact ay_conj_intro
    removedBlock
    (AyVivificationOriginal lit shorter rest)
    (ay_visible_witnesses_project_removed
      removedBlock shorter rest witnesses)
    (ay_vivification_backward lit shorter rest
      (ay_visible_witnesses_project_pruned
        removedBlock shorter rest witnesses))

theorem ay_autarky_vivification_visible_equisat
    (removedBlock : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyAutarkyExtension
      (AyVivificationOriginal lit shorter rest)
      removedBlock ->
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyAutarkyVivificationOriginal removedBlock lit shorter rest)
      (AyVisibleWitnesses removedBlock shorter rest) := by
  intro extension
  intro side
  exact ay_equisat_intro
    (AyAutarkyVivificationOriginal removedBlock lit shorter rest)
    (AyVisibleWitnesses removedBlock shorter rest)
    (ay_autarky_vivification_visible_forward
      removedBlock lit shorter rest extension side)
    (ay_autarky_vivification_visible_backward
      removedBlock lit shorter rest)
