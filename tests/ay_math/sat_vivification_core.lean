-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for SAT vivification/asymmetric branch
-- pruning. The transformation replaces a clause `lit OR shorter` by the
-- shorter clause when the failed/asymmetric branch proves that assuming `lit`
-- together with the remaining formula implies `shorter`.

def AyVivDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyVivConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyVivEquisat (original : Prop) (transformed : Prop) :=
  AyVivConj (original -> transformed) (transformed -> original)

def AyVivificationOriginal (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyVivConj (AyVivDisj lit shorter) rest

def AyVivificationPruned (shorter : Prop) (rest : Prop) :=
  AyVivConj shorter rest

def AyVivificationSideCondition (lit : Prop) (shorter : Prop) (rest : Prop) :=
  lit -> rest -> shorter

theorem ay_viv_disj_right
    (p : Prop) (q : Prop) :
    q -> AyVivDisj p q := by
  intro hq
  intro result
  intro _left
  intro right_to_result
  exact right_to_result hq

theorem ay_viv_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyVivConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_viv_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyVivEquisat original transformed := by
  intro forward
  intro backward
  exact ay_viv_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_vivification_forward
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyVivificationOriginal lit shorter rest ->
    AyVivificationPruned shorter rest := by
  intro branch_prunes
  intro original
  intro result
  intro build
  exact original result
    (fun clause hrest =>
      clause result
        (fun hlit => build (branch_prunes hlit hrest) hrest)
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
        (ay_viv_disj_right lit shorter hshorter)
        hrest)

theorem ay_vivification_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyVivEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyVivificationPruned shorter rest) := by
  intro branch_prunes
  exact ay_viv_equisat_intro
    (AyVivificationOriginal lit shorter rest)
    (AyVivificationPruned shorter rest)
    (ay_vivification_forward lit shorter rest branch_prunes)
    (ay_vivification_backward lit shorter rest)

theorem ay_asymmetric_branch_pruning_sound
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    (lit -> rest -> shorter) ->
    AyVivificationOriginal lit shorter rest ->
    AyVivificationPruned shorter rest := by
  intro branch_prunes
  exact ay_vivification_forward lit shorter rest branch_prunes

theorem ay_asymmetric_branch_pruning_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    (lit -> rest -> shorter) ->
    AyVivEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyVivificationPruned shorter rest) := by
  intro branch_prunes
  exact ay_vivification_equisat lit shorter rest branch_prunes
