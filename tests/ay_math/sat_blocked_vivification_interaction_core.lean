-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained blocked-clause deletion plus vivification interaction kernels.
-- Propositions stand for satisfiable formula fragments; Church encodings keep
-- the package independent of fragile imports.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyBlockedOriginal (blockedClause : Prop) (residual : Prop) :=
  AyConj blockedClause residual

def AyBlockedReconstruction (residual : Prop) (blockedClause : Prop) :=
  residual -> blockedClause

def AyVivificationOriginal (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyConj (AyDisj lit shorter) rest

def AyVivificationPruned (shorter : Prop) (rest : Prop) :=
  AyConj shorter rest

def AyVivificationSideCondition (lit : Prop) (shorter : Prop) (rest : Prop) :=
  lit -> rest -> shorter

def AyBlockedVivificationOriginal
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :=
  AyBlockedOriginal blockedClause
    (AyVivificationOriginal lit shorter rest)

def AyBlockedVivificationAfterViv
    (blockedClause : Prop) (shorter : Prop) (rest : Prop) :=
  AyBlockedOriginal blockedClause
    (AyVivificationPruned shorter rest)

def AyBlockedVivificationReduced
    (shorter : Prop) (rest : Prop) :=
  AyVivificationPruned shorter rest

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

theorem ay_equisat_forward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    original -> transformed := by
  intro equisat
  exact equisat (original -> transformed)
    (fun forward _backward => forward)

theorem ay_equisat_backward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    transformed -> original := by
  intro equisat
  exact equisat (transformed -> original)
    (fun _forward backward => backward)

theorem ay_equisat_trans
    (a : Prop) (b : Prop) (c : Prop) :
    AyEquisat a b ->
    AyEquisat b c ->
    AyEquisat a c := by
  intro ab
  intro bc
  exact ay_equisat_intro a c
    (fun ha =>
      ay_equisat_forward b c bc
        (ay_equisat_forward a b ab ha))
    (fun hc =>
      ay_equisat_backward a b ab
        (ay_equisat_backward b c bc hc))

theorem ay_blocked_delete_projection
    (blockedClause : Prop) (residual : Prop) :
    AyBlockedOriginal blockedClause residual ->
    residual := by
  intro original
  exact original residual
    (fun _hblocked hresidual => hresidual)

theorem ay_blocked_delete_reconstruction
    (blockedClause : Prop) (residual : Prop) :
    AyBlockedReconstruction residual blockedClause ->
    residual ->
    AyBlockedOriginal blockedClause residual := by
  intro reconstruct
  intro hresidual
  exact ay_conj_intro blockedClause residual
    (reconstruct hresidual)
    hresidual

theorem ay_blocked_delete_equisat
    (blockedClause : Prop) (residual : Prop) :
    AyBlockedReconstruction residual blockedClause ->
    AyEquisat
      (AyBlockedOriginal blockedClause residual)
      residual := by
  intro reconstruct
  exact ay_equisat_intro
    (AyBlockedOriginal blockedClause residual)
    residual
    (ay_blocked_delete_projection blockedClause residual)
    (ay_blocked_delete_reconstruction blockedClause residual reconstruct)

theorem ay_vivification_strengthen_forward
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

theorem ay_vivification_strengthen_backward
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

theorem ay_vivification_strengthening_equisat
    (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyVivificationOriginal lit shorter rest)
      (AyVivificationPruned shorter rest) := by
  intro side
  exact ay_equisat_intro
    (AyVivificationOriginal lit shorter rest)
    (AyVivificationPruned shorter rest)
    (ay_vivification_strengthen_forward lit shorter rest side)
    (ay_vivification_strengthen_backward lit shorter rest)

theorem ay_blocked_then_vivification_forward
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyBlockedVivificationOriginal blockedClause lit shorter rest ->
    AyBlockedVivificationReduced shorter rest := by
  intro side
  intro original
  exact ay_vivification_strengthen_forward lit shorter rest side
    (ay_blocked_delete_projection
      blockedClause
      (AyVivificationOriginal lit shorter rest)
      original)

theorem ay_blocked_then_vivification_backward
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyBlockedReconstruction
      (AyVivificationOriginal lit shorter rest)
      blockedClause ->
    AyBlockedVivificationReduced shorter rest ->
    AyBlockedVivificationOriginal blockedClause lit shorter rest := by
  intro reconstruct
  intro reduced
  exact ay_blocked_delete_reconstruction
    blockedClause
    (AyVivificationOriginal lit shorter rest)
    reconstruct
    (ay_vivification_strengthen_backward lit shorter rest reduced)

theorem ay_blocked_then_vivification_equisat
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyBlockedReconstruction
      (AyVivificationOriginal lit shorter rest)
      blockedClause ->
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyBlockedVivificationOriginal blockedClause lit shorter rest)
      (AyBlockedVivificationReduced shorter rest) := by
  intro reconstruct
  intro side
  exact ay_equisat_intro
    (AyBlockedVivificationOriginal blockedClause lit shorter rest)
    (AyBlockedVivificationReduced shorter rest)
    (ay_blocked_then_vivification_forward
      blockedClause lit shorter rest side)
    (ay_blocked_then_vivification_backward
      blockedClause lit shorter rest reconstruct)

theorem ay_vivification_lifts_under_blocked_clause_forward
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyBlockedVivificationOriginal blockedClause lit shorter rest ->
    AyBlockedVivificationAfterViv blockedClause shorter rest := by
  intro side
  intro original
  exact original (AyBlockedVivificationAfterViv blockedClause shorter rest)
    (fun hblocked viv_original =>
      ay_conj_intro blockedClause (AyVivificationPruned shorter rest)
        hblocked
        (ay_vivification_strengthen_forward
          lit shorter rest side viv_original))

theorem ay_vivification_lifts_under_blocked_clause_backward
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyBlockedVivificationAfterViv blockedClause shorter rest ->
    AyBlockedVivificationOriginal blockedClause lit shorter rest := by
  intro afterViv
  exact afterViv (AyBlockedVivificationOriginal blockedClause lit shorter rest)
    (fun hblocked pruned =>
      ay_conj_intro blockedClause
        (AyVivificationOriginal lit shorter rest)
        hblocked
        (ay_vivification_strengthen_backward
          lit shorter rest pruned))

theorem ay_vivification_lifts_under_blocked_clause_equisat
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyBlockedVivificationOriginal blockedClause lit shorter rest)
      (AyBlockedVivificationAfterViv blockedClause shorter rest) := by
  intro side
  exact ay_equisat_intro
    (AyBlockedVivificationOriginal blockedClause lit shorter rest)
    (AyBlockedVivificationAfterViv blockedClause shorter rest)
    (ay_vivification_lifts_under_blocked_clause_forward
      blockedClause lit shorter rest side)
    (ay_vivification_lifts_under_blocked_clause_backward
      blockedClause lit shorter rest)

theorem ay_vivification_then_blocked_equisat
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyBlockedReconstruction
      (AyVivificationPruned shorter rest)
      blockedClause ->
    AyVivificationSideCondition lit shorter rest ->
    AyEquisat
      (AyBlockedVivificationOriginal blockedClause lit shorter rest)
      (AyBlockedVivificationReduced shorter rest) := by
  intro reconstruct
  intro side
  exact ay_equisat_trans
    (AyBlockedVivificationOriginal blockedClause lit shorter rest)
    (AyBlockedVivificationAfterViv blockedClause shorter rest)
    (AyBlockedVivificationReduced shorter rest)
    (ay_vivification_lifts_under_blocked_clause_equisat
      blockedClause lit shorter rest side)
    (ay_blocked_delete_equisat
      blockedClause
      (AyVivificationPruned shorter rest)
      reconstruct)

theorem ay_blocked_vivification_orders_transport
    (blockedClause : Prop) (lit : Prop) (shorter : Prop) (rest : Prop) :
    AyBlockedReconstruction
      (AyVivificationOriginal lit shorter rest)
      blockedClause ->
    AyBlockedReconstruction
      (AyVivificationPruned shorter rest)
      blockedClause ->
    AyVivificationSideCondition lit shorter rest ->
    AyConj
      (AyEquisat
        (AyBlockedVivificationOriginal blockedClause lit shorter rest)
        (AyBlockedVivificationReduced shorter rest))
      (AyEquisat
        (AyBlockedVivificationOriginal blockedClause lit shorter rest)
        (AyBlockedVivificationReduced shorter rest)) := by
  intro reconstructBefore
  intro reconstructAfter
  intro side
  exact ay_conj_intro
    (AyEquisat
      (AyBlockedVivificationOriginal blockedClause lit shorter rest)
      (AyBlockedVivificationReduced shorter rest))
    (AyEquisat
      (AyBlockedVivificationOriginal blockedClause lit shorter rest)
      (AyBlockedVivificationReduced shorter rest))
    (ay_blocked_then_vivification_equisat
      blockedClause lit shorter rest reconstructBefore side)
    (ay_vivification_then_blocked_equisat
      blockedClause lit shorter rest reconstructAfter side)
