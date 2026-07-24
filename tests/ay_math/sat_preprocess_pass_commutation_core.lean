-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Safe commutation of independent SAT preprocessing passes. The propositions
-- stand for CNF satisfiability states, model payloads, replay certificates,
-- and public SAT/UNSAT outcome contracts.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyTwoPassOrder
    (originalCnf : Prop) (afterFirst : Prop)
    (visibleCnf : Prop) :=
  AyConj
    (AyEquisat originalCnf afterFirst)
    (AyEquisat afterFirst visibleCnf)

def AyIndependentPasses
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :=
  AyConj
    (AyTwoPassOrder originalCnf afterA visibleAB)
    (AyConj
      (AyTwoPassOrder originalCnf afterB visibleBA)
      (AyEquisat visibleAB visibleBA))

def AyCanonicalArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyPublicOutcome
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

theorem ay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_conj_left (before -> after) (after -> before) eq

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_conj_right (before -> after) (after -> before) eq

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_conj_left cnf model sat

theorem ay_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_conj_right cnf model sat

theorem ay_order_first_pass
    (originalCnf : Prop) (afterFirst : Prop)
    (visibleCnf : Prop) :
    AyTwoPassOrder originalCnf afterFirst visibleCnf ->
    AyEquisat originalCnf afterFirst := by
  intro order
  exact ay_conj_left
    (AyEquisat originalCnf afterFirst)
    (AyEquisat afterFirst visibleCnf)
    order

theorem ay_order_second_pass
    (originalCnf : Prop) (afterFirst : Prop)
    (visibleCnf : Prop) :
    AyTwoPassOrder originalCnf afterFirst visibleCnf ->
    AyEquisat afterFirst visibleCnf := by
  intro order
  exact ay_conj_right
    (AyEquisat originalCnf afterFirst)
    (AyEquisat afterFirst visibleCnf)
    order

theorem ay_order_canonical
    (originalCnf : Prop) (afterFirst : Prop)
    (visibleCnf : Prop) :
    AyTwoPassOrder originalCnf afterFirst visibleCnf ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  intro order
  exact ay_equisat_trans originalCnf afterFirst visibleCnf
    (ay_order_first_pass originalCnf afterFirst visibleCnf order)
    (ay_order_second_pass originalCnf afterFirst visibleCnf order)

theorem ay_independent_order_ab
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyTwoPassOrder originalCnf afterA visibleAB := by
  intro independent
  exact ay_conj_left
    (AyTwoPassOrder originalCnf afterA visibleAB)
    (AyConj
      (AyTwoPassOrder originalCnf afterB visibleBA)
      (AyEquisat visibleAB visibleBA))
    independent

theorem ay_independent_order_ba
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyTwoPassOrder originalCnf afterB visibleBA := by
  intro independent
  exact ay_conj_left
    (AyTwoPassOrder originalCnf afterB visibleBA)
    (AyEquisat visibleAB visibleBA)
    (ay_conj_right
      (AyTwoPassOrder originalCnf afterA visibleAB)
      (AyConj
        (AyTwoPassOrder originalCnf afterB visibleBA)
        (AyEquisat visibleAB visibleBA))
      independent)

theorem ay_independent_visible_commutes
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyEquisat visibleAB visibleBA := by
  intro independent
  exact ay_conj_right
    (AyTwoPassOrder originalCnf afterB visibleBA)
    (AyEquisat visibleAB visibleBA)
    (ay_conj_right
      (AyTwoPassOrder originalCnf afterA visibleAB)
      (AyConj
        (AyTwoPassOrder originalCnf afterB visibleBA)
        (AyEquisat visibleAB visibleBA))
      independent)

theorem ay_independent_ab_canonical
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyCanonicalArtifact originalCnf visibleAB := by
  intro independent
  exact ay_order_canonical originalCnf afterA visibleAB
    (ay_independent_order_ab
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_independent_ba_canonical
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyCanonicalArtifact originalCnf visibleBA := by
  intro independent
  exact ay_order_canonical originalCnf afterB visibleBA
    (ay_independent_order_ba
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_ab_canonical_to_ba_canonical
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyCanonicalArtifact originalCnf visibleAB ->
    AyCanonicalArtifact originalCnf visibleBA := by
  intro independent
  intro canonicalAB
  exact ay_equisat_trans originalCnf visibleAB visibleBA
    canonicalAB
    (ay_independent_visible_commutes
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_ba_canonical_to_ab_canonical
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyCanonicalArtifact originalCnf visibleBA ->
    AyCanonicalArtifact originalCnf visibleAB := by
  intro independent
  intro canonicalBA
  exact ay_equisat_trans originalCnf visibleBA visibleAB
    canonicalBA
    (ay_equisat_intro visibleBA visibleAB
      (ay_equisat_backward visibleAB visibleBA
        (ay_independent_visible_commutes
          originalCnf afterA afterB visibleAB visibleBA independent))
      (ay_equisat_forward visibleAB visibleBA
        (ay_independent_visible_commutes
          originalCnf afterA afterB visibleAB visibleBA independent)))

theorem ay_canonical_forward
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  exact ay_equisat_forward originalCnf visibleCnf

theorem ay_canonical_backward
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  exact ay_equisat_backward originalCnf visibleCnf

theorem ay_commute_visible_sat_ab_to_ba
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (model : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySat visibleAB model ->
    AySat visibleBA model := by
  intro independent
  intro sat
  exact ay_conj_intro visibleBA model
    (ay_equisat_forward visibleAB visibleBA
      (ay_independent_visible_commutes
        originalCnf afterA afterB visibleAB visibleBA independent)
      (ay_sat_cnf visibleAB model sat))
    (ay_sat_model visibleAB model sat)

theorem ay_commute_visible_sat_ba_to_ab
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (model : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySat visibleBA model ->
    AySat visibleAB model := by
  intro independent
  intro sat
  exact ay_conj_intro visibleAB model
    (ay_equisat_backward visibleAB visibleBA
      (ay_independent_visible_commutes
        originalCnf afterA afterB visibleAB visibleBA independent)
      (ay_sat_cnf visibleBA model sat))
    (ay_sat_model visibleBA model sat)

theorem ay_canonical_visible_sat_pullback
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro canonical
  intro pullback
  intro sat
  exact ay_conj_intro originalCnf originalModel
    (ay_canonical_backward originalCnf visibleCnf canonical
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_commuted_ab_sat_pullback
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySatPullback visibleModel originalModel ->
    AySat visibleAB visibleModel ->
    AySat originalCnf originalModel := by
  intro independent
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleAB visibleModel originalModel
    (ay_independent_ab_canonical
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_commuted_ba_sat_pullback
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySatPullback visibleModel originalModel ->
    AySat visibleBA visibleModel ->
    AySat originalCnf originalModel := by
  intro independent
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleBA visibleModel originalModel
    (ay_independent_ba_canonical
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_canonical_unsat_pushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro canonical
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_canonical_forward originalCnf visibleCnf canonical horiginal)
    hcertificate

theorem ay_commuted_ab_unsat_pushback
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleAB certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro independent
  exact ay_canonical_unsat_pushback
    originalCnf visibleAB certificate conflict
    (ay_independent_ab_canonical
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_commuted_ba_unsat_pushback
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleBA certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro independent
  exact ay_canonical_unsat_pushback
    originalCnf visibleBA certificate conflict
    (ay_independent_ba_canonical
      originalCnf afterA afterB visibleAB visibleBA independent)

theorem ay_commute_replay_ab_to_ba
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleBA certificate conflict ->
    AyReplay visibleAB certificate conflict := by
  intro independent
  intro replayBA
  intro hab
  exact replayBA
    (ay_equisat_forward visibleAB visibleBA
      (ay_independent_visible_commutes
        originalCnf afterA afterB visibleAB visibleBA independent)
      hab)

theorem ay_commute_replay_ba_to_ab
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleAB certificate conflict ->
    AyReplay visibleBA certificate conflict := by
  intro independent
  intro replayAB
  intro hba
  exact replayAB
    (ay_equisat_backward visibleAB visibleBA
      (ay_independent_visible_commutes
        originalCnf afterA afterB visibleAB visibleBA independent)
      hba)

theorem ay_commuted_ab_unsat_pushback_artifact
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleAB certificate conflict ->
    AyUnsatPushback originalCnf visibleAB certificate conflict := by
  intro independent
  intro replay
  exact ay_conj_intro
    (originalCnf -> visibleAB)
    (AyReplay visibleAB certificate conflict)
    (ay_canonical_forward originalCnf visibleAB
      (ay_independent_ab_canonical
        originalCnf afterA afterB visibleAB visibleBA independent))
    replay

theorem ay_commuted_ba_unsat_pushback_artifact
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleBA certificate conflict ->
    AyUnsatPushback originalCnf visibleBA certificate conflict := by
  intro independent
  intro replay
  exact ay_conj_intro
    (originalCnf -> visibleBA)
    (AyReplay visibleBA certificate conflict)
    (ay_canonical_forward originalCnf visibleBA
      (ay_independent_ba_canonical
        originalCnf afterA afterB visibleAB visibleBA independent))
    replay

theorem ay_public_outcome_sat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySat originalCnf originalModel ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

theorem ay_public_outcome_unsat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    (certificate -> originalCnf -> conflict) ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

theorem ay_commuted_ab_sat_public_sound
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySatPullback visibleModel originalModel ->
    AySat visibleAB visibleModel ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro independent
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    originalCnf originalModel certificate conflict
    (ay_commuted_ab_sat_pullback
      originalCnf afterA afterB visibleAB visibleBA
      visibleModel originalModel independent pullback sat)

theorem ay_commuted_ba_sat_public_sound
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AySatPullback visibleModel originalModel ->
    AySat visibleBA visibleModel ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro independent
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    originalCnf originalModel certificate conflict
    (ay_commuted_ba_sat_pullback
      originalCnf afterA afterB visibleAB visibleBA
      visibleModel originalModel independent pullback sat)

theorem ay_commuted_ab_unsat_public_sound
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleAB certificate conflict ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro independent
  intro replay
  exact ay_public_outcome_unsat
    originalCnf originalModel certificate conflict
    (ay_commuted_ab_unsat_pushback
      originalCnf afterA afterB visibleAB visibleBA
      certificate conflict independent replay)

theorem ay_commuted_ba_unsat_public_sound
    (originalCnf : Prop)
    (afterA : Prop) (afterB : Prop)
    (visibleAB : Prop) (visibleBA : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyIndependentPasses
      originalCnf afterA afterB visibleAB visibleBA ->
    AyReplay visibleBA certificate conflict ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro independent
  intro replay
  exact ay_public_outcome_unsat
    originalCnf originalModel certificate conflict
    (ay_commuted_ba_unsat_pushback
      originalCnf afterA afterB visibleAB visibleBA
      certificate conflict independent replay)
