-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Soundness of heuristic SAT preprocessing schedules. The propositions stand
-- for CNF states, accepted pass artifacts, selected pass order/repetition,
-- model reconstruction payloads, replay certificates, and public outcomes.

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

def AyAcceptedPass (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyScheduleChoice (orderTag : Prop) (repeatTag : Prop) :=
  AyConj orderTag repeatTag

def AyHeuristicSchedule
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :=
  AyConj
    (AyScheduleChoice orderTag repeatTag)
    (AyConj
      (AyAcceptedPass originalCnf step1Cnf)
      (AyConj
        (AyAcceptedPass step1Cnf step2Cnf)
        (AyAcceptedPass step2Cnf visibleCnf)))

def AyCanonicalArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyScheduleContract
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

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

theorem ay_schedule_choice_order
    (orderTag : Prop) (repeatTag : Prop) :
    AyScheduleChoice orderTag repeatTag ->
    orderTag := by
  intro choice
  exact ay_conj_left orderTag repeatTag choice

theorem ay_schedule_choice_repeat
    (orderTag : Prop) (repeatTag : Prop) :
    AyScheduleChoice orderTag repeatTag ->
    repeatTag := by
  intro choice
  exact ay_conj_right orderTag repeatTag choice

theorem ay_schedule_choice
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyScheduleChoice orderTag repeatTag := by
  intro schedule
  exact ay_conj_left
    (AyScheduleChoice orderTag repeatTag)
    (AyConj
      (AyAcceptedPass originalCnf step1Cnf)
      (AyConj
        (AyAcceptedPass step1Cnf step2Cnf)
        (AyAcceptedPass step2Cnf visibleCnf)))
    schedule

theorem ay_schedule_first_pass
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyAcceptedPass originalCnf step1Cnf := by
  intro schedule
  exact ay_conj_left
    (AyAcceptedPass originalCnf step1Cnf)
    (AyConj
      (AyAcceptedPass step1Cnf step2Cnf)
      (AyAcceptedPass step2Cnf visibleCnf))
    (ay_conj_right
      (AyScheduleChoice orderTag repeatTag)
      (AyConj
        (AyAcceptedPass originalCnf step1Cnf)
        (AyConj
          (AyAcceptedPass step1Cnf step2Cnf)
          (AyAcceptedPass step2Cnf visibleCnf)))
      schedule)

theorem ay_schedule_repeat_pass
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyAcceptedPass step1Cnf step2Cnf := by
  intro schedule
  exact ay_conj_left
    (AyAcceptedPass step1Cnf step2Cnf)
    (AyAcceptedPass step2Cnf visibleCnf)
    (ay_conj_right
      (AyAcceptedPass originalCnf step1Cnf)
      (AyConj
        (AyAcceptedPass step1Cnf step2Cnf)
        (AyAcceptedPass step2Cnf visibleCnf))
      (ay_conj_right
        (AyScheduleChoice orderTag repeatTag)
        (AyConj
          (AyAcceptedPass originalCnf step1Cnf)
          (AyConj
            (AyAcceptedPass step1Cnf step2Cnf)
            (AyAcceptedPass step2Cnf visibleCnf)))
        schedule))

theorem ay_schedule_final_pass
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyAcceptedPass step2Cnf visibleCnf := by
  intro schedule
  exact ay_conj_right
    (AyAcceptedPass step1Cnf step2Cnf)
    (AyAcceptedPass step2Cnf visibleCnf)
    (ay_conj_right
      (AyAcceptedPass originalCnf step1Cnf)
      (AyConj
        (AyAcceptedPass step1Cnf step2Cnf)
        (AyAcceptedPass step2Cnf visibleCnf))
      (ay_conj_right
        (AyScheduleChoice orderTag repeatTag)
        (AyConj
          (AyAcceptedPass originalCnf step1Cnf)
          (AyConj
            (AyAcceptedPass step1Cnf step2Cnf)
            (AyAcceptedPass step2Cnf visibleCnf)))
        schedule))

theorem ay_schedule_original_to_step2
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyEquisat originalCnf step2Cnf := by
  intro schedule
  exact ay_equisat_trans originalCnf step1Cnf step2Cnf
    (ay_schedule_first_pass
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)
    (ay_schedule_repeat_pass
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

theorem ay_schedule_canonical_artifact
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  intro schedule
  exact ay_equisat_trans originalCnf step2Cnf visibleCnf
    (ay_schedule_original_to_step2
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)
    (ay_schedule_final_pass
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

theorem ay_schedule_compress_adjacent_first_repeat
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyConj
      (AyEquisat originalCnf step2Cnf)
      (AyEquisat step2Cnf visibleCnf) := by
  intro schedule
  exact ay_conj_intro
    (AyEquisat originalCnf step2Cnf)
    (AyEquisat step2Cnf visibleCnf)
    (ay_schedule_original_to_step2
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)
    (ay_schedule_final_pass
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

theorem ay_schedule_compress_to_canonical
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  exact ay_schedule_canonical_artifact
    originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag

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

theorem ay_schedule_forward_map
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    originalCnf ->
    visibleCnf := by
  intro schedule
  exact ay_canonical_forward originalCnf visibleCnf
    (ay_schedule_canonical_artifact
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

theorem ay_schedule_backward_map
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    visibleCnf ->
    originalCnf := by
  intro schedule
  exact ay_canonical_backward originalCnf visibleCnf
    (ay_schedule_canonical_artifact
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

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

theorem ay_schedule_visible_sat_pullback
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro schedule
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleCnf visibleModel originalModel
    (ay_schedule_canonical_artifact
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

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

theorem ay_schedule_unsat_pushback
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro schedule
  exact ay_canonical_unsat_pushback
    originalCnf visibleCnf certificate conflict
    (ay_schedule_canonical_artifact
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)

theorem ay_schedule_unsat_pushback_artifact
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback originalCnf visibleCnf certificate conflict := by
  intro schedule
  intro replay
  exact ay_conj_intro
    (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_schedule_forward_map
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)
    replay

theorem ay_schedule_contract
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro schedule
  intro pullback
  intro replay
  exact ay_conj_intro
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    (ay_schedule_canonical_artifact
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag schedule)
    (ay_conj_intro
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict)
      pullback
      replay)

theorem ay_contract_canonical
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  intro contract
  exact ay_conj_left
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    contract

theorem ay_contract_pullback
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySatPullback visibleModel originalModel := by
  intro contract
  exact ay_conj_left
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact originalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_replay
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro contract
  exact ay_conj_right
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact originalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_sat_obligation
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro contract
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleCnf visibleModel originalModel
    (ay_contract_canonical
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
    (ay_contract_pullback
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)

theorem ay_contract_unsat_obligation
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro contract
  exact ay_canonical_unsat_pushback
    originalCnf visibleCnf certificate conflict
    (ay_contract_canonical
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
    (ay_contract_replay
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)

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

theorem ay_schedule_sat_public_sound
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro schedule
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    originalCnf originalModel certificate conflict
    (ay_schedule_visible_sat_pullback
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag
      visibleModel originalModel schedule pullback sat)

theorem ay_schedule_unsat_public_sound
    (originalCnf : Prop) (step1Cnf : Prop)
    (step2Cnf : Prop) (visibleCnf : Prop)
    (orderTag : Prop) (repeatTag : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyHeuristicSchedule
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag ->
    AyReplay visibleCnf certificate conflict ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro schedule
  intro replay
  exact ay_public_outcome_unsat
    originalCnf originalModel certificate conflict
    (ay_schedule_unsat_pushback
      originalCnf step1Cnf step2Cnf visibleCnf orderTag repeatTag
      certificate conflict schedule replay)

theorem ay_contract_sat_public_sound
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro contract
  intro sat
  exact ay_public_outcome_sat
    originalCnf originalModel certificate conflict
    (ay_contract_sat_obligation
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract sat)

theorem ay_contract_unsat_public_sound
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyScheduleContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyPublicOutcome originalCnf originalModel certificate conflict := by
  intro contract
  exact ay_public_outcome_unsat
    originalCnf originalModel certificate conflict
    (ay_contract_unsat_obligation
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
