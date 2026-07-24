-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cached accepted preprocessing schedules for SAT-COMP certificates. The
-- propositions stand for schedule keys, CNF guards, compressed artifacts,
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

def AyScheduleKeyMatch (cachedKey : Prop) (currentKey : Prop) :=
  AyConj (cachedKey -> currentKey) (currentKey -> cachedKey)

def AyCnfGuard (cachedCnf : Prop) (currentCnf : Prop) :=
  AyEquisat cachedCnf currentCnf

def AyCanonicalArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AyCachedSchedule
    (cachedKey : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :=
  AyConj cachedKey (AyCanonicalArtifact cachedCnf visibleCnf)

def AyAcceptedReuse
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyCachedSchedule cachedKey cachedCnf visibleCnf)
    (AyConj
      (AyScheduleKeyMatch cachedKey currentKey)
      (AyCnfGuard cachedCnf currentCnf))

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (currentCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyCacheContract
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AyPublicOutcome
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

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

theorem ay_equisat_symm
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    AyEquisat after before := by
  intro eq
  exact ay_equisat_intro after before
    (ay_equisat_backward before after eq)
    (ay_equisat_forward before after eq)

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

theorem ay_key_match_cached_to_current
    (cachedKey : Prop) (currentKey : Prop) :
    AyScheduleKeyMatch cachedKey currentKey ->
    cachedKey ->
    currentKey := by
  intro hmatch
  intro hcached
  exact ay_conj_left
    (cachedKey -> currentKey)
    (currentKey -> cachedKey)
    hmatch
    hcached

theorem ay_key_match_current_to_cached
    (cachedKey : Prop) (currentKey : Prop) :
    AyScheduleKeyMatch cachedKey currentKey ->
    currentKey ->
    cachedKey := by
  intro hmatch
  intro hcurrent
  exact ay_conj_right
    (cachedKey -> currentKey)
    (currentKey -> cachedKey)
    hmatch
    hcurrent

theorem ay_cached_schedule_key
    (cachedKey : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCachedSchedule cachedKey cachedCnf visibleCnf ->
    cachedKey := by
  intro cached
  exact ay_conj_left cachedKey
    (AyCanonicalArtifact cachedCnf visibleCnf)
    cached

theorem ay_cached_schedule_artifact
    (cachedKey : Prop) (cachedCnf : Prop) (visibleCnf : Prop) :
    AyCachedSchedule cachedKey cachedCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro cached
  exact ay_conj_right cachedKey
    (AyCanonicalArtifact cachedCnf visibleCnf)
    cached

theorem ay_reuse_cached_schedule
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyCachedSchedule cachedKey cachedCnf visibleCnf := by
  intro reuse
  exact ay_conj_left
    (AyCachedSchedule cachedKey cachedCnf visibleCnf)
    (AyConj
      (AyScheduleKeyMatch cachedKey currentKey)
      (AyCnfGuard cachedCnf currentCnf))
    reuse

theorem ay_reuse_key_match
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyScheduleKeyMatch cachedKey currentKey := by
  intro reuse
  exact ay_conj_left
    (AyScheduleKeyMatch cachedKey currentKey)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCachedSchedule cachedKey cachedCnf visibleCnf)
      (AyConj
        (AyScheduleKeyMatch cachedKey currentKey)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_cnf_guard
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyCnfGuard cachedCnf currentCnf := by
  intro reuse
  exact ay_conj_right
    (AyScheduleKeyMatch cachedKey currentKey)
    (AyCnfGuard cachedCnf currentCnf)
    (ay_conj_right
      (AyCachedSchedule cachedKey cachedCnf visibleCnf)
      (AyConj
        (AyScheduleKeyMatch cachedKey currentKey)
        (AyCnfGuard cachedCnf currentCnf))
      reuse)

theorem ay_reuse_current_key
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    currentKey := by
  intro reuse
  exact ay_key_match_cached_to_current cachedKey currentKey
    (ay_reuse_key_match cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)
    (ay_cached_schedule_key cachedKey cachedCnf visibleCnf
      (ay_reuse_cached_schedule cachedKey currentKey cachedCnf currentCnf
        visibleCnf reuse))

theorem ay_reuse_cached_artifact
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact cachedCnf visibleCnf := by
  intro reuse
  exact ay_cached_schedule_artifact cachedKey cachedCnf visibleCnf
    (ay_reuse_cached_schedule cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_reuse_current_canonical
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro reuse
  exact ay_equisat_trans currentCnf cachedCnf visibleCnf
    (ay_equisat_symm cachedCnf currentCnf
      (ay_reuse_cnf_guard cachedKey currentKey cachedCnf currentCnf
        visibleCnf reuse))
    (ay_reuse_cached_artifact cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_reuse_forward_map
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    currentCnf ->
    visibleCnf := by
  intro reuse
  exact ay_equisat_forward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_reuse_backward_map
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    visibleCnf ->
    currentCnf := by
  intro reuse
  exact ay_equisat_backward currentCnf visibleCnf
    (ay_reuse_current_canonical cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)

theorem ay_reuse_visible_sat_pullback
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro reuse
  intro pullback
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_reuse_backward_map cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_reuse_unsat_pushback
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro reuse
  intro replay
  intro hcertificate
  intro hcurrent
  exact replay
    (ay_reuse_forward_map cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse hcurrent)
    hcertificate

theorem ay_reuse_unsat_pushback_artifact
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback currentCnf visibleCnf certificate conflict := by
  intro reuse
  intro replay
  exact ay_conj_intro
    (currentCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_reuse_forward_map cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)
    replay

theorem ay_cache_contract
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro reuse
  intro pullback
  intro replay
  exact ay_conj_intro
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    (ay_reuse_current_canonical cachedKey currentKey cachedCnf currentCnf
      visibleCnf reuse)
    (ay_conj_intro
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict)
      pullback
      replay)

theorem ay_contract_canonical
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyCanonicalArtifact currentCnf visibleCnf := by
  intro contract
  exact ay_conj_left
    (AyCanonicalArtifact currentCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    contract

theorem ay_contract_pullback
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySatPullback visibleModel originalModel := by
  intro contract
  exact ay_conj_left
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact currentCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_replay
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro contract
  exact ay_conj_right
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact currentCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_contract_sat_obligation
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySat currentCnf originalModel := by
  intro contract
  intro sat
  exact ay_conj_intro currentCnf originalModel
    (ay_equisat_backward currentCnf visibleCnf
      (ay_contract_canonical
        currentCnf visibleCnf visibleModel originalModel
        certificate conflict contract)
      (ay_sat_cnf visibleCnf visibleModel sat))
    (ay_contract_pullback
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract
      (ay_sat_model visibleCnf visibleModel sat))

theorem ay_contract_unsat_obligation
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    certificate ->
    currentCnf ->
    conflict := by
  intro contract
  intro hcertificate
  intro hcurrent
  exact ay_contract_replay
    currentCnf visibleCnf visibleModel originalModel
    certificate conflict contract
    (ay_equisat_forward currentCnf visibleCnf
      (ay_contract_canonical
        currentCnf visibleCnf visibleModel originalModel
        certificate conflict contract)
      hcurrent)
    hcertificate

theorem ay_public_outcome_sat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySat currentCnf originalModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_public_outcome_unsat
    (currentCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    (certificate -> currentCnf -> conflict) ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySat currentCnf originalModel)
    (certificate -> currentCnf -> conflict)

theorem ay_reuse_sat_public_sound
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro pullback
  intro sat
  exact ay_public_outcome_sat
    currentCnf originalModel certificate conflict
    (ay_reuse_visible_sat_pullback
      cachedKey currentKey cachedCnf currentCnf visibleCnf
      visibleModel originalModel reuse pullback sat)

theorem ay_reuse_unsat_public_sound
    (cachedKey : Prop) (currentKey : Prop)
    (cachedCnf : Prop) (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedReuse cachedKey currentKey cachedCnf currentCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro reuse
  intro replay
  exact ay_public_outcome_unsat
    currentCnf originalModel certificate conflict
    (ay_reuse_unsat_pushback
      cachedKey currentKey cachedCnf currentCnf visibleCnf
      certificate conflict reuse replay)

theorem ay_contract_sat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro contract
  intro sat
  exact ay_public_outcome_sat
    currentCnf originalModel certificate conflict
    (ay_contract_sat_obligation
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract sat)

theorem ay_contract_unsat_public_sound
    (currentCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCacheContract
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyPublicOutcome currentCnf originalModel certificate conflict := by
  intro contract
  exact ay_public_outcome_unsat
    currentCnf originalModel certificate conflict
    (ay_contract_unsat_obligation
      currentCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
