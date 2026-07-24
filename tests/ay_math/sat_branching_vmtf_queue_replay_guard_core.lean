-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded VMTF queue replay guard soundness skeleton for ay SAT solving.
-- Variable-move-to-front queue order may guide branching only when queue
-- order, tie-breaking, bump events, restart epoch, solver build, fallback
-- baseline, and validator gate are replayable for the same variable map.

def ay_bvqr_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bvqr_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bvqr_equisat (before : Prop) (after : Prop) :=
  ay_bvqr_conj (before -> after) (after -> before)

def ay_bvqr_queue_guard
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :=
  ay_bvqr_conj queueOrder
    (ay_bvqr_conj tieBreaking
      (ay_bvqr_conj bumpEvents
        (ay_bvqr_conj variableMap
          (ay_bvqr_conj restartEpoch
            (ay_bvqr_conj solverBuild
              (ay_bvqr_conj fallbackBaseline validatorGate))))))

def ay_bvqr_replay_agreement
    (queueMatch : Prop) (tieBreakMatch : Prop) (bumpMatch : Prop)
    (variableMapMatch : Prop) (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :=
  ay_bvqr_conj queueMatch
    (ay_bvqr_conj tieBreakMatch
      (ay_bvqr_conj bumpMatch
        (ay_bvqr_conj variableMapMatch
          (ay_bvqr_conj epochMatch
            (ay_bvqr_conj buildMatch
              (ay_bvqr_conj fallbackMatch validatorAccepts))))))

def ay_bvqr_accepted_hint
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :=
  ay_bvqr_conj guard (ay_bvqr_conj agreement branchingHint)

def ay_bvqr_outcome (model : Prop) (conflict : Prop) :=
  ay_bvqr_disj model conflict

def ay_bvqr_public_report (outcome : Prop) (formula : Prop) :=
  ay_bvqr_conj outcome formula

def ay_bvqr_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bvqr_conj hintCert public

def ay_bvqr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bvqr_conj fallbackPublic diagnostic

theorem ay_bvqr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bvqr_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bvqr_conj_left
    (left : Prop) (right : Prop) :
    ay_bvqr_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bvqr_conj_right
    (left : Prop) (right : Prop) :
    ay_bvqr_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bvqr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bvqr_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bvqr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bvqr_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bvqr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bvqr_equisat before after :=
  fun forward backward =>
    ay_bvqr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bvqr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bvqr_equisat before after -> before -> after :=
  fun equisat =>
    ay_bvqr_conj_left (before -> after) (after -> before) equisat

theorem ay_bvqr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bvqr_equisat before after -> after -> before :=
  fun equisat =>
    ay_bvqr_conj_right (before -> after) (after -> before) equisat

theorem ay_bvqr_queue_guard_intro
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    queueOrder ->
    tieBreaking ->
    bumpEvents ->
    variableMap ->
    restartEpoch ->
    solverBuild ->
    fallbackBaseline ->
    validatorGate ->
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate :=
  fun queueH tieH bumpH mapH epochH buildH fallbackH validatorH =>
    ay_bvqr_conj_intro queueOrder
      (ay_bvqr_conj tieBreaking
        (ay_bvqr_conj bumpEvents
          (ay_bvqr_conj variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate))))))
      queueH
      (ay_bvqr_conj_intro tieBreaking
        (ay_bvqr_conj bumpEvents
          (ay_bvqr_conj variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate)))))
        tieH
        (ay_bvqr_conj_intro bumpEvents
          (ay_bvqr_conj variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate))))
          bumpH
          (ay_bvqr_conj_intro variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate)))
            mapH
            (ay_bvqr_conj_intro restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate))
              epochH
              (ay_bvqr_conj_intro solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate)
                buildH
                (ay_bvqr_conj_intro fallbackBaseline validatorGate
                  fallbackH validatorH))))))

theorem ay_bvqr_queue_guard_order
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    queueOrder :=
  fun guard =>
    ay_bvqr_conj_left queueOrder
      (ay_bvqr_conj tieBreaking
        (ay_bvqr_conj bumpEvents
          (ay_bvqr_conj variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate))))))
      guard

theorem ay_bvqr_queue_guard_tail
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    ay_bvqr_conj tieBreaking
      (ay_bvqr_conj bumpEvents
        (ay_bvqr_conj variableMap
          (ay_bvqr_conj restartEpoch
            (ay_bvqr_conj solverBuild
              (ay_bvqr_conj fallbackBaseline validatorGate))))) :=
  fun guard =>
    ay_bvqr_conj_right queueOrder
      (ay_bvqr_conj tieBreaking
        (ay_bvqr_conj bumpEvents
          (ay_bvqr_conj variableMap
            (ay_bvqr_conj restartEpoch
              (ay_bvqr_conj solverBuild
                (ay_bvqr_conj fallbackBaseline validatorGate))))))
      guard

theorem ay_bvqr_queue_guard_tie_breaking
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    tieBreaking :=
  fun guard =>
    ay_bvqr_conj_left tieBreaking
      (ay_bvqr_conj bumpEvents
        (ay_bvqr_conj variableMap
          (ay_bvqr_conj restartEpoch
            (ay_bvqr_conj solverBuild
              (ay_bvqr_conj fallbackBaseline validatorGate)))))
      (ay_bvqr_queue_guard_tail queueOrder tieBreaking bumpEvents variableMap
        restartEpoch solverBuild fallbackBaseline validatorGate guard)

theorem ay_bvqr_queue_guard_after_tie
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    ay_bvqr_conj bumpEvents
      (ay_bvqr_conj variableMap
        (ay_bvqr_conj restartEpoch
          (ay_bvqr_conj solverBuild
            (ay_bvqr_conj fallbackBaseline validatorGate)))) :=
  fun guard =>
    ay_bvqr_conj_right tieBreaking
      (ay_bvqr_conj bumpEvents
        (ay_bvqr_conj variableMap
          (ay_bvqr_conj restartEpoch
            (ay_bvqr_conj solverBuild
              (ay_bvqr_conj fallbackBaseline validatorGate)))))
      (ay_bvqr_queue_guard_tail queueOrder tieBreaking bumpEvents variableMap
        restartEpoch solverBuild fallbackBaseline validatorGate guard)

theorem ay_bvqr_queue_guard_bumps
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    bumpEvents :=
  fun guard =>
    ay_bvqr_conj_left bumpEvents
      (ay_bvqr_conj variableMap
        (ay_bvqr_conj restartEpoch
          (ay_bvqr_conj solverBuild
            (ay_bvqr_conj fallbackBaseline validatorGate))))
      (ay_bvqr_queue_guard_after_tie queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_after_bumps
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    ay_bvqr_conj variableMap
      (ay_bvqr_conj restartEpoch
        (ay_bvqr_conj solverBuild
          (ay_bvqr_conj fallbackBaseline validatorGate))) :=
  fun guard =>
    ay_bvqr_conj_right bumpEvents
      (ay_bvqr_conj variableMap
        (ay_bvqr_conj restartEpoch
          (ay_bvqr_conj solverBuild
            (ay_bvqr_conj fallbackBaseline validatorGate))))
      (ay_bvqr_queue_guard_after_tie queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_variable_map
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    variableMap :=
  fun guard =>
    ay_bvqr_conj_left variableMap
      (ay_bvqr_conj restartEpoch
        (ay_bvqr_conj solverBuild
          (ay_bvqr_conj fallbackBaseline validatorGate)))
      (ay_bvqr_queue_guard_after_bumps queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_after_map
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    ay_bvqr_conj restartEpoch
      (ay_bvqr_conj solverBuild
        (ay_bvqr_conj fallbackBaseline validatorGate)) :=
  fun guard =>
    ay_bvqr_conj_right variableMap
      (ay_bvqr_conj restartEpoch
        (ay_bvqr_conj solverBuild
          (ay_bvqr_conj fallbackBaseline validatorGate)))
      (ay_bvqr_queue_guard_after_bumps queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_epoch
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    restartEpoch :=
  fun guard =>
    ay_bvqr_conj_left restartEpoch
      (ay_bvqr_conj solverBuild
        (ay_bvqr_conj fallbackBaseline validatorGate))
      (ay_bvqr_queue_guard_after_map queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_after_epoch
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    ay_bvqr_conj solverBuild
      (ay_bvqr_conj fallbackBaseline validatorGate) :=
  fun guard =>
    ay_bvqr_conj_right restartEpoch
      (ay_bvqr_conj solverBuild
        (ay_bvqr_conj fallbackBaseline validatorGate))
      (ay_bvqr_queue_guard_after_map queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_solver_build
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    solverBuild :=
  fun guard =>
    ay_bvqr_conj_left solverBuild
      (ay_bvqr_conj fallbackBaseline validatorGate)
      (ay_bvqr_queue_guard_after_epoch queueOrder tieBreaking bumpEvents
        variableMap restartEpoch solverBuild fallbackBaseline validatorGate
        guard)

theorem ay_bvqr_queue_guard_fallback
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    fallbackBaseline :=
  fun guard =>
    ay_bvqr_conj_left fallbackBaseline validatorGate
      (ay_bvqr_conj_right solverBuild
        (ay_bvqr_conj fallbackBaseline validatorGate)
        (ay_bvqr_queue_guard_after_epoch queueOrder tieBreaking bumpEvents
          variableMap restartEpoch solverBuild fallbackBaseline validatorGate
          guard))

theorem ay_bvqr_queue_guard_validator
    (queueOrder : Prop) (tieBreaking : Prop) (bumpEvents : Prop)
    (variableMap : Prop) (restartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bvqr_queue_guard queueOrder tieBreaking bumpEvents variableMap
      restartEpoch solverBuild fallbackBaseline validatorGate ->
    validatorGate :=
  fun guard =>
    ay_bvqr_conj_right fallbackBaseline validatorGate
      (ay_bvqr_conj_right solverBuild
        (ay_bvqr_conj fallbackBaseline validatorGate)
        (ay_bvqr_queue_guard_after_epoch queueOrder tieBreaking bumpEvents
          variableMap restartEpoch solverBuild fallbackBaseline validatorGate
          guard))

theorem ay_bvqr_replay_agreement_intro
    (queueMatch : Prop) (tieBreakMatch : Prop) (bumpMatch : Prop)
    (variableMapMatch : Prop) (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :
    queueMatch ->
    tieBreakMatch ->
    bumpMatch ->
    variableMapMatch ->
    epochMatch ->
    buildMatch ->
    fallbackMatch ->
    validatorAccepts ->
    ay_bvqr_replay_agreement queueMatch tieBreakMatch bumpMatch
      variableMapMatch epochMatch buildMatch fallbackMatch
      validatorAccepts :=
  fun queueH tieH bumpH mapH epochH buildH fallbackH validatorH =>
    ay_bvqr_queue_guard_intro queueMatch tieBreakMatch bumpMatch
      variableMapMatch epochMatch buildMatch fallbackMatch validatorAccepts
      queueH tieH bumpH mapH epochH buildH fallbackH validatorH

theorem ay_bvqr_replay_agreement_queue
    (queueMatch : Prop) (tieBreakMatch : Prop) (bumpMatch : Prop)
    (variableMapMatch : Prop) (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :
    ay_bvqr_replay_agreement queueMatch tieBreakMatch bumpMatch
      variableMapMatch epochMatch buildMatch fallbackMatch
      validatorAccepts ->
    queueMatch :=
  fun agreement =>
    ay_bvqr_queue_guard_order queueMatch tieBreakMatch bumpMatch
      variableMapMatch epochMatch buildMatch fallbackMatch validatorAccepts
      agreement

theorem ay_bvqr_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    guard ->
    agreement ->
    branchingHint ->
    ay_bvqr_accepted_hint guard agreement branchingHint :=
  fun guardH agreementH hintH =>
    ay_bvqr_conj_intro guard (ay_bvqr_conj agreement branchingHint)
      guardH
      (ay_bvqr_conj_intro agreement branchingHint agreementH hintH)

theorem ay_bvqr_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bvqr_accepted_hint guard agreement branchingHint -> guard :=
  fun accepted =>
    ay_bvqr_conj_left guard (ay_bvqr_conj agreement branchingHint)
      accepted

theorem ay_bvqr_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bvqr_accepted_hint guard agreement branchingHint -> agreement :=
  fun accepted =>
    ay_bvqr_conj_left agreement branchingHint
      (ay_bvqr_conj_right guard (ay_bvqr_conj agreement branchingHint)
        accepted)

theorem ay_bvqr_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bvqr_accepted_hint guard agreement branchingHint -> branchingHint :=
  fun accepted =>
    ay_bvqr_conj_right agreement branchingHint
      (ay_bvqr_conj_right guard (ay_bvqr_conj agreement branchingHint)
        accepted)

theorem ay_bvqr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bvqr_conj_intro (ay_bvqr_outcome model conflict) formula
      (ay_bvqr_disj_left model conflict modelH)
      formulaH

theorem ay_bvqr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bvqr_conj_intro (ay_bvqr_outcome model conflict) formula
      (ay_bvqr_disj_right model conflict conflictH)
      formulaH

theorem ay_bvqr_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bvqr_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bvqr_conj_intro hintCert public hintH publicH

theorem ay_bvqr_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bvqr_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bvqr_conj_right hintCert public accepted

theorem ay_bvqr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bvqr_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bvqr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bvqr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bvqr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bvqr_conj_left fallbackPublic diagnostic noClaim

theorem ay_bvqr_missing_bump_events_no_claim
    (missingBumpEvents : Prop) (fallbackPublic : Prop) :
    missingBumpEvents ->
    fallbackPublic ->
    ay_bvqr_no_claim missingBumpEvents fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro missingBumpEvents fallbackPublic
      fallbackH diagnosticH

theorem ay_bvqr_stale_queue_order_no_claim
    (staleQueueOrder : Prop) (fallbackPublic : Prop) :
    staleQueueOrder ->
    fallbackPublic ->
    ay_bvqr_no_claim staleQueueOrder fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro staleQueueOrder fallbackPublic
      fallbackH diagnosticH

theorem ay_bvqr_variable_map_drift_no_claim
    (variableMapDrift : Prop) (fallbackPublic : Prop) :
    variableMapDrift ->
    fallbackPublic ->
    ay_bvqr_no_claim variableMapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro variableMapDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bvqr_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_bvqr_no_claim epochMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro epochMismatch fallbackPublic fallbackH diagnosticH

theorem ay_bvqr_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bvqr_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvqr_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bvqr_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bvqr_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bvqr_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvqr_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bvqr_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bvqr_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bvqr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bvqr_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bvqr_accepted_hint guard agreement branchingHint ->
    model ->
    formula ->
    ay_bvqr_accepted_report
      (ay_bvqr_accepted_hint guard agreement branchingHint)
      (ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bvqr_accepted_report_intro
      (ay_bvqr_accepted_hint guard agreement branchingHint)
      (ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula)
      accepted
      (ay_bvqr_public_sat_report model conflict formula modelH formulaH)

theorem ay_bvqr_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bvqr_accepted_hint guard agreement branchingHint ->
    conflict ->
    formula ->
    ay_bvqr_accepted_report
      (ay_bvqr_accepted_hint guard agreement branchingHint)
      (ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bvqr_accepted_report_intro
      (ay_bvqr_accepted_hint guard agreement branchingHint)
      (ay_bvqr_public_report (ay_bvqr_outcome model conflict) formula)
      accepted
      (ay_bvqr_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bvqr_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bvqr_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bvqr_accepted_report_public hintCert public accepted

theorem ay_bvqr_queue_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bvqr_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bvqr_equisat_forward beforeHint afterHint equisat beforeH
