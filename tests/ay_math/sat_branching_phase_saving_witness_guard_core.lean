-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded phase-saving witness guard soundness skeleton for ay SAT solving.
-- Cached phases and saved assignments may guide branching only when they are
-- linked to the same stable variable map, trail snapshot, conflict/restart
-- epoch, solver build, fallback baseline, and validator gate.

def ay_bpsw_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpsw_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bpsw_equisat (before : Prop) (after : Prop) :=
  ay_bpsw_conj (before -> after) (after -> before)

def ay_bpsw_witness_guard
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :=
  ay_bpsw_conj cachedPhases
    (ay_bpsw_conj savedAssignments
      (ay_bpsw_conj stableVariableMap
        (ay_bpsw_conj trailSnapshot
          (ay_bpsw_conj conflictRestartEpoch
            (ay_bpsw_conj solverBuild
              (ay_bpsw_conj fallbackBaseline validatorGate))))))

def ay_bpsw_guard_agreement
    (phaseMatch : Prop) (assignmentMatch : Prop)
    (variableMapMatch : Prop) (trailMatch : Prop)
    (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :=
  ay_bpsw_conj phaseMatch
    (ay_bpsw_conj assignmentMatch
      (ay_bpsw_conj variableMapMatch
        (ay_bpsw_conj trailMatch
          (ay_bpsw_conj epochMatch
            (ay_bpsw_conj buildMatch
              (ay_bpsw_conj fallbackMatch validatorAccepts))))))

def ay_bpsw_accepted_hint
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :=
  ay_bpsw_conj guard (ay_bpsw_conj agreement branchingHint)

def ay_bpsw_outcome (model : Prop) (conflict : Prop) :=
  ay_bpsw_disj model conflict

def ay_bpsw_public_report (outcome : Prop) (formula : Prop) :=
  ay_bpsw_conj outcome formula

def ay_bpsw_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bpsw_conj hintCert public

def ay_bpsw_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bpsw_conj fallbackPublic diagnostic

theorem ay_bpsw_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bpsw_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bpsw_conj_left
    (left : Prop) (right : Prop) :
    ay_bpsw_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bpsw_conj_right
    (left : Prop) (right : Prop) :
    ay_bpsw_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bpsw_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bpsw_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bpsw_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bpsw_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bpsw_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bpsw_equisat before after :=
  fun forward backward =>
    ay_bpsw_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bpsw_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bpsw_equisat before after -> before -> after :=
  fun equisat =>
    ay_bpsw_conj_left (before -> after) (after -> before) equisat

theorem ay_bpsw_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bpsw_equisat before after -> after -> before :=
  fun equisat =>
    ay_bpsw_conj_right (before -> after) (after -> before) equisat

theorem ay_bpsw_witness_guard_intro
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    cachedPhases ->
    savedAssignments ->
    stableVariableMap ->
    trailSnapshot ->
    conflictRestartEpoch ->
    solverBuild ->
    fallbackBaseline ->
    validatorGate ->
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate :=
  fun phaseH assignmentH mapH trailH epochH buildH fallbackH validatorH =>
    ay_bpsw_conj_intro cachedPhases
      (ay_bpsw_conj savedAssignments
        (ay_bpsw_conj stableVariableMap
          (ay_bpsw_conj trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate))))))
      phaseH
      (ay_bpsw_conj_intro savedAssignments
        (ay_bpsw_conj stableVariableMap
          (ay_bpsw_conj trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate)))))
        assignmentH
        (ay_bpsw_conj_intro stableVariableMap
          (ay_bpsw_conj trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate))))
          mapH
          (ay_bpsw_conj_intro trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate)))
            trailH
            (ay_bpsw_conj_intro conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate))
              epochH
              (ay_bpsw_conj_intro solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate)
                buildH
                (ay_bpsw_conj_intro fallbackBaseline validatorGate
                  fallbackH validatorH))))))

theorem ay_bpsw_witness_guard_cached_phases
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    cachedPhases :=
  fun guard =>
    ay_bpsw_conj_left cachedPhases
      (ay_bpsw_conj savedAssignments
        (ay_bpsw_conj stableVariableMap
          (ay_bpsw_conj trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate))))))
      guard

theorem ay_bpsw_witness_guard_tail
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    ay_bpsw_conj savedAssignments
      (ay_bpsw_conj stableVariableMap
        (ay_bpsw_conj trailSnapshot
          (ay_bpsw_conj conflictRestartEpoch
            (ay_bpsw_conj solverBuild
              (ay_bpsw_conj fallbackBaseline validatorGate))))) :=
  fun guard =>
    ay_bpsw_conj_right cachedPhases
      (ay_bpsw_conj savedAssignments
        (ay_bpsw_conj stableVariableMap
          (ay_bpsw_conj trailSnapshot
            (ay_bpsw_conj conflictRestartEpoch
              (ay_bpsw_conj solverBuild
                (ay_bpsw_conj fallbackBaseline validatorGate))))))
      guard

theorem ay_bpsw_witness_guard_saved_assignments
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    savedAssignments :=
  fun guard =>
    ay_bpsw_conj_left savedAssignments
      (ay_bpsw_conj stableVariableMap
        (ay_bpsw_conj trailSnapshot
          (ay_bpsw_conj conflictRestartEpoch
            (ay_bpsw_conj solverBuild
              (ay_bpsw_conj fallbackBaseline validatorGate)))))
      (ay_bpsw_witness_guard_tail cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_after_assignments
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    ay_bpsw_conj stableVariableMap
      (ay_bpsw_conj trailSnapshot
        (ay_bpsw_conj conflictRestartEpoch
          (ay_bpsw_conj solverBuild
            (ay_bpsw_conj fallbackBaseline validatorGate)))) :=
  fun guard =>
    ay_bpsw_conj_right savedAssignments
      (ay_bpsw_conj stableVariableMap
        (ay_bpsw_conj trailSnapshot
          (ay_bpsw_conj conflictRestartEpoch
            (ay_bpsw_conj solverBuild
              (ay_bpsw_conj fallbackBaseline validatorGate)))))
      (ay_bpsw_witness_guard_tail cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_variable_map
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    stableVariableMap :=
  fun guard =>
    ay_bpsw_conj_left stableVariableMap
      (ay_bpsw_conj trailSnapshot
        (ay_bpsw_conj conflictRestartEpoch
          (ay_bpsw_conj solverBuild
            (ay_bpsw_conj fallbackBaseline validatorGate))))
      (ay_bpsw_witness_guard_after_assignments cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_after_variable_map
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    ay_bpsw_conj trailSnapshot
      (ay_bpsw_conj conflictRestartEpoch
        (ay_bpsw_conj solverBuild
          (ay_bpsw_conj fallbackBaseline validatorGate))) :=
  fun guard =>
    ay_bpsw_conj_right stableVariableMap
      (ay_bpsw_conj trailSnapshot
        (ay_bpsw_conj conflictRestartEpoch
          (ay_bpsw_conj solverBuild
            (ay_bpsw_conj fallbackBaseline validatorGate))))
      (ay_bpsw_witness_guard_after_assignments cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_trail
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    trailSnapshot :=
  fun guard =>
    ay_bpsw_conj_left trailSnapshot
      (ay_bpsw_conj conflictRestartEpoch
        (ay_bpsw_conj solverBuild
          (ay_bpsw_conj fallbackBaseline validatorGate)))
      (ay_bpsw_witness_guard_after_variable_map cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_after_trail
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    ay_bpsw_conj conflictRestartEpoch
      (ay_bpsw_conj solverBuild
        (ay_bpsw_conj fallbackBaseline validatorGate)) :=
  fun guard =>
    ay_bpsw_conj_right trailSnapshot
      (ay_bpsw_conj conflictRestartEpoch
        (ay_bpsw_conj solverBuild
          (ay_bpsw_conj fallbackBaseline validatorGate)))
      (ay_bpsw_witness_guard_after_variable_map cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_epoch
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    conflictRestartEpoch :=
  fun guard =>
    ay_bpsw_conj_left conflictRestartEpoch
      (ay_bpsw_conj solverBuild
        (ay_bpsw_conj fallbackBaseline validatorGate))
      (ay_bpsw_witness_guard_after_trail cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_after_epoch
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    ay_bpsw_conj solverBuild
      (ay_bpsw_conj fallbackBaseline validatorGate) :=
  fun guard =>
    ay_bpsw_conj_right conflictRestartEpoch
      (ay_bpsw_conj solverBuild
        (ay_bpsw_conj fallbackBaseline validatorGate))
      (ay_bpsw_witness_guard_after_trail cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_solver_build
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    solverBuild :=
  fun guard =>
    ay_bpsw_conj_left solverBuild
      (ay_bpsw_conj fallbackBaseline validatorGate)
      (ay_bpsw_witness_guard_after_epoch cachedPhases savedAssignments
        stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
        fallbackBaseline validatorGate guard)

theorem ay_bpsw_witness_guard_fallback
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    fallbackBaseline :=
  fun guard =>
    ay_bpsw_conj_left fallbackBaseline validatorGate
      (ay_bpsw_conj_right solverBuild
        (ay_bpsw_conj fallbackBaseline validatorGate)
        (ay_bpsw_witness_guard_after_epoch cachedPhases savedAssignments
          stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
          fallbackBaseline validatorGate guard))

theorem ay_bpsw_witness_guard_validator
    (cachedPhases : Prop) (savedAssignments : Prop)
    (stableVariableMap : Prop) (trailSnapshot : Prop)
    (conflictRestartEpoch : Prop) (solverBuild : Prop)
    (fallbackBaseline : Prop) (validatorGate : Prop) :
    ay_bpsw_witness_guard cachedPhases savedAssignments stableVariableMap
      trailSnapshot conflictRestartEpoch solverBuild fallbackBaseline
      validatorGate ->
    validatorGate :=
  fun guard =>
    ay_bpsw_conj_right fallbackBaseline validatorGate
      (ay_bpsw_conj_right solverBuild
        (ay_bpsw_conj fallbackBaseline validatorGate)
        (ay_bpsw_witness_guard_after_epoch cachedPhases savedAssignments
          stableVariableMap trailSnapshot conflictRestartEpoch solverBuild
          fallbackBaseline validatorGate guard))

theorem ay_bpsw_guard_agreement_intro
    (phaseMatch : Prop) (assignmentMatch : Prop)
    (variableMapMatch : Prop) (trailMatch : Prop)
    (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :
    phaseMatch ->
    assignmentMatch ->
    variableMapMatch ->
    trailMatch ->
    epochMatch ->
    buildMatch ->
    fallbackMatch ->
    validatorAccepts ->
    ay_bpsw_guard_agreement phaseMatch assignmentMatch variableMapMatch
      trailMatch epochMatch buildMatch fallbackMatch validatorAccepts :=
  fun phaseH assignmentH mapH trailH epochH buildH fallbackH validatorH =>
    ay_bpsw_witness_guard_intro phaseMatch assignmentMatch variableMapMatch
      trailMatch epochMatch buildMatch fallbackMatch validatorAccepts
      phaseH assignmentH mapH trailH epochH buildH fallbackH validatorH

theorem ay_bpsw_guard_agreement_variable_map
    (phaseMatch : Prop) (assignmentMatch : Prop)
    (variableMapMatch : Prop) (trailMatch : Prop)
    (epochMatch : Prop) (buildMatch : Prop)
    (fallbackMatch : Prop) (validatorAccepts : Prop) :
    ay_bpsw_guard_agreement phaseMatch assignmentMatch variableMapMatch
      trailMatch epochMatch buildMatch fallbackMatch validatorAccepts ->
    variableMapMatch :=
  fun agreement =>
    ay_bpsw_witness_guard_variable_map phaseMatch assignmentMatch
      variableMapMatch trailMatch epochMatch buildMatch fallbackMatch
      validatorAccepts agreement

theorem ay_bpsw_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    guard ->
    agreement ->
    branchingHint ->
    ay_bpsw_accepted_hint guard agreement branchingHint :=
  fun guardH agreementH hintH =>
    ay_bpsw_conj_intro guard (ay_bpsw_conj agreement branchingHint)
      guardH
      (ay_bpsw_conj_intro agreement branchingHint agreementH hintH)

theorem ay_bpsw_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bpsw_accepted_hint guard agreement branchingHint -> guard :=
  fun accepted =>
    ay_bpsw_conj_left guard (ay_bpsw_conj agreement branchingHint)
      accepted

theorem ay_bpsw_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bpsw_accepted_hint guard agreement branchingHint -> agreement :=
  fun accepted =>
    ay_bpsw_conj_left agreement branchingHint
      (ay_bpsw_conj_right guard (ay_bpsw_conj agreement branchingHint)
        accepted)

theorem ay_bpsw_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bpsw_accepted_hint guard agreement branchingHint -> branchingHint :=
  fun accepted =>
    ay_bpsw_conj_right agreement branchingHint
      (ay_bpsw_conj_right guard (ay_bpsw_conj agreement branchingHint)
        accepted)

theorem ay_bpsw_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bpsw_conj_intro (ay_bpsw_outcome model conflict) formula
      (ay_bpsw_disj_left model conflict modelH)
      formulaH

theorem ay_bpsw_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bpsw_conj_intro (ay_bpsw_outcome model conflict) formula
      (ay_bpsw_disj_right model conflict conflictH)
      formulaH

theorem ay_bpsw_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bpsw_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bpsw_conj_intro hintCert public hintH publicH

theorem ay_bpsw_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bpsw_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpsw_conj_right hintCert public accepted

theorem ay_bpsw_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bpsw_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bpsw_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bpsw_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpsw_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bpsw_conj_left fallbackPublic diagnostic noClaim

theorem ay_bpsw_stale_variable_map_no_claim
    (staleVariableMap : Prop) (fallbackPublic : Prop) :
    staleVariableMap ->
    fallbackPublic ->
    ay_bpsw_no_claim staleVariableMap fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro staleVariableMap fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsw_trail_drift_no_claim
    (trailDrift : Prop) (fallbackPublic : Prop) :
    trailDrift ->
    fallbackPublic ->
    ay_bpsw_no_claim trailDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro trailDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsw_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_bpsw_no_claim epochMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro epochMismatch fallbackPublic fallbackH diagnosticH

theorem ay_bpsw_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bpsw_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bpsw_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bpsw_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsw_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bpsw_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsw_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsw_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpsw_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bpsw_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bpsw_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpsw_accepted_hint guard agreement branchingHint ->
    model ->
    formula ->
    ay_bpsw_accepted_report
      (ay_bpsw_accepted_hint guard agreement branchingHint)
      (ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bpsw_accepted_report_intro
      (ay_bpsw_accepted_hint guard agreement branchingHint)
      (ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula)
      accepted
      (ay_bpsw_public_sat_report model conflict formula modelH formulaH)

theorem ay_bpsw_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpsw_accepted_hint guard agreement branchingHint ->
    conflict ->
    formula ->
    ay_bpsw_accepted_report
      (ay_bpsw_accepted_hint guard agreement branchingHint)
      (ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bpsw_accepted_report_intro
      (ay_bpsw_accepted_hint guard agreement branchingHint)
      (ay_bpsw_public_report (ay_bpsw_outcome model conflict) formula)
      accepted
      (ay_bpsw_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bpsw_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bpsw_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpsw_accepted_report_public hintCert public accepted

theorem ay_bpsw_phase_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bpsw_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bpsw_equisat_forward beforeHint afterHint equisat beforeH
