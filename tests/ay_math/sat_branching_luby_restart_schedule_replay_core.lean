-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded Luby/geometric restart schedule replay soundness skeleton for ay SAT
-- solving. Restart schedule choices guide search only when the schedule
-- generator, counters, budgets, epoch lineage, fallback baseline, solver
-- build, validator gate, and audit evidence agree.

def ay_blsr_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_blsr_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_blsr_equisat (before : Prop) (after : Prop) :=
  ay_blsr_conj (before -> after) (after -> before)

def ay_blsr_schedule_guard
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  ay_blsr_conj scheduleGenerator
    (ay_blsr_conj conflictCounter
      (ay_blsr_conj propagationBudget
        (ay_blsr_conj restartEpochLineage
          (ay_blsr_conj fallbackBaseline
            (ay_blsr_conj solverBuildIdentity
              (ay_blsr_conj validatorGate auditEvidence))))))

def ay_blsr_replay_agreement
    (generatorMatch : Prop) (counterMatch : Prop)
    (budgetMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_blsr_conj generatorMatch
    (ay_blsr_conj counterMatch
      (ay_blsr_conj budgetMatch
        (ay_blsr_conj epochMatch
          (ay_blsr_conj fallbackMatch
            (ay_blsr_conj buildMatch
              (ay_blsr_conj validatorAccepts auditMatch))))))

def ay_blsr_accepted_replay
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :=
  ay_blsr_conj guard (ay_blsr_conj agreement restartHint)

def ay_blsr_outcome (model : Prop) (conflict : Prop) :=
  ay_blsr_disj model conflict

def ay_blsr_public_report (outcome : Prop) (formula : Prop) :=
  ay_blsr_conj outcome formula

def ay_blsr_accepted_report (replayCert : Prop) (public : Prop) :=
  ay_blsr_conj replayCert public

def ay_blsr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_blsr_conj fallbackPublic diagnostic

theorem ay_blsr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_blsr_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_blsr_conj_left
    (left : Prop) (right : Prop) :
    ay_blsr_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_blsr_conj_right
    (left : Prop) (right : Prop) :
    ay_blsr_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_blsr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_blsr_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_blsr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_blsr_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_blsr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_blsr_equisat before after :=
  fun forward backward =>
    ay_blsr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_blsr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_blsr_equisat before after -> before -> after :=
  fun equisat =>
    ay_blsr_conj_left (before -> after) (after -> before) equisat

theorem ay_blsr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_blsr_equisat before after -> after -> before :=
  fun equisat =>
    ay_blsr_conj_right (before -> after) (after -> before) equisat

theorem ay_blsr_schedule_guard_intro
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    scheduleGenerator ->
    conflictCounter ->
    propagationBudget ->
    restartEpochLineage ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence :=
  fun generatorH counterH budgetH epochH fallbackH buildH validatorH auditH =>
    ay_blsr_conj_intro scheduleGenerator
      (ay_blsr_conj conflictCounter
        (ay_blsr_conj propagationBudget
          (ay_blsr_conj restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence))))))
      generatorH
      (ay_blsr_conj_intro conflictCounter
        (ay_blsr_conj propagationBudget
          (ay_blsr_conj restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence)))))
        counterH
        (ay_blsr_conj_intro propagationBudget
          (ay_blsr_conj restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence))))
          budgetH
          (ay_blsr_conj_intro restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence)))
            epochH
            (ay_blsr_conj_intro fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence))
              fallbackH
              (ay_blsr_conj_intro solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence)
                buildH
                (ay_blsr_conj_intro validatorGate auditEvidence
                  validatorH auditH))))))

theorem ay_blsr_schedule_guard_generator
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    scheduleGenerator :=
  fun guard =>
    ay_blsr_conj_left scheduleGenerator
      (ay_blsr_conj conflictCounter
        (ay_blsr_conj propagationBudget
          (ay_blsr_conj restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence))))))
      guard

theorem ay_blsr_schedule_guard_tail
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    ay_blsr_conj conflictCounter
      (ay_blsr_conj propagationBudget
        (ay_blsr_conj restartEpochLineage
          (ay_blsr_conj fallbackBaseline
            (ay_blsr_conj solverBuildIdentity
              (ay_blsr_conj validatorGate auditEvidence))))) :=
  fun guard =>
    ay_blsr_conj_right scheduleGenerator
      (ay_blsr_conj conflictCounter
        (ay_blsr_conj propagationBudget
          (ay_blsr_conj restartEpochLineage
            (ay_blsr_conj fallbackBaseline
              (ay_blsr_conj solverBuildIdentity
                (ay_blsr_conj validatorGate auditEvidence))))))
      guard

theorem ay_blsr_schedule_guard_counter
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    conflictCounter :=
  fun guard =>
    ay_blsr_conj_left conflictCounter
      (ay_blsr_conj propagationBudget
        (ay_blsr_conj restartEpochLineage
          (ay_blsr_conj fallbackBaseline
            (ay_blsr_conj solverBuildIdentity
              (ay_blsr_conj validatorGate auditEvidence)))))
      (ay_blsr_schedule_guard_tail scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_after_counter
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    ay_blsr_conj propagationBudget
      (ay_blsr_conj restartEpochLineage
        (ay_blsr_conj fallbackBaseline
          (ay_blsr_conj solverBuildIdentity
            (ay_blsr_conj validatorGate auditEvidence)))) :=
  fun guard =>
    ay_blsr_conj_right conflictCounter
      (ay_blsr_conj propagationBudget
        (ay_blsr_conj restartEpochLineage
          (ay_blsr_conj fallbackBaseline
            (ay_blsr_conj solverBuildIdentity
              (ay_blsr_conj validatorGate auditEvidence)))))
      (ay_blsr_schedule_guard_tail scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_budget
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    propagationBudget :=
  fun guard =>
    ay_blsr_conj_left propagationBudget
      (ay_blsr_conj restartEpochLineage
        (ay_blsr_conj fallbackBaseline
          (ay_blsr_conj solverBuildIdentity
            (ay_blsr_conj validatorGate auditEvidence))))
      (ay_blsr_schedule_guard_after_counter scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_after_budget
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    ay_blsr_conj restartEpochLineage
      (ay_blsr_conj fallbackBaseline
        (ay_blsr_conj solverBuildIdentity
          (ay_blsr_conj validatorGate auditEvidence))) :=
  fun guard =>
    ay_blsr_conj_right propagationBudget
      (ay_blsr_conj restartEpochLineage
        (ay_blsr_conj fallbackBaseline
          (ay_blsr_conj solverBuildIdentity
            (ay_blsr_conj validatorGate auditEvidence))))
      (ay_blsr_schedule_guard_after_counter scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_epoch
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    restartEpochLineage :=
  fun guard =>
    ay_blsr_conj_left restartEpochLineage
      (ay_blsr_conj fallbackBaseline
        (ay_blsr_conj solverBuildIdentity
          (ay_blsr_conj validatorGate auditEvidence)))
      (ay_blsr_schedule_guard_after_budget scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_after_epoch
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    ay_blsr_conj fallbackBaseline
      (ay_blsr_conj solverBuildIdentity
        (ay_blsr_conj validatorGate auditEvidence)) :=
  fun guard =>
    ay_blsr_conj_right restartEpochLineage
      (ay_blsr_conj fallbackBaseline
        (ay_blsr_conj solverBuildIdentity
          (ay_blsr_conj validatorGate auditEvidence)))
      (ay_blsr_schedule_guard_after_budget scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_fallback
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    ay_blsr_conj_left fallbackBaseline
      (ay_blsr_conj solverBuildIdentity
        (ay_blsr_conj validatorGate auditEvidence))
      (ay_blsr_schedule_guard_after_epoch scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_after_fallback
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    ay_blsr_conj solverBuildIdentity
      (ay_blsr_conj validatorGate auditEvidence) :=
  fun guard =>
    ay_blsr_conj_right fallbackBaseline
      (ay_blsr_conj solverBuildIdentity
        (ay_blsr_conj validatorGate auditEvidence))
      (ay_blsr_schedule_guard_after_epoch scheduleGenerator conflictCounter
        propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_build
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    ay_blsr_conj_left solverBuildIdentity
      (ay_blsr_conj validatorGate auditEvidence)
      (ay_blsr_schedule_guard_after_fallback scheduleGenerator
        conflictCounter propagationBudget restartEpochLineage fallbackBaseline
        solverBuildIdentity validatorGate auditEvidence guard)

theorem ay_blsr_schedule_guard_validator
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    ay_blsr_conj_left validatorGate auditEvidence
      (ay_blsr_conj_right solverBuildIdentity
        (ay_blsr_conj validatorGate auditEvidence)
        (ay_blsr_schedule_guard_after_fallback scheduleGenerator
          conflictCounter propagationBudget restartEpochLineage fallbackBaseline
          solverBuildIdentity validatorGate auditEvidence guard))

theorem ay_blsr_schedule_guard_audit
    (scheduleGenerator : Prop) (conflictCounter : Prop)
    (propagationBudget : Prop) (restartEpochLineage : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_blsr_schedule_guard scheduleGenerator conflictCounter
      propagationBudget restartEpochLineage fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    ay_blsr_conj_right validatorGate auditEvidence
      (ay_blsr_conj_right solverBuildIdentity
        (ay_blsr_conj validatorGate auditEvidence)
        (ay_blsr_schedule_guard_after_fallback scheduleGenerator
          conflictCounter propagationBudget restartEpochLineage fallbackBaseline
          solverBuildIdentity validatorGate auditEvidence guard))

theorem ay_blsr_replay_agreement_intro
    (generatorMatch : Prop) (counterMatch : Prop)
    (budgetMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    generatorMatch ->
    counterMatch ->
    budgetMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_blsr_replay_agreement generatorMatch counterMatch budgetMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun generatorH counterH budgetH epochH fallbackH buildH validatorH auditH =>
    ay_blsr_schedule_guard_intro generatorMatch counterMatch budgetMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      generatorH counterH budgetH epochH fallbackH buildH validatorH auditH

theorem ay_blsr_replay_agreement_generator
    (generatorMatch : Prop) (counterMatch : Prop)
    (budgetMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_blsr_replay_agreement generatorMatch counterMatch budgetMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    generatorMatch :=
  fun agreement =>
    ay_blsr_schedule_guard_generator generatorMatch counterMatch budgetMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch agreement

theorem ay_blsr_accepted_replay_intro
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    guard ->
    agreement ->
    restartHint ->
    ay_blsr_accepted_replay guard agreement restartHint :=
  fun guardH agreementH hintH =>
    ay_blsr_conj_intro guard (ay_blsr_conj agreement restartHint)
      guardH
      (ay_blsr_conj_intro agreement restartHint agreementH hintH)

theorem ay_blsr_accepted_replay_guard
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_blsr_accepted_replay guard agreement restartHint -> guard :=
  fun accepted =>
    ay_blsr_conj_left guard (ay_blsr_conj agreement restartHint)
      accepted

theorem ay_blsr_accepted_replay_agreement
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_blsr_accepted_replay guard agreement restartHint -> agreement :=
  fun accepted =>
    ay_blsr_conj_left agreement restartHint
      (ay_blsr_conj_right guard (ay_blsr_conj agreement restartHint)
        accepted)

theorem ay_blsr_accepted_replay_guidance
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_blsr_accepted_replay guard agreement restartHint -> restartHint :=
  fun accepted =>
    ay_blsr_conj_right agreement restartHint
      (ay_blsr_conj_right guard (ay_blsr_conj agreement restartHint)
        accepted)

theorem ay_blsr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_blsr_public_report (ay_blsr_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_blsr_conj_intro (ay_blsr_outcome model conflict) formula
      (ay_blsr_disj_left model conflict modelH)
      formulaH

theorem ay_blsr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_blsr_public_report (ay_blsr_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_blsr_conj_intro (ay_blsr_outcome model conflict) formula
      (ay_blsr_disj_right model conflict conflictH)
      formulaH

theorem ay_blsr_accepted_report_intro
    (replayCert : Prop) (public : Prop) :
    replayCert ->
    public ->
    ay_blsr_accepted_report replayCert public :=
  fun replayH publicH =>
    ay_blsr_conj_intro replayCert public replayH publicH

theorem ay_blsr_accepted_report_public
    (replayCert : Prop) (public : Prop) :
    ay_blsr_accepted_report replayCert public -> public :=
  fun accepted =>
    ay_blsr_conj_right replayCert public accepted

theorem ay_blsr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_blsr_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_blsr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_blsr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_blsr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_blsr_conj_left fallbackPublic diagnostic noClaim

theorem ay_blsr_generator_drift_no_claim
    (generatorDrift : Prop) (fallbackPublic : Prop) :
    generatorDrift ->
    fallbackPublic ->
    ay_blsr_no_claim generatorDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro generatorDrift fallbackPublic fallbackH diagnosticH

theorem ay_blsr_counter_mismatch_no_claim
    (counterMismatch : Prop) (fallbackPublic : Prop) :
    counterMismatch ->
    fallbackPublic ->
    ay_blsr_no_claim counterMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro counterMismatch fallbackPublic fallbackH diagnosticH

theorem ay_blsr_budget_mismatch_no_claim
    (budgetMismatch : Prop) (fallbackPublic : Prop) :
    budgetMismatch ->
    fallbackPublic ->
    ay_blsr_no_claim budgetMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro budgetMismatch fallbackPublic fallbackH diagnosticH

theorem ay_blsr_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_blsr_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_blsr_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_blsr_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_blsr_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_blsr_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_blsr_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_blsr_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_blsr_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_blsr_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blsr_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_blsr_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_blsr_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_blsr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_blsr_accepted_replay_guides_sat
    (guard : Prop) (agreement : Prop) (restartHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_blsr_accepted_replay guard agreement restartHint ->
    model ->
    formula ->
    ay_blsr_accepted_report
      (ay_blsr_accepted_replay guard agreement restartHint)
      (ay_blsr_public_report (ay_blsr_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_blsr_accepted_report_intro
      (ay_blsr_accepted_replay guard agreement restartHint)
      (ay_blsr_public_report (ay_blsr_outcome model conflict) formula)
      accepted
      (ay_blsr_public_sat_report model conflict formula modelH formulaH)

theorem ay_blsr_accepted_replay_guides_unsat
    (guard : Prop) (agreement : Prop) (restartHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_blsr_accepted_replay guard agreement restartHint ->
    conflict ->
    formula ->
    ay_blsr_accepted_report
      (ay_blsr_accepted_replay guard agreement restartHint)
      (ay_blsr_public_report (ay_blsr_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_blsr_accepted_report_intro
      (ay_blsr_accepted_replay guard agreement restartHint)
      (ay_blsr_public_report (ay_blsr_outcome model conflict) formula)
      accepted
      (ay_blsr_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_blsr_accepted_replay_preserves_public_soundness
    (replayCert : Prop) (public : Prop) :
    ay_blsr_accepted_report replayCert public -> public :=
  fun accepted =>
    ay_blsr_accepted_report_public replayCert public accepted

theorem ay_blsr_schedule_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_blsr_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_blsr_equisat_forward beforeHint afterHint equisat beforeH
