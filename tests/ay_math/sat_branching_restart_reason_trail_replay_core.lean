-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart reason-trail replay soundness skeleton for ay SAT solving.
-- Restart decisions based on conflicts, LBD windows, activity, phase saving,
-- and budget counters are only performance hints when the reason trail is
-- deterministic, build-matched, dependency-guarded, and carries public
-- soundness/fallback evidence.

def AyBRRTConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBRRTDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBRRTEquisat (before : Prop) (after : Prop) :=
  AyBRRTConj (before -> after) (after -> before)

def AyBRRTReasonTrail
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :=
  AyBRRTConj conflictEvents
    (AyBRRTConj lbdWindow
      (AyBRRTConj clauseActivity
        (AyBRRTConj phaseSaving
          (AyBRRTConj budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback)))))))

def AyBRRTAgreement
    (eventMatch : Prop) (lbdMatch : Prop)
    (activityMatch : Prop) (phaseMatch : Prop)
    (budgetMatch : Prop) (trailMatch : Prop)
    (buildMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :=
  AyBRRTConj eventMatch
    (AyBRRTConj lbdMatch
      (AyBRRTConj activityMatch
        (AyBRRTConj phaseMatch
          (AyBRRTConj budgetMatch
            (AyBRRTConj trailMatch
              (AyBRRTConj buildMatch
                (AyBRRTConj dependencyMatch publicGuardMatch)))))))

def AyBRRTAcceptedReplay
    (trail : Prop) (agreement : Prop) (restartHint : Prop) :=
  AyBRRTConj trail (AyBRRTConj agreement restartHint)

def AyBRRTOutcome (model : Prop) (conflict : Prop) :=
  AyBRRTDisj model conflict

def AyBRRTPublicReport (outcome : Prop) (formula : Prop) :=
  AyBRRTConj outcome formula

def AyBRRTAcceptedReport (replay : Prop) (public : Prop) :=
  AyBRRTConj replay public

def AyBRRTNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBRRTConj fallbackPublic diagnostic

theorem ay_brrt_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBRRTConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brrt_conj_left
    (left : Prop) (right : Prop) :
    AyBRRTConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brrt_conj_right
    (left : Prop) (right : Prop) :
    AyBRRTConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brrt_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBRRTDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brrt_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBRRTDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brrt_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBRRTEquisat before after :=
  fun forward backward =>
    ay_brrt_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brrt_equisat_forward
    (before : Prop) (after : Prop) :
    AyBRRTEquisat before after -> before -> after :=
  fun equisat =>
    ay_brrt_conj_left (before -> after) (after -> before) equisat

theorem ay_brrt_equisat_backward
    (before : Prop) (after : Prop) :
    AyBRRTEquisat before after -> after -> before :=
  fun equisat =>
    ay_brrt_conj_right (before -> after) (after -> before) equisat

theorem ay_brrt_reason_trail_intro
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    conflictEvents ->
    lbdWindow ->
    clauseActivity ->
    phaseSaving ->
    budgetCounters ->
    deterministicTrail ->
    solverBuild ->
    dependencyGuard ->
    publicFallback ->
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback :=
  fun conflictH lbdH activityH phaseH budgetH trailH buildH
      dependencyH publicH =>
    ay_brrt_conj_intro conflictEvents
      (AyBRRTConj lbdWindow
        (AyBRRTConj clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))))))
      conflictH
      (ay_brrt_conj_intro lbdWindow
        (AyBRRTConj clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback))))))
        lbdH
        (ay_brrt_conj_intro clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))))
          activityH
          (ay_brrt_conj_intro phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback))))
            phaseH
            (ay_brrt_conj_intro budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))
              budgetH
              (ay_brrt_conj_intro deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback))
                trailH
                (ay_brrt_conj_intro solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)
                  buildH
                  (ay_brrt_conj_intro dependencyGuard publicFallback
                    dependencyH publicH)))))))

theorem ay_brrt_reason_trail_conflicts
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    conflictEvents :=
  fun trail =>
    ay_brrt_conj_left conflictEvents
      (AyBRRTConj lbdWindow
        (AyBRRTConj clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))))))
      trail

theorem ay_brrt_reason_trail_tail
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    AyBRRTConj lbdWindow
      (AyBRRTConj clauseActivity
        (AyBRRTConj phaseSaving
          (AyBRRTConj budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback)))))) :=
  fun trail =>
    ay_brrt_conj_right conflictEvents
      (AyBRRTConj lbdWindow
        (AyBRRTConj clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))))))
      trail

theorem ay_brrt_reason_trail_lbd
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    lbdWindow :=
  fun trail =>
    ay_brrt_conj_left lbdWindow
      (AyBRRTConj clauseActivity
        (AyBRRTConj phaseSaving
          (AyBRRTConj budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback))))))
      (ay_brrt_reason_trail_tail conflictEvents lbdWindow
        clauseActivity phaseSaving budgetCounters deterministicTrail
        solverBuild dependencyGuard publicFallback trail)

theorem ay_brrt_reason_trail_activity
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    clauseActivity :=
  fun trail =>
    ay_brrt_conj_left clauseActivity
      (AyBRRTConj phaseSaving
        (AyBRRTConj budgetCounters
          (AyBRRTConj deterministicTrail
            (AyBRRTConj solverBuild
              (AyBRRTConj dependencyGuard publicFallback)))))
      (ay_brrt_conj_right lbdWindow
        (AyBRRTConj clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback))))))
        (ay_brrt_reason_trail_tail conflictEvents lbdWindow
          clauseActivity phaseSaving budgetCounters deterministicTrail
          solverBuild dependencyGuard publicFallback trail))

theorem ay_brrt_reason_trail_phase
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    phaseSaving :=
  fun trail =>
    ay_brrt_conj_left phaseSaving
      (AyBRRTConj budgetCounters
        (AyBRRTConj deterministicTrail
          (AyBRRTConj solverBuild
            (AyBRRTConj dependencyGuard publicFallback))))
      (ay_brrt_conj_right clauseActivity
        (AyBRRTConj phaseSaving
          (AyBRRTConj budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback)))))
        (ay_brrt_conj_right lbdWindow
          (AyBRRTConj clauseActivity
            (AyBRRTConj phaseSaving
              (AyBRRTConj budgetCounters
                (AyBRRTConj deterministicTrail
                  (AyBRRTConj solverBuild
                    (AyBRRTConj dependencyGuard publicFallback))))))
          (ay_brrt_reason_trail_tail conflictEvents lbdWindow
            clauseActivity phaseSaving budgetCounters deterministicTrail
            solverBuild dependencyGuard publicFallback trail)))

theorem ay_brrt_reason_trail_budget
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    budgetCounters :=
  fun trail =>
    ay_brrt_conj_left budgetCounters
      (AyBRRTConj deterministicTrail
        (AyBRRTConj solverBuild
          (AyBRRTConj dependencyGuard publicFallback)))
      (ay_brrt_conj_right phaseSaving
        (AyBRRTConj budgetCounters
          (AyBRRTConj deterministicTrail
            (AyBRRTConj solverBuild
              (AyBRRTConj dependencyGuard publicFallback))))
        (ay_brrt_conj_right clauseActivity
          (AyBRRTConj phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback)))))
          (ay_brrt_conj_right lbdWindow
            (AyBRRTConj clauseActivity
              (AyBRRTConj phaseSaving
                (AyBRRTConj budgetCounters
                  (AyBRRTConj deterministicTrail
                    (AyBRRTConj solverBuild
                      (AyBRRTConj dependencyGuard publicFallback))))))
            (ay_brrt_reason_trail_tail conflictEvents lbdWindow
              clauseActivity phaseSaving budgetCounters deterministicTrail
              solverBuild dependencyGuard publicFallback trail))))

theorem ay_brrt_reason_trail_deterministic
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    deterministicTrail :=
  fun trail =>
    ay_brrt_conj_left deterministicTrail
      (AyBRRTConj solverBuild
        (AyBRRTConj dependencyGuard publicFallback))
      (ay_brrt_conj_right budgetCounters
        (AyBRRTConj deterministicTrail
          (AyBRRTConj solverBuild
            (AyBRRTConj dependencyGuard publicFallback)))
        (ay_brrt_conj_right phaseSaving
          (AyBRRTConj budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback))))
          (ay_brrt_conj_right clauseActivity
            (AyBRRTConj phaseSaving
              (AyBRRTConj budgetCounters
                (AyBRRTConj deterministicTrail
                  (AyBRRTConj solverBuild
                    (AyBRRTConj dependencyGuard publicFallback)))))
            (ay_brrt_conj_right lbdWindow
              (AyBRRTConj clauseActivity
                (AyBRRTConj phaseSaving
                  (AyBRRTConj budgetCounters
                    (AyBRRTConj deterministicTrail
                      (AyBRRTConj solverBuild
                        (AyBRRTConj dependencyGuard publicFallback))))))
              (ay_brrt_reason_trail_tail conflictEvents lbdWindow
                clauseActivity phaseSaving budgetCounters
                deterministicTrail solverBuild dependencyGuard
                publicFallback trail)))))

theorem ay_brrt_reason_trail_build
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    solverBuild :=
  fun trail =>
    ay_brrt_conj_left solverBuild
      (AyBRRTConj dependencyGuard publicFallback)
      (ay_brrt_conj_right deterministicTrail
        (AyBRRTConj solverBuild
          (AyBRRTConj dependencyGuard publicFallback))
        (ay_brrt_conj_right budgetCounters
          (AyBRRTConj deterministicTrail
            (AyBRRTConj solverBuild
              (AyBRRTConj dependencyGuard publicFallback)))
          (ay_brrt_conj_right phaseSaving
            (AyBRRTConj budgetCounters
              (AyBRRTConj deterministicTrail
                (AyBRRTConj solverBuild
                  (AyBRRTConj dependencyGuard publicFallback))))
            (ay_brrt_conj_right clauseActivity
              (AyBRRTConj phaseSaving
                (AyBRRTConj budgetCounters
                  (AyBRRTConj deterministicTrail
                    (AyBRRTConj solverBuild
                      (AyBRRTConj dependencyGuard publicFallback)))))
              (ay_brrt_conj_right lbdWindow
                (AyBRRTConj clauseActivity
                  (AyBRRTConj phaseSaving
                    (AyBRRTConj budgetCounters
                      (AyBRRTConj deterministicTrail
                        (AyBRRTConj solverBuild
                          (AyBRRTConj dependencyGuard publicFallback))))))
                (ay_brrt_reason_trail_tail conflictEvents lbdWindow
                  clauseActivity phaseSaving budgetCounters
                  deterministicTrail solverBuild dependencyGuard
                  publicFallback trail))))))

theorem ay_brrt_reason_trail_dependency
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    dependencyGuard :=
  fun trail =>
    ay_brrt_conj_left dependencyGuard publicFallback
      (ay_brrt_conj_right solverBuild
        (AyBRRTConj dependencyGuard publicFallback)
        (ay_brrt_conj_right deterministicTrail
          (AyBRRTConj solverBuild
            (AyBRRTConj dependencyGuard publicFallback))
          (ay_brrt_conj_right budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback)))
            (ay_brrt_conj_right phaseSaving
              (AyBRRTConj budgetCounters
                (AyBRRTConj deterministicTrail
                  (AyBRRTConj solverBuild
                    (AyBRRTConj dependencyGuard publicFallback))))
              (ay_brrt_conj_right clauseActivity
                (AyBRRTConj phaseSaving
                  (AyBRRTConj budgetCounters
                    (AyBRRTConj deterministicTrail
                      (AyBRRTConj solverBuild
                        (AyBRRTConj dependencyGuard publicFallback)))))
                (ay_brrt_conj_right lbdWindow
                  (AyBRRTConj clauseActivity
                    (AyBRRTConj phaseSaving
                      (AyBRRTConj budgetCounters
                        (AyBRRTConj deterministicTrail
                          (AyBRRTConj solverBuild
                            (AyBRRTConj dependencyGuard publicFallback))))))
                  (ay_brrt_reason_trail_tail conflictEvents lbdWindow
                    clauseActivity phaseSaving budgetCounters
                    deterministicTrail solverBuild dependencyGuard
                    publicFallback trail)))))))

theorem ay_brrt_reason_trail_public
    (conflictEvents : Prop) (lbdWindow : Prop)
    (clauseActivity : Prop) (phaseSaving : Prop)
    (budgetCounters : Prop) (deterministicTrail : Prop)
    (solverBuild : Prop) (dependencyGuard : Prop)
    (publicFallback : Prop) :
    AyBRRTReasonTrail conflictEvents lbdWindow clauseActivity
      phaseSaving budgetCounters deterministicTrail solverBuild
      dependencyGuard publicFallback ->
    publicFallback :=
  fun trail =>
    ay_brrt_conj_right dependencyGuard publicFallback
      (ay_brrt_conj_right solverBuild
        (AyBRRTConj dependencyGuard publicFallback)
        (ay_brrt_conj_right deterministicTrail
          (AyBRRTConj solverBuild
            (AyBRRTConj dependencyGuard publicFallback))
          (ay_brrt_conj_right budgetCounters
            (AyBRRTConj deterministicTrail
              (AyBRRTConj solverBuild
                (AyBRRTConj dependencyGuard publicFallback)))
            (ay_brrt_conj_right phaseSaving
              (AyBRRTConj budgetCounters
                (AyBRRTConj deterministicTrail
                  (AyBRRTConj solverBuild
                    (AyBRRTConj dependencyGuard publicFallback))))
              (ay_brrt_conj_right clauseActivity
                (AyBRRTConj phaseSaving
                  (AyBRRTConj budgetCounters
                    (AyBRRTConj deterministicTrail
                      (AyBRRTConj solverBuild
                        (AyBRRTConj dependencyGuard publicFallback)))))
                (ay_brrt_conj_right lbdWindow
                  (AyBRRTConj clauseActivity
                    (AyBRRTConj phaseSaving
                      (AyBRRTConj budgetCounters
                        (AyBRRTConj deterministicTrail
                          (AyBRRTConj solverBuild
                            (AyBRRTConj dependencyGuard publicFallback))))))
                  (ay_brrt_reason_trail_tail conflictEvents lbdWindow
                    clauseActivity phaseSaving budgetCounters
                    deterministicTrail solverBuild dependencyGuard
                    publicFallback trail)))))))

theorem ay_brrt_agreement_intro
    (eventMatch : Prop) (lbdMatch : Prop)
    (activityMatch : Prop) (phaseMatch : Prop)
    (budgetMatch : Prop) (trailMatch : Prop)
    (buildMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    eventMatch ->
    lbdMatch ->
    activityMatch ->
    phaseMatch ->
    budgetMatch ->
    trailMatch ->
    buildMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    AyBRRTAgreement eventMatch lbdMatch activityMatch phaseMatch
      budgetMatch trailMatch buildMatch dependencyMatch publicGuardMatch :=
  fun eventH lbdH activityH phaseH budgetH trailH buildH
      dependencyH publicH =>
    ay_brrt_conj_intro eventMatch
      (AyBRRTConj lbdMatch
        (AyBRRTConj activityMatch
          (AyBRRTConj phaseMatch
            (AyBRRTConj budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch)))))))
      eventH
      (ay_brrt_conj_intro lbdMatch
        (AyBRRTConj activityMatch
          (AyBRRTConj phaseMatch
            (AyBRRTConj budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch))))))
        lbdH
        (ay_brrt_conj_intro activityMatch
          (AyBRRTConj phaseMatch
            (AyBRRTConj budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch)))))
          activityH
          (ay_brrt_conj_intro phaseMatch
            (AyBRRTConj budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch))))
            phaseH
            (ay_brrt_conj_intro budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch)))
              budgetH
              (ay_brrt_conj_intro trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch))
                trailH
                (ay_brrt_conj_intro buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch)
                  buildH
                  (ay_brrt_conj_intro dependencyMatch publicGuardMatch
                    dependencyH publicH)))))))

theorem ay_brrt_agreement_events
    (eventMatch : Prop) (lbdMatch : Prop)
    (activityMatch : Prop) (phaseMatch : Prop)
    (budgetMatch : Prop) (trailMatch : Prop)
    (buildMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRRTAgreement eventMatch lbdMatch activityMatch phaseMatch
      budgetMatch trailMatch buildMatch dependencyMatch publicGuardMatch ->
    eventMatch :=
  fun agreement =>
    ay_brrt_conj_left eventMatch
      (AyBRRTConj lbdMatch
        (AyBRRTConj activityMatch
          (AyBRRTConj phaseMatch
            (AyBRRTConj budgetMatch
              (AyBRRTConj trailMatch
                (AyBRRTConj buildMatch
                  (AyBRRTConj dependencyMatch publicGuardMatch)))))))
      agreement

theorem ay_brrt_accepted_replay_intro
    (trail : Prop) (agreement : Prop) (restartHint : Prop) :
    trail ->
    agreement ->
    restartHint ->
    AyBRRTAcceptedReplay trail agreement restartHint :=
  fun trailH agreementH hintH =>
    ay_brrt_conj_intro trail (AyBRRTConj agreement restartHint)
      trailH
      (ay_brrt_conj_intro agreement restartHint agreementH hintH)

theorem ay_brrt_accepted_replay_trail
    (trail : Prop) (agreement : Prop) (restartHint : Prop) :
    AyBRRTAcceptedReplay trail agreement restartHint -> trail :=
  fun accepted =>
    ay_brrt_conj_left trail (AyBRRTConj agreement restartHint)
      accepted

theorem ay_brrt_accepted_replay_agreement
    (trail : Prop) (agreement : Prop) (restartHint : Prop) :
    AyBRRTAcceptedReplay trail agreement restartHint -> agreement :=
  fun accepted =>
    ay_brrt_conj_left agreement restartHint
      (ay_brrt_conj_right trail (AyBRRTConj agreement restartHint)
        accepted)

theorem ay_brrt_accepted_replay_hint
    (trail : Prop) (agreement : Prop) (restartHint : Prop) :
    AyBRRTAcceptedReplay trail agreement restartHint -> restartHint :=
  fun accepted =>
    ay_brrt_conj_right agreement restartHint
      (ay_brrt_conj_right trail (AyBRRTConj agreement restartHint)
        accepted)

theorem ay_brrt_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBRRTPublicReport (AyBRRTOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brrt_conj_intro (AyBRRTOutcome model conflict) formula
      (ay_brrt_disj_left model conflict modelH)
      formulaH

theorem ay_brrt_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBRRTPublicReport (AyBRRTOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brrt_conj_intro (AyBRRTOutcome model conflict) formula
      (ay_brrt_disj_right model conflict conflictH)
      formulaH

theorem ay_brrt_accepted_report_intro
    (replay : Prop) (public : Prop) :
    replay -> public -> AyBRRTAcceptedReport replay public :=
  fun replayH publicH =>
    ay_brrt_conj_intro replay public replayH publicH

theorem ay_brrt_accepted_report_public
    (replay : Prop) (public : Prop) :
    AyBRRTAcceptedReport replay public -> public :=
  fun report =>
    ay_brrt_conj_right replay public report

theorem ay_brrt_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBRRTNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrt_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brrt_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRRTNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brrt_conj_left fallbackPublic diagnostic noClaim

theorem ay_brrt_missing_reason_event_no_claim
    (missingReasonEvent : Prop) (fallbackPublic : Prop) :
    missingReasonEvent ->
    fallbackPublic ->
    AyBRRTNoClaim missingReasonEvent fallbackPublic :=
  fun missingH fallbackH =>
    ay_brrt_no_claim_intro missingReasonEvent fallbackPublic
      missingH fallbackH

theorem ay_brrt_stale_counter_no_claim
    (staleCounter : Prop) (fallbackPublic : Prop) :
    staleCounter ->
    fallbackPublic ->
    AyBRRTNoClaim staleCounter fallbackPublic :=
  fun staleH fallbackH =>
    ay_brrt_no_claim_intro staleCounter fallbackPublic staleH fallbackH

theorem ay_brrt_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    AyBRRTNoClaim replayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_brrt_no_claim_intro replayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_brrt_dependency_guard_failure_no_claim
    (dependencyFailure : Prop) (fallbackPublic : Prop) :
    dependencyFailure ->
    fallbackPublic ->
    AyBRRTNoClaim dependencyFailure fallbackPublic :=
  fun failureH fallbackH =>
    ay_brrt_no_claim_intro dependencyFailure fallbackPublic
      failureH fallbackH

theorem ay_brrt_bad_replay_cannot_publish
    (badReplay : Prop) (fallbackPublic : Prop) :
    badReplay ->
    fallbackPublic ->
    AyBRRTNoClaim badReplay fallbackPublic :=
  fun badH fallbackH =>
    ay_brrt_no_claim_intro badReplay fallbackPublic badH fallbackH

theorem ay_brrt_accepted_replay_guides_sat
    (trail : Prop) (agreement : Prop) (restartHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    trail ->
    agreement ->
    restartHint ->
    model ->
    formula ->
    AyBRRTAcceptedReport
      (AyBRRTAcceptedReplay trail agreement restartHint)
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula) :=
  fun trailH agreementH hintH modelH formulaH =>
    ay_brrt_accepted_report_intro
      (AyBRRTAcceptedReplay trail agreement restartHint)
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula)
      (ay_brrt_accepted_replay_intro trail agreement restartHint
        trailH agreementH hintH)
      (ay_brrt_public_sat_report model conflict formula modelH formulaH)

theorem ay_brrt_accepted_replay_guides_unsat
    (trail : Prop) (agreement : Prop) (restartHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    trail ->
    agreement ->
    restartHint ->
    conflict ->
    formula ->
    AyBRRTAcceptedReport
      (AyBRRTAcceptedReplay trail agreement restartHint)
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula) :=
  fun trailH agreementH hintH conflictH formulaH =>
    ay_brrt_accepted_report_intro
      (AyBRRTAcceptedReplay trail agreement restartHint)
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula)
      (ay_brrt_accepted_replay_intro trail agreement restartHint
        trailH agreementH hintH)
      (ay_brrt_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_brrt_accepted_replay_report_soundness
    (replay : Prop) (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBRRTAcceptedReport replay
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula) ->
    AyBRRTPublicReport (AyBRRTOutcome model conflict) formula :=
  fun report =>
    ay_brrt_accepted_report_public replay
      (AyBRRTPublicReport (AyBRRTOutcome model conflict) formula)
      report

theorem ay_brrt_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRRTNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brrt_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
