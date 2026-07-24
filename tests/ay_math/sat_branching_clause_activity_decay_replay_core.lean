-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause/variable activity decay replay soundness skeleton for ay SAT
-- solving. Activity scores used for branching and clause retention are only
-- performance hints when decay schedule, bump events, solver build id,
-- deterministic replay, retained dependencies, and public soundness agree.

def AyBCADConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBCADDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBCADEquisat (before : Prop) (after : Prop) :=
  AyBCADConj (before -> after) (after -> before)

def AyBCADReplayEvidence
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :=
  AyBCADConj decaySchedule
    (AyBCADConj bumpEvents
      (AyBCADConj solverBuildId
        (AyBCADConj deterministicReplay
          (AyBCADConj retainedDependencies publicSoundnessGuard))))

def AyBCADAgreement
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :=
  AyBCADConj decayMatch
    (AyBCADConj bumpMatch
      (AyBCADConj buildMatch
        (AyBCADConj replayMatch
          (AyBCADConj dependencyMatch publicGuardMatch))))

def AyBCADAcceptedReplay
    (evidence : Prop) (agreement : Prop) (activityHint : Prop) :=
  AyBCADConj evidence (AyBCADConj agreement activityHint)

def AyBCADOutcome (model : Prop) (conflict : Prop) :=
  AyBCADDisj model conflict

def AyBCADPublicReport (outcome : Prop) (formula : Prop) :=
  AyBCADConj outcome formula

def AyBCADAcceptedReport (replay : Prop) (public : Prop) :=
  AyBCADConj replay public

def AyBCADNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBCADConj fallbackPublic diagnostic

theorem ay_bcad_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBCADConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcad_conj_left
    (left : Prop) (right : Prop) :
    AyBCADConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcad_conj_right
    (left : Prop) (right : Prop) :
    AyBCADConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcad_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBCADDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcad_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBCADDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcad_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBCADEquisat before after :=
  fun forward backward =>
    ay_bcad_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcad_equisat_forward
    (before : Prop) (after : Prop) :
    AyBCADEquisat before after -> before -> after :=
  fun equisat =>
    ay_bcad_conj_left (before -> after) (after -> before) equisat

theorem ay_bcad_equisat_backward
    (before : Prop) (after : Prop) :
    AyBCADEquisat before after -> after -> before :=
  fun equisat =>
    ay_bcad_conj_right (before -> after) (after -> before) equisat

theorem ay_bcad_replay_evidence_intro
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    decaySchedule ->
    bumpEvents ->
    solverBuildId ->
    deterministicReplay ->
    retainedDependencies ->
    publicSoundnessGuard ->
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard :=
  fun decayH bumpH buildH replayH dependencyH publicH =>
    ay_bcad_conj_intro decaySchedule
      (AyBCADConj bumpEvents
        (AyBCADConj solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))))
      decayH
      (ay_bcad_conj_intro bumpEvents
        (AyBCADConj solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard)))
        bumpH
        (ay_bcad_conj_intro solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))
          buildH
          (ay_bcad_conj_intro deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard)
            replayH
            (ay_bcad_conj_intro retainedDependencies publicSoundnessGuard
              dependencyH publicH))))

theorem ay_bcad_replay_evidence_decay
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    decaySchedule :=
  fun evidence =>
    ay_bcad_conj_left decaySchedule
      (AyBCADConj bumpEvents
        (AyBCADConj solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))))
      evidence

theorem ay_bcad_replay_evidence_tail
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    AyBCADConj bumpEvents
      (AyBCADConj solverBuildId
        (AyBCADConj deterministicReplay
          (AyBCADConj retainedDependencies publicSoundnessGuard))) :=
  fun evidence =>
    ay_bcad_conj_right decaySchedule
      (AyBCADConj bumpEvents
        (AyBCADConj solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))))
      evidence

theorem ay_bcad_replay_evidence_bumps
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    bumpEvents :=
  fun evidence =>
    ay_bcad_conj_left bumpEvents
      (AyBCADConj solverBuildId
        (AyBCADConj deterministicReplay
          (AyBCADConj retainedDependencies publicSoundnessGuard)))
      (ay_bcad_replay_evidence_tail decaySchedule bumpEvents
        solverBuildId deterministicReplay retainedDependencies
        publicSoundnessGuard evidence)

theorem ay_bcad_replay_evidence_build
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    solverBuildId :=
  fun evidence =>
    ay_bcad_conj_left solverBuildId
      (AyBCADConj deterministicReplay
        (AyBCADConj retainedDependencies publicSoundnessGuard))
      (ay_bcad_conj_right bumpEvents
        (AyBCADConj solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard)))
        (ay_bcad_replay_evidence_tail decaySchedule bumpEvents
          solverBuildId deterministicReplay retainedDependencies
          publicSoundnessGuard evidence))

theorem ay_bcad_replay_evidence_replay
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    deterministicReplay :=
  fun evidence =>
    ay_bcad_conj_left deterministicReplay
      (AyBCADConj retainedDependencies publicSoundnessGuard)
      (ay_bcad_conj_right solverBuildId
        (AyBCADConj deterministicReplay
          (AyBCADConj retainedDependencies publicSoundnessGuard))
        (ay_bcad_conj_right bumpEvents
          (AyBCADConj solverBuildId
            (AyBCADConj deterministicReplay
              (AyBCADConj retainedDependencies publicSoundnessGuard)))
          (ay_bcad_replay_evidence_tail decaySchedule bumpEvents
            solverBuildId deterministicReplay retainedDependencies
            publicSoundnessGuard evidence)))

theorem ay_bcad_replay_evidence_dependencies
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    retainedDependencies :=
  fun evidence =>
    ay_bcad_conj_left retainedDependencies publicSoundnessGuard
      (ay_bcad_conj_right deterministicReplay
        (AyBCADConj retainedDependencies publicSoundnessGuard)
        (ay_bcad_conj_right solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))
          (ay_bcad_conj_right bumpEvents
            (AyBCADConj solverBuildId
              (AyBCADConj deterministicReplay
                (AyBCADConj retainedDependencies publicSoundnessGuard)))
            (ay_bcad_replay_evidence_tail decaySchedule bumpEvents
              solverBuildId deterministicReplay retainedDependencies
              publicSoundnessGuard evidence))))

theorem ay_bcad_replay_evidence_public
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_bcad_conj_right retainedDependencies publicSoundnessGuard
      (ay_bcad_conj_right deterministicReplay
        (AyBCADConj retainedDependencies publicSoundnessGuard)
        (ay_bcad_conj_right solverBuildId
          (AyBCADConj deterministicReplay
            (AyBCADConj retainedDependencies publicSoundnessGuard))
          (ay_bcad_conj_right bumpEvents
            (AyBCADConj solverBuildId
              (AyBCADConj deterministicReplay
                (AyBCADConj retainedDependencies publicSoundnessGuard)))
            (ay_bcad_replay_evidence_tail decaySchedule bumpEvents
              solverBuildId deterministicReplay retainedDependencies
              publicSoundnessGuard evidence))))

theorem ay_bcad_agreement_intro
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    decayMatch ->
    bumpMatch ->
    buildMatch ->
    replayMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch :=
  fun decayH bumpH buildH replayH dependencyH publicH =>
    ay_bcad_conj_intro decayMatch
      (AyBCADConj bumpMatch
        (AyBCADConj buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))))
      decayH
      (ay_bcad_conj_intro bumpMatch
        (AyBCADConj buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch)))
        bumpH
        (ay_bcad_conj_intro buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))
          buildH
          (ay_bcad_conj_intro replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch)
            replayH
            (ay_bcad_conj_intro dependencyMatch publicGuardMatch
              dependencyH publicH))))

theorem ay_bcad_agreement_decay
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    decayMatch :=
  fun agreement =>
    ay_bcad_conj_left decayMatch
      (AyBCADConj bumpMatch
        (AyBCADConj buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))))
      agreement

theorem ay_bcad_agreement_tail
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    AyBCADConj bumpMatch
      (AyBCADConj buildMatch
        (AyBCADConj replayMatch
          (AyBCADConj dependencyMatch publicGuardMatch))) :=
  fun agreement =>
    ay_bcad_conj_right decayMatch
      (AyBCADConj bumpMatch
        (AyBCADConj buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))))
      agreement

theorem ay_bcad_agreement_bump
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    bumpMatch :=
  fun agreement =>
    ay_bcad_conj_left bumpMatch
      (AyBCADConj buildMatch
        (AyBCADConj replayMatch
          (AyBCADConj dependencyMatch publicGuardMatch)))
      (ay_bcad_agreement_tail decayMatch bumpMatch buildMatch replayMatch
        dependencyMatch publicGuardMatch agreement)

theorem ay_bcad_agreement_build
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    buildMatch :=
  fun agreement =>
    ay_bcad_conj_left buildMatch
      (AyBCADConj replayMatch
        (AyBCADConj dependencyMatch publicGuardMatch))
      (ay_bcad_conj_right bumpMatch
        (AyBCADConj buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch)))
        (ay_bcad_agreement_tail decayMatch bumpMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch agreement))

theorem ay_bcad_agreement_replay
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    replayMatch :=
  fun agreement =>
    ay_bcad_conj_left replayMatch
      (AyBCADConj dependencyMatch publicGuardMatch)
      (ay_bcad_conj_right buildMatch
        (AyBCADConj replayMatch
          (AyBCADConj dependencyMatch publicGuardMatch))
        (ay_bcad_conj_right bumpMatch
          (AyBCADConj buildMatch
            (AyBCADConj replayMatch
              (AyBCADConj dependencyMatch publicGuardMatch)))
          (ay_bcad_agreement_tail decayMatch bumpMatch buildMatch
            replayMatch dependencyMatch publicGuardMatch agreement)))

theorem ay_bcad_agreement_dependency
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_bcad_conj_left dependencyMatch publicGuardMatch
      (ay_bcad_conj_right replayMatch
        (AyBCADConj dependencyMatch publicGuardMatch)
        (ay_bcad_conj_right buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))
          (ay_bcad_conj_right bumpMatch
            (AyBCADConj buildMatch
              (AyBCADConj replayMatch
                (AyBCADConj dependencyMatch publicGuardMatch)))
            (ay_bcad_agreement_tail decayMatch bumpMatch buildMatch
              replayMatch dependencyMatch publicGuardMatch agreement))))

theorem ay_bcad_agreement_public
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    publicGuardMatch :=
  fun agreement =>
    ay_bcad_conj_right dependencyMatch publicGuardMatch
      (ay_bcad_conj_right replayMatch
        (AyBCADConj dependencyMatch publicGuardMatch)
        (ay_bcad_conj_right buildMatch
          (AyBCADConj replayMatch
            (AyBCADConj dependencyMatch publicGuardMatch))
          (ay_bcad_conj_right bumpMatch
            (AyBCADConj buildMatch
              (AyBCADConj replayMatch
                (AyBCADConj dependencyMatch publicGuardMatch)))
            (ay_bcad_agreement_tail decayMatch bumpMatch buildMatch
              replayMatch dependencyMatch publicGuardMatch agreement))))

theorem ay_bcad_accepted_replay_intro
    (evidence : Prop) (agreement : Prop) (activityHint : Prop) :
    evidence ->
    agreement ->
    activityHint ->
    AyBCADAcceptedReplay evidence agreement activityHint :=
  fun evidenceH agreementH hintH =>
    ay_bcad_conj_intro evidence (AyBCADConj agreement activityHint)
      evidenceH
      (ay_bcad_conj_intro agreement activityHint agreementH hintH)

theorem ay_bcad_accepted_replay_evidence
    (evidence : Prop) (agreement : Prop) (activityHint : Prop) :
    AyBCADAcceptedReplay evidence agreement activityHint -> evidence :=
  fun accepted =>
    ay_bcad_conj_left evidence (AyBCADConj agreement activityHint)
      accepted

theorem ay_bcad_accepted_replay_agreement
    (evidence : Prop) (agreement : Prop) (activityHint : Prop) :
    AyBCADAcceptedReplay evidence agreement activityHint -> agreement :=
  fun accepted =>
    ay_bcad_conj_left agreement activityHint
      (ay_bcad_conj_right evidence (AyBCADConj agreement activityHint)
        accepted)

theorem ay_bcad_accepted_replay_hint
    (evidence : Prop) (agreement : Prop) (activityHint : Prop) :
    AyBCADAcceptedReplay evidence agreement activityHint -> activityHint :=
  fun accepted =>
    ay_bcad_conj_right agreement activityHint
      (ay_bcad_conj_right evidence (AyBCADConj agreement activityHint)
        accepted)

theorem ay_bcad_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBCADPublicReport (AyBCADOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcad_conj_intro (AyBCADOutcome model conflict) formula
      (ay_bcad_disj_left model conflict modelH)
      formulaH

theorem ay_bcad_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBCADPublicReport (AyBCADOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcad_conj_intro (AyBCADOutcome model conflict) formula
      (ay_bcad_disj_right model conflict conflictH)
      formulaH

theorem ay_bcad_accepted_report_intro
    (replay : Prop) (public : Prop) :
    replay -> public -> AyBCADAcceptedReport replay public :=
  fun replayH publicH =>
    ay_bcad_conj_intro replay public replayH publicH

theorem ay_bcad_accepted_report_public
    (replay : Prop) (public : Prop) :
    AyBCADAcceptedReport replay public -> public :=
  fun report =>
    ay_bcad_conj_right replay public report

theorem ay_bcad_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBCADNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcad_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcad_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCADNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcad_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcad_stale_scores_no_claim
    (staleScores : Prop) (fallbackPublic : Prop) :
    staleScores ->
    fallbackPublic ->
    AyBCADNoClaim staleScores fallbackPublic :=
  fun staleH fallbackH =>
    ay_bcad_no_claim_intro staleScores fallbackPublic staleH fallbackH

theorem ay_bcad_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    AyBCADNoClaim replayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcad_no_claim_intro replayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcad_missing_bump_no_claim
    (missingBump : Prop) (fallbackPublic : Prop) :
    missingBump ->
    fallbackPublic ->
    AyBCADNoClaim missingBump fallbackPublic :=
  fun missingH fallbackH =>
    ay_bcad_no_claim_intro missingBump fallbackPublic missingH fallbackH

theorem ay_bcad_dependency_mismatch_no_claim
    (dependencyMismatch : Prop) (fallbackPublic : Prop) :
    dependencyMismatch ->
    fallbackPublic ->
    AyBCADNoClaim dependencyMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcad_no_claim_intro dependencyMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcad_build_mismatch_no_claim
    (buildMismatch : Prop) (fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    AyBCADNoClaim buildMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcad_no_claim_intro buildMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcad_bad_replay_cannot_publish
    (badReplay : Prop) (fallbackPublic : Prop) :
    badReplay ->
    fallbackPublic ->
    AyBCADNoClaim badReplay fallbackPublic :=
  fun badH fallbackH =>
    ay_bcad_no_claim_intro badReplay fallbackPublic badH fallbackH

theorem ay_bcad_accepted_replay_guides_sat
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop)
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (activityHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    activityHint ->
    model ->
    formula ->
    AyBCADAcceptedReport
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula) :=
  fun evidence agreement hintH modelH formulaH =>
    ay_bcad_accepted_report_intro
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula)
      (ay_bcad_accepted_replay_intro
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint
        evidence agreement hintH)
      (ay_bcad_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcad_accepted_replay_guides_unsat
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop)
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (activityHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
      deterministicReplay retainedDependencies publicSoundnessGuard ->
    AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
      dependencyMatch publicGuardMatch ->
    activityHint ->
    conflict ->
    formula ->
    AyBCADAcceptedReport
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula) :=
  fun evidence agreement hintH conflictH formulaH =>
    ay_bcad_accepted_report_intro
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula)
      (ay_bcad_accepted_replay_intro
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint
        evidence agreement hintH)
      (ay_bcad_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bcad_accepted_replay_report_soundness
    (decaySchedule : Prop) (bumpEvents : Prop)
    (solverBuildId : Prop) (deterministicReplay : Prop)
    (retainedDependencies : Prop) (publicSoundnessGuard : Prop)
    (decayMatch : Prop) (bumpMatch : Prop)
    (buildMatch : Prop) (replayMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (activityHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBCADAcceptedReport
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula) ->
    AyBCADPublicReport (AyBCADOutcome model conflict) formula :=
  fun report =>
    ay_bcad_accepted_report_public
      (AyBCADAcceptedReplay
        (AyBCADReplayEvidence decaySchedule bumpEvents solverBuildId
          deterministicReplay retainedDependencies publicSoundnessGuard)
        (AyBCADAgreement decayMatch bumpMatch buildMatch replayMatch
          dependencyMatch publicGuardMatch)
        activityHint)
      (AyBCADPublicReport (AyBCADOutcome model conflict) formula)
      report

theorem ay_bcad_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCADNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcad_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
