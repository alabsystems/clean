-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded variable score heap replay soundness skeleton for ay SAT solving.
-- A variable-ordering heap used for branching is only a performance hint when
-- score updates, heap ordering, decay/bump events, solver build id,
-- deterministic replay, dependency guards, and public soundness guards agree.

def AyBVSHConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBVSHDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBVSHEquisat (before : Prop) (after : Prop) :=
  AyBVSHConj (before -> after) (after -> before)

def AyBVSHHeapEvidence
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :=
  AyBVSHConj scoreUpdates
    (AyBVSHConj heapOrdering
      (AyBVSHConj decayBumpEvents
        (AyBVSHConj solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard)))))

def AyBVSHAgreement
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :=
  AyBVSHConj scoreMatch
    (AyBVSHConj orderingMatch
      (AyBVSHConj eventMatch
        (AyBVSHConj buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch)))))

def AyBVSHAcceptedReplay
    (evidence : Prop) (agreement : Prop) (branchingHint : Prop) :=
  AyBVSHConj evidence (AyBVSHConj agreement branchingHint)

def AyBVSHOutcome (model : Prop) (conflict : Prop) :=
  AyBVSHDisj model conflict

def AyBVSHPublicReport (outcome : Prop) (formula : Prop) :=
  AyBVSHConj outcome formula

def AyBVSHAcceptedReport (replay : Prop) (public : Prop) :=
  AyBVSHConj replay public

def AyBVSHNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBVSHConj fallbackPublic diagnostic

theorem ay_bvsh_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBVSHConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bvsh_conj_left
    (left : Prop) (right : Prop) :
    AyBVSHConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bvsh_conj_right
    (left : Prop) (right : Prop) :
    AyBVSHConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bvsh_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBVSHDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bvsh_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBVSHDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bvsh_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBVSHEquisat before after :=
  fun forward backward =>
    ay_bvsh_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bvsh_equisat_forward
    (before : Prop) (after : Prop) :
    AyBVSHEquisat before after -> before -> after :=
  fun equisat =>
    ay_bvsh_conj_left (before -> after) (after -> before) equisat

theorem ay_bvsh_equisat_backward
    (before : Prop) (after : Prop) :
    AyBVSHEquisat before after -> after -> before :=
  fun equisat =>
    ay_bvsh_conj_right (before -> after) (after -> before) equisat

theorem ay_bvsh_heap_evidence_intro
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    scoreUpdates ->
    heapOrdering ->
    decayBumpEvents ->
    solverBuildId ->
    deterministicReplay ->
    dependencyGuard ->
    publicSoundnessGuard ->
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard :=
  fun scoreH orderingH eventH buildH replayH dependencyH publicH =>
    ay_bvsh_conj_intro scoreUpdates
      (AyBVSHConj heapOrdering
        (AyBVSHConj decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)))))
      scoreH
      (ay_bvsh_conj_intro heapOrdering
        (AyBVSHConj decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard))))
        orderingH
        (ay_bvsh_conj_intro decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)))
          eventH
          (ay_bvsh_conj_intro solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard))
            buildH
            (ay_bvsh_conj_intro deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)
              replayH
              (ay_bvsh_conj_intro dependencyGuard publicSoundnessGuard
                dependencyH publicH)))))

theorem ay_bvsh_heap_evidence_scores
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    scoreUpdates :=
  fun evidence =>
    ay_bvsh_conj_left scoreUpdates
      (AyBVSHConj heapOrdering
        (AyBVSHConj decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bvsh_heap_evidence_tail
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    AyBVSHConj heapOrdering
      (AyBVSHConj decayBumpEvents
        (AyBVSHConj solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard)))) :=
  fun evidence =>
    ay_bvsh_conj_right scoreUpdates
      (AyBVSHConj heapOrdering
        (AyBVSHConj decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bvsh_heap_evidence_ordering
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    heapOrdering :=
  fun evidence =>
    ay_bvsh_conj_left heapOrdering
      (AyBVSHConj decayBumpEvents
        (AyBVSHConj solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard))))
      (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
        decayBumpEvents solverBuildId deterministicReplay
        dependencyGuard publicSoundnessGuard evidence)

theorem ay_bvsh_heap_evidence_events
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    decayBumpEvents :=
  fun evidence =>
    ay_bvsh_conj_left decayBumpEvents
      (AyBVSHConj solverBuildId
        (AyBVSHConj deterministicReplay
          (AyBVSHConj dependencyGuard publicSoundnessGuard)))
      (ay_bvsh_conj_right heapOrdering
        (AyBVSHConj decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard))))
        (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
          decayBumpEvents solverBuildId deterministicReplay
          dependencyGuard publicSoundnessGuard evidence))

theorem ay_bvsh_heap_evidence_build
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    solverBuildId :=
  fun evidence =>
    ay_bvsh_conj_left solverBuildId
      (AyBVSHConj deterministicReplay
        (AyBVSHConj dependencyGuard publicSoundnessGuard))
      (ay_bvsh_conj_right decayBumpEvents
        (AyBVSHConj solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard)))
        (ay_bvsh_conj_right heapOrdering
          (AyBVSHConj decayBumpEvents
            (AyBVSHConj solverBuildId
              (AyBVSHConj deterministicReplay
                (AyBVSHConj dependencyGuard publicSoundnessGuard))))
          (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
            decayBumpEvents solverBuildId deterministicReplay
            dependencyGuard publicSoundnessGuard evidence)))

theorem ay_bvsh_heap_evidence_replay
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    deterministicReplay :=
  fun evidence =>
    ay_bvsh_conj_left deterministicReplay
      (AyBVSHConj dependencyGuard publicSoundnessGuard)
      (ay_bvsh_conj_right solverBuildId
        (AyBVSHConj deterministicReplay
          (AyBVSHConj dependencyGuard publicSoundnessGuard))
        (ay_bvsh_conj_right decayBumpEvents
          (AyBVSHConj solverBuildId
            (AyBVSHConj deterministicReplay
              (AyBVSHConj dependencyGuard publicSoundnessGuard)))
          (ay_bvsh_conj_right heapOrdering
            (AyBVSHConj decayBumpEvents
              (AyBVSHConj solverBuildId
                (AyBVSHConj deterministicReplay
                  (AyBVSHConj dependencyGuard publicSoundnessGuard))))
            (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
              decayBumpEvents solverBuildId deterministicReplay
              dependencyGuard publicSoundnessGuard evidence))))

theorem ay_bvsh_heap_evidence_dependency
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    dependencyGuard :=
  fun evidence =>
    ay_bvsh_conj_left dependencyGuard publicSoundnessGuard
      (ay_bvsh_conj_right deterministicReplay
        (AyBVSHConj dependencyGuard publicSoundnessGuard)
        (ay_bvsh_conj_right solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard))
          (ay_bvsh_conj_right decayBumpEvents
            (AyBVSHConj solverBuildId
              (AyBVSHConj deterministicReplay
                (AyBVSHConj dependencyGuard publicSoundnessGuard)))
            (ay_bvsh_conj_right heapOrdering
              (AyBVSHConj decayBumpEvents
                (AyBVSHConj solverBuildId
                  (AyBVSHConj deterministicReplay
                    (AyBVSHConj dependencyGuard publicSoundnessGuard))))
              (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
                decayBumpEvents solverBuildId deterministicReplay
                dependencyGuard publicSoundnessGuard evidence)))))

theorem ay_bvsh_heap_evidence_public
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_bvsh_conj_right dependencyGuard publicSoundnessGuard
      (ay_bvsh_conj_right deterministicReplay
        (AyBVSHConj dependencyGuard publicSoundnessGuard)
        (ay_bvsh_conj_right solverBuildId
          (AyBVSHConj deterministicReplay
            (AyBVSHConj dependencyGuard publicSoundnessGuard))
          (ay_bvsh_conj_right decayBumpEvents
            (AyBVSHConj solverBuildId
              (AyBVSHConj deterministicReplay
                (AyBVSHConj dependencyGuard publicSoundnessGuard)))
            (ay_bvsh_conj_right heapOrdering
              (AyBVSHConj decayBumpEvents
                (AyBVSHConj solverBuildId
                  (AyBVSHConj deterministicReplay
                    (AyBVSHConj dependencyGuard publicSoundnessGuard))))
              (ay_bvsh_heap_evidence_tail scoreUpdates heapOrdering
                decayBumpEvents solverBuildId deterministicReplay
                dependencyGuard publicSoundnessGuard evidence)))))

theorem ay_bvsh_agreement_intro
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    scoreMatch ->
    orderingMatch ->
    eventMatch ->
    buildMatch ->
    replayMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch :=
  fun scoreH orderingH eventH buildH replayH dependencyH publicH =>
    ay_bvsh_conj_intro scoreMatch
      (AyBVSHConj orderingMatch
        (AyBVSHConj eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)))))
      scoreH
      (ay_bvsh_conj_intro orderingMatch
        (AyBVSHConj eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch))))
        orderingH
        (ay_bvsh_conj_intro eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)))
          eventH
          (ay_bvsh_conj_intro buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch))
            buildH
            (ay_bvsh_conj_intro replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)
              replayH
              (ay_bvsh_conj_intro dependencyMatch publicGuardMatch
                dependencyH publicH)))))

theorem ay_bvsh_agreement_score
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    scoreMatch :=
  fun agreement =>
    ay_bvsh_conj_left scoreMatch
      (AyBVSHConj orderingMatch
        (AyBVSHConj eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)))))
      agreement

theorem ay_bvsh_agreement_tail
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    AyBVSHConj orderingMatch
      (AyBVSHConj eventMatch
        (AyBVSHConj buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch)))) :=
  fun agreement =>
    ay_bvsh_conj_right scoreMatch
      (AyBVSHConj orderingMatch
        (AyBVSHConj eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)))))
      agreement

theorem ay_bvsh_agreement_ordering
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    orderingMatch :=
  fun agreement =>
    ay_bvsh_conj_left orderingMatch
      (AyBVSHConj eventMatch
        (AyBVSHConj buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch))))
      (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
        buildMatch replayMatch dependencyMatch publicGuardMatch agreement)

theorem ay_bvsh_agreement_event
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    eventMatch :=
  fun agreement =>
    ay_bvsh_conj_left eventMatch
      (AyBVSHConj buildMatch
        (AyBVSHConj replayMatch
          (AyBVSHConj dependencyMatch publicGuardMatch)))
      (ay_bvsh_conj_right orderingMatch
        (AyBVSHConj eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch))))
        (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
          buildMatch replayMatch dependencyMatch publicGuardMatch
          agreement))

theorem ay_bvsh_agreement_build
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    buildMatch :=
  fun agreement =>
    ay_bvsh_conj_left buildMatch
      (AyBVSHConj replayMatch
        (AyBVSHConj dependencyMatch publicGuardMatch))
      (ay_bvsh_conj_right eventMatch
        (AyBVSHConj buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch)))
        (ay_bvsh_conj_right orderingMatch
          (AyBVSHConj eventMatch
            (AyBVSHConj buildMatch
              (AyBVSHConj replayMatch
                (AyBVSHConj dependencyMatch publicGuardMatch))))
          (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
            buildMatch replayMatch dependencyMatch publicGuardMatch
            agreement)))

theorem ay_bvsh_agreement_replay
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    replayMatch :=
  fun agreement =>
    ay_bvsh_conj_left replayMatch
      (AyBVSHConj dependencyMatch publicGuardMatch)
      (ay_bvsh_conj_right buildMatch
        (AyBVSHConj replayMatch
          (AyBVSHConj dependencyMatch publicGuardMatch))
        (ay_bvsh_conj_right eventMatch
          (AyBVSHConj buildMatch
            (AyBVSHConj replayMatch
              (AyBVSHConj dependencyMatch publicGuardMatch)))
          (ay_bvsh_conj_right orderingMatch
            (AyBVSHConj eventMatch
              (AyBVSHConj buildMatch
                (AyBVSHConj replayMatch
                  (AyBVSHConj dependencyMatch publicGuardMatch))))
            (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
              buildMatch replayMatch dependencyMatch publicGuardMatch
              agreement))))

theorem ay_bvsh_agreement_dependency
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_bvsh_conj_left dependencyMatch publicGuardMatch
      (ay_bvsh_conj_right replayMatch
        (AyBVSHConj dependencyMatch publicGuardMatch)
        (ay_bvsh_conj_right buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch))
          (ay_bvsh_conj_right eventMatch
            (AyBVSHConj buildMatch
              (AyBVSHConj replayMatch
                (AyBVSHConj dependencyMatch publicGuardMatch)))
            (ay_bvsh_conj_right orderingMatch
              (AyBVSHConj eventMatch
                (AyBVSHConj buildMatch
                  (AyBVSHConj replayMatch
                    (AyBVSHConj dependencyMatch publicGuardMatch))))
              (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
                buildMatch replayMatch dependencyMatch publicGuardMatch
                agreement)))))

theorem ay_bvsh_agreement_public
    (scoreMatch : Prop) (orderingMatch : Prop)
    (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    publicGuardMatch :=
  fun agreement =>
    ay_bvsh_conj_right dependencyMatch publicGuardMatch
      (ay_bvsh_conj_right replayMatch
        (AyBVSHConj dependencyMatch publicGuardMatch)
        (ay_bvsh_conj_right buildMatch
          (AyBVSHConj replayMatch
            (AyBVSHConj dependencyMatch publicGuardMatch))
          (ay_bvsh_conj_right eventMatch
            (AyBVSHConj buildMatch
              (AyBVSHConj replayMatch
                (AyBVSHConj dependencyMatch publicGuardMatch)))
            (ay_bvsh_conj_right orderingMatch
              (AyBVSHConj eventMatch
                (AyBVSHConj buildMatch
                  (AyBVSHConj replayMatch
                    (AyBVSHConj dependencyMatch publicGuardMatch))))
              (ay_bvsh_agreement_tail scoreMatch orderingMatch eventMatch
                buildMatch replayMatch dependencyMatch publicGuardMatch
                agreement)))))

theorem ay_bvsh_accepted_replay_intro
    (evidence : Prop) (agreement : Prop) (branchingHint : Prop) :
    evidence ->
    agreement ->
    branchingHint ->
    AyBVSHAcceptedReplay evidence agreement branchingHint :=
  fun evidenceH agreementH hintH =>
    ay_bvsh_conj_intro evidence (AyBVSHConj agreement branchingHint)
      evidenceH
      (ay_bvsh_conj_intro agreement branchingHint agreementH hintH)

theorem ay_bvsh_accepted_replay_evidence
    (evidence : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBVSHAcceptedReplay evidence agreement branchingHint -> evidence :=
  fun accepted =>
    ay_bvsh_conj_left evidence (AyBVSHConj agreement branchingHint)
      accepted

theorem ay_bvsh_accepted_replay_agreement
    (evidence : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBVSHAcceptedReplay evidence agreement branchingHint -> agreement :=
  fun accepted =>
    ay_bvsh_conj_left agreement branchingHint
      (ay_bvsh_conj_right evidence (AyBVSHConj agreement branchingHint)
        accepted)

theorem ay_bvsh_accepted_replay_hint
    (evidence : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBVSHAcceptedReplay evidence agreement branchingHint ->
    branchingHint :=
  fun accepted =>
    ay_bvsh_conj_right agreement branchingHint
      (ay_bvsh_conj_right evidence (AyBVSHConj agreement branchingHint)
        accepted)

theorem ay_bvsh_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBVSHPublicReport (AyBVSHOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bvsh_conj_intro (AyBVSHOutcome model conflict) formula
      (ay_bvsh_disj_left model conflict modelH)
      formulaH

theorem ay_bvsh_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBVSHPublicReport (AyBVSHOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bvsh_conj_intro (AyBVSHOutcome model conflict) formula
      (ay_bvsh_disj_right model conflict conflictH)
      formulaH

theorem ay_bvsh_accepted_report_intro
    (replay : Prop) (public : Prop) :
    replay -> public -> AyBVSHAcceptedReport replay public :=
  fun replayH publicH =>
    ay_bvsh_conj_intro replay public replayH publicH

theorem ay_bvsh_accepted_report_public
    (replay : Prop) (public : Prop) :
    AyBVSHAcceptedReport replay public -> public :=
  fun report =>
    ay_bvsh_conj_right replay public report

theorem ay_bvsh_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBVSHNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvsh_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bvsh_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBVSHNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bvsh_conj_left fallbackPublic diagnostic noClaim

theorem ay_bvsh_stale_heap_no_claim
    (staleHeap : Prop) (fallbackPublic : Prop) :
    staleHeap ->
    fallbackPublic ->
    AyBVSHNoClaim staleHeap fallbackPublic :=
  fun staleH fallbackH =>
    ay_bvsh_no_claim_intro staleHeap fallbackPublic staleH fallbackH

theorem ay_bvsh_ordering_mismatch_no_claim
    (orderingMismatch : Prop) (fallbackPublic : Prop) :
    orderingMismatch ->
    fallbackPublic ->
    AyBVSHNoClaim orderingMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bvsh_no_claim_intro orderingMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bvsh_missing_score_update_no_claim
    (missingUpdate : Prop) (fallbackPublic : Prop) :
    missingUpdate ->
    fallbackPublic ->
    AyBVSHNoClaim missingUpdate fallbackPublic :=
  fun missingH fallbackH =>
    ay_bvsh_no_claim_intro missingUpdate fallbackPublic
      missingH fallbackH

theorem ay_bvsh_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    AyBVSHNoClaim replayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bvsh_no_claim_intro replayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bvsh_dependency_guard_failure_no_claim
    (dependencyFailure : Prop) (fallbackPublic : Prop) :
    dependencyFailure ->
    fallbackPublic ->
    AyBVSHNoClaim dependencyFailure fallbackPublic :=
  fun failureH fallbackH =>
    ay_bvsh_no_claim_intro dependencyFailure fallbackPublic
      failureH fallbackH

theorem ay_bvsh_bad_heap_cannot_publish
    (badHeap : Prop) (fallbackPublic : Prop) :
    badHeap ->
    fallbackPublic ->
    AyBVSHNoClaim badHeap fallbackPublic :=
  fun badH fallbackH =>
    ay_bvsh_no_claim_intro badHeap fallbackPublic badH fallbackH

theorem ay_bvsh_accepted_heap_guides_sat
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) (scoreMatch : Prop)
    (orderingMatch : Prop) (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) (branchingHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    branchingHint ->
    model ->
    formula ->
    AyBVSHAcceptedReport
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula) :=
  fun evidence agreement hintH modelH formulaH =>
    ay_bvsh_accepted_report_intro
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula)
      (ay_bvsh_accepted_replay_intro
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint
        evidence agreement hintH)
      (ay_bvsh_public_sat_report model conflict formula modelH formulaH)

theorem ay_bvsh_accepted_heap_guides_unsat
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) (scoreMatch : Prop)
    (orderingMatch : Prop) (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) (branchingHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
      solverBuildId deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
      replayMatch dependencyMatch publicGuardMatch ->
    branchingHint ->
    conflict ->
    formula ->
    AyBVSHAcceptedReport
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula) :=
  fun evidence agreement hintH conflictH formulaH =>
    ay_bvsh_accepted_report_intro
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula)
      (ay_bvsh_accepted_replay_intro
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint
        evidence agreement hintH)
      (ay_bvsh_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bvsh_accepted_heap_report_soundness
    (scoreUpdates : Prop) (heapOrdering : Prop)
    (decayBumpEvents : Prop) (solverBuildId : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) (scoreMatch : Prop)
    (orderingMatch : Prop) (eventMatch : Prop) (buildMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) (branchingHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBVSHAcceptedReport
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula) ->
    AyBVSHPublicReport (AyBVSHOutcome model conflict) formula :=
  fun report =>
    ay_bvsh_accepted_report_public
      (AyBVSHAcceptedReplay
        (AyBVSHHeapEvidence scoreUpdates heapOrdering decayBumpEvents
          solverBuildId deterministicReplay dependencyGuard
          publicSoundnessGuard)
        (AyBVSHAgreement scoreMatch orderingMatch eventMatch buildMatch
          replayMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBVSHPublicReport (AyBVSHOutcome model conflict) formula)
      report

theorem ay_bvsh_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBVSHNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bvsh_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
