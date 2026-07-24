-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart phase-saving guard soundness skeleton for ay SAT solving.
-- Phase-saving state reused across aggressive restarts is a performance hint
-- only when phase snapshot lineage, assignment compatibility, restart policy
-- replay, formula fingerprint, learned-clause dependency guard, and public
-- soundness guard agree.

def AyBRPSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBRPSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBRPSEquisat (before : Prop) (after : Prop) :=
  AyBRPSConj (before -> after) (after -> before)

def AyBRPSPhaseGuard
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :=
  AyBRPSConj phaseLineage
    (AyBRPSConj assignmentCompatibility
      (AyBRPSConj restartReplay
        (AyBRPSConj formulaFingerprint
          (AyBRPSConj dependencyGuard publicSoundnessGuard))))

def AyBRPSAgreement
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :=
  AyBRPSConj lineageMatch
    (AyBRPSConj assignmentMatch
      (AyBRPSConj replayMatch
        (AyBRPSConj fingerprintMatch
          (AyBRPSConj dependencyMatch publicGuardMatch))))

def AyBRPSAcceptedReuse
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :=
  AyBRPSConj guard (AyBRPSConj agreement branchingHint)

def AyBRPSOutcome (model : Prop) (conflict : Prop) :=
  AyBRPSDisj model conflict

def AyBRPSPublicReport (outcome : Prop) (formula : Prop) :=
  AyBRPSConj outcome formula

def AyBRPSAcceptedReport (reuse : Prop) (public : Prop) :=
  AyBRPSConj reuse public

def AyBRPSNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBRPSConj fallbackPublic diagnostic

theorem ay_brps_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBRPSConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brps_conj_left
    (left : Prop) (right : Prop) :
    AyBRPSConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brps_conj_right
    (left : Prop) (right : Prop) :
    AyBRPSConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brps_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBRPSDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brps_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBRPSDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brps_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBRPSEquisat before after :=
  fun forward backward =>
    ay_brps_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brps_equisat_forward
    (before : Prop) (after : Prop) :
    AyBRPSEquisat before after -> before -> after :=
  fun equisat =>
    ay_brps_conj_left (before -> after) (after -> before) equisat

theorem ay_brps_equisat_backward
    (before : Prop) (after : Prop) :
    AyBRPSEquisat before after -> after -> before :=
  fun equisat =>
    ay_brps_conj_right (before -> after) (after -> before) equisat

theorem ay_brps_phase_guard_intro
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    phaseLineage ->
    assignmentCompatibility ->
    restartReplay ->
    formulaFingerprint ->
    dependencyGuard ->
    publicSoundnessGuard ->
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard :=
  fun lineageH assignmentH replayH fingerprintH dependencyH publicH =>
    ay_brps_conj_intro phaseLineage
      (AyBRPSConj assignmentCompatibility
        (AyBRPSConj restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))))
      lineageH
      (ay_brps_conj_intro assignmentCompatibility
        (AyBRPSConj restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard)))
        assignmentH
        (ay_brps_conj_intro restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))
          replayH
          (ay_brps_conj_intro formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard)
            fingerprintH
            (ay_brps_conj_intro dependencyGuard publicSoundnessGuard
              dependencyH publicH))))

theorem ay_brps_phase_guard_lineage
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    phaseLineage :=
  fun guard =>
    ay_brps_conj_left phaseLineage
      (AyBRPSConj assignmentCompatibility
        (AyBRPSConj restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))))
      guard

theorem ay_brps_phase_guard_tail
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    AyBRPSConj assignmentCompatibility
      (AyBRPSConj restartReplay
        (AyBRPSConj formulaFingerprint
          (AyBRPSConj dependencyGuard publicSoundnessGuard))) :=
  fun guard =>
    ay_brps_conj_right phaseLineage
      (AyBRPSConj assignmentCompatibility
        (AyBRPSConj restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))))
      guard

theorem ay_brps_phase_guard_assignment
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    assignmentCompatibility :=
  fun guard =>
    ay_brps_conj_left assignmentCompatibility
      (AyBRPSConj restartReplay
        (AyBRPSConj formulaFingerprint
          (AyBRPSConj dependencyGuard publicSoundnessGuard)))
      (ay_brps_phase_guard_tail phaseLineage assignmentCompatibility
        restartReplay formulaFingerprint dependencyGuard
        publicSoundnessGuard guard)

theorem ay_brps_phase_guard_replay
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    restartReplay :=
  fun guard =>
    ay_brps_conj_left restartReplay
      (AyBRPSConj formulaFingerprint
        (AyBRPSConj dependencyGuard publicSoundnessGuard))
      (ay_brps_conj_right assignmentCompatibility
        (AyBRPSConj restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard)))
        (ay_brps_phase_guard_tail phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard guard))

theorem ay_brps_phase_guard_fingerprint
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    formulaFingerprint :=
  fun guard =>
    ay_brps_conj_left formulaFingerprint
      (AyBRPSConj dependencyGuard publicSoundnessGuard)
      (ay_brps_conj_right restartReplay
        (AyBRPSConj formulaFingerprint
          (AyBRPSConj dependencyGuard publicSoundnessGuard))
        (ay_brps_conj_right assignmentCompatibility
          (AyBRPSConj restartReplay
            (AyBRPSConj formulaFingerprint
              (AyBRPSConj dependencyGuard publicSoundnessGuard)))
          (ay_brps_phase_guard_tail phaseLineage assignmentCompatibility
            restartReplay formulaFingerprint dependencyGuard
            publicSoundnessGuard guard)))

theorem ay_brps_phase_guard_dependency
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    dependencyGuard :=
  fun guard =>
    ay_brps_conj_left dependencyGuard publicSoundnessGuard
      (ay_brps_conj_right formulaFingerprint
        (AyBRPSConj dependencyGuard publicSoundnessGuard)
        (ay_brps_conj_right restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))
          (ay_brps_conj_right assignmentCompatibility
            (AyBRPSConj restartReplay
              (AyBRPSConj formulaFingerprint
                (AyBRPSConj dependencyGuard publicSoundnessGuard)))
            (ay_brps_phase_guard_tail phaseLineage assignmentCompatibility
              restartReplay formulaFingerprint dependencyGuard
              publicSoundnessGuard guard))))

theorem ay_brps_phase_guard_public
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun guard =>
    ay_brps_conj_right dependencyGuard publicSoundnessGuard
      (ay_brps_conj_right formulaFingerprint
        (AyBRPSConj dependencyGuard publicSoundnessGuard)
        (ay_brps_conj_right restartReplay
          (AyBRPSConj formulaFingerprint
            (AyBRPSConj dependencyGuard publicSoundnessGuard))
          (ay_brps_conj_right assignmentCompatibility
            (AyBRPSConj restartReplay
              (AyBRPSConj formulaFingerprint
                (AyBRPSConj dependencyGuard publicSoundnessGuard)))
            (ay_brps_phase_guard_tail phaseLineage assignmentCompatibility
              restartReplay formulaFingerprint dependencyGuard
              publicSoundnessGuard guard))))

theorem ay_brps_agreement_intro
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    lineageMatch ->
    assignmentMatch ->
    replayMatch ->
    fingerprintMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch :=
  fun lineageH assignmentH replayH fingerprintH dependencyH publicH =>
    ay_brps_conj_intro lineageMatch
      (AyBRPSConj assignmentMatch
        (AyBRPSConj replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))))
      lineageH
      (ay_brps_conj_intro assignmentMatch
        (AyBRPSConj replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch)))
        assignmentH
        (ay_brps_conj_intro replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))
          replayH
          (ay_brps_conj_intro fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch)
            fingerprintH
            (ay_brps_conj_intro dependencyMatch publicGuardMatch
              dependencyH publicH))))

theorem ay_brps_agreement_lineage
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    lineageMatch :=
  fun agreement =>
    ay_brps_conj_left lineageMatch
      (AyBRPSConj assignmentMatch
        (AyBRPSConj replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))))
      agreement

theorem ay_brps_agreement_tail
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    AyBRPSConj assignmentMatch
      (AyBRPSConj replayMatch
        (AyBRPSConj fingerprintMatch
          (AyBRPSConj dependencyMatch publicGuardMatch))) :=
  fun agreement =>
    ay_brps_conj_right lineageMatch
      (AyBRPSConj assignmentMatch
        (AyBRPSConj replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))))
      agreement

theorem ay_brps_agreement_assignment
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    assignmentMatch :=
  fun agreement =>
    ay_brps_conj_left assignmentMatch
      (AyBRPSConj replayMatch
        (AyBRPSConj fingerprintMatch
          (AyBRPSConj dependencyMatch publicGuardMatch)))
      (ay_brps_agreement_tail lineageMatch assignmentMatch replayMatch
        fingerprintMatch dependencyMatch publicGuardMatch agreement)

theorem ay_brps_agreement_replay
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    replayMatch :=
  fun agreement =>
    ay_brps_conj_left replayMatch
      (AyBRPSConj fingerprintMatch
        (AyBRPSConj dependencyMatch publicGuardMatch))
      (ay_brps_conj_right assignmentMatch
        (AyBRPSConj replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch)))
        (ay_brps_agreement_tail lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch agreement))

theorem ay_brps_agreement_fingerprint
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    fingerprintMatch :=
  fun agreement =>
    ay_brps_conj_left fingerprintMatch
      (AyBRPSConj dependencyMatch publicGuardMatch)
      (ay_brps_conj_right replayMatch
        (AyBRPSConj fingerprintMatch
          (AyBRPSConj dependencyMatch publicGuardMatch))
        (ay_brps_conj_right assignmentMatch
          (AyBRPSConj replayMatch
            (AyBRPSConj fingerprintMatch
              (AyBRPSConj dependencyMatch publicGuardMatch)))
          (ay_brps_agreement_tail lineageMatch assignmentMatch replayMatch
            fingerprintMatch dependencyMatch publicGuardMatch agreement)))

theorem ay_brps_agreement_dependency
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_brps_conj_left dependencyMatch publicGuardMatch
      (ay_brps_conj_right fingerprintMatch
        (AyBRPSConj dependencyMatch publicGuardMatch)
        (ay_brps_conj_right replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))
          (ay_brps_conj_right assignmentMatch
            (AyBRPSConj replayMatch
              (AyBRPSConj fingerprintMatch
                (AyBRPSConj dependencyMatch publicGuardMatch)))
            (ay_brps_agreement_tail lineageMatch assignmentMatch
              replayMatch fingerprintMatch dependencyMatch
              publicGuardMatch agreement))))

theorem ay_brps_agreement_public
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop) :
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    publicGuardMatch :=
  fun agreement =>
    ay_brps_conj_right dependencyMatch publicGuardMatch
      (ay_brps_conj_right fingerprintMatch
        (AyBRPSConj dependencyMatch publicGuardMatch)
        (ay_brps_conj_right replayMatch
          (AyBRPSConj fingerprintMatch
            (AyBRPSConj dependencyMatch publicGuardMatch))
          (ay_brps_conj_right assignmentMatch
            (AyBRPSConj replayMatch
              (AyBRPSConj fingerprintMatch
                (AyBRPSConj dependencyMatch publicGuardMatch)))
            (ay_brps_agreement_tail lineageMatch assignmentMatch
              replayMatch fingerprintMatch dependencyMatch
              publicGuardMatch agreement))))

theorem ay_brps_accepted_reuse_intro
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    guard ->
    agreement ->
    branchingHint ->
    AyBRPSAcceptedReuse guard agreement branchingHint :=
  fun guardH agreementH hintH =>
    ay_brps_conj_intro guard (AyBRPSConj agreement branchingHint)
      guardH
      (ay_brps_conj_intro agreement branchingHint agreementH hintH)

theorem ay_brps_accepted_reuse_guard
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBRPSAcceptedReuse guard agreement branchingHint -> guard :=
  fun accepted =>
    ay_brps_conj_left guard (AyBRPSConj agreement branchingHint)
      accepted

theorem ay_brps_accepted_reuse_agreement
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBRPSAcceptedReuse guard agreement branchingHint -> agreement :=
  fun accepted =>
    ay_brps_conj_left agreement branchingHint
      (ay_brps_conj_right guard (AyBRPSConj agreement branchingHint)
        accepted)

theorem ay_brps_accepted_reuse_hint
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    AyBRPSAcceptedReuse guard agreement branchingHint -> branchingHint :=
  fun accepted =>
    ay_brps_conj_right agreement branchingHint
      (ay_brps_conj_right guard (AyBRPSConj agreement branchingHint)
        accepted)

theorem ay_brps_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBRPSPublicReport (AyBRPSOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brps_conj_intro (AyBRPSOutcome model conflict) formula
      (ay_brps_disj_left model conflict modelH)
      formulaH

theorem ay_brps_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBRPSPublicReport (AyBRPSOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brps_conj_intro (AyBRPSOutcome model conflict) formula
      (ay_brps_disj_right model conflict conflictH)
      formulaH

theorem ay_brps_accepted_report_intro
    (reuse : Prop) (public : Prop) :
    reuse -> public -> AyBRPSAcceptedReport reuse public :=
  fun reuseH publicH =>
    ay_brps_conj_intro reuse public reuseH publicH

theorem ay_brps_accepted_report_public
    (reuse : Prop) (public : Prop) :
    AyBRPSAcceptedReport reuse public -> public :=
  fun report =>
    ay_brps_conj_right reuse public report

theorem ay_brps_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBRPSNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brps_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brps_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRPSNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brps_conj_left fallbackPublic diagnostic noClaim

theorem ay_brps_stale_phase_no_claim
    (stalePhase : Prop) (fallbackPublic : Prop) :
    stalePhase ->
    fallbackPublic ->
    AyBRPSNoClaim stalePhase fallbackPublic :=
  fun staleH fallbackH =>
    ay_brps_no_claim_intro stalePhase fallbackPublic staleH fallbackH

theorem ay_brps_assignment_mismatch_no_claim
    (assignmentMismatch : Prop) (fallbackPublic : Prop) :
    assignmentMismatch ->
    fallbackPublic ->
    AyBRPSNoClaim assignmentMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_brps_no_claim_intro assignmentMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_brps_policy_replay_mismatch_no_claim
    (policyReplayMismatch : Prop) (fallbackPublic : Prop) :
    policyReplayMismatch ->
    fallbackPublic ->
    AyBRPSNoClaim policyReplayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_brps_no_claim_intro policyReplayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_brps_dependency_guard_failure_no_claim
    (dependencyFailure : Prop) (fallbackPublic : Prop) :
    dependencyFailure ->
    fallbackPublic ->
    AyBRPSNoClaim dependencyFailure fallbackPublic :=
  fun failureH fallbackH =>
    ay_brps_no_claim_intro dependencyFailure fallbackPublic
      failureH fallbackH

theorem ay_brps_bad_reuse_cannot_publish
    (badReuse : Prop) (fallbackPublic : Prop) :
    badReuse ->
    fallbackPublic ->
    AyBRPSNoClaim badReuse fallbackPublic :=
  fun badH fallbackH =>
    ay_brps_no_claim_intro badReuse fallbackPublic badH fallbackH

theorem ay_brps_accepted_reuse_guides_sat
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop)
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (branchingHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    branchingHint ->
    model ->
    formula ->
    AyBRPSAcceptedReport
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula) :=
  fun guard agreement hintH modelH formulaH =>
    ay_brps_accepted_report_intro
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula)
      (ay_brps_accepted_reuse_intro
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint
        guard agreement hintH)
      (ay_brps_public_sat_report model conflict formula modelH formulaH)

theorem ay_brps_accepted_reuse_guides_unsat
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop)
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (branchingHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRPSPhaseGuard phaseLineage assignmentCompatibility
      restartReplay formulaFingerprint dependencyGuard
      publicSoundnessGuard ->
    AyBRPSAgreement lineageMatch assignmentMatch replayMatch
      fingerprintMatch dependencyMatch publicGuardMatch ->
    branchingHint ->
    conflict ->
    formula ->
    AyBRPSAcceptedReport
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula) :=
  fun guard agreement hintH conflictH formulaH =>
    ay_brps_accepted_report_intro
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula)
      (ay_brps_accepted_reuse_intro
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint
        guard agreement hintH)
      (ay_brps_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_brps_accepted_reuse_report_soundness
    (phaseLineage : Prop) (assignmentCompatibility : Prop)
    (restartReplay : Prop) (formulaFingerprint : Prop)
    (dependencyGuard : Prop) (publicSoundnessGuard : Prop)
    (lineageMatch : Prop) (assignmentMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (dependencyMatch : Prop) (publicGuardMatch : Prop)
    (branchingHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRPSAcceptedReport
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula) ->
    AyBRPSPublicReport (AyBRPSOutcome model conflict) formula :=
  fun report =>
    ay_brps_accepted_report_public
      (AyBRPSAcceptedReuse
        (AyBRPSPhaseGuard phaseLineage assignmentCompatibility
          restartReplay formulaFingerprint dependencyGuard
          publicSoundnessGuard)
        (AyBRPSAgreement lineageMatch assignmentMatch replayMatch
          fingerprintMatch dependencyMatch publicGuardMatch)
        branchingHint)
      (AyBRPSPublicReport (AyBRPSOutcome model conflict) formula)
      report

theorem ay_brps_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRPSNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brps_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
