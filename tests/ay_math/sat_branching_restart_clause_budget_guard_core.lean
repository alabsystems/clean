-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart and learned-clause budget guard soundness skeleton for ay
-- SAT solving. Aggressive restart budgets and clause database reductions are
-- admissible SAT-COMP performance hints only when restart policy replay,
-- LBD/activity tier audits, retained dependency coverage, proof/model checker
-- compatibility, and the public soundness guard agree.

def AyBRCBConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBRCBDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBRCBEquisat (before : Prop) (after : Prop) :=
  AyBRCBConj (before -> after) (after -> before)

def AyBRCBGuardEvidence
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :=
  AyBRCBConj restartReplay
    (AyBRCBConj tierAudit
      (AyBRCBConj retainedDependencies
        (AyBRCBConj checkerCompatibility publicSoundnessGuard)))

def AyBRCBGuardAgreement
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :=
  AyBRCBConj restartMatch
    (AyBRCBConj tierMatch
      (AyBRCBConj dependencyMatch
        (AyBRCBConj checkerMatch publicGuardMatch)))

def AyBRCBAcceptedGuard
    (evidence : Prop) (agreement : Prop) (performanceHint : Prop) :=
  AyBRCBConj evidence (AyBRCBConj agreement performanceHint)

def AyBRCBOutcome (model : Prop) (conflict : Prop) :=
  AyBRCBDisj model conflict

def AyBRCBPublicReport (outcome : Prop) (formula : Prop) :=
  AyBRCBConj outcome formula

def AyBRCBAcceptedReport (guard : Prop) (public : Prop) :=
  AyBRCBConj guard public

def AyBRCBNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBRCBConj fallbackPublic diagnostic

theorem ay_brcb_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBRCBConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brcb_conj_left
    (left : Prop) (right : Prop) :
    AyBRCBConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brcb_conj_right
    (left : Prop) (right : Prop) :
    AyBRCBConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brcb_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBRCBDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brcb_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBRCBDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brcb_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBRCBEquisat before after :=
  fun forward backward =>
    ay_brcb_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brcb_equisat_forward
    (before : Prop) (after : Prop) :
    AyBRCBEquisat before after -> before -> after :=
  fun equisat =>
    ay_brcb_conj_left (before -> after) (after -> before) equisat

theorem ay_brcb_equisat_backward
    (before : Prop) (after : Prop) :
    AyBRCBEquisat before after -> after -> before :=
  fun equisat =>
    ay_brcb_conj_right (before -> after) (after -> before) equisat

theorem ay_brcb_guard_evidence_intro
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    restartReplay ->
    tierAudit ->
    retainedDependencies ->
    checkerCompatibility ->
    publicSoundnessGuard ->
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard :=
  fun restartH tierH dependencyH checkerH publicH =>
    ay_brcb_conj_intro restartReplay
      (AyBRCBConj tierAudit
        (AyBRCBConj retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard)))
      restartH
      (ay_brcb_conj_intro tierAudit
        (AyBRCBConj retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard))
        tierH
        (ay_brcb_conj_intro retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard)
          dependencyH
          (ay_brcb_conj_intro checkerCompatibility publicSoundnessGuard
            checkerH publicH)))

theorem ay_brcb_guard_evidence_restart
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    restartReplay :=
  fun evidence =>
    ay_brcb_conj_left restartReplay
      (AyBRCBConj tierAudit
        (AyBRCBConj retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard)))
      evidence

theorem ay_brcb_guard_evidence_tail
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    AyBRCBConj tierAudit
      (AyBRCBConj retainedDependencies
        (AyBRCBConj checkerCompatibility publicSoundnessGuard)) :=
  fun evidence =>
    ay_brcb_conj_right restartReplay
      (AyBRCBConj tierAudit
        (AyBRCBConj retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard)))
      evidence

theorem ay_brcb_guard_evidence_tier
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    tierAudit :=
  fun evidence =>
    ay_brcb_conj_left tierAudit
      (AyBRCBConj retainedDependencies
        (AyBRCBConj checkerCompatibility publicSoundnessGuard))
      (ay_brcb_guard_evidence_tail restartReplay tierAudit
        retainedDependencies checkerCompatibility publicSoundnessGuard
        evidence)

theorem ay_brcb_guard_evidence_dependencies
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    retainedDependencies :=
  fun evidence =>
    ay_brcb_conj_left retainedDependencies
      (AyBRCBConj checkerCompatibility publicSoundnessGuard)
      (ay_brcb_conj_right tierAudit
        (AyBRCBConj retainedDependencies
          (AyBRCBConj checkerCompatibility publicSoundnessGuard))
        (ay_brcb_guard_evidence_tail restartReplay tierAudit
          retainedDependencies checkerCompatibility publicSoundnessGuard
          evidence))

theorem ay_brcb_guard_evidence_checker
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    checkerCompatibility :=
  fun evidence =>
    ay_brcb_conj_left checkerCompatibility publicSoundnessGuard
      (ay_brcb_conj_right retainedDependencies
        (AyBRCBConj checkerCompatibility publicSoundnessGuard)
        (ay_brcb_conj_right tierAudit
          (AyBRCBConj retainedDependencies
            (AyBRCBConj checkerCompatibility publicSoundnessGuard))
          (ay_brcb_guard_evidence_tail restartReplay tierAudit
            retainedDependencies checkerCompatibility publicSoundnessGuard
            evidence)))

theorem ay_brcb_guard_evidence_public
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_brcb_conj_right checkerCompatibility publicSoundnessGuard
      (ay_brcb_conj_right retainedDependencies
        (AyBRCBConj checkerCompatibility publicSoundnessGuard)
        (ay_brcb_conj_right tierAudit
          (AyBRCBConj retainedDependencies
            (AyBRCBConj checkerCompatibility publicSoundnessGuard))
          (ay_brcb_guard_evidence_tail restartReplay tierAudit
            retainedDependencies checkerCompatibility publicSoundnessGuard
            evidence)))

theorem ay_brcb_guard_agreement_intro
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    restartMatch ->
    tierMatch ->
    dependencyMatch ->
    checkerMatch ->
    publicGuardMatch ->
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch :=
  fun restartH tierH dependencyH checkerH publicH =>
    ay_brcb_conj_intro restartMatch
      (AyBRCBConj tierMatch
        (AyBRCBConj dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch)))
      restartH
      (ay_brcb_conj_intro tierMatch
        (AyBRCBConj dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch))
        tierH
        (ay_brcb_conj_intro dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch)
          dependencyH
          (ay_brcb_conj_intro checkerMatch publicGuardMatch
            checkerH publicH)))

theorem ay_brcb_guard_agreement_restart
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    restartMatch :=
  fun agreement =>
    ay_brcb_conj_left restartMatch
      (AyBRCBConj tierMatch
        (AyBRCBConj dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch)))
      agreement

theorem ay_brcb_guard_agreement_tail
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    AyBRCBConj tierMatch
      (AyBRCBConj dependencyMatch
        (AyBRCBConj checkerMatch publicGuardMatch)) :=
  fun agreement =>
    ay_brcb_conj_right restartMatch
      (AyBRCBConj tierMatch
        (AyBRCBConj dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch)))
      agreement

theorem ay_brcb_guard_agreement_tier
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    tierMatch :=
  fun agreement =>
    ay_brcb_conj_left tierMatch
      (AyBRCBConj dependencyMatch
        (AyBRCBConj checkerMatch publicGuardMatch))
      (ay_brcb_guard_agreement_tail restartMatch tierMatch
        dependencyMatch checkerMatch publicGuardMatch agreement)

theorem ay_brcb_guard_agreement_dependency
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_brcb_conj_left dependencyMatch
      (AyBRCBConj checkerMatch publicGuardMatch)
      (ay_brcb_conj_right tierMatch
        (AyBRCBConj dependencyMatch
          (AyBRCBConj checkerMatch publicGuardMatch))
        (ay_brcb_guard_agreement_tail restartMatch tierMatch
          dependencyMatch checkerMatch publicGuardMatch agreement))

theorem ay_brcb_guard_agreement_checker
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    checkerMatch :=
  fun agreement =>
    ay_brcb_conj_left checkerMatch publicGuardMatch
      (ay_brcb_conj_right dependencyMatch
        (AyBRCBConj checkerMatch publicGuardMatch)
        (ay_brcb_conj_right tierMatch
          (AyBRCBConj dependencyMatch
            (AyBRCBConj checkerMatch publicGuardMatch))
          (ay_brcb_guard_agreement_tail restartMatch tierMatch
            dependencyMatch checkerMatch publicGuardMatch agreement)))

theorem ay_brcb_guard_agreement_public
    (restartMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    publicGuardMatch :=
  fun agreement =>
    ay_brcb_conj_right checkerMatch publicGuardMatch
      (ay_brcb_conj_right dependencyMatch
        (AyBRCBConj checkerMatch publicGuardMatch)
        (ay_brcb_conj_right tierMatch
          (AyBRCBConj dependencyMatch
            (AyBRCBConj checkerMatch publicGuardMatch))
          (ay_brcb_guard_agreement_tail restartMatch tierMatch
            dependencyMatch checkerMatch publicGuardMatch agreement)))

theorem ay_brcb_accepted_guard_intro
    (evidence : Prop) (agreement : Prop) (performanceHint : Prop) :
    evidence ->
    agreement ->
    performanceHint ->
    AyBRCBAcceptedGuard evidence agreement performanceHint :=
  fun evidenceH agreementH hintH =>
    ay_brcb_conj_intro evidence
      (AyBRCBConj agreement performanceHint)
      evidenceH
      (ay_brcb_conj_intro agreement performanceHint agreementH hintH)

theorem ay_brcb_accepted_guard_evidence
    (evidence : Prop) (agreement : Prop) (performanceHint : Prop) :
    AyBRCBAcceptedGuard evidence agreement performanceHint -> evidence :=
  fun accepted =>
    ay_brcb_conj_left evidence (AyBRCBConj agreement performanceHint)
      accepted

theorem ay_brcb_accepted_guard_agreement
    (evidence : Prop) (agreement : Prop) (performanceHint : Prop) :
    AyBRCBAcceptedGuard evidence agreement performanceHint -> agreement :=
  fun accepted =>
    ay_brcb_conj_left agreement performanceHint
      (ay_brcb_conj_right evidence
        (AyBRCBConj agreement performanceHint)
        accepted)

theorem ay_brcb_accepted_guard_hint
    (evidence : Prop) (agreement : Prop) (performanceHint : Prop) :
    AyBRCBAcceptedGuard evidence agreement performanceHint ->
    performanceHint :=
  fun accepted =>
    ay_brcb_conj_right agreement performanceHint
      (ay_brcb_conj_right evidence
        (AyBRCBConj agreement performanceHint)
        accepted)

theorem ay_brcb_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBRCBPublicReport (AyBRCBOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brcb_conj_intro (AyBRCBOutcome model conflict) formula
      (ay_brcb_disj_left model conflict modelH)
      formulaH

theorem ay_brcb_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBRCBPublicReport (AyBRCBOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brcb_conj_intro (AyBRCBOutcome model conflict) formula
      (ay_brcb_disj_right model conflict conflictH)
      formulaH

theorem ay_brcb_accepted_report_intro
    (guard : Prop) (public : Prop) :
    guard -> public -> AyBRCBAcceptedReport guard public :=
  fun guardH publicH =>
    ay_brcb_conj_intro guard public guardH publicH

theorem ay_brcb_accepted_report_public
    (guard : Prop) (public : Prop) :
    AyBRCBAcceptedReport guard public -> public :=
  fun report =>
    ay_brcb_conj_right guard public report

theorem ay_brcb_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBRCBNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcb_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brcb_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRCBNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brcb_conj_left fallbackPublic diagnostic noClaim

theorem ay_brcb_missing_dependency_no_claim
    (missingDependency : Prop) (fallbackPublic : Prop) :
    missingDependency ->
    fallbackPublic ->
    AyBRCBNoClaim missingDependency fallbackPublic :=
  fun missingH fallbackH =>
    ay_brcb_no_claim_intro missingDependency fallbackPublic
      missingH fallbackH

theorem ay_brcb_stale_tier_no_claim
    (staleTier : Prop) (fallbackPublic : Prop) :
    staleTier ->
    fallbackPublic ->
    AyBRCBNoClaim staleTier fallbackPublic :=
  fun staleH fallbackH =>
    ay_brcb_no_claim_intro staleTier fallbackPublic staleH fallbackH

theorem ay_brcb_policy_replay_mismatch_no_claim
    (policyReplayMismatch : Prop) (fallbackPublic : Prop) :
    policyReplayMismatch ->
    fallbackPublic ->
    AyBRCBNoClaim policyReplayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_brcb_no_claim_intro policyReplayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_brcb_checker_rejection_no_claim
    (checkerRejection : Prop) (fallbackPublic : Prop) :
    checkerRejection ->
    fallbackPublic ->
    AyBRCBNoClaim checkerRejection fallbackPublic :=
  fun rejectedH fallbackH =>
    ay_brcb_no_claim_intro checkerRejection fallbackPublic
      rejectedH fallbackH

theorem ay_brcb_bad_guard_cannot_publish
    (badGuard : Prop) (fallbackPublic : Prop) :
    badGuard ->
    fallbackPublic ->
    AyBRCBNoClaim badGuard fallbackPublic :=
  fun badH fallbackH =>
    ay_brcb_no_claim_intro badGuard fallbackPublic badH fallbackH

theorem ay_brcb_accepted_guard_guides_sat
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) (restartMatch : Prop)
    (tierMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicGuardMatch : Prop)
    (performanceHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    performanceHint ->
    model ->
    formula ->
    AyBRCBAcceptedReport
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula) :=
  fun evidence agreement hintH modelH formulaH =>
    ay_brcb_accepted_report_intro
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula)
      (ay_brcb_accepted_guard_intro
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint
        evidence agreement hintH)
      (ay_brcb_public_sat_report model conflict formula modelH formulaH)

theorem ay_brcb_accepted_guard_guides_unsat
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) (restartMatch : Prop)
    (tierMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicGuardMatch : Prop)
    (performanceHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
      checkerCompatibility publicSoundnessGuard ->
    AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
      checkerMatch publicGuardMatch ->
    performanceHint ->
    conflict ->
    formula ->
    AyBRCBAcceptedReport
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula) :=
  fun evidence agreement hintH conflictH formulaH =>
    ay_brcb_accepted_report_intro
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula)
      (ay_brcb_accepted_guard_intro
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint
        evidence agreement hintH)
      (ay_brcb_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_brcb_accepted_guard_report_soundness
    (restartReplay : Prop) (tierAudit : Prop)
    (retainedDependencies : Prop) (checkerCompatibility : Prop)
    (publicSoundnessGuard : Prop) (restartMatch : Prop)
    (tierMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicGuardMatch : Prop)
    (performanceHint : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBRCBAcceptedReport
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula) ->
    AyBRCBPublicReport (AyBRCBOutcome model conflict) formula :=
  fun report =>
    ay_brcb_accepted_report_public
      (AyBRCBAcceptedGuard
        (AyBRCBGuardEvidence restartReplay tierAudit retainedDependencies
          checkerCompatibility publicSoundnessGuard)
        (AyBRCBGuardAgreement restartMatch tierMatch dependencyMatch
          checkerMatch publicGuardMatch)
        performanceHint)
      (AyBRCBPublicReport (AyBRCBOutcome model conflict) formula)
      report

theorem ay_brcb_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRCBNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brcb_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
