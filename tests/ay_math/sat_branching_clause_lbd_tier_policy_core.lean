-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded LBD tier retention policy soundness skeleton for ay SAT solving.
-- Learned-clause LBD tiers and retention/deletion policies may guide search
-- only when LBD evidence, tier manifests, dependency witnesses, checker
-- replay, and formula fingerprints agree. Stale or mismatched tiers fall back
-- to no-claim/recompute.

def AyBLBDConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBLBDDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBLBDEquisat (before : Prop) (after : Prop) :=
  AyBLBDConj (before -> after) (after -> before)

def AyBLBDTierPolicy
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :=
  AyBLBDConj learnedClause
    (AyBLBDConj lbdEvidence
      (AyBLBDConj tierManifest
        (AyBLBDConj dependencyWitness
          (AyBLBDConj checkerReplay formulaFingerprint))))

def AyBLBDAgreement
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :=
  AyBLBDConj lbdMatch
    (AyBLBDConj tierMatch
      (AyBLBDConj dependencyMatch
        (AyBLBDConj checkerMatch fingerprintMatch)))

def AyBLBDAcceptedPolicy
    (policy : Prop) (agreement : Prop) (retentionDecision : Prop) :=
  AyBLBDConj policy (AyBLBDConj agreement retentionDecision)

def AyBLBDOutcome (model : Prop) (conflict : Prop) :=
  AyBLBDDisj model conflict

def AyBLBDPublicReport (outcome : Prop) (formula : Prop) :=
  AyBLBDConj outcome formula

def AyBLBDAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBLBDConj evidence public

def AyBLBDNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBLBDConj fallbackPublic diagnostic

theorem ay_blbd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBLBDConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_blbd_conj_left
    (left : Prop) (right : Prop) :
    AyBLBDConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_blbd_conj_right
    (left : Prop) (right : Prop) :
    AyBLBDConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_blbd_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBLBDDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_blbd_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBLBDDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_blbd_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBLBDEquisat before after :=
  fun forward backward =>
    ay_blbd_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_blbd_equisat_forward
    (before : Prop) (after : Prop) :
    AyBLBDEquisat before after -> before -> after :=
  fun equisat =>
    ay_blbd_conj_left (before -> after) (after -> before) equisat

theorem ay_blbd_equisat_backward
    (before : Prop) (after : Prop) :
    AyBLBDEquisat before after -> after -> before :=
  fun equisat =>
    ay_blbd_conj_right (before -> after) (after -> before) equisat

theorem ay_blbd_tier_policy_intro
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    learnedClause ->
    lbdEvidence ->
    tierManifest ->
    dependencyWitness ->
    checkerReplay ->
    formulaFingerprint ->
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint :=
  fun learnedH lbdH tierH dependencyH checkerH fingerprintH =>
    ay_blbd_conj_intro learnedClause
      (AyBLBDConj lbdEvidence
        (AyBLBDConj tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))))
      learnedH
      (ay_blbd_conj_intro lbdEvidence
        (AyBLBDConj tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint)))
        lbdH
        (ay_blbd_conj_intro tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))
          tierH
          (ay_blbd_conj_intro dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint)
            dependencyH
            (ay_blbd_conj_intro checkerReplay formulaFingerprint
              checkerH fingerprintH))))

theorem ay_blbd_tier_policy_learned
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    learnedClause :=
  fun policy =>
    ay_blbd_conj_left learnedClause
      (AyBLBDConj lbdEvidence
        (AyBLBDConj tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))))
      policy

theorem ay_blbd_tier_policy_tail
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    AyBLBDConj lbdEvidence
      (AyBLBDConj tierManifest
        (AyBLBDConj dependencyWitness
          (AyBLBDConj checkerReplay formulaFingerprint))) :=
  fun policy =>
    ay_blbd_conj_right learnedClause
      (AyBLBDConj lbdEvidence
        (AyBLBDConj tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))))
      policy

theorem ay_blbd_tier_policy_lbd
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    lbdEvidence :=
  fun policy =>
    ay_blbd_conj_left lbdEvidence
      (AyBLBDConj tierManifest
        (AyBLBDConj dependencyWitness
          (AyBLBDConj checkerReplay formulaFingerprint)))
      (ay_blbd_tier_policy_tail learnedClause lbdEvidence tierManifest
        dependencyWitness checkerReplay formulaFingerprint policy)

theorem ay_blbd_tier_policy_manifest
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    tierManifest :=
  fun policy =>
    ay_blbd_conj_left tierManifest
      (AyBLBDConj dependencyWitness
        (AyBLBDConj checkerReplay formulaFingerprint))
      (ay_blbd_conj_right lbdEvidence
        (AyBLBDConj tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint)))
        (ay_blbd_tier_policy_tail learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint policy))

theorem ay_blbd_tier_policy_dependency
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    dependencyWitness :=
  fun policy =>
    ay_blbd_conj_left dependencyWitness
      (AyBLBDConj checkerReplay formulaFingerprint)
      (ay_blbd_conj_right tierManifest
        (AyBLBDConj dependencyWitness
          (AyBLBDConj checkerReplay formulaFingerprint))
        (ay_blbd_conj_right lbdEvidence
          (AyBLBDConj tierManifest
            (AyBLBDConj dependencyWitness
              (AyBLBDConj checkerReplay formulaFingerprint)))
          (ay_blbd_tier_policy_tail learnedClause lbdEvidence tierManifest
            dependencyWitness checkerReplay formulaFingerprint policy)))

theorem ay_blbd_tier_policy_checker
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    checkerReplay :=
  fun policy =>
    ay_blbd_conj_left checkerReplay formulaFingerprint
      (ay_blbd_conj_right dependencyWitness
        (AyBLBDConj checkerReplay formulaFingerprint)
        (ay_blbd_conj_right tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))
          (ay_blbd_conj_right lbdEvidence
            (AyBLBDConj tierManifest
              (AyBLBDConj dependencyWitness
                (AyBLBDConj checkerReplay formulaFingerprint)))
            (ay_blbd_tier_policy_tail learnedClause lbdEvidence
              tierManifest dependencyWitness checkerReplay
              formulaFingerprint policy))))

theorem ay_blbd_tier_policy_fingerprint
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    formulaFingerprint :=
  fun policy =>
    ay_blbd_conj_right checkerReplay formulaFingerprint
      (ay_blbd_conj_right dependencyWitness
        (AyBLBDConj checkerReplay formulaFingerprint)
        (ay_blbd_conj_right tierManifest
          (AyBLBDConj dependencyWitness
            (AyBLBDConj checkerReplay formulaFingerprint))
          (ay_blbd_conj_right lbdEvidence
            (AyBLBDConj tierManifest
              (AyBLBDConj dependencyWitness
                (AyBLBDConj checkerReplay formulaFingerprint)))
            (ay_blbd_tier_policy_tail learnedClause lbdEvidence
              tierManifest dependencyWitness checkerReplay
              formulaFingerprint policy))))

theorem ay_blbd_agreement_intro
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    lbdMatch ->
    tierMatch ->
    dependencyMatch ->
    checkerMatch ->
    fingerprintMatch ->
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch :=
  fun lbdH tierH dependencyH checkerH fingerprintH =>
    ay_blbd_conj_intro lbdMatch
      (AyBLBDConj tierMatch
        (AyBLBDConj dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch)))
      lbdH
      (ay_blbd_conj_intro tierMatch
        (AyBLBDConj dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch))
        tierH
        (ay_blbd_conj_intro dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch)
          dependencyH
          (ay_blbd_conj_intro checkerMatch fingerprintMatch
            checkerH fingerprintH)))

theorem ay_blbd_agreement_lbd
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    lbdMatch :=
  fun agreement =>
    ay_blbd_conj_left lbdMatch
      (AyBLBDConj tierMatch
        (AyBLBDConj dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch)))
      agreement

theorem ay_blbd_agreement_tail
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    AyBLBDConj tierMatch
      (AyBLBDConj dependencyMatch
        (AyBLBDConj checkerMatch fingerprintMatch)) :=
  fun agreement =>
    ay_blbd_conj_right lbdMatch
      (AyBLBDConj tierMatch
        (AyBLBDConj dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch)))
      agreement

theorem ay_blbd_agreement_tier
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    tierMatch :=
  fun agreement =>
    ay_blbd_conj_left tierMatch
      (AyBLBDConj dependencyMatch
        (AyBLBDConj checkerMatch fingerprintMatch))
      (ay_blbd_agreement_tail lbdMatch tierMatch dependencyMatch
        checkerMatch fingerprintMatch agreement)

theorem ay_blbd_agreement_dependency
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_blbd_conj_left dependencyMatch
      (AyBLBDConj checkerMatch fingerprintMatch)
      (ay_blbd_conj_right tierMatch
        (AyBLBDConj dependencyMatch
          (AyBLBDConj checkerMatch fingerprintMatch))
        (ay_blbd_agreement_tail lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch agreement))

theorem ay_blbd_agreement_checker
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    checkerMatch :=
  fun agreement =>
    ay_blbd_conj_left checkerMatch fingerprintMatch
      (ay_blbd_conj_right dependencyMatch
        (AyBLBDConj checkerMatch fingerprintMatch)
        (ay_blbd_conj_right tierMatch
          (AyBLBDConj dependencyMatch
            (AyBLBDConj checkerMatch fingerprintMatch))
          (ay_blbd_agreement_tail lbdMatch tierMatch dependencyMatch
            checkerMatch fingerprintMatch agreement)))

theorem ay_blbd_agreement_fingerprint
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) :
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    fingerprintMatch :=
  fun agreement =>
    ay_blbd_conj_right checkerMatch fingerprintMatch
      (ay_blbd_conj_right dependencyMatch
        (AyBLBDConj checkerMatch fingerprintMatch)
        (ay_blbd_conj_right tierMatch
          (AyBLBDConj dependencyMatch
            (AyBLBDConj checkerMatch fingerprintMatch))
          (ay_blbd_agreement_tail lbdMatch tierMatch dependencyMatch
            checkerMatch fingerprintMatch agreement)))

theorem ay_blbd_accepted_policy_intro
    (policy : Prop) (agreement : Prop) (retentionDecision : Prop) :
    policy ->
    agreement ->
    retentionDecision ->
    AyBLBDAcceptedPolicy policy agreement retentionDecision :=
  fun policyH agreementH decisionH =>
    ay_blbd_conj_intro policy
      (AyBLBDConj agreement retentionDecision)
      policyH
      (ay_blbd_conj_intro agreement retentionDecision
        agreementH decisionH)

theorem ay_blbd_accepted_policy_policy
    (policy : Prop) (agreement : Prop) (retentionDecision : Prop) :
    AyBLBDAcceptedPolicy policy agreement retentionDecision -> policy :=
  fun accepted =>
    ay_blbd_conj_left policy (AyBLBDConj agreement retentionDecision)
      accepted

theorem ay_blbd_accepted_policy_agreement
    (policy : Prop) (agreement : Prop) (retentionDecision : Prop) :
    AyBLBDAcceptedPolicy policy agreement retentionDecision ->
    agreement :=
  fun accepted =>
    ay_blbd_conj_left agreement retentionDecision
      (ay_blbd_conj_right policy
        (AyBLBDConj agreement retentionDecision)
        accepted)

theorem ay_blbd_accepted_policy_decision
    (policy : Prop) (agreement : Prop) (retentionDecision : Prop) :
    AyBLBDAcceptedPolicy policy agreement retentionDecision ->
    retentionDecision :=
  fun accepted =>
    ay_blbd_conj_right agreement retentionDecision
      (ay_blbd_conj_right policy
        (AyBLBDConj agreement retentionDecision)
        accepted)

theorem ay_blbd_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBLBDPublicReport (AyBLBDOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_blbd_conj_intro (AyBLBDOutcome model conflict) formula
      (ay_blbd_disj_left model conflict modelH)
      formulaH

theorem ay_blbd_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBLBDPublicReport (AyBLBDOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_blbd_conj_intro (AyBLBDOutcome model conflict) formula
      (ay_blbd_disj_right model conflict conflictH)
      formulaH

theorem ay_blbd_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBLBDAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_blbd_conj_intro evidence public evidenceH publicH

theorem ay_blbd_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBLBDAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_blbd_conj_left evidence public report

theorem ay_blbd_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBLBDAcceptedReport evidence public -> public :=
  fun report =>
    ay_blbd_conj_right evidence public report

theorem ay_blbd_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBLBDNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_blbd_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_blbd_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBLBDNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_blbd_conj_left fallbackPublic diagnostic noClaim

theorem ay_blbd_stale_lbd_no_claim
    (staleLbd : Prop) (fallbackPublic : Prop) :
    staleLbd ->
    fallbackPublic ->
    AyBLBDNoClaim staleLbd fallbackPublic :=
  fun staleH fallbackH =>
    ay_blbd_no_claim_intro staleLbd fallbackPublic staleH fallbackH

theorem ay_blbd_tier_mismatch_no_claim
    (tierMismatch : Prop) (fallbackPublic : Prop) :
    tierMismatch ->
    fallbackPublic ->
    AyBLBDNoClaim tierMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_blbd_no_claim_intro tierMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_blbd_dependency_mismatch_no_claim
    (dependencyMismatch : Prop) (fallbackPublic : Prop) :
    dependencyMismatch ->
    fallbackPublic ->
    AyBLBDNoClaim dependencyMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_blbd_no_claim_intro dependencyMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_blbd_fingerprint_mismatch_no_claim
    (fingerprintMismatch : Prop) (fallbackPublic : Prop) :
    fingerprintMismatch ->
    fallbackPublic ->
    AyBLBDNoClaim fingerprintMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_blbd_no_claim_intro fingerprintMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_blbd_mismatched_tier_cannot_justify_policy
    (tierMismatch : Prop) (fallbackPublic : Prop) :
    tierMismatch ->
    fallbackPublic ->
    AyBLBDNoClaim tierMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_blbd_tier_mismatch_no_claim tierMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_blbd_accepted_policy_guides_sat
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop)
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) (retentionDecision : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    retentionDecision ->
    model ->
    formula ->
    AyBLBDAcceptedReport
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula) :=
  fun policy agreement decisionH modelH formulaH =>
    ay_blbd_accepted_report_intro
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula)
      (ay_blbd_accepted_policy_intro
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision
        policy agreement decisionH)
      (ay_blbd_public_sat_report model conflict formula modelH formulaH)

theorem ay_blbd_accepted_policy_guides_unsat
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop)
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) (retentionDecision : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
      dependencyWitness checkerReplay formulaFingerprint ->
    AyBLBDAgreement lbdMatch tierMatch dependencyMatch
      checkerMatch fingerprintMatch ->
    retentionDecision ->
    conflict ->
    formula ->
    AyBLBDAcceptedReport
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula) :=
  fun policy agreement decisionH conflictH formulaH =>
    ay_blbd_accepted_report_intro
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula)
      (ay_blbd_accepted_policy_intro
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision
        policy agreement decisionH)
      (ay_blbd_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_blbd_accepted_policy_report_soundness
    (learnedClause : Prop) (lbdEvidence : Prop)
    (tierManifest : Prop) (dependencyWitness : Prop)
    (checkerReplay : Prop) (formulaFingerprint : Prop)
    (lbdMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (fingerprintMatch : Prop) (retentionDecision : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBLBDAcceptedReport
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula) ->
    AyBLBDPublicReport (AyBLBDOutcome model conflict) formula :=
  fun report =>
    ay_blbd_accepted_report_public
      (AyBLBDAcceptedPolicy
        (AyBLBDTierPolicy learnedClause lbdEvidence tierManifest
          dependencyWitness checkerReplay formulaFingerprint)
        (AyBLBDAgreement lbdMatch tierMatch dependencyMatch
          checkerMatch fingerprintMatch)
        retentionDecision)
      (AyBLBDPublicReport (AyBLBDOutcome model conflict) formula)
      report

theorem ay_blbd_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBLBDNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_blbd_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
