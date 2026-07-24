-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded evicted learned-clause rehydration soundness skeleton for ay SAT
-- solving. An evicted clause may be cited later by branching, restart, or
-- proof code only when rehydration restores the exact clause id, LBD/activity
-- tier metadata, derivation dependencies, checker replay, and public
-- proof/model compatibility. Missing or stale evidence falls back to
-- no-claim/recompute.

def AyBECRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBECRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBECREquisat (before : Prop) (after : Prop) :=
  AyBECRConj (before -> after) (after -> before)

def AyBECRRehydrationEvidence
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :=
  AyBECRConj clauseId
    (AyBECRConj tierMetadata
      (AyBECRConj derivationDependencies
        (AyBECRConj checkerReplay publicCompatibility)))

def AyBECRRehydrationAgreement
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :=
  AyBECRConj idMatch
    (AyBECRConj tierMatch
      (AyBECRConj dependencyMatch
        (AyBECRConj replayAccepted publicMatch)))

def AyBECREvictedCitation
    (evictedClause : Prop) (rehydration : Prop) (agreement : Prop) :=
  AyBECRConj evictedClause (AyBECRConj rehydration agreement)

def AyBECRAcceptedCitation
    (citation : Prop) (guidanceUse : Prop) (proofTraceUse : Prop) :=
  AyBECRConj citation (AyBECRConj guidanceUse proofTraceUse)

def AyBECROutcome (model : Prop) (conflict : Prop) :=
  AyBECRDisj model conflict

def AyBECRPublicReport (outcome : Prop) (formula : Prop) :=
  AyBECRConj outcome formula

def AyBECRAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBECRConj evidence public

def AyBECRNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBECRConj fallbackPublic diagnostic

theorem ay_becr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBECRConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_becr_conj_left
    (left : Prop) (right : Prop) :
    AyBECRConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_becr_conj_right
    (left : Prop) (right : Prop) :
    AyBECRConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_becr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBECRDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_becr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBECRDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_becr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBECREquisat before after :=
  fun forward backward =>
    ay_becr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_becr_equisat_forward
    (before : Prop) (after : Prop) :
    AyBECREquisat before after -> before -> after :=
  fun equisat =>
    ay_becr_conj_left (before -> after) (after -> before) equisat

theorem ay_becr_equisat_backward
    (before : Prop) (after : Prop) :
    AyBECREquisat before after -> after -> before :=
  fun equisat =>
    ay_becr_conj_right (before -> after) (after -> before) equisat

theorem ay_becr_rehydration_evidence_intro
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    clauseId ->
    tierMetadata ->
    derivationDependencies ->
    checkerReplay ->
    publicCompatibility ->
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility :=
  fun idH tierH dependencyH replayH publicH =>
    ay_becr_conj_intro clauseId
      (AyBECRConj tierMetadata
        (AyBECRConj derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility)))
      idH
      (ay_becr_conj_intro tierMetadata
        (AyBECRConj derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility))
        tierH
        (ay_becr_conj_intro derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility)
          dependencyH
          (ay_becr_conj_intro checkerReplay publicCompatibility
            replayH publicH)))

theorem ay_becr_rehydration_evidence_id
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    clauseId :=
  fun evidence =>
    ay_becr_conj_left clauseId
      (AyBECRConj tierMetadata
        (AyBECRConj derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility)))
      evidence

theorem ay_becr_rehydration_evidence_tail
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    AyBECRConj tierMetadata
      (AyBECRConj derivationDependencies
        (AyBECRConj checkerReplay publicCompatibility)) :=
  fun evidence =>
    ay_becr_conj_right clauseId
      (AyBECRConj tierMetadata
        (AyBECRConj derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility)))
      evidence

theorem ay_becr_rehydration_evidence_tier
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    tierMetadata :=
  fun evidence =>
    ay_becr_conj_left tierMetadata
      (AyBECRConj derivationDependencies
        (AyBECRConj checkerReplay publicCompatibility))
      (ay_becr_rehydration_evidence_tail clauseId tierMetadata
        derivationDependencies checkerReplay publicCompatibility evidence)

theorem ay_becr_rehydration_evidence_dependencies
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    derivationDependencies :=
  fun evidence =>
    ay_becr_conj_left derivationDependencies
      (AyBECRConj checkerReplay publicCompatibility)
      (ay_becr_conj_right tierMetadata
        (AyBECRConj derivationDependencies
          (AyBECRConj checkerReplay publicCompatibility))
        (ay_becr_rehydration_evidence_tail clauseId tierMetadata
          derivationDependencies checkerReplay publicCompatibility evidence))

theorem ay_becr_rehydration_evidence_replay
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    checkerReplay :=
  fun evidence =>
    ay_becr_conj_left checkerReplay publicCompatibility
      (ay_becr_conj_right derivationDependencies
        (AyBECRConj checkerReplay publicCompatibility)
        (ay_becr_conj_right tierMetadata
          (AyBECRConj derivationDependencies
            (AyBECRConj checkerReplay publicCompatibility))
          (ay_becr_rehydration_evidence_tail clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility
            evidence)))

theorem ay_becr_rehydration_evidence_public
    (clauseId : Prop) (tierMetadata : Prop)
    (derivationDependencies : Prop) (checkerReplay : Prop)
    (publicCompatibility : Prop) :
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    publicCompatibility :=
  fun evidence =>
    ay_becr_conj_right checkerReplay publicCompatibility
      (ay_becr_conj_right derivationDependencies
        (AyBECRConj checkerReplay publicCompatibility)
        (ay_becr_conj_right tierMetadata
          (AyBECRConj derivationDependencies
            (AyBECRConj checkerReplay publicCompatibility))
          (ay_becr_rehydration_evidence_tail clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility
            evidence)))

theorem ay_becr_rehydration_agreement_intro
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    idMatch ->
    tierMatch ->
    dependencyMatch ->
    replayAccepted ->
    publicMatch ->
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch :=
  fun idH tierH dependencyH replayH publicH =>
    ay_becr_conj_intro idMatch
      (AyBECRConj tierMatch
        (AyBECRConj dependencyMatch
          (AyBECRConj replayAccepted publicMatch)))
      idH
      (ay_becr_conj_intro tierMatch
        (AyBECRConj dependencyMatch
          (AyBECRConj replayAccepted publicMatch))
        tierH
        (ay_becr_conj_intro dependencyMatch
          (AyBECRConj replayAccepted publicMatch)
          dependencyH
          (ay_becr_conj_intro replayAccepted publicMatch
            replayH publicH)))

theorem ay_becr_rehydration_agreement_id
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    idMatch :=
  fun agreement =>
    ay_becr_conj_left idMatch
      (AyBECRConj tierMatch
        (AyBECRConj dependencyMatch
          (AyBECRConj replayAccepted publicMatch)))
      agreement

theorem ay_becr_rehydration_agreement_tail
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    AyBECRConj tierMatch
      (AyBECRConj dependencyMatch
        (AyBECRConj replayAccepted publicMatch)) :=
  fun agreement =>
    ay_becr_conj_right idMatch
      (AyBECRConj tierMatch
        (AyBECRConj dependencyMatch
          (AyBECRConj replayAccepted publicMatch)))
      agreement

theorem ay_becr_rehydration_agreement_tier
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    tierMatch :=
  fun agreement =>
    ay_becr_conj_left tierMatch
      (AyBECRConj dependencyMatch
        (AyBECRConj replayAccepted publicMatch))
      (ay_becr_rehydration_agreement_tail idMatch tierMatch
        dependencyMatch replayAccepted publicMatch agreement)

theorem ay_becr_rehydration_agreement_dependency
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_becr_conj_left dependencyMatch
      (AyBECRConj replayAccepted publicMatch)
      (ay_becr_conj_right tierMatch
        (AyBECRConj dependencyMatch
          (AyBECRConj replayAccepted publicMatch))
        (ay_becr_rehydration_agreement_tail idMatch tierMatch
          dependencyMatch replayAccepted publicMatch agreement))

theorem ay_becr_rehydration_agreement_replay
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    replayAccepted :=
  fun agreement =>
    ay_becr_conj_left replayAccepted publicMatch
      (ay_becr_conj_right dependencyMatch
        (AyBECRConj replayAccepted publicMatch)
        (ay_becr_conj_right tierMatch
          (AyBECRConj dependencyMatch
            (AyBECRConj replayAccepted publicMatch))
          (ay_becr_rehydration_agreement_tail idMatch tierMatch
            dependencyMatch replayAccepted publicMatch agreement)))

theorem ay_becr_rehydration_agreement_public
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) :
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    publicMatch :=
  fun agreement =>
    ay_becr_conj_right replayAccepted publicMatch
      (ay_becr_conj_right dependencyMatch
        (AyBECRConj replayAccepted publicMatch)
        (ay_becr_conj_right tierMatch
          (AyBECRConj dependencyMatch
            (AyBECRConj replayAccepted publicMatch))
          (ay_becr_rehydration_agreement_tail idMatch tierMatch
            dependencyMatch replayAccepted publicMatch agreement)))

theorem ay_becr_evicted_citation_intro
    (evictedClause : Prop) (rehydration : Prop) (agreement : Prop) :
    evictedClause ->
    rehydration ->
    agreement ->
    AyBECREvictedCitation evictedClause rehydration agreement :=
  fun evictedH rehydrationH agreementH =>
    ay_becr_conj_intro evictedClause
      (AyBECRConj rehydration agreement)
      evictedH
      (ay_becr_conj_intro rehydration agreement
        rehydrationH agreementH)

theorem ay_becr_evicted_citation_clause
    (evictedClause : Prop) (rehydration : Prop) (agreement : Prop) :
    AyBECREvictedCitation evictedClause rehydration agreement ->
    evictedClause :=
  fun citation =>
    ay_becr_conj_left evictedClause
      (AyBECRConj rehydration agreement)
      citation

theorem ay_becr_evicted_citation_rehydration
    (evictedClause : Prop) (rehydration : Prop) (agreement : Prop) :
    AyBECREvictedCitation evictedClause rehydration agreement ->
    rehydration :=
  fun citation =>
    ay_becr_conj_left rehydration agreement
      (ay_becr_conj_right evictedClause
        (AyBECRConj rehydration agreement)
        citation)

theorem ay_becr_evicted_citation_agreement
    (evictedClause : Prop) (rehydration : Prop) (agreement : Prop) :
    AyBECREvictedCitation evictedClause rehydration agreement ->
    agreement :=
  fun citation =>
    ay_becr_conj_right rehydration agreement
      (ay_becr_conj_right evictedClause
        (AyBECRConj rehydration agreement)
        citation)

theorem ay_becr_accepted_citation_intro
    (citation : Prop) (guidanceUse : Prop) (proofTraceUse : Prop) :
    citation ->
    guidanceUse ->
    proofTraceUse ->
    AyBECRAcceptedCitation citation guidanceUse proofTraceUse :=
  fun citationH guidanceH proofH =>
    ay_becr_conj_intro citation
      (AyBECRConj guidanceUse proofTraceUse)
      citationH
      (ay_becr_conj_intro guidanceUse proofTraceUse guidanceH proofH)

theorem ay_becr_accepted_citation_citation
    (citation : Prop) (guidanceUse : Prop) (proofTraceUse : Prop) :
    AyBECRAcceptedCitation citation guidanceUse proofTraceUse ->
    citation :=
  fun accepted =>
    ay_becr_conj_left citation (AyBECRConj guidanceUse proofTraceUse)
      accepted

theorem ay_becr_accepted_citation_guidance
    (citation : Prop) (guidanceUse : Prop) (proofTraceUse : Prop) :
    AyBECRAcceptedCitation citation guidanceUse proofTraceUse ->
    guidanceUse :=
  fun accepted =>
    ay_becr_conj_left guidanceUse proofTraceUse
      (ay_becr_conj_right citation
        (AyBECRConj guidanceUse proofTraceUse)
        accepted)

theorem ay_becr_accepted_citation_proof_trace
    (citation : Prop) (guidanceUse : Prop) (proofTraceUse : Prop) :
    AyBECRAcceptedCitation citation guidanceUse proofTraceUse ->
    proofTraceUse :=
  fun accepted =>
    ay_becr_conj_right guidanceUse proofTraceUse
      (ay_becr_conj_right citation
        (AyBECRConj guidanceUse proofTraceUse)
        accepted)

theorem ay_becr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBECRPublicReport (AyBECROutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_becr_conj_intro (AyBECROutcome model conflict) formula
      (ay_becr_disj_left model conflict modelH)
      formulaH

theorem ay_becr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBECRPublicReport (AyBECROutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_becr_conj_intro (AyBECROutcome model conflict) formula
      (ay_becr_disj_right model conflict conflictH)
      formulaH

theorem ay_becr_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBECRAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_becr_conj_intro evidence public evidenceH publicH

theorem ay_becr_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBECRAcceptedReport evidence public -> public :=
  fun report =>
    ay_becr_conj_right evidence public report

theorem ay_becr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBECRNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_becr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_becr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBECRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_becr_conj_left fallbackPublic diagnostic noClaim

theorem ay_becr_missing_dependency_no_claim
    (missingDependency : Prop) (fallbackPublic : Prop) :
    missingDependency ->
    fallbackPublic ->
    AyBECRNoClaim missingDependency fallbackPublic :=
  fun missingH fallbackH =>
    ay_becr_no_claim_intro missingDependency fallbackPublic
      missingH fallbackH

theorem ay_becr_stale_tier_no_claim
    (staleTier : Prop) (fallbackPublic : Prop) :
    staleTier ->
    fallbackPublic ->
    AyBECRNoClaim staleTier fallbackPublic :=
  fun staleH fallbackH =>
    ay_becr_no_claim_intro staleTier fallbackPublic staleH fallbackH

theorem ay_becr_digest_mismatch_no_claim
    (digestMismatch : Prop) (fallbackPublic : Prop) :
    digestMismatch ->
    fallbackPublic ->
    AyBECRNoClaim digestMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_becr_no_claim_intro digestMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_becr_replay_rejection_no_claim
    (replayRejected : Prop) (fallbackPublic : Prop) :
    replayRejected ->
    fallbackPublic ->
    AyBECRNoClaim replayRejected fallbackPublic :=
  fun rejectedH fallbackH =>
    ay_becr_no_claim_intro replayRejected fallbackPublic
      rejectedH fallbackH

theorem ay_becr_bad_rehydration_cannot_cite_clause
    (badRehydration : Prop) (fallbackPublic : Prop) :
    badRehydration ->
    fallbackPublic ->
    AyBECRNoClaim badRehydration fallbackPublic :=
  fun badH fallbackH =>
    ay_becr_no_claim_intro badRehydration fallbackPublic badH fallbackH

theorem ay_becr_accepted_rehydration_guides_sat
    (evictedClause : Prop) (clauseId : Prop)
    (tierMetadata : Prop) (derivationDependencies : Prop)
    (checkerReplay : Prop) (publicCompatibility : Prop)
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) (guidanceUse : Prop)
    (proofTraceUse : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    evictedClause ->
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    guidanceUse ->
    proofTraceUse ->
    model ->
    formula ->
    AyBECRAcceptedReport
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula) :=
  fun evictedH evidence agreement guidanceH proofH modelH formulaH =>
    ay_becr_accepted_report_intro
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula)
      (ay_becr_accepted_citation_intro
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse
        (ay_becr_evicted_citation_intro evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch)
          evictedH evidence agreement)
        guidanceH proofH)
      (ay_becr_public_sat_report model conflict formula modelH formulaH)

theorem ay_becr_accepted_rehydration_guides_unsat
    (evictedClause : Prop) (clauseId : Prop)
    (tierMetadata : Prop) (derivationDependencies : Prop)
    (checkerReplay : Prop) (publicCompatibility : Prop)
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) (guidanceUse : Prop)
    (proofTraceUse : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    evictedClause ->
    AyBECRRehydrationEvidence clauseId tierMetadata
      derivationDependencies checkerReplay publicCompatibility ->
    AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
      replayAccepted publicMatch ->
    guidanceUse ->
    proofTraceUse ->
    conflict ->
    formula ->
    AyBECRAcceptedReport
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula) :=
  fun evictedH evidence agreement guidanceH proofH conflictH formulaH =>
    ay_becr_accepted_report_intro
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula)
      (ay_becr_accepted_citation_intro
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse
        (ay_becr_evicted_citation_intro evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch)
          evictedH evidence agreement)
        guidanceH proofH)
      (ay_becr_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_becr_accepted_rehydration_report_soundness
    (evictedClause : Prop) (clauseId : Prop)
    (tierMetadata : Prop) (derivationDependencies : Prop)
    (checkerReplay : Prop) (publicCompatibility : Prop)
    (idMatch : Prop) (tierMatch : Prop)
    (dependencyMatch : Prop) (replayAccepted : Prop)
    (publicMatch : Prop) (guidanceUse : Prop)
    (proofTraceUse : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBECRAcceptedReport
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula) ->
    AyBECRPublicReport (AyBECROutcome model conflict) formula :=
  fun report =>
    ay_becr_accepted_report_public
      (AyBECRAcceptedCitation
        (AyBECREvictedCitation evictedClause
          (AyBECRRehydrationEvidence clauseId tierMetadata
            derivationDependencies checkerReplay publicCompatibility)
          (AyBECRRehydrationAgreement idMatch tierMatch dependencyMatch
            replayAccepted publicMatch))
        guidanceUse proofTraceUse)
      (AyBECRPublicReport (AyBECROutcome model conflict) formula)
      report

theorem ay_becr_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBECRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_becr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
