-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause-tier eviction audit soundness skeleton for ay SAT solving.
-- Evicting learned clauses by LBD/activity tier is admissible only when the
-- eviction audit, retained dependencies, checker replay, and public
-- proof/model evidence agree. An evicted clause cannot be cited later unless
-- rehydrated and replayed; otherwise the checker falls back to no-claim or
-- recompute.

def AyBTEAConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBTEADisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBTEAEquisat (before : Prop) (after : Prop) :=
  AyBTEAConj (before -> after) (after -> before)

def AyBTEAEvictionAudit
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :=
  AyBTEAConj evictionPolicy
    (AyBTEAConj tierEvidence
      (AyBTEAConj retainedDependencies
        (AyBTEAConj checkerReplay publicEvidence)))

def AyBTEAAgreement
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :=
  AyBTEAConj auditMatch
    (AyBTEAConj dependencyMatch
      (AyBTEAConj checkerMatch publicMatch))

def AyBTEAEvictedCitation
    (evictedClause : Prop) (rehydrated : Prop) (replayed : Prop) :=
  AyBTEAConj evictedClause (AyBTEAConj rehydrated replayed)

def AyBTEAAcceptedEviction
    (audit : Prop) (agreement : Prop) (retainedUse : Prop) :=
  AyBTEAConj audit (AyBTEAConj agreement retainedUse)

def AyBTEAOutcome (model : Prop) (conflict : Prop) :=
  AyBTEADisj model conflict

def AyBTEAPublicReport (outcome : Prop) (formula : Prop) :=
  AyBTEAConj outcome formula

def AyBTEAAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBTEAConj evidence public

def AyBTEANoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBTEAConj fallbackPublic diagnostic

theorem ay_btea_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBTEAConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_btea_conj_left
    (left : Prop) (right : Prop) :
    AyBTEAConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_btea_conj_right
    (left : Prop) (right : Prop) :
    AyBTEAConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_btea_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBTEADisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_btea_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBTEADisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_btea_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBTEAEquisat before after :=
  fun forward backward =>
    ay_btea_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_btea_equisat_forward
    (before : Prop) (after : Prop) :
    AyBTEAEquisat before after -> before -> after :=
  fun equisat =>
    ay_btea_conj_left (before -> after) (after -> before) equisat

theorem ay_btea_equisat_backward
    (before : Prop) (after : Prop) :
    AyBTEAEquisat before after -> after -> before :=
  fun equisat =>
    ay_btea_conj_right (before -> after) (after -> before) equisat

theorem ay_btea_eviction_audit_intro
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    evictionPolicy ->
    tierEvidence ->
    retainedDependencies ->
    checkerReplay ->
    publicEvidence ->
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence :=
  fun policyH tierH dependencyH checkerH publicH =>
    ay_btea_conj_intro evictionPolicy
      (AyBTEAConj tierEvidence
        (AyBTEAConj retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence)))
      policyH
      (ay_btea_conj_intro tierEvidence
        (AyBTEAConj retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence))
        tierH
        (ay_btea_conj_intro retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence)
          dependencyH
          (ay_btea_conj_intro checkerReplay publicEvidence
            checkerH publicH)))

theorem ay_btea_eviction_audit_policy
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    evictionPolicy :=
  fun audit =>
    ay_btea_conj_left evictionPolicy
      (AyBTEAConj tierEvidence
        (AyBTEAConj retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence)))
      audit

theorem ay_btea_eviction_audit_tail
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    AyBTEAConj tierEvidence
      (AyBTEAConj retainedDependencies
        (AyBTEAConj checkerReplay publicEvidence)) :=
  fun audit =>
    ay_btea_conj_right evictionPolicy
      (AyBTEAConj tierEvidence
        (AyBTEAConj retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence)))
      audit

theorem ay_btea_eviction_audit_tier
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    tierEvidence :=
  fun audit =>
    ay_btea_conj_left tierEvidence
      (AyBTEAConj retainedDependencies
        (AyBTEAConj checkerReplay publicEvidence))
      (ay_btea_eviction_audit_tail evictionPolicy tierEvidence
        retainedDependencies checkerReplay publicEvidence audit)

theorem ay_btea_eviction_audit_dependencies
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    retainedDependencies :=
  fun audit =>
    ay_btea_conj_left retainedDependencies
      (AyBTEAConj checkerReplay publicEvidence)
      (ay_btea_conj_right tierEvidence
        (AyBTEAConj retainedDependencies
          (AyBTEAConj checkerReplay publicEvidence))
        (ay_btea_eviction_audit_tail evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence audit))

theorem ay_btea_eviction_audit_checker
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    checkerReplay :=
  fun audit =>
    ay_btea_conj_left checkerReplay publicEvidence
      (ay_btea_conj_right retainedDependencies
        (AyBTEAConj checkerReplay publicEvidence)
        (ay_btea_conj_right tierEvidence
          (AyBTEAConj retainedDependencies
            (AyBTEAConj checkerReplay publicEvidence))
          (ay_btea_eviction_audit_tail evictionPolicy tierEvidence
            retainedDependencies checkerReplay publicEvidence audit)))

theorem ay_btea_eviction_audit_public
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    publicEvidence :=
  fun audit =>
    ay_btea_conj_right checkerReplay publicEvidence
      (ay_btea_conj_right retainedDependencies
        (AyBTEAConj checkerReplay publicEvidence)
        (ay_btea_conj_right tierEvidence
          (AyBTEAConj retainedDependencies
            (AyBTEAConj checkerReplay publicEvidence))
          (ay_btea_eviction_audit_tail evictionPolicy tierEvidence
            retainedDependencies checkerReplay publicEvidence audit)))

theorem ay_btea_agreement_intro
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    auditMatch ->
    dependencyMatch ->
    checkerMatch ->
    publicMatch ->
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch :=
  fun auditH dependencyH checkerH publicH =>
    ay_btea_conj_intro auditMatch
      (AyBTEAConj dependencyMatch
        (AyBTEAConj checkerMatch publicMatch))
      auditH
      (ay_btea_conj_intro dependencyMatch
        (AyBTEAConj checkerMatch publicMatch)
        dependencyH
        (ay_btea_conj_intro checkerMatch publicMatch checkerH publicH))

theorem ay_btea_agreement_audit
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch ->
    auditMatch :=
  fun agreement =>
    ay_btea_conj_left auditMatch
      (AyBTEAConj dependencyMatch
        (AyBTEAConj checkerMatch publicMatch))
      agreement

theorem ay_btea_agreement_tail
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch ->
    AyBTEAConj dependencyMatch
      (AyBTEAConj checkerMatch publicMatch) :=
  fun agreement =>
    ay_btea_conj_right auditMatch
      (AyBTEAConj dependencyMatch
        (AyBTEAConj checkerMatch publicMatch))
      agreement

theorem ay_btea_agreement_dependency
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_btea_conj_left dependencyMatch
      (AyBTEAConj checkerMatch publicMatch)
      (ay_btea_agreement_tail auditMatch dependencyMatch checkerMatch
        publicMatch agreement)

theorem ay_btea_agreement_checker
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch ->
    checkerMatch :=
  fun agreement =>
    ay_btea_conj_left checkerMatch publicMatch
      (ay_btea_conj_right dependencyMatch
        (AyBTEAConj checkerMatch publicMatch)
        (ay_btea_agreement_tail auditMatch dependencyMatch checkerMatch
          publicMatch agreement))

theorem ay_btea_agreement_public
    (auditMatch : Prop) (dependencyMatch : Prop)
    (checkerMatch : Prop) (publicMatch : Prop) :
    AyBTEAAgreement auditMatch dependencyMatch
      checkerMatch publicMatch ->
    publicMatch :=
  fun agreement =>
    ay_btea_conj_right checkerMatch publicMatch
      (ay_btea_conj_right dependencyMatch
        (AyBTEAConj checkerMatch publicMatch)
        (ay_btea_agreement_tail auditMatch dependencyMatch checkerMatch
          publicMatch agreement))

theorem ay_btea_evicted_citation_intro
    (evictedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    evictedClause ->
    rehydrated ->
    replayed ->
    AyBTEAEvictedCitation evictedClause rehydrated replayed :=
  fun evictedH rehydratedH replayedH =>
    ay_btea_conj_intro evictedClause
      (AyBTEAConj rehydrated replayed)
      evictedH
      (ay_btea_conj_intro rehydrated replayed rehydratedH replayedH)

theorem ay_btea_evicted_citation_rehydrated
    (evictedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBTEAEvictedCitation evictedClause rehydrated replayed ->
    rehydrated :=
  fun citation =>
    ay_btea_conj_left rehydrated replayed
      (ay_btea_conj_right evictedClause
        (AyBTEAConj rehydrated replayed)
        citation)

theorem ay_btea_evicted_citation_replayed
    (evictedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBTEAEvictedCitation evictedClause rehydrated replayed ->
    replayed :=
  fun citation =>
    ay_btea_conj_right rehydrated replayed
      (ay_btea_conj_right evictedClause
        (AyBTEAConj rehydrated replayed)
        citation)

theorem ay_btea_evicted_clause_citable_after_replay
    (evictedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBTEAEvictedCitation evictedClause rehydrated replayed ->
    AyBTEAConj rehydrated replayed :=
  fun citation =>
    ay_btea_conj_intro rehydrated replayed
      (ay_btea_evicted_citation_rehydrated evictedClause rehydrated
        replayed citation)
      (ay_btea_evicted_citation_replayed evictedClause rehydrated
        replayed citation)

theorem ay_btea_accepted_eviction_intro
    (audit : Prop) (agreement : Prop) (retainedUse : Prop) :
    audit ->
    agreement ->
    retainedUse ->
    AyBTEAAcceptedEviction audit agreement retainedUse :=
  fun auditH agreementH retainedH =>
    ay_btea_conj_intro audit (AyBTEAConj agreement retainedUse)
      auditH
      (ay_btea_conj_intro agreement retainedUse agreementH retainedH)

theorem ay_btea_accepted_eviction_audit
    (audit : Prop) (agreement : Prop) (retainedUse : Prop) :
    AyBTEAAcceptedEviction audit agreement retainedUse -> audit :=
  fun accepted =>
    ay_btea_conj_left audit (AyBTEAConj agreement retainedUse)
      accepted

theorem ay_btea_accepted_eviction_agreement
    (audit : Prop) (agreement : Prop) (retainedUse : Prop) :
    AyBTEAAcceptedEviction audit agreement retainedUse -> agreement :=
  fun accepted =>
    ay_btea_conj_left agreement retainedUse
      (ay_btea_conj_right audit (AyBTEAConj agreement retainedUse)
        accepted)

theorem ay_btea_accepted_eviction_retained
    (audit : Prop) (agreement : Prop) (retainedUse : Prop) :
    AyBTEAAcceptedEviction audit agreement retainedUse -> retainedUse :=
  fun accepted =>
    ay_btea_conj_right agreement retainedUse
      (ay_btea_conj_right audit (AyBTEAConj agreement retainedUse)
        accepted)

theorem ay_btea_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBTEAPublicReport (AyBTEAOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_btea_conj_intro (AyBTEAOutcome model conflict) formula
      (ay_btea_disj_left model conflict modelH)
      formulaH

theorem ay_btea_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBTEAPublicReport (AyBTEAOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_btea_conj_intro (AyBTEAOutcome model conflict) formula
      (ay_btea_disj_right model conflict conflictH)
      formulaH

theorem ay_btea_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBTEAAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_btea_conj_intro evidence public evidenceH publicH

theorem ay_btea_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBTEAAcceptedReport evidence public -> public :=
  fun report =>
    ay_btea_conj_right evidence public report

theorem ay_btea_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBTEANoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_btea_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_btea_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBTEANoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_btea_conj_left fallbackPublic diagnostic noClaim

theorem ay_btea_evicted_clause_no_claim
    (evictedClause : Prop) (fallbackPublic : Prop) :
    evictedClause ->
    fallbackPublic ->
    AyBTEANoClaim evictedClause fallbackPublic :=
  fun evictedH fallbackH =>
    ay_btea_no_claim_intro evictedClause fallbackPublic
      evictedH fallbackH

theorem ay_btea_audit_mismatch_no_claim
    (auditMismatch : Prop) (fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    AyBTEANoClaim auditMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_btea_no_claim_intro auditMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_btea_dependency_mismatch_no_claim
    (dependencyMismatch : Prop) (fallbackPublic : Prop) :
    dependencyMismatch ->
    fallbackPublic ->
    AyBTEANoClaim dependencyMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_btea_no_claim_intro dependencyMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_btea_evicted_clause_cannot_be_cited
    (evictedClause : Prop) (fallbackPublic : Prop) :
    evictedClause ->
    fallbackPublic ->
    AyBTEANoClaim evictedClause fallbackPublic :=
  fun evictedH fallbackH =>
    ay_btea_evicted_clause_no_claim evictedClause fallbackPublic
      evictedH fallbackH

theorem ay_btea_accepted_eviction_guides_sat
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) (auditMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicMatch : Prop) (retainedUse : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    AyBTEAAgreement auditMatch dependencyMatch checkerMatch publicMatch ->
    retainedUse ->
    model ->
    formula ->
    AyBTEAAcceptedReport
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula) :=
  fun audit agreement retainedH modelH formulaH =>
    ay_btea_accepted_report_intro
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula)
      (ay_btea_accepted_eviction_intro
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse
        audit agreement retainedH)
      (ay_btea_public_sat_report model conflict formula modelH formulaH)

theorem ay_btea_accepted_eviction_guides_unsat
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) (auditMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicMatch : Prop) (retainedUse : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBTEAEvictionAudit evictionPolicy tierEvidence
      retainedDependencies checkerReplay publicEvidence ->
    AyBTEAAgreement auditMatch dependencyMatch checkerMatch publicMatch ->
    retainedUse ->
    conflict ->
    formula ->
    AyBTEAAcceptedReport
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula) :=
  fun audit agreement retainedH conflictH formulaH =>
    ay_btea_accepted_report_intro
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula)
      (ay_btea_accepted_eviction_intro
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse
        audit agreement retainedH)
      (ay_btea_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_btea_accepted_eviction_report_soundness
    (evictionPolicy : Prop) (tierEvidence : Prop)
    (retainedDependencies : Prop) (checkerReplay : Prop)
    (publicEvidence : Prop) (auditMatch : Prop)
    (dependencyMatch : Prop) (checkerMatch : Prop)
    (publicMatch : Prop) (retainedUse : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBTEAAcceptedReport
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula) ->
    AyBTEAPublicReport (AyBTEAOutcome model conflict) formula :=
  fun report =>
    ay_btea_accepted_report_public
      (AyBTEAAcceptedEviction
        (AyBTEAEvictionAudit evictionPolicy tierEvidence
          retainedDependencies checkerReplay publicEvidence)
        (AyBTEAAgreement auditMatch dependencyMatch checkerMatch
          publicMatch)
        retainedUse)
      (AyBTEAPublicReport (AyBTEAOutcome model conflict) formula)
      report

theorem ay_btea_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBTEANoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_btea_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
