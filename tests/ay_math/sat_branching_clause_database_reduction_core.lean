-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded learned-clause database reduction soundness skeleton for ay SAT
-- solving. Retained learned clauses can be reused only when dependency
-- witnesses, retained-clause replay, formula fingerprint, and checker evidence
-- agree. Deleted clauses cannot be cited by public evidence unless rehydrated
-- and replayed; unsafe reductions fall back to no-claim/recompute.

def AyBCDRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBCDRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBCDREquisat (before : Prop) (after : Prop) :=
  AyBCDRConj (before -> after) (after -> before)

def AyBCDRDatabaseState (formula : Prop) (database : Prop) :=
  AyBCDRConj formula database

def AyBCDRReduction
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :=
  AyBCDRConj originalDb
    (AyBCDRConj retainedDb (AyBCDRConj deletedDb reductionPolicy))

def AyBCDRRetainedClause
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :=
  AyBCDRConj learnedClause
    (AyBCDRConj dependencyWitness
      (AyBCDRConj replayEvidence
        (AyBCDRConj formulaFingerprint checkerEvidence)))

def AyBCDRReuseAgreement
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :=
  AyBCDRConj dependencyMatch
    (AyBCDRConj replayMatch
      (AyBCDRConj fingerprintMatch checkerMatch))

def AyBCDRDeletedCitation
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :=
  AyBCDRConj deletedClause (AyBCDRConj rehydrated replayed)

def AyBCDRAcceptedEvidence
    (reduction : Prop) (retained : Prop) (agreement : Prop) :=
  AyBCDRConj reduction (AyBCDRConj retained agreement)

def AyBCDROutcome (model : Prop) (conflict : Prop) :=
  AyBCDRDisj model conflict

def AyBCDRPublicReport (outcome : Prop) (formula : Prop) :=
  AyBCDRConj outcome formula

def AyBCDRAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBCDRConj evidence public

def AyBCDRNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBCDRConj fallbackPublic diagnostic

theorem ay_bcdr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBCDRConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcdr_conj_left
    (left : Prop) (right : Prop) :
    AyBCDRConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcdr_conj_right
    (left : Prop) (right : Prop) :
    AyBCDRConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcdr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBCDRDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcdr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBCDRDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcdr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBCDREquisat before after :=
  fun forward backward =>
    ay_bcdr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcdr_equisat_forward
    (before : Prop) (after : Prop) :
    AyBCDREquisat before after -> before -> after :=
  fun equisat =>
    ay_bcdr_conj_left (before -> after) (after -> before) equisat

theorem ay_bcdr_equisat_backward
    (before : Prop) (after : Prop) :
    AyBCDREquisat before after -> after -> before :=
  fun equisat =>
    ay_bcdr_conj_right (before -> after) (after -> before) equisat

theorem ay_bcdr_database_state_intro
    (formula : Prop) (database : Prop) :
    formula -> database -> AyBCDRDatabaseState formula database :=
  fun formulaH databaseH =>
    ay_bcdr_conj_intro formula database formulaH databaseH

theorem ay_bcdr_database_state_formula
    (formula : Prop) (database : Prop) :
    AyBCDRDatabaseState formula database -> formula :=
  fun state =>
    ay_bcdr_conj_left formula database state

theorem ay_bcdr_database_state_database
    (formula : Prop) (database : Prop) :
    AyBCDRDatabaseState formula database -> database :=
  fun state =>
    ay_bcdr_conj_right formula database state

theorem ay_bcdr_preprocess_transport
    (before : Prop) (after : Prop) (database : Prop) :
    AyBCDREquisat before after ->
    AyBCDRDatabaseState before database ->
    AyBCDRDatabaseState after database :=
  fun equisat state =>
    ay_bcdr_conj_intro after database
      (ay_bcdr_equisat_forward before after equisat
        (ay_bcdr_database_state_formula before database state))
      (ay_bcdr_database_state_database before database state)

theorem ay_bcdr_reduction_intro
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    originalDb ->
    retainedDb ->
    deletedDb ->
    reductionPolicy ->
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy :=
  fun originalH retainedH deletedH policyH =>
    ay_bcdr_conj_intro originalDb
      (AyBCDRConj retainedDb (AyBCDRConj deletedDb reductionPolicy))
      originalH
      (ay_bcdr_conj_intro retainedDb
        (AyBCDRConj deletedDb reductionPolicy)
        retainedH
        (ay_bcdr_conj_intro deletedDb reductionPolicy
          deletedH policyH))

theorem ay_bcdr_reduction_original
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    originalDb :=
  fun reduction =>
    ay_bcdr_conj_left originalDb
      (AyBCDRConj retainedDb (AyBCDRConj deletedDb reductionPolicy))
      reduction

theorem ay_bcdr_reduction_tail
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    AyBCDRConj retainedDb (AyBCDRConj deletedDb reductionPolicy) :=
  fun reduction =>
    ay_bcdr_conj_right originalDb
      (AyBCDRConj retainedDb (AyBCDRConj deletedDb reductionPolicy))
      reduction

theorem ay_bcdr_reduction_retained
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    retainedDb :=
  fun reduction =>
    ay_bcdr_conj_left retainedDb (AyBCDRConj deletedDb reductionPolicy)
      (ay_bcdr_reduction_tail originalDb retainedDb deletedDb
        reductionPolicy reduction)

theorem ay_bcdr_reduction_deleted
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    deletedDb :=
  fun reduction =>
    ay_bcdr_conj_left deletedDb reductionPolicy
      (ay_bcdr_conj_right retainedDb
        (AyBCDRConj deletedDb reductionPolicy)
        (ay_bcdr_reduction_tail originalDb retainedDb deletedDb
          reductionPolicy reduction))

theorem ay_bcdr_reduction_policy
    (originalDb : Prop) (retainedDb : Prop) (deletedDb : Prop)
    (reductionPolicy : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    reductionPolicy :=
  fun reduction =>
    ay_bcdr_conj_right deletedDb reductionPolicy
      (ay_bcdr_conj_right retainedDb
        (AyBCDRConj deletedDb reductionPolicy)
        (ay_bcdr_reduction_tail originalDb retainedDb deletedDb
          reductionPolicy reduction))

theorem ay_bcdr_retained_clause_intro
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    learnedClause ->
    dependencyWitness ->
    replayEvidence ->
    formulaFingerprint ->
    checkerEvidence ->
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence :=
  fun learnedH dependencyH replayH fingerprintH checkerH =>
    ay_bcdr_conj_intro learnedClause
      (AyBCDRConj dependencyWitness
        (AyBCDRConj replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence)))
      learnedH
      (ay_bcdr_conj_intro dependencyWitness
        (AyBCDRConj replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence))
        dependencyH
        (ay_bcdr_conj_intro replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence)
          replayH
          (ay_bcdr_conj_intro formulaFingerprint checkerEvidence
            fingerprintH checkerH)))

theorem ay_bcdr_retained_clause_learned
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    learnedClause :=
  fun retained =>
    ay_bcdr_conj_left learnedClause
      (AyBCDRConj dependencyWitness
        (AyBCDRConj replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence)))
      retained

theorem ay_bcdr_retained_clause_tail
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    AyBCDRConj dependencyWitness
      (AyBCDRConj replayEvidence
        (AyBCDRConj formulaFingerprint checkerEvidence)) :=
  fun retained =>
    ay_bcdr_conj_right learnedClause
      (AyBCDRConj dependencyWitness
        (AyBCDRConj replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence)))
      retained

theorem ay_bcdr_retained_clause_dependency
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    dependencyWitness :=
  fun retained =>
    ay_bcdr_conj_left dependencyWitness
      (AyBCDRConj replayEvidence
        (AyBCDRConj formulaFingerprint checkerEvidence))
      (ay_bcdr_retained_clause_tail learnedClause dependencyWitness
        replayEvidence formulaFingerprint checkerEvidence retained)

theorem ay_bcdr_retained_clause_replay
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    replayEvidence :=
  fun retained =>
    ay_bcdr_conj_left replayEvidence
      (AyBCDRConj formulaFingerprint checkerEvidence)
      (ay_bcdr_conj_right dependencyWitness
        (AyBCDRConj replayEvidence
          (AyBCDRConj formulaFingerprint checkerEvidence))
        (ay_bcdr_retained_clause_tail learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence retained))

theorem ay_bcdr_retained_clause_fingerprint
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    formulaFingerprint :=
  fun retained =>
    ay_bcdr_conj_left formulaFingerprint checkerEvidence
      (ay_bcdr_conj_right replayEvidence
        (AyBCDRConj formulaFingerprint checkerEvidence)
        (ay_bcdr_conj_right dependencyWitness
          (AyBCDRConj replayEvidence
            (AyBCDRConj formulaFingerprint checkerEvidence))
          (ay_bcdr_retained_clause_tail learnedClause dependencyWitness
            replayEvidence formulaFingerprint checkerEvidence retained)))

theorem ay_bcdr_retained_clause_checker
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) :
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    checkerEvidence :=
  fun retained =>
    ay_bcdr_conj_right formulaFingerprint checkerEvidence
      (ay_bcdr_conj_right replayEvidence
        (AyBCDRConj formulaFingerprint checkerEvidence)
        (ay_bcdr_conj_right dependencyWitness
          (AyBCDRConj replayEvidence
            (AyBCDRConj formulaFingerprint checkerEvidence))
          (ay_bcdr_retained_clause_tail learnedClause dependencyWitness
            replayEvidence formulaFingerprint checkerEvidence retained)))

theorem ay_bcdr_reuse_agreement_intro
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    dependencyMatch ->
    replayMatch ->
    fingerprintMatch ->
    checkerMatch ->
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch :=
  fun dependencyH replayH fingerprintH checkerH =>
    ay_bcdr_conj_intro dependencyMatch
      (AyBCDRConj replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch))
      dependencyH
      (ay_bcdr_conj_intro replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch)
        replayH
        (ay_bcdr_conj_intro fingerprintMatch checkerMatch
          fingerprintH checkerH))

theorem ay_bcdr_reuse_agreement_dependency
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    dependencyMatch :=
  fun agreement =>
    ay_bcdr_conj_left dependencyMatch
      (AyBCDRConj replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch))
      agreement

theorem ay_bcdr_reuse_agreement_tail
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    AyBCDRConj replayMatch
      (AyBCDRConj fingerprintMatch checkerMatch) :=
  fun agreement =>
    ay_bcdr_conj_right dependencyMatch
      (AyBCDRConj replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch))
      agreement

theorem ay_bcdr_reuse_agreement_replay
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    replayMatch :=
  fun agreement =>
    ay_bcdr_conj_left replayMatch
      (AyBCDRConj fingerprintMatch checkerMatch)
      (ay_bcdr_reuse_agreement_tail dependencyMatch replayMatch
        fingerprintMatch checkerMatch agreement)

theorem ay_bcdr_reuse_agreement_fingerprint
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    fingerprintMatch :=
  fun agreement =>
    ay_bcdr_conj_left fingerprintMatch checkerMatch
      (ay_bcdr_conj_right replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch)
        (ay_bcdr_reuse_agreement_tail dependencyMatch replayMatch
          fingerprintMatch checkerMatch agreement))

theorem ay_bcdr_reuse_agreement_checker
    (dependencyMatch : Prop) (replayMatch : Prop)
    (fingerprintMatch : Prop) (checkerMatch : Prop) :
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_bcdr_conj_right fingerprintMatch checkerMatch
      (ay_bcdr_conj_right replayMatch
        (AyBCDRConj fingerprintMatch checkerMatch)
        (ay_bcdr_reuse_agreement_tail dependencyMatch replayMatch
          fingerprintMatch checkerMatch agreement))

theorem ay_bcdr_deleted_citation_intro
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    deletedClause ->
    rehydrated ->
    replayed ->
    AyBCDRDeletedCitation deletedClause rehydrated replayed :=
  fun deletedH rehydratedH replayedH =>
    ay_bcdr_conj_intro deletedClause
      (AyBCDRConj rehydrated replayed)
      deletedH
      (ay_bcdr_conj_intro rehydrated replayed rehydratedH replayedH)

theorem ay_bcdr_deleted_citation_clause
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBCDRDeletedCitation deletedClause rehydrated replayed ->
    deletedClause :=
  fun citation =>
    ay_bcdr_conj_left deletedClause
      (AyBCDRConj rehydrated replayed)
      citation

theorem ay_bcdr_deleted_citation_rehydrated
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBCDRDeletedCitation deletedClause rehydrated replayed ->
    rehydrated :=
  fun citation =>
    ay_bcdr_conj_left rehydrated replayed
      (ay_bcdr_conj_right deletedClause
        (AyBCDRConj rehydrated replayed)
        citation)

theorem ay_bcdr_deleted_citation_replayed
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBCDRDeletedCitation deletedClause rehydrated replayed ->
    replayed :=
  fun citation =>
    ay_bcdr_conj_right rehydrated replayed
      (ay_bcdr_conj_right deletedClause
        (AyBCDRConj rehydrated replayed)
        citation)

theorem ay_bcdr_accepted_evidence_intro
    (reduction : Prop) (retained : Prop) (agreement : Prop) :
    reduction ->
    retained ->
    agreement ->
    AyBCDRAcceptedEvidence reduction retained agreement :=
  fun reductionH retainedH agreementH =>
    ay_bcdr_conj_intro reduction (AyBCDRConj retained agreement)
      reductionH
      (ay_bcdr_conj_intro retained agreement retainedH agreementH)

theorem ay_bcdr_accepted_evidence_reduction
    (reduction : Prop) (retained : Prop) (agreement : Prop) :
    AyBCDRAcceptedEvidence reduction retained agreement -> reduction :=
  fun evidence =>
    ay_bcdr_conj_left reduction (AyBCDRConj retained agreement)
      evidence

theorem ay_bcdr_accepted_evidence_retained
    (reduction : Prop) (retained : Prop) (agreement : Prop) :
    AyBCDRAcceptedEvidence reduction retained agreement -> retained :=
  fun evidence =>
    ay_bcdr_conj_left retained agreement
      (ay_bcdr_conj_right reduction (AyBCDRConj retained agreement)
        evidence)

theorem ay_bcdr_accepted_evidence_agreement
    (reduction : Prop) (retained : Prop) (agreement : Prop) :
    AyBCDRAcceptedEvidence reduction retained agreement -> agreement :=
  fun evidence =>
    ay_bcdr_conj_right retained agreement
      (ay_bcdr_conj_right reduction (AyBCDRConj retained agreement)
        evidence)

theorem ay_bcdr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBCDRPublicReport (AyBCDROutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcdr_conj_intro (AyBCDROutcome model conflict) formula
      (ay_bcdr_disj_left model conflict modelH)
      formulaH

theorem ay_bcdr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBCDRPublicReport (AyBCDROutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcdr_conj_intro (AyBCDROutcome model conflict) formula
      (ay_bcdr_disj_right model conflict conflictH)
      formulaH

theorem ay_bcdr_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBCDRAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_bcdr_conj_intro evidence public evidenceH publicH

theorem ay_bcdr_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBCDRAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_bcdr_conj_left evidence public report

theorem ay_bcdr_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBCDRAcceptedReport evidence public -> public :=
  fun report =>
    ay_bcdr_conj_right evidence public report

theorem ay_bcdr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBCDRNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcdr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCDRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcdr_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcdr_deleted_clause_needs_rehydration
    (deletedClause : Prop) (fallbackPublic : Prop) :
    deletedClause ->
    fallbackPublic ->
    AyBCDRNoClaim deletedClause fallbackPublic :=
  fun deletedH fallbackH =>
    ay_bcdr_no_claim_intro deletedClause fallbackPublic
      deletedH fallbackH

theorem ay_bcdr_rehydrated_clause_citable
    (deletedClause : Prop) (rehydrated : Prop) (replayed : Prop) :
    AyBCDRDeletedCitation deletedClause rehydrated replayed ->
    AyBCDRConj rehydrated replayed :=
  fun citation =>
    ay_bcdr_conj_intro rehydrated replayed
      (ay_bcdr_deleted_citation_rehydrated deletedClause rehydrated
        replayed citation)
      (ay_bcdr_deleted_citation_replayed deletedClause rehydrated
        replayed citation)

theorem ay_bcdr_dependency_mismatch_no_claim
    (dependencyMismatch : Prop) (fallbackPublic : Prop) :
    dependencyMismatch ->
    fallbackPublic ->
    AyBCDRNoClaim dependencyMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcdr_no_claim_intro dependencyMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcdr_fingerprint_mismatch_no_claim
    (fingerprintMismatch : Prop) (fallbackPublic : Prop) :
    fingerprintMismatch ->
    fallbackPublic ->
    AyBCDRNoClaim fingerprintMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcdr_no_claim_intro fingerprintMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcdr_checker_mismatch_no_claim
    (checkerMismatch : Prop) (fallbackPublic : Prop) :
    checkerMismatch ->
    fallbackPublic ->
    AyBCDRNoClaim checkerMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcdr_no_claim_intro checkerMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcdr_safe_reduction_guides_sat
    (formula : Prop) (originalDb : Prop) (retainedDb : Prop)
    (deletedDb : Prop) (reductionPolicy : Prop)
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) (dependencyMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (checkerMatch : Prop) (model : Prop) (conflict : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    model ->
    formula ->
    AyBCDRAcceptedReport
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula) :=
  fun reduction retained agreement modelH formulaH =>
    ay_bcdr_accepted_report_intro
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula)
      (ay_bcdr_accepted_evidence_intro
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch)
        reduction retained agreement)
      (ay_bcdr_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcdr_safe_reduction_guides_unsat
    (formula : Prop) (originalDb : Prop) (retainedDb : Prop)
    (deletedDb : Prop) (reductionPolicy : Prop)
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) (dependencyMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (checkerMatch : Prop) (model : Prop) (conflict : Prop) :
    AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy ->
    AyBCDRRetainedClause learnedClause dependencyWitness replayEvidence
      formulaFingerprint checkerEvidence ->
    AyBCDRReuseAgreement dependencyMatch replayMatch
      fingerprintMatch checkerMatch ->
    conflict ->
    formula ->
    AyBCDRAcceptedReport
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula) :=
  fun reduction retained agreement conflictH formulaH =>
    ay_bcdr_accepted_report_intro
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula)
      (ay_bcdr_accepted_evidence_intro
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch)
        reduction retained agreement)
      (ay_bcdr_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bcdr_accepted_reduction_report_soundness
    (formula : Prop) (originalDb : Prop) (retainedDb : Prop)
    (deletedDb : Prop) (reductionPolicy : Prop)
    (learnedClause : Prop) (dependencyWitness : Prop)
    (replayEvidence : Prop) (formulaFingerprint : Prop)
    (checkerEvidence : Prop) (dependencyMatch : Prop)
    (replayMatch : Prop) (fingerprintMatch : Prop)
    (checkerMatch : Prop) (model : Prop) (conflict : Prop) :
    AyBCDRAcceptedReport
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula) ->
    AyBCDRPublicReport (AyBCDROutcome model conflict) formula :=
  fun report =>
    ay_bcdr_accepted_report_public
      (AyBCDRAcceptedEvidence
        (AyBCDRReduction originalDb retainedDb deletedDb reductionPolicy)
        (AyBCDRRetainedClause learnedClause dependencyWitness
          replayEvidence formulaFingerprint checkerEvidence)
        (AyBCDRReuseAgreement dependencyMatch replayMatch
          fingerprintMatch checkerMatch))
      (AyBCDRPublicReport (AyBCDROutcome model conflict) formula)
      report

theorem ay_bcdr_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCDRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcdr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
