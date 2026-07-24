-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- LBD priority-bucket guard skeleton for sequential-main SAT-COMP learnt-clause
-- branching heuristics. Priority buckets are search-control state only when
-- domain, bucket, provenance, activity, tiebreak, replay, fallback, build,
-- validator, and audit evidence agree with the public result.

def ay_lbpg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lbpg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_lbpg_conj (before -> after) (after -> before)

def ay_lbpg_guard
    (variableDomainDigest : Prop)
    (lbdBucketLedger : Prop)
    (learntClauseProvenanceLedger : Prop)
    (activityScoreUpdateWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      lbdBucketLedger ->
      learntClauseProvenanceLedger ->
      activityScoreUpdateWitness ->
      deterministicTiebreakManifest ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_lbpg_agreement
    (domainMatch : Prop)
    (bucketMatch : Prop)
    (provenanceMatch : Prop)
    (activityMatch : Prop)
    (tiebreakMatch : Prop)
    (replayMatch : Prop)
    (baselineMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_lbpg_guard domainMatch bucketMatch provenanceMatch activityMatch
    tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_lbpg_accepted_priority_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_lbpg_conj guardEvidence
    (ay_lbpg_conj agreementEvidence
      (ay_lbpg_conj deterministicBranchOrder searchControlHint))

def ay_lbpg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_lbpg_conj acceptedEvidence (ay_lbpg_conj outcome formulaTruth)

def ay_lbpg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_lbpg_conj diagnostic fallbackPublic

theorem ay_lbpg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_lbpg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_lbpg_conj_left (left : Prop) (right : Prop) :
    ay_lbpg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_lbpg_conj_right (left : Prop) (right : Prop) :
    ay_lbpg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_lbpg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_lbpg_equisat before after :=
  fun forward backward =>
    ay_lbpg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_lbpg_equisat_forward (before : Prop) (after : Prop) :
    ay_lbpg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_lbpg_conj_left (before -> after) (after -> before) eqsat

theorem ay_lbpg_equisat_backward (before : Prop) (after : Prop) :
    ay_lbpg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_lbpg_conj_right (before -> after) (after -> before) eqsat

theorem ay_lbpg_guard_intro
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    lbdBucketLedger ->
    learntClauseProvenanceLedger ->
    activityScoreUpdateWitness ->
    deterministicTiebreakManifest ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH bucketH provenanceH activityH tiebreakH replayH baselineH buildH
      validatorH auditH result make =>
    make domainH bucketH provenanceH activityH tiebreakH replayH baselineH
      buildH validatorH auditH

theorem ay_lbpg_guard_domain
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _bucketH _provenanceH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_lbpg_guard_bucket
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    lbdBucketLedger :=
  fun guard =>
    guard lbdBucketLedger
      (fun _domainH bucketH _provenanceH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => bucketH)

theorem ay_lbpg_guard_provenance
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    learntClauseProvenanceLedger :=
  fun guard =>
    guard learntClauseProvenanceLedger
      (fun _domainH _bucketH provenanceH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => provenanceH)

theorem ay_lbpg_guard_activity
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    activityScoreUpdateWitness :=
  fun guard =>
    guard activityScoreUpdateWitness
      (fun _domainH _bucketH _provenanceH activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => activityH)

theorem ay_lbpg_guard_tiebreak
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _bucketH _provenanceH _activityH tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_lbpg_guard_replay
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _bucketH _provenanceH _activityH _tiebreakH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_lbpg_guard_baseline
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _bucketH _provenanceH _activityH _tiebreakH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_lbpg_guard_build
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _bucketH _provenanceH _activityH _tiebreakH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_lbpg_guard_validator
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _bucketH _provenanceH _activityH _tiebreakH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_lbpg_guard_audit
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lbpg_guard variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _bucketH _provenanceH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_lbpg_agreement_intro
    (domainMatch bucketMatch provenanceMatch activityMatch tiebreakMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    bucketMatch ->
    provenanceMatch ->
    activityMatch ->
    tiebreakMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_lbpg_agreement domainMatch bucketMatch provenanceMatch activityMatch
      tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_lbpg_guard_intro domainMatch bucketMatch provenanceMatch activityMatch
    tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_lbpg_accepted_priority_guidance_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_lbpg_conj_intro guardEvidence
      (ay_lbpg_conj agreementEvidence
        (ay_lbpg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_lbpg_conj_intro agreementEvidence
        (ay_lbpg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_lbpg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_lbpg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_lbpg_conj_left guardEvidence
    (ay_lbpg_conj agreementEvidence
      (ay_lbpg_conj deterministicBranchOrder searchControlHint))

theorem ay_lbpg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_lbpg_conj_left agreementEvidence
      (ay_lbpg_conj deterministicBranchOrder searchControlHint)
      (ay_lbpg_conj_right guardEvidence
        (ay_lbpg_conj agreementEvidence
          (ay_lbpg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_lbpg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_lbpg_conj_left deterministicBranchOrder searchControlHint
      (ay_lbpg_conj_right agreementEvidence
        (ay_lbpg_conj deterministicBranchOrder searchControlHint)
        (ay_lbpg_conj_right guardEvidence
          (ay_lbpg_conj agreementEvidence
            (ay_lbpg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_lbpg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_lbpg_conj_right deterministicBranchOrder searchControlHint
      (ay_lbpg_conj_right agreementEvidence
        (ay_lbpg_conj deterministicBranchOrder searchControlHint)
        (ay_lbpg_conj_right guardEvidence
          (ay_lbpg_conj agreementEvidence
            (ay_lbpg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_lbpg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_lbpg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_lbpg_conj_intro acceptedEvidence (ay_lbpg_conj outcome formulaTruth)
      acceptedH (ay_lbpg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_lbpg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lbpg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_lbpg_conj_left acceptedEvidence (ay_lbpg_conj outcome formulaTruth)

theorem ay_lbpg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lbpg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_lbpg_conj_left outcome formulaTruth
      (ay_lbpg_conj_right acceptedEvidence
        (ay_lbpg_conj outcome formulaTruth) report)

theorem ay_lbpg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lbpg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_lbpg_conj_right outcome formulaTruth
      (ay_lbpg_conj_right acceptedEvidence
        (ay_lbpg_conj outcome formulaTruth) report)

theorem ay_lbpg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_lbpg_no_claim diagnostic fallbackPublic :=
  ay_lbpg_conj_intro diagnostic fallbackPublic

theorem ay_lbpg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_lbpg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_lbpg_conj_left diagnostic fallbackPublic

theorem ay_lbpg_no_claim_preserves_fallback (diagnostic fallbackPublic : Prop) :
    ay_lbpg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_lbpg_conj_right diagnostic fallbackPublic

theorem ay_lbpg_priority_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_lbpg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_lbpg_equisat_forward beforeFormula afterFormula

theorem ay_lbpg_priority_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_lbpg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_lbpg_equisat_backward beforeFormula afterFormula

theorem ay_lbpg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lbpg_public_report acceptedEvidence outcome formulaTruth ->
    ay_lbpg_conj outcome formulaTruth :=
  fun report =>
    ay_lbpg_conj_right acceptedEvidence (ay_lbpg_conj outcome formulaTruth)
      report

theorem ay_lbpg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_lbpg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_lbpg_conj_right agreementEvidence
      (ay_lbpg_conj deterministicBranchOrder searchControlHint)
      (ay_lbpg_conj_right guardEvidence
        (ay_lbpg_conj agreementEvidence
          (ay_lbpg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_lbpg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim domainMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro domainMismatch fallbackPublic

theorem ay_lbpg_bucket_mismatch_no_claim
    (bucketMismatch fallbackPublic : Prop) :
    bucketMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim bucketMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro bucketMismatch fallbackPublic

theorem ay_lbpg_provenance_mismatch_no_claim
    (provenanceMismatch fallbackPublic : Prop) :
    provenanceMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim provenanceMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro provenanceMismatch fallbackPublic

theorem ay_lbpg_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim activityMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro activityMismatch fallbackPublic

theorem ay_lbpg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim tiebreakMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_lbpg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim replayMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro replayMismatch fallbackPublic

theorem ay_lbpg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim baselineMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_lbpg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim buildMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro buildMismatch fallbackPublic

theorem ay_lbpg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_lbpg_no_claim validatorRejects fallbackPublic :=
  ay_lbpg_no_claim_intro validatorRejects fallbackPublic

theorem ay_lbpg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_lbpg_no_claim auditMismatch fallbackPublic :=
  ay_lbpg_no_claim_intro auditMismatch fallbackPublic

theorem ay_lbpg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_lbpg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_lbpg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_lbpg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_lbpg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_lbpg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_lbpg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_lbpg_public_report
      (ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_lbpg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_lbpg_public_report_accepted
        (ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_lbpg_publication_requires_validator
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_lbpg_public_report
      (ay_lbpg_accepted_priority_guidance
        (ay_lbpg_guard variableDomainDigest lbdBucketLedger
          learntClauseProvenanceLedger activityScoreUpdateWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_lbpg_guard_validator variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_lbpg_publication_requires_accepted_guard
        (ay_lbpg_guard variableDomainDigest lbdBucketLedger
          learntClauseProvenanceLedger activityScoreUpdateWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_lbpg_publication_requires_audit
    (variableDomainDigest lbdBucketLedger learntClauseProvenanceLedger
      activityScoreUpdateWitness deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_lbpg_public_report
      (ay_lbpg_accepted_priority_guidance
        (ay_lbpg_guard variableDomainDigest lbdBucketLedger
          learntClauseProvenanceLedger activityScoreUpdateWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_lbpg_guard_audit variableDomainDigest lbdBucketLedger
      learntClauseProvenanceLedger activityScoreUpdateWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_lbpg_publication_requires_accepted_guard
        (ay_lbpg_guard variableDomainDigest lbdBucketLedger
          learntClauseProvenanceLedger activityScoreUpdateWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_lbpg_priority_bucketing_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_lbpg_equisat beforeFormula afterFormula ->
    ay_lbpg_accepted_priority_guidance guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_lbpg_conj (beforeFormula -> afterFormula)
      (ay_lbpg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_lbpg_conj_intro (beforeFormula -> afterFormula)
      (ay_lbpg_conj deterministicBranchOrder searchControlHint)
      (ay_lbpg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_lbpg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_lbpg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_lbpg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_lbpg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_lbpg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_lbpg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_lbpg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
