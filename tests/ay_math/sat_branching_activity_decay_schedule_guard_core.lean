-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Activity-decay schedule guard for sequential-main SAT-COMP branching.
-- Decay is search-control only when domain, activity, factor, rounding,
-- tiebreak, decision replay, propagation replay, fallback, build, validator,
-- and audit evidence agree.

def ay_adsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_adsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_adsg_conj (before -> after) (after -> before)

def ay_adsg_guard
    (variableDomainDigest : Prop)
    (activityScoreLedger : Prop)
    (decayFactorManifest : Prop)
    (rescaleRoundingPolicyWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityScoreLedger ->
      decayFactorManifest ->
      rescaleRoundingPolicyWitness ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_adsg_agreement
    (domainMatch activityMatch factorMatch roundingMatch tiebreakMatch
      decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch : Prop) : Prop :=
  ay_adsg_guard domainMatch activityMatch factorMatch roundingMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

def ay_adsg_accepted_decay
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_adsg_conj guardEvidence
    (ay_adsg_conj agreementEvidence
      (ay_adsg_conj deterministicBranchOrder searchControlHint))

def ay_adsg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_adsg_conj acceptedEvidence (ay_adsg_conj outcome formulaTruth)

def ay_adsg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_adsg_conj diagnostic fallbackPublic

theorem ay_adsg_conj_intro (left right : Prop) :
    left -> right -> ay_adsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_adsg_conj_left (left right : Prop) :
    ay_adsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_adsg_conj_right (left right : Prop) :
    ay_adsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_adsg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_adsg_equisat before after :=
  fun forward backward =>
    ay_adsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_adsg_equisat_forward (before after : Prop) :
    ay_adsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_adsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_adsg_equisat_backward (before after : Prop) :
    ay_adsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_adsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_adsg_guard_intro
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityScoreLedger ->
    decayFactorManifest ->
    rescaleRoundingPolicyWitness ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH activityH factorH roundingH tiebreakH decisionH replayH
      baselineH buildH validatorH auditH result make =>
    make domainH activityH factorH roundingH tiebreakH decisionH replayH
      baselineH buildH validatorH auditH

theorem ay_adsg_guard_domain
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_adsg_guard_activity
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityScoreLedger :=
  fun guard =>
    guard activityScoreLedger
      (fun _domainH activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH _auditH => activityH)

theorem ay_adsg_guard_factor
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decayFactorManifest :=
  fun guard =>
    guard decayFactorManifest
      (fun _domainH _activityH factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH _auditH => factorH)

theorem ay_adsg_guard_rounding
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    rescaleRoundingPolicyWitness :=
  fun guard =>
    guard rescaleRoundingPolicyWitness
      (fun _domainH _activityH _factorH roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH _auditH => roundingH)

theorem ay_adsg_guard_tiebreak
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _activityH _factorH _roundingH tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_adsg_guard_decision
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _activityH _factorH _roundingH _tiebreakH decisionH
          _replayH _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_adsg_guard_replay
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          replayH _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_adsg_guard_baseline
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_adsg_guard_build
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH buildH _validatorH _auditH => buildH)

theorem ay_adsg_guard_validator
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_adsg_guard_audit
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_adsg_guard variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _factorH _roundingH _tiebreakH _decisionH
          _replayH _baselineH _buildH _validatorH auditH => auditH)

theorem ay_adsg_agreement_intro
    (domainMatch activityMatch factorMatch roundingMatch tiebreakMatch
      decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch : Prop) :
    domainMatch ->
    activityMatch ->
    factorMatch ->
    roundingMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_adsg_agreement domainMatch activityMatch factorMatch roundingMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_adsg_guard_intro domainMatch activityMatch factorMatch roundingMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_adsg_accepted_decay_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_adsg_conj_intro guardEvidence
      (ay_adsg_conj agreementEvidence
        (ay_adsg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_adsg_conj_intro agreementEvidence
        (ay_adsg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_adsg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_adsg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_adsg_conj_left guardEvidence
    (ay_adsg_conj agreementEvidence
      (ay_adsg_conj deterministicBranchOrder searchControlHint))

theorem ay_adsg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_adsg_conj_left agreementEvidence
      (ay_adsg_conj deterministicBranchOrder searchControlHint)
      (ay_adsg_conj_right guardEvidence
        (ay_adsg_conj agreementEvidence
          (ay_adsg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_adsg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_adsg_conj_left deterministicBranchOrder searchControlHint
      (ay_adsg_conj_right agreementEvidence
        (ay_adsg_conj deterministicBranchOrder searchControlHint)
        (ay_adsg_conj_right guardEvidence
          (ay_adsg_conj agreementEvidence
            (ay_adsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_adsg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_adsg_conj_right deterministicBranchOrder searchControlHint
      (ay_adsg_conj_right agreementEvidence
        (ay_adsg_conj deterministicBranchOrder searchControlHint)
        (ay_adsg_conj_right guardEvidence
          (ay_adsg_conj agreementEvidence
            (ay_adsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_adsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_adsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_adsg_conj_intro acceptedEvidence (ay_adsg_conj outcome formulaTruth)
      acceptedH (ay_adsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_adsg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_adsg_conj_left acceptedEvidence (ay_adsg_conj outcome formulaTruth)

theorem ay_adsg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adsg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_adsg_conj_left outcome formulaTruth
      (ay_adsg_conj_right acceptedEvidence
        (ay_adsg_conj outcome formulaTruth) report)

theorem ay_adsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_adsg_conj_right outcome formulaTruth
      (ay_adsg_conj_right acceptedEvidence
        (ay_adsg_conj outcome formulaTruth) report)

theorem ay_adsg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_adsg_no_claim diagnostic fallbackPublic :=
  ay_adsg_conj_intro diagnostic fallbackPublic

theorem ay_adsg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_adsg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_adsg_conj_left diagnostic fallbackPublic

theorem ay_adsg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_adsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_adsg_conj_right diagnostic fallbackPublic

theorem ay_adsg_decay_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_adsg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_adsg_equisat_forward beforeFormula afterFormula

theorem ay_adsg_decay_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_adsg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_adsg_equisat_backward beforeFormula afterFormula

theorem ay_adsg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adsg_public_report acceptedEvidence outcome formulaTruth ->
    ay_adsg_conj outcome formulaTruth :=
  fun report =>
    ay_adsg_conj_right acceptedEvidence (ay_adsg_conj outcome formulaTruth)
      report

theorem ay_adsg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_adsg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_adsg_conj_right agreementEvidence
      (ay_adsg_conj deterministicBranchOrder searchControlHint)
      (ay_adsg_conj_right guardEvidence
        (ay_adsg_conj agreementEvidence
          (ay_adsg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_adsg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim domainMismatch fallbackPublic :=
  ay_adsg_no_claim_intro domainMismatch fallbackPublic

theorem ay_adsg_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim activityMismatch fallbackPublic :=
  ay_adsg_no_claim_intro activityMismatch fallbackPublic

theorem ay_adsg_factor_mismatch_no_claim
    (factorMismatch fallbackPublic : Prop) :
    factorMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim factorMismatch fallbackPublic :=
  ay_adsg_no_claim_intro factorMismatch fallbackPublic

theorem ay_adsg_rounding_mismatch_no_claim
    (roundingMismatch fallbackPublic : Prop) :
    roundingMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim roundingMismatch fallbackPublic :=
  ay_adsg_no_claim_intro roundingMismatch fallbackPublic

theorem ay_adsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim tiebreakMismatch fallbackPublic :=
  ay_adsg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_adsg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim decisionMismatch fallbackPublic :=
  ay_adsg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_adsg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim replayMismatch fallbackPublic :=
  ay_adsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_adsg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim baselineMismatch fallbackPublic :=
  ay_adsg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_adsg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim buildMismatch fallbackPublic :=
  ay_adsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_adsg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_adsg_no_claim validatorRejects fallbackPublic :=
  ay_adsg_no_claim_intro validatorRejects fallbackPublic

theorem ay_adsg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_adsg_no_claim auditMismatch fallbackPublic :=
  ay_adsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_adsg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_adsg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_adsg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_adsg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_adsg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_adsg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_adsg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_adsg_public_report
      (ay_adsg_accepted_decay guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_adsg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_adsg_public_report_accepted
        (ay_adsg_accepted_decay guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_adsg_publication_requires_validator
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_adsg_public_report
      (ay_adsg_accepted_decay
        (ay_adsg_guard variableDomainDigest activityScoreLedger
          decayFactorManifest rescaleRoundingPolicyWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_adsg_guard_validator variableDomainDigest activityScoreLedger
      decayFactorManifest rescaleRoundingPolicyWitness
      deterministicTiebreakManifest decisionOrderReplay propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_adsg_publication_requires_accepted_guard
        (ay_adsg_guard variableDomainDigest activityScoreLedger
          decayFactorManifest rescaleRoundingPolicyWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_adsg_publication_requires_audit
    (variableDomainDigest activityScoreLedger decayFactorManifest
      rescaleRoundingPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_adsg_public_report
      (ay_adsg_accepted_decay
        (ay_adsg_guard variableDomainDigest activityScoreLedger
          decayFactorManifest rescaleRoundingPolicyWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_adsg_guard_audit variableDomainDigest activityScoreLedger
      decayFactorManifest rescaleRoundingPolicyWitness
      deterministicTiebreakManifest decisionOrderReplay propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_adsg_publication_requires_accepted_guard
        (ay_adsg_guard variableDomainDigest activityScoreLedger
          decayFactorManifest rescaleRoundingPolicyWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_adsg_activity_decay_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_adsg_equisat beforeFormula afterFormula ->
    ay_adsg_accepted_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_adsg_conj (beforeFormula -> afterFormula)
      (ay_adsg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_adsg_conj_intro (beforeFormula -> afterFormula)
      (ay_adsg_conj deterministicBranchOrder searchControlHint)
      (ay_adsg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_adsg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_adsg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_adsg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_adsg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_adsg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_adsg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_adsg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
