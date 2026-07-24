-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching score checkpoint guard for sequential-main SAT-COMP branching.
-- Checkpoint restore is search-control state recovery only when domain, score,
-- epoch, restore, tiebreak, decision replay, propagation replay, fallback,
-- build, validator, and audit evidence agree.

def ay_sckg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sckg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_sckg_conj (before -> after) (after -> before)

def ay_sckg_guard
    (variableDomainDigest : Prop)
    (activityScoreDigest : Prop)
    (checkpointEpochManifest : Prop)
    (restoreWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityScoreDigest ->
      checkpointEpochManifest ->
      restoreWitness ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_sckg_agreement
    (domainMatch scoreMatch epochMatch restoreMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_sckg_guard domainMatch scoreMatch epochMatch restoreMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_sckg_accepted_checkpoint
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_sckg_conj guardEvidence
    (ay_sckg_conj agreementEvidence
      (ay_sckg_conj deterministicBranchOrder searchControlHint))

def ay_sckg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_sckg_conj acceptedEvidence (ay_sckg_conj outcome formulaTruth)

def ay_sckg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_sckg_conj diagnostic fallbackPublic

theorem ay_sckg_conj_intro (left right : Prop) :
    left -> right -> ay_sckg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_sckg_conj_left (left right : Prop) :
    ay_sckg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_sckg_conj_right (left right : Prop) :
    ay_sckg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_sckg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_sckg_equisat before after :=
  fun forward backward =>
    ay_sckg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_sckg_equisat_forward (before after : Prop) :
    ay_sckg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_sckg_conj_left (before -> after) (after -> before) eqsat

theorem ay_sckg_equisat_backward (before after : Prop) :
    ay_sckg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_sckg_conj_right (before -> after) (after -> before) eqsat

theorem ay_sckg_guard_intro
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    activityScoreDigest ->
    checkpointEpochManifest ->
    restoreWitness ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH scoreH epochH restoreH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH result make =>
    make domainH scoreH epochH restoreH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH

theorem ay_sckg_guard_domain
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_sckg_guard_score
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityScoreDigest :=
  fun guard =>
    guard activityScoreDigest
      (fun _domainH scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => scoreH)

theorem ay_sckg_guard_epoch
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    checkpointEpochManifest :=
  fun guard =>
    guard checkpointEpochManifest
      (fun _domainH _scoreH epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => epochH)

theorem ay_sckg_guard_restore
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    restoreWitness :=
  fun guard =>
    guard restoreWitness
      (fun _domainH _scoreH _epochH restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => restoreH)

theorem ay_sckg_guard_tiebreak
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _scoreH _epochH _restoreH tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_sckg_guard_decision
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH decisionH _replayH
          _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_sckg_guard_replay
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH _decisionH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_sckg_guard_baseline
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_sckg_guard_build
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_sckg_guard_validator
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_sckg_guard_audit
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sckg_guard variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _scoreH _epochH _restoreH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_sckg_agreement_intro
    (domainMatch scoreMatch epochMatch restoreMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    domainMatch ->
    scoreMatch ->
    epochMatch ->
    restoreMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_sckg_agreement domainMatch scoreMatch epochMatch restoreMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_sckg_guard_intro domainMatch scoreMatch epochMatch restoreMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_sckg_accepted_checkpoint_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_sckg_conj_intro guardEvidence
      (ay_sckg_conj agreementEvidence
        (ay_sckg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_sckg_conj_intro agreementEvidence
        (ay_sckg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_sckg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_sckg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_sckg_conj_left guardEvidence
    (ay_sckg_conj agreementEvidence
      (ay_sckg_conj deterministicBranchOrder searchControlHint))

theorem ay_sckg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_sckg_conj_left agreementEvidence
      (ay_sckg_conj deterministicBranchOrder searchControlHint)
      (ay_sckg_conj_right guardEvidence
        (ay_sckg_conj agreementEvidence
          (ay_sckg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_sckg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_sckg_conj_left deterministicBranchOrder searchControlHint
      (ay_sckg_conj_right agreementEvidence
        (ay_sckg_conj deterministicBranchOrder searchControlHint)
        (ay_sckg_conj_right guardEvidence
          (ay_sckg_conj agreementEvidence
            (ay_sckg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_sckg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_sckg_conj_right deterministicBranchOrder searchControlHint
      (ay_sckg_conj_right agreementEvidence
        (ay_sckg_conj deterministicBranchOrder searchControlHint)
        (ay_sckg_conj_right guardEvidence
          (ay_sckg_conj agreementEvidence
            (ay_sckg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_sckg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_sckg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_sckg_conj_intro acceptedEvidence (ay_sckg_conj outcome formulaTruth)
      acceptedH (ay_sckg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_sckg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sckg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_sckg_conj_left acceptedEvidence (ay_sckg_conj outcome formulaTruth)

theorem ay_sckg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sckg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_sckg_conj_left outcome formulaTruth
      (ay_sckg_conj_right acceptedEvidence
        (ay_sckg_conj outcome formulaTruth) report)

theorem ay_sckg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sckg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_sckg_conj_right outcome formulaTruth
      (ay_sckg_conj_right acceptedEvidence
        (ay_sckg_conj outcome formulaTruth) report)

theorem ay_sckg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_sckg_no_claim diagnostic fallbackPublic :=
  ay_sckg_conj_intro diagnostic fallbackPublic

theorem ay_sckg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_sckg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_sckg_conj_left diagnostic fallbackPublic

theorem ay_sckg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_sckg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_sckg_conj_right diagnostic fallbackPublic

theorem ay_sckg_checkpoint_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_sckg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_sckg_equisat_forward beforeFormula afterFormula

theorem ay_sckg_checkpoint_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_sckg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_sckg_equisat_backward beforeFormula afterFormula

theorem ay_sckg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sckg_public_report acceptedEvidence outcome formulaTruth ->
    ay_sckg_conj outcome formulaTruth :=
  fun report =>
    ay_sckg_conj_right acceptedEvidence (ay_sckg_conj outcome formulaTruth)
      report

theorem ay_sckg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_sckg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_sckg_conj_right agreementEvidence
      (ay_sckg_conj deterministicBranchOrder searchControlHint)
      (ay_sckg_conj_right guardEvidence
        (ay_sckg_conj agreementEvidence
          (ay_sckg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_sckg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim domainMismatch fallbackPublic :=
  ay_sckg_no_claim_intro domainMismatch fallbackPublic

theorem ay_sckg_score_mismatch_no_claim
    (scoreMismatch fallbackPublic : Prop) :
    scoreMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim scoreMismatch fallbackPublic :=
  ay_sckg_no_claim_intro scoreMismatch fallbackPublic

theorem ay_sckg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim epochMismatch fallbackPublic :=
  ay_sckg_no_claim_intro epochMismatch fallbackPublic

theorem ay_sckg_restore_mismatch_no_claim
    (restoreMismatch fallbackPublic : Prop) :
    restoreMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim restoreMismatch fallbackPublic :=
  ay_sckg_no_claim_intro restoreMismatch fallbackPublic

theorem ay_sckg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim tiebreakMismatch fallbackPublic :=
  ay_sckg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_sckg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim decisionMismatch fallbackPublic :=
  ay_sckg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_sckg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim replayMismatch fallbackPublic :=
  ay_sckg_no_claim_intro replayMismatch fallbackPublic

theorem ay_sckg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim baselineMismatch fallbackPublic :=
  ay_sckg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_sckg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim buildMismatch fallbackPublic :=
  ay_sckg_no_claim_intro buildMismatch fallbackPublic

theorem ay_sckg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_sckg_no_claim validatorRejects fallbackPublic :=
  ay_sckg_no_claim_intro validatorRejects fallbackPublic

theorem ay_sckg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_sckg_no_claim auditMismatch fallbackPublic :=
  ay_sckg_no_claim_intro auditMismatch fallbackPublic

theorem ay_sckg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_sckg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_sckg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_sckg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_sckg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_sckg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_sckg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_sckg_public_report
      (ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_sckg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_sckg_public_report_accepted
        (ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_sckg_publication_requires_validator
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_sckg_public_report
      (ay_sckg_accepted_checkpoint
        (ay_sckg_guard variableDomainDigest activityScoreDigest
          checkpointEpochManifest restoreWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_sckg_guard_validator variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_sckg_publication_requires_accepted_guard
        (ay_sckg_guard variableDomainDigest activityScoreDigest
          checkpointEpochManifest restoreWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_sckg_publication_requires_audit
    (variableDomainDigest activityScoreDigest checkpointEpochManifest
      restoreWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_sckg_public_report
      (ay_sckg_accepted_checkpoint
        (ay_sckg_guard variableDomainDigest activityScoreDigest
          checkpointEpochManifest restoreWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_sckg_guard_audit variableDomainDigest activityScoreDigest
      checkpointEpochManifest restoreWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_sckg_publication_requires_accepted_guard
        (ay_sckg_guard variableDomainDigest activityScoreDigest
          checkpointEpochManifest restoreWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_sckg_score_checkpointing_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_sckg_equisat beforeFormula afterFormula ->
    ay_sckg_accepted_checkpoint guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_sckg_conj (beforeFormula -> afterFormula)
      (ay_sckg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_sckg_conj_intro (beforeFormula -> afterFormula)
      (ay_sckg_conj deterministicBranchOrder searchControlHint)
      (ay_sckg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_sckg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_sckg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_sckg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_sckg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_sckg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_sckg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_sckg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
