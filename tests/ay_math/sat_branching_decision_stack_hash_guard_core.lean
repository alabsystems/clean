-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-stack hash guard for sequential-main SAT-COMP branching.
-- Stack hashes are search-state audit metadata only when domain, stack,
-- level, trail, tiebreak, decision replay, propagation replay, fallback,
-- build, validator, and audit evidence agree.

def ay_dshg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dshg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_dshg_conj (before -> after) (after -> before)

def ay_dshg_guard
    (variableDomainDigest : Prop)
    (decisionStackDigest : Prop)
    (decisionLevelLedger : Prop)
    (assignmentTrailDigest : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      decisionStackDigest ->
      decisionLevelLedger ->
      assignmentTrailDigest ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_dshg_agreement
    (domainMatch stackMatch levelMatch trailMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_dshg_guard domainMatch stackMatch levelMatch trailMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_dshg_accepted_stack_hash
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_dshg_conj guardEvidence
    (ay_dshg_conj agreementEvidence
      (ay_dshg_conj deterministicBranchOrder searchControlHint))

def ay_dshg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_dshg_conj acceptedEvidence (ay_dshg_conj outcome formulaTruth)

def ay_dshg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_dshg_conj diagnostic fallbackPublic

theorem ay_dshg_conj_intro (left right : Prop) :
    left -> right -> ay_dshg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_dshg_conj_left (left right : Prop) :
    ay_dshg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_dshg_conj_right (left right : Prop) :
    ay_dshg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_dshg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_dshg_equisat before after :=
  fun forward backward =>
    ay_dshg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_dshg_equisat_forward (before after : Prop) :
    ay_dshg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_dshg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dshg_equisat_backward (before after : Prop) :
    ay_dshg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_dshg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dshg_guard_intro
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    decisionStackDigest ->
    decisionLevelLedger ->
    assignmentTrailDigest ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript :=
  fun domainH stackH levelH trailH tiebreakH decisionH replayH baselineH buildH
      validatorH auditH result make =>
    make domainH stackH levelH trailH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH

theorem ay_dshg_guard_domain
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _stackH _levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_dshg_guard_stack
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _domainH stackH _levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => stackH)

theorem ay_dshg_guard_level
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    decisionLevelLedger :=
  fun guard =>
    guard decisionLevelLedger
      (fun _domainH _stackH levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => levelH)

theorem ay_dshg_guard_trail
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    assignmentTrailDigest :=
  fun guard =>
    guard assignmentTrailDigest
      (fun _domainH _stackH _levelH trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => trailH)

theorem ay_dshg_guard_tiebreak
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _stackH _levelH _trailH tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_dshg_guard_decision
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _stackH _levelH _trailH _tiebreakH decisionH _replayH
          _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_dshg_guard_replay
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _stackH _levelH _trailH _tiebreakH _decisionH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_dshg_guard_baseline
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _stackH _levelH _trailH _tiebreakH _decisionH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_dshg_guard_build
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _stackH _levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_dshg_guard_validator
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _stackH _levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_dshg_guard_audit
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_dshg_guard variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _stackH _levelH _trailH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_dshg_agreement_intro
    (domainMatch stackMatch levelMatch trailMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    domainMatch ->
    stackMatch ->
    levelMatch ->
    trailMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_dshg_agreement domainMatch stackMatch levelMatch trailMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_dshg_guard_intro domainMatch stackMatch levelMatch trailMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_dshg_accepted_stack_hash_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_dshg_conj_intro guardEvidence
      (ay_dshg_conj agreementEvidence
        (ay_dshg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_dshg_conj_intro agreementEvidence
        (ay_dshg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_dshg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_dshg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_dshg_conj_left guardEvidence
    (ay_dshg_conj agreementEvidence
      (ay_dshg_conj deterministicBranchOrder searchControlHint))

theorem ay_dshg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_dshg_conj_left agreementEvidence
      (ay_dshg_conj deterministicBranchOrder searchControlHint)
      (ay_dshg_conj_right guardEvidence
        (ay_dshg_conj agreementEvidence
          (ay_dshg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_dshg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_dshg_conj_left deterministicBranchOrder searchControlHint
      (ay_dshg_conj_right agreementEvidence
        (ay_dshg_conj deterministicBranchOrder searchControlHint)
        (ay_dshg_conj_right guardEvidence
          (ay_dshg_conj agreementEvidence
            (ay_dshg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_dshg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_dshg_conj_right deterministicBranchOrder searchControlHint
      (ay_dshg_conj_right agreementEvidence
        (ay_dshg_conj deterministicBranchOrder searchControlHint)
        (ay_dshg_conj_right guardEvidence
          (ay_dshg_conj agreementEvidence
            (ay_dshg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_dshg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_dshg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_dshg_conj_intro acceptedEvidence (ay_dshg_conj outcome formulaTruth)
      acceptedH (ay_dshg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_dshg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dshg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_dshg_conj_left acceptedEvidence (ay_dshg_conj outcome formulaTruth)

theorem ay_dshg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dshg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_dshg_conj_left outcome formulaTruth
      (ay_dshg_conj_right acceptedEvidence
        (ay_dshg_conj outcome formulaTruth) report)

theorem ay_dshg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dshg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_dshg_conj_right outcome formulaTruth
      (ay_dshg_conj_right acceptedEvidence
        (ay_dshg_conj outcome formulaTruth) report)

theorem ay_dshg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_dshg_no_claim diagnostic fallbackPublic :=
  ay_dshg_conj_intro diagnostic fallbackPublic

theorem ay_dshg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_dshg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_dshg_conj_left diagnostic fallbackPublic

theorem ay_dshg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_dshg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_dshg_conj_right diagnostic fallbackPublic

theorem ay_dshg_stack_hash_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_dshg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_dshg_equisat_forward beforeFormula afterFormula

theorem ay_dshg_stack_hash_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_dshg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_dshg_equisat_backward beforeFormula afterFormula

theorem ay_dshg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dshg_public_report acceptedEvidence outcome formulaTruth ->
    ay_dshg_conj outcome formulaTruth :=
  fun report =>
    ay_dshg_conj_right acceptedEvidence (ay_dshg_conj outcome formulaTruth)
      report

theorem ay_dshg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_dshg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_dshg_conj_right agreementEvidence
      (ay_dshg_conj deterministicBranchOrder searchControlHint)
      (ay_dshg_conj_right guardEvidence
        (ay_dshg_conj agreementEvidence
          (ay_dshg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_dshg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim domainMismatch fallbackPublic :=
  ay_dshg_no_claim_intro domainMismatch fallbackPublic

theorem ay_dshg_stack_mismatch_no_claim
    (stackMismatch fallbackPublic : Prop) :
    stackMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim stackMismatch fallbackPublic :=
  ay_dshg_no_claim_intro stackMismatch fallbackPublic

theorem ay_dshg_level_mismatch_no_claim
    (levelMismatch fallbackPublic : Prop) :
    levelMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim levelMismatch fallbackPublic :=
  ay_dshg_no_claim_intro levelMismatch fallbackPublic

theorem ay_dshg_trail_mismatch_no_claim
    (trailMismatch fallbackPublic : Prop) :
    trailMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim trailMismatch fallbackPublic :=
  ay_dshg_no_claim_intro trailMismatch fallbackPublic

theorem ay_dshg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim tiebreakMismatch fallbackPublic :=
  ay_dshg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_dshg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim decisionMismatch fallbackPublic :=
  ay_dshg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_dshg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim replayMismatch fallbackPublic :=
  ay_dshg_no_claim_intro replayMismatch fallbackPublic

theorem ay_dshg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim baselineMismatch fallbackPublic :=
  ay_dshg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_dshg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim buildMismatch fallbackPublic :=
  ay_dshg_no_claim_intro buildMismatch fallbackPublic

theorem ay_dshg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_dshg_no_claim validatorRejects fallbackPublic :=
  ay_dshg_no_claim_intro validatorRejects fallbackPublic

theorem ay_dshg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_dshg_no_claim auditMismatch fallbackPublic :=
  ay_dshg_no_claim_intro auditMismatch fallbackPublic

theorem ay_dshg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_dshg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_dshg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_dshg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_dshg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_dshg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_dshg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_dshg_public_report
      (ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_dshg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_dshg_public_report_accepted
        (ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_dshg_publication_requires_validator
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_dshg_public_report
      (ay_dshg_accepted_stack_hash
        (ay_dshg_guard variableDomainDigest decisionStackDigest
          decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_dshg_guard_validator variableDomainDigest decisionStackDigest
      decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_dshg_publication_requires_accepted_guard
        (ay_dshg_guard variableDomainDigest decisionStackDigest
          decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_dshg_publication_requires_audit
    (variableDomainDigest decisionStackDigest decisionLevelLedger
      assignmentTrailDigest deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_dshg_public_report
      (ay_dshg_accepted_stack_hash
        (ay_dshg_guard variableDomainDigest decisionStackDigest
          decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_dshg_guard_audit variableDomainDigest decisionStackDigest
      decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_dshg_publication_requires_accepted_guard
        (ay_dshg_guard variableDomainDigest decisionStackDigest
          decisionLevelLedger assignmentTrailDigest deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_dshg_decision_stack_hashing_is_search_audit_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_dshg_equisat beforeFormula afterFormula ->
    ay_dshg_accepted_stack_hash guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_dshg_conj (beforeFormula -> afterFormula)
      (ay_dshg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_dshg_conj_intro (beforeFormula -> afterFormula)
      (ay_dshg_conj deterministicBranchOrder searchControlHint)
      (ay_dshg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_dshg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_dshg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_dshg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_dshg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_dshg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_dshg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_dshg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
