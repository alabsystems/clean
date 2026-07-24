-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Random-seed manifest guard for reproducible sequential-main SAT-COMP
-- branching. Seed-driven tie-breaking is search-control only when domain,
-- seed, stream, tiebreak, decision-order, replay, fallback, build, validator,
-- and audit evidence agree with the public result.

def ay_rsmg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rsmg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rsmg_conj (before -> after) (after -> before)

def ay_rsmg_guard
    (variableDomainDigest : Prop)
    (seedManifest : Prop)
    (pseudorandomStreamDigest : Prop)
    (tiebreakLedger : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      seedManifest ->
      pseudorandomStreamDigest ->
      tiebreakLedger ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rsmg_agreement
    (domainMatch seedMatch streamMatch tiebreakMatch decisionMatch replayMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) : Prop :=
  ay_rsmg_guard domainMatch seedMatch streamMatch tiebreakMatch decisionMatch
    replayMatch baselineMatch buildMatch validatorAccepts auditMatch

def ay_rsmg_accepted_seed_use
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_rsmg_conj guardEvidence
    (ay_rsmg_conj agreementEvidence
      (ay_rsmg_conj deterministicBranchOrder searchControlHint))

def ay_rsmg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_rsmg_conj acceptedEvidence (ay_rsmg_conj outcome formulaTruth)

def ay_rsmg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_rsmg_conj diagnostic fallbackPublic

theorem ay_rsmg_conj_intro (left right : Prop) :
    left -> right -> ay_rsmg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rsmg_conj_left (left right : Prop) :
    ay_rsmg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rsmg_conj_right (left right : Prop) :
    ay_rsmg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rsmg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_rsmg_equisat before after :=
  fun forward backward =>
    ay_rsmg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rsmg_equisat_forward (before after : Prop) :
    ay_rsmg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rsmg_conj_left (before -> after) (after -> before) eqsat

theorem ay_rsmg_equisat_backward (before after : Prop) :
    ay_rsmg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rsmg_conj_right (before -> after) (after -> before) eqsat

theorem ay_rsmg_guard_intro
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    seedManifest ->
    pseudorandomStreamDigest ->
    tiebreakLedger ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH seedH streamH tiebreakH decisionH replayH baselineH buildH
      validatorH auditH result make =>
    make domainH seedH streamH tiebreakH decisionH replayH baselineH buildH
      validatorH auditH

theorem ay_rsmg_guard_domain
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _seedH _streamH _tiebreakH _decisionH _replayH _baselineH
          _buildH _validatorH _auditH => domainH)

theorem ay_rsmg_guard_seed
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    seedManifest :=
  fun guard =>
    guard seedManifest
      (fun _domainH seedH _streamH _tiebreakH _decisionH _replayH _baselineH
          _buildH _validatorH _auditH => seedH)

theorem ay_rsmg_guard_stream
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    pseudorandomStreamDigest :=
  fun guard =>
    guard pseudorandomStreamDigest
      (fun _domainH _seedH streamH _tiebreakH _decisionH _replayH _baselineH
          _buildH _validatorH _auditH => streamH)

theorem ay_rsmg_guard_tiebreak
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    tiebreakLedger :=
  fun guard =>
    guard tiebreakLedger
      (fun _domainH _seedH _streamH tiebreakH _decisionH _replayH _baselineH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_rsmg_guard_decision
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _seedH _streamH _tiebreakH decisionH _replayH _baselineH
          _buildH _validatorH _auditH => decisionH)

theorem ay_rsmg_guard_replay
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _seedH _streamH _tiebreakH _decisionH replayH _baselineH
          _buildH _validatorH _auditH => replayH)

theorem ay_rsmg_guard_baseline
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _seedH _streamH _tiebreakH _decisionH _replayH baselineH
          _buildH _validatorH _auditH => baselineH)

theorem ay_rsmg_guard_build
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _seedH _streamH _tiebreakH _decisionH _replayH _baselineH
          buildH _validatorH _auditH => buildH)

theorem ay_rsmg_guard_validator
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _seedH _streamH _tiebreakH _decisionH _replayH _baselineH
          _buildH validatorH _auditH => validatorH)

theorem ay_rsmg_guard_audit
    (variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_rsmg_guard variableDomainDigest seedManifest pseudorandomStreamDigest
      tiebreakLedger decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _seedH _streamH _tiebreakH _decisionH _replayH _baselineH
          _buildH _validatorH auditH => auditH)

theorem ay_rsmg_agreement_intro
    (domainMatch seedMatch streamMatch tiebreakMatch decisionMatch replayMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    seedMatch ->
    streamMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rsmg_agreement domainMatch seedMatch streamMatch tiebreakMatch
      decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_rsmg_guard_intro domainMatch seedMatch streamMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_rsmg_accepted_seed_use_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_rsmg_conj_intro guardEvidence
      (ay_rsmg_conj agreementEvidence
        (ay_rsmg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_rsmg_conj_intro agreementEvidence
        (ay_rsmg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_rsmg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_rsmg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_rsmg_conj_left guardEvidence
    (ay_rsmg_conj agreementEvidence
      (ay_rsmg_conj deterministicBranchOrder searchControlHint))

theorem ay_rsmg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_rsmg_conj_left agreementEvidence
      (ay_rsmg_conj deterministicBranchOrder searchControlHint)
      (ay_rsmg_conj_right guardEvidence
        (ay_rsmg_conj agreementEvidence
          (ay_rsmg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_rsmg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_rsmg_conj_left deterministicBranchOrder searchControlHint
      (ay_rsmg_conj_right agreementEvidence
        (ay_rsmg_conj deterministicBranchOrder searchControlHint)
        (ay_rsmg_conj_right guardEvidence
          (ay_rsmg_conj agreementEvidence
            (ay_rsmg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_rsmg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_rsmg_conj_right deterministicBranchOrder searchControlHint
      (ay_rsmg_conj_right agreementEvidence
        (ay_rsmg_conj deterministicBranchOrder searchControlHint)
        (ay_rsmg_conj_right guardEvidence
          (ay_rsmg_conj agreementEvidence
            (ay_rsmg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_rsmg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rsmg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rsmg_conj_intro acceptedEvidence (ay_rsmg_conj outcome formulaTruth)
      acceptedH (ay_rsmg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rsmg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rsmg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_rsmg_conj_left acceptedEvidence (ay_rsmg_conj outcome formulaTruth)

theorem ay_rsmg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rsmg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_rsmg_conj_left outcome formulaTruth
      (ay_rsmg_conj_right acceptedEvidence
        (ay_rsmg_conj outcome formulaTruth) report)

theorem ay_rsmg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rsmg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rsmg_conj_right outcome formulaTruth
      (ay_rsmg_conj_right acceptedEvidence
        (ay_rsmg_conj outcome formulaTruth) report)

theorem ay_rsmg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_rsmg_no_claim diagnostic fallbackPublic :=
  ay_rsmg_conj_intro diagnostic fallbackPublic

theorem ay_rsmg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_rsmg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_rsmg_conj_left diagnostic fallbackPublic

theorem ay_rsmg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_rsmg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_rsmg_conj_right diagnostic fallbackPublic

theorem ay_rsmg_seed_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rsmg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_rsmg_equisat_forward beforeFormula afterFormula

theorem ay_rsmg_seed_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rsmg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_rsmg_equisat_backward beforeFormula afterFormula

theorem ay_rsmg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rsmg_public_report acceptedEvidence outcome formulaTruth ->
    ay_rsmg_conj outcome formulaTruth :=
  fun report =>
    ay_rsmg_conj_right acceptedEvidence (ay_rsmg_conj outcome formulaTruth)
      report

theorem ay_rsmg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_rsmg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_rsmg_conj_right agreementEvidence
      (ay_rsmg_conj deterministicBranchOrder searchControlHint)
      (ay_rsmg_conj_right guardEvidence
        (ay_rsmg_conj agreementEvidence
          (ay_rsmg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_rsmg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim domainMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro domainMismatch fallbackPublic

theorem ay_rsmg_seed_mismatch_no_claim
    (seedMismatch fallbackPublic : Prop) :
    seedMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim seedMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro seedMismatch fallbackPublic

theorem ay_rsmg_stream_mismatch_no_claim
    (streamMismatch fallbackPublic : Prop) :
    streamMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim streamMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro streamMismatch fallbackPublic

theorem ay_rsmg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim tiebreakMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_rsmg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim decisionMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_rsmg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim replayMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro replayMismatch fallbackPublic

theorem ay_rsmg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim baselineMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_rsmg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim buildMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro buildMismatch fallbackPublic

theorem ay_rsmg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_rsmg_no_claim validatorRejects fallbackPublic :=
  ay_rsmg_no_claim_intro validatorRejects fallbackPublic

theorem ay_rsmg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_rsmg_no_claim auditMismatch fallbackPublic :=
  ay_rsmg_no_claim_intro auditMismatch fallbackPublic

theorem ay_rsmg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_rsmg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_rsmg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_rsmg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_rsmg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_rsmg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_rsmg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_rsmg_public_report
      (ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_rsmg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_rsmg_public_report_accepted
        (ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_rsmg_publication_requires_validator
    (variableDomainDigest seedManifest pseudorandomStreamDigest tiebreakLedger
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_rsmg_public_report
      (ay_rsmg_accepted_seed_use
        (ay_rsmg_guard variableDomainDigest seedManifest
          pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_rsmg_guard_validator variableDomainDigest seedManifest
      pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_rsmg_publication_requires_accepted_guard
        (ay_rsmg_guard variableDomainDigest seedManifest
          pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_rsmg_publication_requires_audit
    (variableDomainDigest seedManifest pseudorandomStreamDigest tiebreakLedger
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_rsmg_public_report
      (ay_rsmg_accepted_seed_use
        (ay_rsmg_guard variableDomainDigest seedManifest
          pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_rsmg_guard_audit variableDomainDigest seedManifest
      pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_rsmg_publication_requires_accepted_guard
        (ay_rsmg_guard variableDomainDigest seedManifest
          pseudorandomStreamDigest tiebreakLedger decisionOrderReplay
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_rsmg_seed_branching_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_rsmg_equisat beforeFormula afterFormula ->
    ay_rsmg_accepted_seed_use guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_rsmg_conj (beforeFormula -> afterFormula)
      (ay_rsmg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_rsmg_conj_intro (beforeFormula -> afterFormula)
      (ay_rsmg_conj deterministicBranchOrder searchControlHint)
      (ay_rsmg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_rsmg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_rsmg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_rsmg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_rsmg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_rsmg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_rsmg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_rsmg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
