-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Conflict-feedback branching guard for sequential-main SAT-COMP branching.
-- Conflict feedback is search-control/heuristic metadata only when domain,
-- conflict analysis, bumped variables, learnt-clause provenance, tiebreak,
-- decision replay, propagation replay, fallback, build, validator, and audit
-- evidence agree.

def ay_cfgd_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cfgd_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cfgd_conj (before -> after) (after -> before)

def ay_cfgd_guard
    (variableDomainDigest : Prop)
    (conflictAnalysisLedger : Prop)
    (bumpedVariableLedger : Prop)
    (learntClauseProvenanceWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      conflictAnalysisLedger ->
      bumpedVariableLedger ->
      learntClauseProvenanceWitness ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cfgd_agreement
    (domainMatch conflictMatch bumpMatch provenanceMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_cfgd_guard domainMatch conflictMatch bumpMatch provenanceMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_cfgd_accepted_feedback
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_cfgd_conj guardEvidence
    (ay_cfgd_conj agreementEvidence
      (ay_cfgd_conj deterministicBranchOrder searchControlHint))

def ay_cfgd_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_cfgd_conj acceptedEvidence (ay_cfgd_conj outcome formulaTruth)

def ay_cfgd_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_cfgd_conj diagnostic fallbackPublic

theorem ay_cfgd_conj_intro (left right : Prop) :
    left -> right -> ay_cfgd_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cfgd_conj_left (left right : Prop) :
    ay_cfgd_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cfgd_conj_right (left right : Prop) :
    ay_cfgd_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cfgd_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_cfgd_equisat before after :=
  fun forward backward =>
    ay_cfgd_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cfgd_equisat_forward (before after : Prop) :
    ay_cfgd_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cfgd_conj_left (before -> after) (after -> before) eqsat

theorem ay_cfgd_equisat_backward (before after : Prop) :
    ay_cfgd_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cfgd_conj_right (before -> after) (after -> before) eqsat

theorem ay_cfgd_guard_intro
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    conflictAnalysisLedger ->
    bumpedVariableLedger ->
    learntClauseProvenanceWitness ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH conflictH bumpH provenanceH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH result make =>
    make domainH conflictH bumpH provenanceH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH

theorem ay_cfgd_guard_domain
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_cfgd_guard_conflict
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    conflictAnalysisLedger :=
  fun guard =>
    guard conflictAnalysisLedger
      (fun _domainH conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => conflictH)

theorem ay_cfgd_guard_bump
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    bumpedVariableLedger :=
  fun guard =>
    guard bumpedVariableLedger
      (fun _domainH _conflictH bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => bumpH)

theorem ay_cfgd_guard_provenance
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    learntClauseProvenanceWitness :=
  fun guard =>
    guard learntClauseProvenanceWitness
      (fun _domainH _conflictH _bumpH provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => provenanceH)

theorem ay_cfgd_guard_tiebreak
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _conflictH _bumpH _provenanceH tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_cfgd_guard_decision
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH decisionH _replayH
          _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_cfgd_guard_replay
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_cfgd_guard_baseline
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_cfgd_guard_build
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_cfgd_guard_validator
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_cfgd_guard_audit
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _conflictH _bumpH _provenanceH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_cfgd_agreement_intro
    (domainMatch conflictMatch bumpMatch provenanceMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    domainMatch ->
    conflictMatch ->
    bumpMatch ->
    provenanceMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_cfgd_agreement domainMatch conflictMatch bumpMatch provenanceMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_cfgd_guard_intro domainMatch conflictMatch bumpMatch provenanceMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_cfgd_accepted_feedback_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_cfgd_conj_intro guardEvidence
      (ay_cfgd_conj agreementEvidence
        (ay_cfgd_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_cfgd_conj_intro agreementEvidence
        (ay_cfgd_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_cfgd_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_cfgd_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_cfgd_conj_left guardEvidence
    (ay_cfgd_conj agreementEvidence
      (ay_cfgd_conj deterministicBranchOrder searchControlHint))

theorem ay_cfgd_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_cfgd_conj_left agreementEvidence
      (ay_cfgd_conj deterministicBranchOrder searchControlHint)
      (ay_cfgd_conj_right guardEvidence
        (ay_cfgd_conj agreementEvidence
          (ay_cfgd_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_cfgd_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_cfgd_conj_left deterministicBranchOrder searchControlHint
      (ay_cfgd_conj_right agreementEvidence
        (ay_cfgd_conj deterministicBranchOrder searchControlHint)
        (ay_cfgd_conj_right guardEvidence
          (ay_cfgd_conj agreementEvidence
            (ay_cfgd_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_cfgd_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_cfgd_conj_right deterministicBranchOrder searchControlHint
      (ay_cfgd_conj_right agreementEvidence
        (ay_cfgd_conj deterministicBranchOrder searchControlHint)
        (ay_cfgd_conj_right guardEvidence
          (ay_cfgd_conj agreementEvidence
            (ay_cfgd_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_cfgd_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cfgd_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cfgd_conj_intro acceptedEvidence (ay_cfgd_conj outcome formulaTruth)
      acceptedH (ay_cfgd_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cfgd_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cfgd_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_cfgd_conj_left acceptedEvidence (ay_cfgd_conj outcome formulaTruth)

theorem ay_cfgd_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cfgd_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_cfgd_conj_left outcome formulaTruth
      (ay_cfgd_conj_right acceptedEvidence
        (ay_cfgd_conj outcome formulaTruth) report)

theorem ay_cfgd_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cfgd_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_cfgd_conj_right outcome formulaTruth
      (ay_cfgd_conj_right acceptedEvidence
        (ay_cfgd_conj outcome formulaTruth) report)

theorem ay_cfgd_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_cfgd_no_claim diagnostic fallbackPublic :=
  ay_cfgd_conj_intro diagnostic fallbackPublic

theorem ay_cfgd_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_cfgd_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_cfgd_conj_left diagnostic fallbackPublic

theorem ay_cfgd_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_cfgd_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_cfgd_conj_right diagnostic fallbackPublic

theorem ay_cfgd_feedback_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_cfgd_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_cfgd_equisat_forward beforeFormula afterFormula

theorem ay_cfgd_feedback_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_cfgd_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_cfgd_equisat_backward beforeFormula afterFormula

theorem ay_cfgd_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cfgd_public_report acceptedEvidence outcome formulaTruth ->
    ay_cfgd_conj outcome formulaTruth :=
  fun report =>
    ay_cfgd_conj_right acceptedEvidence (ay_cfgd_conj outcome formulaTruth)
      report

theorem ay_cfgd_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_cfgd_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_cfgd_conj_right agreementEvidence
      (ay_cfgd_conj deterministicBranchOrder searchControlHint)
      (ay_cfgd_conj_right guardEvidence
        (ay_cfgd_conj agreementEvidence
          (ay_cfgd_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_cfgd_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim domainMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro domainMismatch fallbackPublic

theorem ay_cfgd_conflict_mismatch_no_claim
    (conflictMismatch fallbackPublic : Prop) :
    conflictMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim conflictMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro conflictMismatch fallbackPublic

theorem ay_cfgd_bump_mismatch_no_claim
    (bumpMismatch fallbackPublic : Prop) :
    bumpMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim bumpMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro bumpMismatch fallbackPublic

theorem ay_cfgd_provenance_mismatch_no_claim
    (provenanceMismatch fallbackPublic : Prop) :
    provenanceMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim provenanceMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro provenanceMismatch fallbackPublic

theorem ay_cfgd_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim tiebreakMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_cfgd_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim decisionMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro decisionMismatch fallbackPublic

theorem ay_cfgd_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim replayMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro replayMismatch fallbackPublic

theorem ay_cfgd_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim baselineMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro baselineMismatch fallbackPublic

theorem ay_cfgd_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim buildMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro buildMismatch fallbackPublic

theorem ay_cfgd_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_cfgd_no_claim validatorRejects fallbackPublic :=
  ay_cfgd_no_claim_intro validatorRejects fallbackPublic

theorem ay_cfgd_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_cfgd_no_claim auditMismatch fallbackPublic :=
  ay_cfgd_no_claim_intro auditMismatch fallbackPublic

theorem ay_cfgd_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_cfgd_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_cfgd_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_cfgd_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_cfgd_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_cfgd_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_cfgd_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_cfgd_public_report
      (ay_cfgd_accepted_feedback guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_cfgd_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_cfgd_public_report_accepted
        (ay_cfgd_accepted_feedback guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_cfgd_publication_requires_validator
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_cfgd_public_report
      (ay_cfgd_accepted_feedback
        (ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
          bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_cfgd_guard_validator variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_cfgd_publication_requires_accepted_guard
        (ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
          bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_cfgd_publication_requires_audit
    (variableDomainDigest conflictAnalysisLedger bumpedVariableLedger
      learntClauseProvenanceWitness deterministicTiebreakManifest decisionOrderReplay
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_cfgd_public_report
      (ay_cfgd_accepted_feedback
        (ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
          bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_cfgd_guard_audit variableDomainDigest conflictAnalysisLedger
      bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_cfgd_publication_requires_accepted_guard
        (ay_cfgd_guard variableDomainDigest conflictAnalysisLedger
          bumpedVariableLedger learntClauseProvenanceWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_cfgd_conflict_feedback_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_cfgd_equisat beforeFormula afterFormula ->
    ay_cfgd_accepted_feedback guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_cfgd_conj (beforeFormula -> afterFormula)
      (ay_cfgd_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_cfgd_conj_intro (beforeFormula -> afterFormula)
      (ay_cfgd_conj deterministicBranchOrder searchControlHint)
      (ay_cfgd_equisat_forward beforeFormula afterFormula eqsat)
      (ay_cfgd_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_cfgd_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_cfgd_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_cfgd_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_cfgd_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_cfgd_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_cfgd_public_report_intro acceptedEvidence unsatOutcome formulaTruth
