-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause/activity score rescale guard for sequential-main SAT-COMP branching.
-- Rescaling is heuristic state only when domain, clause activity, variable
-- activity, factor, ordering, tiebreak, replay, fallback, build, validator,
-- and audit evidence agree with the public result.

def ay_carg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_carg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_carg_conj (before -> after) (after -> before)

def ay_carg_guard
    (variableDomainDigest : Prop)
    (clauseActivityLedger : Prop)
    (variableActivityLedger : Prop)
    (rescaleFactorManifest : Prop)
    (orderingEquivalenceWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      clauseActivityLedger ->
      variableActivityLedger ->
      rescaleFactorManifest ->
      orderingEquivalenceWitness ->
      deterministicTiebreakManifest ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_carg_agreement
    (domainMatch clauseLedgerMatch variableLedgerMatch factorMatch orderMatch
      tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch : Prop) : Prop :=
  ay_carg_guard domainMatch clauseLedgerMatch variableLedgerMatch factorMatch
    orderMatch tiebreakMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

def ay_carg_accepted_rescale
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_carg_conj guardEvidence
    (ay_carg_conj agreementEvidence
      (ay_carg_conj deterministicBranchOrder searchControlHint))

def ay_carg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_carg_conj acceptedEvidence (ay_carg_conj outcome formulaTruth)

def ay_carg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_carg_conj diagnostic fallbackPublic

theorem ay_carg_conj_intro (left right : Prop) :
    left -> right -> ay_carg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_carg_conj_left (left right : Prop) :
    ay_carg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_carg_conj_right (left right : Prop) :
    ay_carg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_carg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_carg_equisat before after :=
  fun forward backward =>
    ay_carg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_carg_equisat_forward (before after : Prop) :
    ay_carg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_carg_conj_left (before -> after) (after -> before) eqsat

theorem ay_carg_equisat_backward (before after : Prop) :
    ay_carg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_carg_conj_right (before -> after) (after -> before) eqsat

theorem ay_carg_guard_intro
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    clauseActivityLedger ->
    variableActivityLedger ->
    rescaleFactorManifest ->
    orderingEquivalenceWitness ->
    deterministicTiebreakManifest ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH clauseH variableH factorH orderH tiebreakH replayH baselineH
      buildH validatorH auditH result make =>
    make domainH clauseH variableH factorH orderH tiebreakH replayH baselineH
      buildH validatorH auditH

theorem ay_carg_guard_domain
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _clauseH _variableH _factorH _orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_carg_guard_clause_ledger
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    clauseActivityLedger :=
  fun guard =>
    guard clauseActivityLedger
      (fun _domainH clauseH _variableH _factorH _orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => clauseH)

theorem ay_carg_guard_variable_ledger
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableActivityLedger :=
  fun guard =>
    guard variableActivityLedger
      (fun _domainH _clauseH variableH _factorH _orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => variableH)

theorem ay_carg_guard_factor
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    rescaleFactorManifest :=
  fun guard =>
    guard rescaleFactorManifest
      (fun _domainH _clauseH _variableH factorH _orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => factorH)

theorem ay_carg_guard_order
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    orderingEquivalenceWitness :=
  fun guard =>
    guard orderingEquivalenceWitness
      (fun _domainH _clauseH _variableH _factorH orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => orderH)

theorem ay_carg_guard_tiebreak
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _clauseH _variableH _factorH _orderH tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_carg_guard_replay
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _clauseH _variableH _factorH _orderH _tiebreakH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_carg_guard_baseline
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _clauseH _variableH _factorH _orderH _tiebreakH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_carg_guard_build
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _clauseH _variableH _factorH _orderH _tiebreakH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_carg_guard_validator
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _clauseH _variableH _factorH _orderH _tiebreakH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_carg_guard_audit
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_carg_guard variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _clauseH _variableH _factorH _orderH _tiebreakH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_carg_agreement_intro
    (domainMatch clauseLedgerMatch variableLedgerMatch factorMatch orderMatch
      tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch : Prop) :
    domainMatch ->
    clauseLedgerMatch ->
    variableLedgerMatch ->
    factorMatch ->
    orderMatch ->
    tiebreakMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_carg_agreement domainMatch clauseLedgerMatch variableLedgerMatch
      factorMatch orderMatch tiebreakMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_carg_guard_intro domainMatch clauseLedgerMatch variableLedgerMatch
    factorMatch orderMatch tiebreakMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_carg_accepted_rescale_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_carg_conj_intro guardEvidence
      (ay_carg_conj agreementEvidence
        (ay_carg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_carg_conj_intro agreementEvidence
        (ay_carg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_carg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_carg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_carg_conj_left guardEvidence
    (ay_carg_conj agreementEvidence
      (ay_carg_conj deterministicBranchOrder searchControlHint))

theorem ay_carg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_carg_conj_left agreementEvidence
      (ay_carg_conj deterministicBranchOrder searchControlHint)
      (ay_carg_conj_right guardEvidence
        (ay_carg_conj agreementEvidence
          (ay_carg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_carg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_carg_conj_left deterministicBranchOrder searchControlHint
      (ay_carg_conj_right agreementEvidence
        (ay_carg_conj deterministicBranchOrder searchControlHint)
        (ay_carg_conj_right guardEvidence
          (ay_carg_conj agreementEvidence
            (ay_carg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_carg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_carg_conj_right deterministicBranchOrder searchControlHint
      (ay_carg_conj_right agreementEvidence
        (ay_carg_conj deterministicBranchOrder searchControlHint)
        (ay_carg_conj_right guardEvidence
          (ay_carg_conj agreementEvidence
            (ay_carg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_carg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_carg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_carg_conj_intro acceptedEvidence (ay_carg_conj outcome formulaTruth)
      acceptedH (ay_carg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_carg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_carg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_carg_conj_left acceptedEvidence (ay_carg_conj outcome formulaTruth)

theorem ay_carg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_carg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_carg_conj_left outcome formulaTruth
      (ay_carg_conj_right acceptedEvidence
        (ay_carg_conj outcome formulaTruth) report)

theorem ay_carg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_carg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_carg_conj_right outcome formulaTruth
      (ay_carg_conj_right acceptedEvidence
        (ay_carg_conj outcome formulaTruth) report)

theorem ay_carg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_carg_no_claim diagnostic fallbackPublic :=
  ay_carg_conj_intro diagnostic fallbackPublic

theorem ay_carg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_carg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_carg_conj_left diagnostic fallbackPublic

theorem ay_carg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_carg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_carg_conj_right diagnostic fallbackPublic

theorem ay_carg_rescale_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_carg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_carg_equisat_forward beforeFormula afterFormula

theorem ay_carg_rescale_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_carg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_carg_equisat_backward beforeFormula afterFormula

theorem ay_carg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_carg_public_report acceptedEvidence outcome formulaTruth ->
    ay_carg_conj outcome formulaTruth :=
  fun report =>
    ay_carg_conj_right acceptedEvidence (ay_carg_conj outcome formulaTruth)
      report

theorem ay_carg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_carg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_carg_conj_right agreementEvidence
      (ay_carg_conj deterministicBranchOrder searchControlHint)
      (ay_carg_conj_right guardEvidence
        (ay_carg_conj agreementEvidence
          (ay_carg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_carg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_carg_no_claim domainMismatch fallbackPublic :=
  ay_carg_no_claim_intro domainMismatch fallbackPublic

theorem ay_carg_ledger_mismatch_no_claim
    (ledgerMismatch fallbackPublic : Prop) :
    ledgerMismatch ->
    fallbackPublic ->
    ay_carg_no_claim ledgerMismatch fallbackPublic :=
  ay_carg_no_claim_intro ledgerMismatch fallbackPublic

theorem ay_carg_clause_ledger_mismatch_no_claim
    (clauseLedgerMismatch fallbackPublic : Prop) :
    clauseLedgerMismatch ->
    fallbackPublic ->
    ay_carg_no_claim clauseLedgerMismatch fallbackPublic :=
  ay_carg_no_claim_intro clauseLedgerMismatch fallbackPublic

theorem ay_carg_variable_ledger_mismatch_no_claim
    (variableLedgerMismatch fallbackPublic : Prop) :
    variableLedgerMismatch ->
    fallbackPublic ->
    ay_carg_no_claim variableLedgerMismatch fallbackPublic :=
  ay_carg_no_claim_intro variableLedgerMismatch fallbackPublic

theorem ay_carg_factor_mismatch_no_claim
    (factorMismatch fallbackPublic : Prop) :
    factorMismatch ->
    fallbackPublic ->
    ay_carg_no_claim factorMismatch fallbackPublic :=
  ay_carg_no_claim_intro factorMismatch fallbackPublic

theorem ay_carg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch ->
    fallbackPublic ->
    ay_carg_no_claim orderMismatch fallbackPublic :=
  ay_carg_no_claim_intro orderMismatch fallbackPublic

theorem ay_carg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_carg_no_claim tiebreakMismatch fallbackPublic :=
  ay_carg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_carg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_carg_no_claim replayMismatch fallbackPublic :=
  ay_carg_no_claim_intro replayMismatch fallbackPublic

theorem ay_carg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_carg_no_claim baselineMismatch fallbackPublic :=
  ay_carg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_carg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_carg_no_claim buildMismatch fallbackPublic :=
  ay_carg_no_claim_intro buildMismatch fallbackPublic

theorem ay_carg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_carg_no_claim validatorRejects fallbackPublic :=
  ay_carg_no_claim_intro validatorRejects fallbackPublic

theorem ay_carg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_carg_no_claim auditMismatch fallbackPublic :=
  ay_carg_no_claim_intro auditMismatch fallbackPublic

theorem ay_carg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_carg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_carg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_carg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_carg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_carg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_carg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_carg_public_report
      (ay_carg_accepted_rescale guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_carg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_carg_public_report_accepted
        (ay_carg_accepted_rescale guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_carg_publication_requires_validator
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      deterministicBranchOrder searchControlHint outcome formulaTruth : Prop) :
    ay_carg_public_report
      (ay_carg_accepted_rescale
        (ay_carg_guard variableDomainDigest clauseActivityLedger
          variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_carg_guard_validator variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_carg_publication_requires_accepted_guard
        (ay_carg_guard variableDomainDigest clauseActivityLedger
          variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_carg_publication_requires_audit
    (variableDomainDigest clauseActivityLedger variableActivityLedger
      rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      deterministicBranchOrder searchControlHint outcome formulaTruth : Prop) :
    ay_carg_public_report
      (ay_carg_accepted_rescale
        (ay_carg_guard variableDomainDigest clauseActivityLedger
          variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_carg_guard_audit variableDomainDigest clauseActivityLedger
      variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
      deterministicTiebreakManifest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_carg_publication_requires_accepted_guard
        (ay_carg_guard variableDomainDigest clauseActivityLedger
          variableActivityLedger rescaleFactorManifest orderingEquivalenceWitness
          deterministicTiebreakManifest propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_carg_activity_rescaling_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_carg_equisat beforeFormula afterFormula ->
    ay_carg_accepted_rescale guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_carg_conj (beforeFormula -> afterFormula)
      (ay_carg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_carg_conj_intro (beforeFormula -> afterFormula)
      (ay_carg_conj deterministicBranchOrder searchControlHint)
      (ay_carg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_carg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_carg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_carg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_carg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_carg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_carg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_carg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
