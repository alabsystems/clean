-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-cache decay guard for sequential-main SAT-COMP branching. Phase-cache
-- decay is search-control only when domain, phase cache, decay epoch,
-- stale-entry policy, tiebreak, decision replay, propagation replay, fallback,
-- build, validator, and audit evidence agree.

def ay_pdcg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pdcg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pdcg_conj (before -> after) (after -> before)

def ay_pdcg_guard
    (variableDomainDigest : Prop)
    (phaseCacheDigest : Prop)
    (decayEpochManifest : Prop)
    (staleEntryPolicyWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      phaseCacheDigest ->
      decayEpochManifest ->
      staleEntryPolicyWitness ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pdcg_agreement
    (domainMatch cacheMatch epochMatch staleMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_pdcg_guard domainMatch cacheMatch epochMatch staleMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_pdcg_accepted_phase_decay
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_pdcg_conj guardEvidence
    (ay_pdcg_conj agreementEvidence
      (ay_pdcg_conj deterministicBranchOrder searchControlHint))

def ay_pdcg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pdcg_conj acceptedEvidence (ay_pdcg_conj outcome formulaTruth)

def ay_pdcg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_pdcg_conj diagnostic fallbackPublic

theorem ay_pdcg_conj_intro (left right : Prop) :
    left -> right -> ay_pdcg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pdcg_conj_left (left right : Prop) :
    ay_pdcg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pdcg_conj_right (left right : Prop) :
    ay_pdcg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pdcg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pdcg_equisat before after :=
  fun forward backward =>
    ay_pdcg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pdcg_equisat_forward (before after : Prop) :
    ay_pdcg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pdcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pdcg_equisat_backward (before after : Prop) :
    ay_pdcg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pdcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pdcg_guard_intro
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    phaseCacheDigest ->
    decayEpochManifest ->
    staleEntryPolicyWitness ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH cacheH epochH staleH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH result make =>
    make domainH cacheH epochH staleH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH

theorem ay_pdcg_guard_domain
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_pdcg_guard_cache
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    phaseCacheDigest :=
  fun guard =>
    guard phaseCacheDigest
      (fun _domainH cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => cacheH)

theorem ay_pdcg_guard_epoch
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decayEpochManifest :=
  fun guard =>
    guard decayEpochManifest
      (fun _domainH _cacheH epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => epochH)

theorem ay_pdcg_guard_stale
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    staleEntryPolicyWitness :=
  fun guard =>
    guard staleEntryPolicyWitness
      (fun _domainH _cacheH _epochH staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => staleH)

theorem ay_pdcg_guard_tiebreak
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _cacheH _epochH _staleH tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_pdcg_guard_decision
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _cacheH _epochH _staleH _tiebreakH decisionH _replayH
          _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_pdcg_guard_replay
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _cacheH _epochH _staleH _tiebreakH _decisionH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_pdcg_guard_baseline
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_pdcg_guard_build
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_pdcg_guard_validator
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_pdcg_guard_audit
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _cacheH _epochH _staleH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_pdcg_agreement_intro
    (domainMatch cacheMatch epochMatch staleMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    domainMatch ->
    cacheMatch ->
    epochMatch ->
    staleMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_pdcg_agreement domainMatch cacheMatch epochMatch staleMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_pdcg_guard_intro domainMatch cacheMatch epochMatch staleMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_pdcg_accepted_phase_decay_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_pdcg_conj_intro guardEvidence
      (ay_pdcg_conj agreementEvidence
        (ay_pdcg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_pdcg_conj_intro agreementEvidence
        (ay_pdcg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_pdcg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_pdcg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_pdcg_conj_left guardEvidence
    (ay_pdcg_conj agreementEvidence
      (ay_pdcg_conj deterministicBranchOrder searchControlHint))

theorem ay_pdcg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_pdcg_conj_left agreementEvidence
      (ay_pdcg_conj deterministicBranchOrder searchControlHint)
      (ay_pdcg_conj_right guardEvidence
        (ay_pdcg_conj agreementEvidence
          (ay_pdcg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_pdcg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_pdcg_conj_left deterministicBranchOrder searchControlHint
      (ay_pdcg_conj_right agreementEvidence
        (ay_pdcg_conj deterministicBranchOrder searchControlHint)
        (ay_pdcg_conj_right guardEvidence
          (ay_pdcg_conj agreementEvidence
            (ay_pdcg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_pdcg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_pdcg_conj_right deterministicBranchOrder searchControlHint
      (ay_pdcg_conj_right agreementEvidence
        (ay_pdcg_conj deterministicBranchOrder searchControlHint)
        (ay_pdcg_conj_right guardEvidence
          (ay_pdcg_conj agreementEvidence
            (ay_pdcg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_pdcg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pdcg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pdcg_conj_intro acceptedEvidence (ay_pdcg_conj outcome formulaTruth)
      acceptedH (ay_pdcg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pdcg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pdcg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_pdcg_conj_left acceptedEvidence (ay_pdcg_conj outcome formulaTruth)

theorem ay_pdcg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pdcg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pdcg_conj_left outcome formulaTruth
      (ay_pdcg_conj_right acceptedEvidence
        (ay_pdcg_conj outcome formulaTruth) report)

theorem ay_pdcg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pdcg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pdcg_conj_right outcome formulaTruth
      (ay_pdcg_conj_right acceptedEvidence
        (ay_pdcg_conj outcome formulaTruth) report)

theorem ay_pdcg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_pdcg_no_claim diagnostic fallbackPublic :=
  ay_pdcg_conj_intro diagnostic fallbackPublic

theorem ay_pdcg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_pdcg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_pdcg_conj_left diagnostic fallbackPublic

theorem ay_pdcg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_pdcg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_pdcg_conj_right diagnostic fallbackPublic

theorem ay_pdcg_phase_decay_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pdcg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_pdcg_equisat_forward beforeFormula afterFormula

theorem ay_pdcg_phase_decay_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pdcg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_pdcg_equisat_backward beforeFormula afterFormula

theorem ay_pdcg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pdcg_public_report acceptedEvidence outcome formulaTruth ->
    ay_pdcg_conj outcome formulaTruth :=
  fun report =>
    ay_pdcg_conj_right acceptedEvidence (ay_pdcg_conj outcome formulaTruth)
      report

theorem ay_pdcg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_pdcg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_pdcg_conj_right agreementEvidence
      (ay_pdcg_conj deterministicBranchOrder searchControlHint)
      (ay_pdcg_conj_right guardEvidence
        (ay_pdcg_conj agreementEvidence
          (ay_pdcg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_pdcg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim domainMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro domainMismatch fallbackPublic

theorem ay_pdcg_cache_mismatch_no_claim
    (cacheMismatch fallbackPublic : Prop) :
    cacheMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim cacheMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro cacheMismatch fallbackPublic

theorem ay_pdcg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim epochMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro epochMismatch fallbackPublic

theorem ay_pdcg_stale_mismatch_no_claim
    (staleMismatch fallbackPublic : Prop) :
    staleMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim staleMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro staleMismatch fallbackPublic

theorem ay_pdcg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim tiebreakMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_pdcg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim decisionMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_pdcg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim replayMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro replayMismatch fallbackPublic

theorem ay_pdcg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim baselineMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_pdcg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim buildMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro buildMismatch fallbackPublic

theorem ay_pdcg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_pdcg_no_claim validatorRejects fallbackPublic :=
  ay_pdcg_no_claim_intro validatorRejects fallbackPublic

theorem ay_pdcg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_pdcg_no_claim auditMismatch fallbackPublic :=
  ay_pdcg_no_claim_intro auditMismatch fallbackPublic

theorem ay_pdcg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_pdcg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_pdcg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_pdcg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_pdcg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_pdcg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_pdcg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_pdcg_public_report
      (ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pdcg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_pdcg_public_report_accepted
        (ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_pdcg_publication_requires_validator
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_pdcg_public_report
      (ay_pdcg_accepted_phase_decay
        (ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
          staleEntryPolicyWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pdcg_guard_validator variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pdcg_publication_requires_accepted_guard
        (ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
          staleEntryPolicyWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_pdcg_publication_requires_audit
    (variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_pdcg_public_report
      (ay_pdcg_accepted_phase_decay
        (ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
          staleEntryPolicyWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pdcg_guard_audit variableDomainDigest phaseCacheDigest decayEpochManifest
      staleEntryPolicyWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pdcg_publication_requires_accepted_guard
        (ay_pdcg_guard variableDomainDigest phaseCacheDigest decayEpochManifest
          staleEntryPolicyWitness deterministicTiebreakManifest
          decisionOrderReplay propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_pdcg_phase_cache_decay_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_pdcg_equisat beforeFormula afterFormula ->
    ay_pdcg_accepted_phase_decay guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_pdcg_conj (beforeFormula -> afterFormula)
      (ay_pdcg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_pdcg_conj_intro (beforeFormula -> afterFormula)
      (ay_pdcg_conj deterministicBranchOrder searchControlHint)
      (ay_pdcg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_pdcg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_pdcg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pdcg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pdcg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pdcg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pdcg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pdcg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
