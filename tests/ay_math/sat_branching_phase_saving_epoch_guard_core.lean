-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-saving epoch guard skeleton for sequential-main SAT-COMP branching.
-- Saved phases are search-control state only when domain, epoch, reset,
-- backtrack, replay, tiebreak, fallback, build, validator, and audit evidence
-- agree with the public result.

def ay_pseg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pseg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pseg_conj (before -> after) (after -> before)

def ay_pseg_guard
    (variableDomainDigest : Prop)
    (phaseTableEpochDigest : Prop)
    (decisionLevelResetEvidence : Prop)
    (chronologicalBacktrackWitness : Prop)
    (propagationReplay : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      phaseTableEpochDigest ->
      decisionLevelResetEvidence ->
      chronologicalBacktrackWitness ->
      propagationReplay ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pseg_agreement
    (domainMatch : Prop)
    (epochMatch : Prop)
    (resetMatch : Prop)
    (backtrackMatch : Prop)
    (replayMatch : Prop)
    (tiebreakMatch : Prop)
    (baselineMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_pseg_guard domainMatch epochMatch resetMatch backtrackMatch replayMatch
    tiebreakMatch baselineMatch buildMatch validatorAccepts auditMatch

def ay_pseg_accepted_phase_saving
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_pseg_conj guardEvidence
    (ay_pseg_conj agreementEvidence
      (ay_pseg_conj deterministicBranchOrder searchControlHint))

def ay_pseg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_pseg_conj acceptedEvidence (ay_pseg_conj outcome formulaTruth)

def ay_pseg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_pseg_conj diagnostic fallbackPublic

theorem ay_pseg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_pseg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pseg_conj_left (left : Prop) (right : Prop) :
    ay_pseg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pseg_conj_right (left : Prop) (right : Prop) :
    ay_pseg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pseg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_pseg_equisat before after :=
  fun forward backward =>
    ay_pseg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pseg_equisat_forward (before : Prop) (after : Prop) :
    ay_pseg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pseg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pseg_equisat_backward (before : Prop) (after : Prop) :
    ay_pseg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pseg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pseg_guard_intro
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    phaseTableEpochDigest ->
    decisionLevelResetEvidence ->
    chronologicalBacktrackWitness ->
    propagationReplay ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH epochH resetH backtrackH replayH tiebreakH baselineH buildH
      validatorH auditH result make =>
    make domainH epochH resetH backtrackH replayH tiebreakH baselineH buildH
      validatorH auditH

theorem ay_pseg_guard_domain
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _epochH _resetH _backtrackH _replayH _tiebreakH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_pseg_guard_epoch
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    phaseTableEpochDigest :=
  fun guard =>
    guard phaseTableEpochDigest
      (fun _domainH epochH _resetH _backtrackH _replayH _tiebreakH
          _baselineH _buildH _validatorH _auditH => epochH)

theorem ay_pseg_guard_reset
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    decisionLevelResetEvidence :=
  fun guard =>
    guard decisionLevelResetEvidence
      (fun _domainH _epochH resetH _backtrackH _replayH _tiebreakH
          _baselineH _buildH _validatorH _auditH => resetH)

theorem ay_pseg_guard_backtrack
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    chronologicalBacktrackWitness :=
  fun guard =>
    guard chronologicalBacktrackWitness
      (fun _domainH _epochH _resetH backtrackH _replayH _tiebreakH
          _baselineH _buildH _validatorH _auditH => backtrackH)

theorem ay_pseg_guard_replay
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _epochH _resetH _backtrackH replayH _tiebreakH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_pseg_guard_tiebreak
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _epochH _resetH _backtrackH _replayH tiebreakH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_pseg_guard_baseline
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _epochH _resetH _backtrackH _replayH _tiebreakH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_pseg_guard_build
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _epochH _resetH _backtrackH _replayH _tiebreakH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_pseg_guard_validator
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _epochH _resetH _backtrackH _replayH _tiebreakH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_pseg_guard_audit
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_pseg_guard variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _epochH _resetH _backtrackH _replayH _tiebreakH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_pseg_agreement_intro
    (domainMatch epochMatch resetMatch backtrackMatch replayMatch tiebreakMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    epochMatch ->
    resetMatch ->
    backtrackMatch ->
    replayMatch ->
    tiebreakMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_pseg_agreement domainMatch epochMatch resetMatch backtrackMatch
      replayMatch tiebreakMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_pseg_guard_intro domainMatch epochMatch resetMatch backtrackMatch
    replayMatch tiebreakMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_pseg_accepted_phase_saving_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_pseg_conj_intro guardEvidence
      (ay_pseg_conj agreementEvidence
        (ay_pseg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_pseg_conj_intro agreementEvidence
        (ay_pseg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_pseg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_pseg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_pseg_conj_left guardEvidence
    (ay_pseg_conj agreementEvidence
      (ay_pseg_conj deterministicBranchOrder searchControlHint))

theorem ay_pseg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_pseg_conj_left agreementEvidence
      (ay_pseg_conj deterministicBranchOrder searchControlHint)
      (ay_pseg_conj_right guardEvidence
        (ay_pseg_conj agreementEvidence
          (ay_pseg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_pseg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_pseg_conj_left deterministicBranchOrder searchControlHint
      (ay_pseg_conj_right agreementEvidence
        (ay_pseg_conj deterministicBranchOrder searchControlHint)
        (ay_pseg_conj_right guardEvidence
          (ay_pseg_conj agreementEvidence
            (ay_pseg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_pseg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_pseg_conj_right deterministicBranchOrder searchControlHint
      (ay_pseg_conj_right agreementEvidence
        (ay_pseg_conj deterministicBranchOrder searchControlHint)
        (ay_pseg_conj_right guardEvidence
          (ay_pseg_conj agreementEvidence
            (ay_pseg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_pseg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pseg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pseg_conj_intro acceptedEvidence (ay_pseg_conj outcome formulaTruth)
      acceptedH (ay_pseg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pseg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pseg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_pseg_conj_left acceptedEvidence (ay_pseg_conj outcome formulaTruth)

theorem ay_pseg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pseg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pseg_conj_left outcome formulaTruth
      (ay_pseg_conj_right acceptedEvidence
        (ay_pseg_conj outcome formulaTruth) report)

theorem ay_pseg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pseg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pseg_conj_right outcome formulaTruth
      (ay_pseg_conj_right acceptedEvidence
        (ay_pseg_conj outcome formulaTruth) report)

theorem ay_pseg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_pseg_no_claim diagnostic fallbackPublic :=
  ay_pseg_conj_intro diagnostic fallbackPublic

theorem ay_pseg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_pseg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_pseg_conj_left diagnostic fallbackPublic

theorem ay_pseg_no_claim_preserves_fallback (diagnostic fallbackPublic : Prop) :
    ay_pseg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_pseg_conj_right diagnostic fallbackPublic

theorem ay_pseg_phase_saving_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pseg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_pseg_equisat_forward beforeFormula afterFormula

theorem ay_pseg_phase_saving_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pseg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_pseg_equisat_backward beforeFormula afterFormula

theorem ay_pseg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pseg_public_report acceptedEvidence outcome formulaTruth ->
    ay_pseg_conj outcome formulaTruth :=
  fun report =>
    ay_pseg_conj_right acceptedEvidence (ay_pseg_conj outcome formulaTruth)
      report

theorem ay_pseg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_pseg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_pseg_conj_right agreementEvidence
      (ay_pseg_conj deterministicBranchOrder searchControlHint)
      (ay_pseg_conj_right guardEvidence
        (ay_pseg_conj agreementEvidence
          (ay_pseg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_pseg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim domainMismatch fallbackPublic :=
  ay_pseg_no_claim_intro domainMismatch fallbackPublic

theorem ay_pseg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim epochMismatch fallbackPublic :=
  ay_pseg_no_claim_intro epochMismatch fallbackPublic

theorem ay_pseg_reset_mismatch_no_claim
    (resetMismatch fallbackPublic : Prop) :
    resetMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim resetMismatch fallbackPublic :=
  ay_pseg_no_claim_intro resetMismatch fallbackPublic

theorem ay_pseg_backtrack_mismatch_no_claim
    (backtrackMismatch fallbackPublic : Prop) :
    backtrackMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim backtrackMismatch fallbackPublic :=
  ay_pseg_no_claim_intro backtrackMismatch fallbackPublic

theorem ay_pseg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim replayMismatch fallbackPublic :=
  ay_pseg_no_claim_intro replayMismatch fallbackPublic

theorem ay_pseg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim tiebreakMismatch fallbackPublic :=
  ay_pseg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_pseg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim baselineMismatch fallbackPublic :=
  ay_pseg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_pseg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim buildMismatch fallbackPublic :=
  ay_pseg_no_claim_intro buildMismatch fallbackPublic

theorem ay_pseg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_pseg_no_claim validatorRejects fallbackPublic :=
  ay_pseg_no_claim_intro validatorRejects fallbackPublic

theorem ay_pseg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_pseg_no_claim auditMismatch fallbackPublic :=
  ay_pseg_no_claim_intro auditMismatch fallbackPublic

theorem ay_pseg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_pseg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_pseg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_pseg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_pseg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_pseg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_pseg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_pseg_public_report
      (ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pseg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_pseg_public_report_accepted
        (ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_pseg_publication_requires_validator
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_pseg_public_report
      (ay_pseg_accepted_phase_saving
        (ay_pseg_guard variableDomainDigest phaseTableEpochDigest
          decisionLevelResetEvidence chronologicalBacktrackWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pseg_guard_validator variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pseg_publication_requires_accepted_guard
        (ay_pseg_guard variableDomainDigest phaseTableEpochDigest
          decisionLevelResetEvidence chronologicalBacktrackWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_pseg_publication_requires_audit
    (variableDomainDigest phaseTableEpochDigest decisionLevelResetEvidence
      chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_pseg_public_report
      (ay_pseg_accepted_phase_saving
        (ay_pseg_guard variableDomainDigest phaseTableEpochDigest
          decisionLevelResetEvidence chronologicalBacktrackWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pseg_guard_audit variableDomainDigest phaseTableEpochDigest
      decisionLevelResetEvidence chronologicalBacktrackWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pseg_publication_requires_accepted_guard
        (ay_pseg_guard variableDomainDigest phaseTableEpochDigest
          decisionLevelResetEvidence chronologicalBacktrackWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_pseg_phase_saving_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_pseg_equisat beforeFormula afterFormula ->
    ay_pseg_accepted_phase_saving guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_pseg_conj (beforeFormula -> afterFormula)
      (ay_pseg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_pseg_conj_intro (beforeFormula -> afterFormula)
      (ay_pseg_conj deterministicBranchOrder searchControlHint)
      (ay_pseg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_pseg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_pseg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pseg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pseg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pseg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pseg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pseg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
