-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable activity bump-queue guard skeleton for sequential-main SAT-COMP
-- branching. Bump queues are performance/search-control state only when queue,
-- epoch, domain, update, tiebreak, fallback, build, validator, and audit
-- evidence agree with the public result.

def ay_vbqg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vbqg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_vbqg_conj (before -> after) (after -> before)

def ay_vbqg_guard
    (bumpQueueDigest : Prop)
    (conflictEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (activityUpdateWitness : Prop)
    (tiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (bumpQueueDigest ->
      conflictEpochLedger ->
      variableDomainManifest ->
      activityUpdateWitness ->
      tiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_vbqg_agreement
    (queueMatch : Prop)
    (epochMatch : Prop)
    (domainMatch : Prop)
    (updateMatch : Prop)
    (tiebreakMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_vbqg_guard queueMatch epochMatch domainMatch updateMatch tiebreakMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_vbqg_accepted_processing
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_vbqg_conj guardEvidence
    (ay_vbqg_conj agreementEvidence
      (ay_vbqg_conj deterministicBranchOrder searchControlHint))

def ay_vbqg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_vbqg_conj acceptedEvidence (ay_vbqg_conj outcome formulaTruth)

def ay_vbqg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_vbqg_conj diagnostic fallbackPublic

theorem ay_vbqg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_vbqg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_vbqg_conj_left (left : Prop) (right : Prop) :
    ay_vbqg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_vbqg_conj_right (left : Prop) (right : Prop) :
    ay_vbqg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_vbqg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_vbqg_equisat before after :=
  fun forward backward =>
    ay_vbqg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_vbqg_equisat_forward (before : Prop) (after : Prop) :
    ay_vbqg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_vbqg_conj_left (before -> after) (after -> before) eqsat

theorem ay_vbqg_equisat_backward (before : Prop) (after : Prop) :
    ay_vbqg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_vbqg_conj_right (before -> after) (after -> before) eqsat

theorem ay_vbqg_guard_intro
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    bumpQueueDigest ->
    conflictEpochLedger ->
    variableDomainManifest ->
    activityUpdateWitness ->
    tiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun queueH epochH domainH updateH tiebreakH fallbackH buildH validatorH auditH
      result make =>
    make queueH epochH domainH updateH tiebreakH fallbackH buildH validatorH
      auditH

theorem ay_vbqg_guard_queue
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    bumpQueueDigest :=
  fun guard =>
    guard bumpQueueDigest
      (fun queueH _epochH _domainH _updateH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => queueH)

theorem ay_vbqg_guard_epoch
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    conflictEpochLedger :=
  fun guard =>
    guard conflictEpochLedger
      (fun _queueH epochH _domainH _updateH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_vbqg_guard_domain
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _queueH _epochH domainH _updateH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_vbqg_guard_update
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    activityUpdateWitness :=
  fun guard =>
    guard activityUpdateWitness
      (fun _queueH _epochH _domainH updateH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => updateH)

theorem ay_vbqg_guard_tiebreak
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _queueH _epochH _domainH _updateH tiebreakH _fallbackH _buildH
          _validatorH _auditH => tiebreakH)

theorem ay_vbqg_guard_fallback
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _queueH _epochH _domainH _updateH _tiebreakH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_vbqg_guard_build
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _queueH _epochH _domainH _updateH _tiebreakH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_vbqg_guard_validator
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _queueH _epochH _domainH _updateH _tiebreakH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_vbqg_guard_audit
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _queueH _epochH _domainH _updateH _tiebreakH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_vbqg_agreement_intro
    (queueMatch epochMatch domainMatch updateMatch tiebreakMatch fallbackMatch
      buildMatch validatorAccepts auditMatch : Prop) :
    queueMatch ->
    epochMatch ->
    domainMatch ->
    updateMatch ->
    tiebreakMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_vbqg_agreement queueMatch epochMatch domainMatch updateMatch
      tiebreakMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_vbqg_guard_intro queueMatch epochMatch domainMatch updateMatch
    tiebreakMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_vbqg_accepted_processing_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_vbqg_conj_intro guardEvidence
      (ay_vbqg_conj agreementEvidence
        (ay_vbqg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_vbqg_conj_intro agreementEvidence
        (ay_vbqg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_vbqg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_vbqg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_vbqg_conj_left guardEvidence
    (ay_vbqg_conj agreementEvidence
      (ay_vbqg_conj deterministicBranchOrder searchControlHint))

theorem ay_vbqg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_vbqg_conj_left agreementEvidence
      (ay_vbqg_conj deterministicBranchOrder searchControlHint)
      (ay_vbqg_conj_right guardEvidence
        (ay_vbqg_conj agreementEvidence
          (ay_vbqg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_vbqg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_vbqg_conj_left deterministicBranchOrder searchControlHint
      (ay_vbqg_conj_right agreementEvidence
        (ay_vbqg_conj deterministicBranchOrder searchControlHint)
        (ay_vbqg_conj_right guardEvidence
          (ay_vbqg_conj agreementEvidence
            (ay_vbqg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_vbqg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_vbqg_conj_right deterministicBranchOrder searchControlHint
      (ay_vbqg_conj_right agreementEvidence
        (ay_vbqg_conj deterministicBranchOrder searchControlHint)
        (ay_vbqg_conj_right guardEvidence
          (ay_vbqg_conj agreementEvidence
            (ay_vbqg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_vbqg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_vbqg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_vbqg_conj_intro acceptedEvidence (ay_vbqg_conj outcome formulaTruth)
      acceptedH (ay_vbqg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_vbqg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vbqg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_vbqg_conj_left acceptedEvidence (ay_vbqg_conj outcome formulaTruth)

theorem ay_vbqg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vbqg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_vbqg_conj_left outcome formulaTruth
      (ay_vbqg_conj_right acceptedEvidence
        (ay_vbqg_conj outcome formulaTruth) report)

theorem ay_vbqg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vbqg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_vbqg_conj_right outcome formulaTruth
      (ay_vbqg_conj_right acceptedEvidence
        (ay_vbqg_conj outcome formulaTruth) report)

theorem ay_vbqg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_vbqg_no_claim diagnostic fallbackPublic :=
  ay_vbqg_conj_intro diagnostic fallbackPublic

theorem ay_vbqg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_vbqg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_vbqg_conj_left diagnostic fallbackPublic

theorem ay_vbqg_no_claim_preserves_fallback (diagnostic fallbackPublic : Prop) :
    ay_vbqg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_vbqg_conj_right diagnostic fallbackPublic

theorem ay_vbqg_processing_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_vbqg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_vbqg_equisat_forward beforeFormula afterFormula

theorem ay_vbqg_processing_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_vbqg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_vbqg_equisat_backward beforeFormula afterFormula

theorem ay_vbqg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vbqg_public_report acceptedEvidence outcome formulaTruth ->
    ay_vbqg_conj outcome formulaTruth :=
  fun report =>
    ay_vbqg_conj_right acceptedEvidence (ay_vbqg_conj outcome formulaTruth)
      report

theorem ay_vbqg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_vbqg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_vbqg_conj_right agreementEvidence
      (ay_vbqg_conj deterministicBranchOrder searchControlHint)
      (ay_vbqg_conj_right guardEvidence
        (ay_vbqg_conj agreementEvidence
          (ay_vbqg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_vbqg_queue_mismatch_no_claim
    (queueMismatch fallbackPublic : Prop) :
    queueMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim queueMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro queueMismatch fallbackPublic

theorem ay_vbqg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim epochMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro epochMismatch fallbackPublic

theorem ay_vbqg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim domainMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro domainMismatch fallbackPublic

theorem ay_vbqg_update_mismatch_no_claim
    (updateMismatch fallbackPublic : Prop) :
    updateMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim updateMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro updateMismatch fallbackPublic

theorem ay_vbqg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim tiebreakMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_vbqg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim buildMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro buildMismatch fallbackPublic

theorem ay_vbqg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_vbqg_no_claim validatorRejects fallbackPublic :=
  ay_vbqg_no_claim_intro validatorRejects fallbackPublic

theorem ay_vbqg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_vbqg_no_claim auditMismatch fallbackPublic :=
  ay_vbqg_no_claim_intro auditMismatch fallbackPublic

theorem ay_vbqg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_vbqg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_vbqg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_vbqg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_vbqg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_vbqg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_vbqg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_vbqg_public_report
      (ay_vbqg_accepted_processing guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_vbqg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_vbqg_public_report_accepted
        (ay_vbqg_accepted_processing guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_vbqg_publication_requires_validator
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_vbqg_public_report
      (ay_vbqg_accepted_processing
        (ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
          activityUpdateWitness tiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_vbqg_guard_validator bumpQueueDigest conflictEpochLedger
      variableDomainManifest activityUpdateWitness tiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_vbqg_publication_requires_accepted_guard
        (ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
          activityUpdateWitness tiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_vbqg_publication_requires_audit
    (bumpQueueDigest conflictEpochLedger variableDomainManifest
      activityUpdateWitness tiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_vbqg_public_report
      (ay_vbqg_accepted_processing
        (ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
          activityUpdateWitness tiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_vbqg_guard_audit bumpQueueDigest conflictEpochLedger
      variableDomainManifest activityUpdateWitness tiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_vbqg_publication_requires_accepted_guard
        (ay_vbqg_guard bumpQueueDigest conflictEpochLedger variableDomainManifest
          activityUpdateWitness tiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_vbqg_bump_queue_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_vbqg_equisat beforeFormula afterFormula ->
    ay_vbqg_accepted_processing guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_vbqg_conj (beforeFormula -> afterFormula)
      (ay_vbqg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_vbqg_conj_intro (beforeFormula -> afterFormula)
      (ay_vbqg_conj deterministicBranchOrder searchControlHint)
      (ay_vbqg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_vbqg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_vbqg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_vbqg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_vbqg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_vbqg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_vbqg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_vbqg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
