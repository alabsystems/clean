-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assignment/trail checksum guard skeleton for sequential-main SAT-COMP
-- branching. Trail reuse is search-control/data reuse only when assignment,
-- trail order, level, reason availability, replay, fallback, build, validator,
-- and audit evidence agree with the checked public result.

def ay_atcg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_atcg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_atcg_conj (before -> after) (after -> before)

def ay_atcg_guard
    (assignmentDigest : Prop)
    (trailOrderDigest : Prop)
    (decisionLevelLedger : Prop)
    (reasonClauseAvailabilityMap : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assignmentDigest ->
      trailOrderDigest ->
      decisionLevelLedger ->
      reasonClauseAvailabilityMap ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_atcg_agreement
    (assignmentMatch : Prop)
    (orderMatch : Prop)
    (levelMatch : Prop)
    (reasonMapMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_atcg_guard assignmentMatch orderMatch levelMatch reasonMapMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_atcg_accepted_reuse
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (reasonReplayObligation : Prop)
    (dataReuseHint : Prop) : Prop :=
  ay_atcg_conj guardEvidence
    (ay_atcg_conj agreementEvidence
      (ay_atcg_conj reasonReplayObligation dataReuseHint))

def ay_atcg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_atcg_conj acceptedEvidence (ay_atcg_conj outcome formulaTruth)

def ay_atcg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_atcg_conj diagnostic fallbackPublic

theorem ay_atcg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_atcg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_atcg_conj_left (left : Prop) (right : Prop) :
    ay_atcg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_atcg_conj_right (left : Prop) (right : Prop) :
    ay_atcg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_atcg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_atcg_equisat before after :=
  fun forward backward =>
    ay_atcg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_atcg_equisat_forward (before : Prop) (after : Prop) :
    ay_atcg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_atcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_atcg_equisat_backward (before : Prop) (after : Prop) :
    ay_atcg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_atcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_atcg_guard_intro
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    assignmentDigest ->
    trailOrderDigest ->
    decisionLevelLedger ->
    reasonClauseAvailabilityMap ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript :=
  fun assignmentH orderH levelH reasonH replayH fallbackH buildH validatorH
      auditH result make =>
    make assignmentH orderH levelH reasonH replayH fallbackH buildH
      validatorH auditH

theorem ay_atcg_guard_assignment
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    assignmentDigest :=
  fun guard =>
    guard assignmentDigest
      (fun assignmentH _orderH _levelH _reasonH _replayH _fallbackH _buildH
          _validatorH _auditH => assignmentH)

theorem ay_atcg_guard_order
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    trailOrderDigest :=
  fun guard =>
    guard trailOrderDigest
      (fun _assignmentH orderH _levelH _reasonH _replayH _fallbackH _buildH
          _validatorH _auditH => orderH)

theorem ay_atcg_guard_level
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    decisionLevelLedger :=
  fun guard =>
    guard decisionLevelLedger
      (fun _assignmentH _orderH levelH _reasonH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_atcg_guard_reason_map
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    reasonClauseAvailabilityMap :=
  fun guard =>
    guard reasonClauseAvailabilityMap
      (fun _assignmentH _orderH _levelH reasonH _replayH _fallbackH _buildH
          _validatorH _auditH => reasonH)

theorem ay_atcg_guard_replay
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _assignmentH _orderH _levelH _reasonH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_atcg_guard_fallback
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _assignmentH _orderH _levelH _reasonH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_atcg_guard_build
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _assignmentH _orderH _levelH _reasonH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_atcg_guard_validator
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _assignmentH _orderH _levelH _reasonH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_atcg_guard_audit
    (assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript : Prop) :
    ay_atcg_guard assignmentDigest trailOrderDigest decisionLevelLedger
      reasonClauseAvailabilityMap propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _assignmentH _orderH _levelH _reasonH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_atcg_agreement_intro
    (assignmentMatch orderMatch levelMatch reasonMapMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    assignmentMatch ->
    orderMatch ->
    levelMatch ->
    reasonMapMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_atcg_agreement assignmentMatch orderMatch levelMatch reasonMapMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_atcg_guard_intro assignmentMatch orderMatch levelMatch reasonMapMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_atcg_accepted_reuse_intro
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    reasonReplayObligation ->
    dataReuseHint ->
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint :=
  fun guardH agreementH reasonH hintH =>
    ay_atcg_conj_intro guardEvidence
      (ay_atcg_conj agreementEvidence
        (ay_atcg_conj reasonReplayObligation dataReuseHint))
      guardH
      (ay_atcg_conj_intro agreementEvidence
        (ay_atcg_conj reasonReplayObligation dataReuseHint)
        agreementH
        (ay_atcg_conj_intro reasonReplayObligation dataReuseHint reasonH
          hintH))

theorem ay_atcg_accepted_reuse_guard
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    guardEvidence :=
  fun accepted =>
    ay_atcg_conj_left guardEvidence
      (ay_atcg_conj agreementEvidence
        (ay_atcg_conj reasonReplayObligation dataReuseHint))
      accepted

theorem ay_atcg_accepted_reuse_agreement
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    agreementEvidence :=
  fun accepted =>
    ay_atcg_conj_left agreementEvidence
      (ay_atcg_conj reasonReplayObligation dataReuseHint)
      (ay_atcg_conj_right guardEvidence
        (ay_atcg_conj agreementEvidence
          (ay_atcg_conj reasonReplayObligation dataReuseHint))
        accepted)

theorem ay_atcg_accepted_reuse_reason_obligation
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    reasonReplayObligation :=
  fun accepted =>
    ay_atcg_conj_left reasonReplayObligation dataReuseHint
      (ay_atcg_conj_right agreementEvidence
        (ay_atcg_conj reasonReplayObligation dataReuseHint)
        (ay_atcg_conj_right guardEvidence
          (ay_atcg_conj agreementEvidence
            (ay_atcg_conj reasonReplayObligation dataReuseHint))
          accepted))

theorem ay_atcg_accepted_reuse_hint
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    dataReuseHint :=
  fun accepted =>
    ay_atcg_conj_right reasonReplayObligation dataReuseHint
      (ay_atcg_conj_right agreementEvidence
        (ay_atcg_conj reasonReplayObligation dataReuseHint)
        (ay_atcg_conj_right guardEvidence
          (ay_atcg_conj agreementEvidence
            (ay_atcg_conj reasonReplayObligation dataReuseHint))
          accepted))

theorem ay_atcg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_atcg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_atcg_conj_intro acceptedEvidence
      (ay_atcg_conj outcome formulaTruth)
      acceptedH (ay_atcg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_atcg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_atcg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_atcg_conj_left acceptedEvidence (ay_atcg_conj outcome formulaTruth)
      report

theorem ay_atcg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_atcg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_atcg_conj_right outcome formulaTruth
      (ay_atcg_conj_right acceptedEvidence
        (ay_atcg_conj outcome formulaTruth) report)

theorem ay_atcg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_atcg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_atcg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_atcg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_atcg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_atcg_conj_right diagnostic fallbackPublic noClaim

theorem ay_atcg_assignment_mismatch_no_claim
    (assignmentMismatch fallbackPublic : Prop) :
    assignmentMismatch -> fallbackPublic ->
    ay_atcg_no_claim assignmentMismatch fallbackPublic :=
  ay_atcg_no_claim_intro assignmentMismatch fallbackPublic

theorem ay_atcg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch -> fallbackPublic ->
    ay_atcg_no_claim orderMismatch fallbackPublic :=
  ay_atcg_no_claim_intro orderMismatch fallbackPublic

theorem ay_atcg_level_mismatch_no_claim
    (levelMismatch fallbackPublic : Prop) :
    levelMismatch -> fallbackPublic ->
    ay_atcg_no_claim levelMismatch fallbackPublic :=
  ay_atcg_no_claim_intro levelMismatch fallbackPublic

theorem ay_atcg_reason_mismatch_no_claim
    (reasonMismatch fallbackPublic : Prop) :
    reasonMismatch -> fallbackPublic ->
    ay_atcg_no_claim reasonMismatch fallbackPublic :=
  ay_atcg_no_claim_intro reasonMismatch fallbackPublic

theorem ay_atcg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_atcg_no_claim replayMismatch fallbackPublic :=
  ay_atcg_no_claim_intro replayMismatch fallbackPublic

theorem ay_atcg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_atcg_no_claim buildMismatch fallbackPublic :=
  ay_atcg_no_claim_intro buildMismatch fallbackPublic

theorem ay_atcg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_atcg_no_claim validatorRejection fallbackPublic :=
  ay_atcg_no_claim_intro validatorRejection fallbackPublic

theorem ay_atcg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_atcg_no_claim auditMismatch fallbackPublic :=
  ay_atcg_no_claim_intro auditMismatch fallbackPublic

theorem ay_atcg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_atcg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_atcg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_atcg_failed_checksum_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_atcg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_atcg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_atcg_accepted_reuse_is_data_reuse
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    dataReuseHint :=
  ay_atcg_accepted_reuse_hint guardEvidence agreementEvidence
    reasonReplayObligation dataReuseHint

theorem ay_atcg_accepted_reuse_preserves_reason_replay
    (guardEvidence agreementEvidence reasonReplayObligation
      dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    reasonReplayObligation :=
  ay_atcg_accepted_reuse_reason_obligation guardEvidence agreementEvidence
    reasonReplayObligation dataReuseHint

theorem ay_atcg_accepted_reuse_preserves_public_soundness
    (guardEvidence agreementEvidence reasonReplayObligation dataReuseHint
      outcome formulaTruth publicSound : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    (guardEvidence -> agreementEvidence -> reasonReplayObligation -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_atcg_accepted_reuse_guard guardEvidence agreementEvidence
        reasonReplayObligation dataReuseHint accepted)
      (ay_atcg_accepted_reuse_agreement guardEvidence agreementEvidence
        reasonReplayObligation dataReuseHint accepted)
      (ay_atcg_accepted_reuse_reason_obligation guardEvidence agreementEvidence
        reasonReplayObligation dataReuseHint accepted)
      outcomeH
      truthH

theorem ay_atcg_accepted_reuse_guides_sat
    (guardEvidence agreementEvidence reasonReplayObligation dataReuseHint
      satOutcome satTruth : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    satOutcome ->
    satTruth ->
    ay_atcg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_atcg_public_report_intro guardEvidence satOutcome satTruth
      (ay_atcg_accepted_reuse_guard guardEvidence agreementEvidence
        reasonReplayObligation dataReuseHint accepted)
      satH
      truthH

theorem ay_atcg_accepted_reuse_guides_unsat
    (guardEvidence agreementEvidence reasonReplayObligation dataReuseHint
      unsatOutcome unsatTruth : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_atcg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_atcg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_atcg_accepted_reuse_guard guardEvidence agreementEvidence
        reasonReplayObligation dataReuseHint accepted)
      unsatH
      truthH

theorem ay_atcg_trail_reuse_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint : Prop) :
    ay_atcg_accepted_reuse guardEvidence agreementEvidence
      reasonReplayObligation dataReuseHint ->
    (dataReuseHint -> reasonReplayObligation -> formulaBefore ->
      formulaAfter) ->
    (dataReuseHint -> reasonReplayObligation -> formulaAfter ->
      formulaBefore) ->
    ay_atcg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_atcg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_atcg_accepted_reuse_hint guardEvidence agreementEvidence
          reasonReplayObligation dataReuseHint accepted)
        (ay_atcg_accepted_reuse_reason_obligation guardEvidence
          agreementEvidence reasonReplayObligation dataReuseHint accepted))
      (backward
        (ay_atcg_accepted_reuse_hint guardEvidence agreementEvidence
          reasonReplayObligation dataReuseHint accepted)
        (ay_atcg_accepted_reuse_reason_obligation guardEvidence
          agreementEvidence reasonReplayObligation dataReuseHint accepted))
