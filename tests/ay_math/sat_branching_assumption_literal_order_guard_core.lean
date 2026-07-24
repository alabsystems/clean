-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption-literal ordering guard skeleton for sequential-main SAT-COMP
-- assumptions and branching. Literal ordering is a search-control hint under
-- the same assumption frame only when replay and publication evidence agree.

def ay_alog_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_alog_equisat (before : Prop) (after : Prop) : Prop :=
  ay_alog_conj (before -> after) (after -> before)

def ay_alog_guard
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionFrameLedger ->
      literalOrderDigest ->
      levelScopeDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_alog_agreement
    (assumptionFrameMatch : Prop)
    (literalOrderMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_alog_guard assumptionFrameMatch literalOrderMatch levelScopeMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_alog_accepted_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_alog_conj guardEvidence
    (ay_alog_conj agreementEvidence
      (ay_alog_conj sameAssumptions searchControlHint))

def ay_alog_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_alog_conj acceptedEvidence (ay_alog_conj outcome formulaTruth)

def ay_alog_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_alog_conj diagnostic fallbackPublic

theorem ay_alog_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_alog_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_alog_conj_left (left : Prop) (right : Prop) :
    ay_alog_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_alog_conj_right (left : Prop) (right : Prop) :
    ay_alog_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_alog_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_alog_equisat before after :=
  fun forward backward =>
    ay_alog_conj_intro (before -> after) (after -> before) forward backward

theorem ay_alog_equisat_forward (before : Prop) (after : Prop) :
    ay_alog_equisat before after -> before -> after :=
  fun eqsat =>
    ay_alog_conj_left (before -> after) (after -> before) eqsat

theorem ay_alog_equisat_backward (before : Prop) (after : Prop) :
    ay_alog_equisat before after -> after -> before :=
  fun eqsat =>
    ay_alog_conj_right (before -> after) (after -> before) eqsat

theorem ay_alog_guard_intro
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    assumptionFrameLedger ->
    literalOrderDigest ->
    levelScopeDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun frameH orderH levelH replayH fallbackH buildH validatorH auditH
      result make =>
    make frameH orderH levelH replayH fallbackH buildH validatorH auditH

theorem ay_alog_guard_assumption_frame
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    assumptionFrameLedger :=
  fun guard =>
    guard assumptionFrameLedger
      (fun frameH _orderH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => frameH)

theorem ay_alog_guard_literal_order
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    literalOrderDigest :=
  fun guard =>
    guard literalOrderDigest
      (fun _frameH orderH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => orderH)

theorem ay_alog_guard_level_scope
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _frameH _orderH levelH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_alog_guard_replay
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _frameH _orderH _levelH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_alog_guard_fallback
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _frameH _orderH _levelH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_alog_guard_build
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _frameH _orderH _levelH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_alog_guard_validator
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _frameH _orderH _levelH _replayH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_alog_guard_audit
    (assumptionFrameLedger : Prop)
    (literalOrderDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_alog_guard assumptionFrameLedger literalOrderDigest levelScopeDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _frameH _orderH _levelH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_alog_agreement_intro
    (assumptionFrameMatch : Prop)
    (literalOrderMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    assumptionFrameMatch ->
    literalOrderMatch ->
    levelScopeMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_alog_agreement assumptionFrameMatch literalOrderMatch levelScopeMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_alog_guard_intro assumptionFrameMatch literalOrderMatch levelScopeMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_alog_accepted_order_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    sameAssumptions ->
    searchControlHint ->
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint :=
  fun guardH agreementH assumptionsH hintH =>
    ay_alog_conj_intro guardEvidence
      (ay_alog_conj agreementEvidence
        (ay_alog_conj sameAssumptions searchControlHint))
      guardH
      (ay_alog_conj_intro agreementEvidence
        (ay_alog_conj sameAssumptions searchControlHint)
        agreementH
        (ay_alog_conj_intro sameAssumptions searchControlHint assumptionsH
          hintH))

theorem ay_alog_accepted_order_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_alog_conj_left guardEvidence
      (ay_alog_conj agreementEvidence
        (ay_alog_conj sameAssumptions searchControlHint))
      accepted

theorem ay_alog_accepted_order_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_alog_conj_left agreementEvidence
      (ay_alog_conj sameAssumptions searchControlHint)
      (ay_alog_conj_right guardEvidence
        (ay_alog_conj agreementEvidence
          (ay_alog_conj sameAssumptions searchControlHint))
        accepted)

theorem ay_alog_accepted_order_hint_same_assumptions
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    sameAssumptions :=
  fun accepted =>
    ay_alog_conj_left sameAssumptions searchControlHint
      (ay_alog_conj_right agreementEvidence
        (ay_alog_conj sameAssumptions searchControlHint)
        (ay_alog_conj_right guardEvidence
          (ay_alog_conj agreementEvidence
            (ay_alog_conj sameAssumptions searchControlHint))
          accepted))

theorem ay_alog_accepted_order_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_alog_conj_right sameAssumptions searchControlHint
      (ay_alog_conj_right agreementEvidence
        (ay_alog_conj sameAssumptions searchControlHint)
        (ay_alog_conj_right guardEvidence
          (ay_alog_conj agreementEvidence
            (ay_alog_conj sameAssumptions searchControlHint))
          accepted))

theorem ay_alog_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_alog_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_alog_conj_intro acceptedEvidence
      (ay_alog_conj outcome formulaTruth)
      acceptedH (ay_alog_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_alog_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_alog_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_alog_conj_left acceptedEvidence (ay_alog_conj outcome formulaTruth)
      report

theorem ay_alog_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_alog_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_alog_conj_right outcome formulaTruth
      (ay_alog_conj_right acceptedEvidence
        (ay_alog_conj outcome formulaTruth) report)

theorem ay_alog_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_alog_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_alog_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_alog_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_alog_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_alog_conj_right diagnostic fallbackPublic noClaim

theorem ay_alog_assumption_frame_mismatch_no_claim
    (assumptionFrameMismatch : Prop)
    (fallbackPublic : Prop) :
    assumptionFrameMismatch -> fallbackPublic ->
    ay_alog_no_claim assumptionFrameMismatch fallbackPublic :=
  ay_alog_no_claim_intro assumptionFrameMismatch fallbackPublic

theorem ay_alog_literal_order_mismatch_no_claim
    (literalOrderMismatch : Prop)
    (fallbackPublic : Prop) :
    literalOrderMismatch -> fallbackPublic ->
    ay_alog_no_claim literalOrderMismatch fallbackPublic :=
  ay_alog_no_claim_intro literalOrderMismatch fallbackPublic

theorem ay_alog_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_alog_no_claim levelScopeMismatch fallbackPublic :=
  ay_alog_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_alog_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_alog_no_claim replayMismatch fallbackPublic :=
  ay_alog_no_claim_intro replayMismatch fallbackPublic

theorem ay_alog_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_alog_no_claim fallbackFailure fallbackPublic :=
  ay_alog_no_claim_intro fallbackFailure fallbackPublic

theorem ay_alog_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_alog_no_claim buildMismatch fallbackPublic :=
  ay_alog_no_claim_intro buildMismatch fallbackPublic

theorem ay_alog_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_alog_no_claim validatorRejection fallbackPublic :=
  ay_alog_no_claim_intro validatorRejection fallbackPublic

theorem ay_alog_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_alog_no_claim auditMismatch fallbackPublic :=
  ay_alog_no_claim_intro auditMismatch fallbackPublic

theorem ay_alog_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_alog_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_alog_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_alog_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_alog_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_alog_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_alog_accepted_order_is_search_control_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    searchControlHint :=
  ay_alog_accepted_order_hint_hint guardEvidence agreementEvidence
    sameAssumptions searchControlHint

theorem ay_alog_accepted_order_under_same_assumptions
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    sameAssumptions :=
  ay_alog_accepted_order_hint_same_assumptions guardEvidence agreementEvidence
    sameAssumptions searchControlHint

theorem ay_alog_accepted_order_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    (guardEvidence -> agreementEvidence -> sameAssumptions -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_alog_accepted_order_hint_guard guardEvidence agreementEvidence
        sameAssumptions searchControlHint accepted)
      (ay_alog_accepted_order_hint_agreement guardEvidence agreementEvidence
        sameAssumptions searchControlHint accepted)
      (ay_alog_accepted_order_hint_same_assumptions guardEvidence
        agreementEvidence sameAssumptions searchControlHint accepted)
      outcomeH
      truthH

theorem ay_alog_accepted_order_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_alog_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_alog_public_report_intro guardEvidence satOutcome satTruth
      (ay_alog_accepted_order_hint_guard guardEvidence agreementEvidence
        sameAssumptions searchControlHint accepted)
      satH
      truthH

theorem ay_alog_accepted_order_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_alog_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_alog_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_alog_accepted_order_hint_guard guardEvidence agreementEvidence
        sameAssumptions searchControlHint accepted)
      unsatH
      truthH

theorem ay_alog_literal_order_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (searchControlHint : Prop) :
    ay_alog_accepted_order_hint guardEvidence agreementEvidence
      sameAssumptions searchControlHint ->
    (sameAssumptions -> searchControlHint -> formulaBefore -> formulaAfter) ->
    (sameAssumptions -> searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_alog_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_alog_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_alog_accepted_order_hint_same_assumptions guardEvidence
          agreementEvidence sameAssumptions searchControlHint accepted)
        (ay_alog_accepted_order_hint_hint guardEvidence agreementEvidence
          sameAssumptions searchControlHint accepted))
      (backward
        (ay_alog_accepted_order_hint_same_assumptions guardEvidence
          agreementEvidence sameAssumptions searchControlHint accepted)
        (ay_alog_accepted_order_hint_hint guardEvidence agreementEvidence
          sameAssumptions searchControlHint accepted))
