-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart/assumption scope interlock guard skeleton for sequential-main SAT.
-- Interlock guidance under assumptions is search guidance only when restart
-- epochs, assumption frames, scope stacks, replay, fallback, build, validator,
-- and audit evidence agree.

def ay_rasg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rasg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rasg_conj (before -> after) (after -> before)

def ay_rasg_guard
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (restartEpochLedger ->
      assumptionFrameManifest ->
      scopeStackDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rasg_agreement
    (restartMatch : Prop)
    (frameMatch : Prop)
    (scopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_rasg_guard restartMatch frameMatch scopeMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_rasg_accepted_interlock
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) : Prop :=
  ay_rasg_conj guardEvidence
    (ay_rasg_conj agreementEvidence interlockGuidance)

def ay_rasg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_rasg_conj acceptedEvidence (ay_rasg_conj outcome formulaTruth)

def ay_rasg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_rasg_conj diagnostic fallbackPublic

theorem ay_rasg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_rasg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rasg_conj_left (left : Prop) (right : Prop) :
    ay_rasg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rasg_conj_right (left : Prop) (right : Prop) :
    ay_rasg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rasg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_rasg_equisat before after :=
  fun forward backward =>
    ay_rasg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rasg_equisat_forward (before : Prop) (after : Prop) :
    ay_rasg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rasg_conj_left (before -> after) (after -> before) eqsat

theorem ay_rasg_equisat_backward (before : Prop) (after : Prop) :
    ay_rasg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rasg_conj_right (before -> after) (after -> before) eqsat

theorem ay_rasg_guard_intro
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    restartEpochLedger ->
    assumptionFrameManifest ->
    scopeStackDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun restartH frameH scopeH replayH fallbackH buildH validatorH auditH
      result build =>
    build restartH frameH scopeH replayH fallbackH buildH validatorH auditH

theorem ay_rasg_guard_restart
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    restartEpochLedger :=
  fun guard =>
    guard restartEpochLedger
      (fun restartH _frameH _scopeH _replayH _fallbackH _buildH
          _validatorH _auditH => restartH)

theorem ay_rasg_guard_frame
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    assumptionFrameManifest :=
  fun guard =>
    guard assumptionFrameManifest
      (fun _restartH frameH _scopeH _replayH _fallbackH _buildH
          _validatorH _auditH => frameH)

theorem ay_rasg_guard_scope
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    scopeStackDigest :=
  fun guard =>
    guard scopeStackDigest
      (fun _restartH _frameH scopeH _replayH _fallbackH _buildH
          _validatorH _auditH => scopeH)

theorem ay_rasg_guard_replay
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _restartH _frameH _scopeH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_rasg_guard_fallback
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _restartH _frameH _scopeH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_rasg_guard_build
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _restartH _frameH _scopeH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_rasg_guard_validator
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _restartH _frameH _scopeH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_rasg_guard_audit
    (restartEpochLedger : Prop)
    (assumptionFrameManifest : Prop)
    (scopeStackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rasg_guard restartEpochLedger assumptionFrameManifest scopeStackDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _restartH _frameH _scopeH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_rasg_agreement_intro
    (restartMatch : Prop)
    (frameMatch : Prop)
    (scopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    restartMatch ->
    frameMatch ->
    scopeMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rasg_agreement restartMatch frameMatch scopeMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_rasg_guard_intro restartMatch frameMatch scopeMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_rasg_accepted_interlock_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    interlockGuidance ->
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance :=
  fun guardH agreementH guidanceH =>
    ay_rasg_conj_intro guardEvidence
      (ay_rasg_conj agreementEvidence interlockGuidance)
      guardH
      (ay_rasg_conj_intro agreementEvidence interlockGuidance
        agreementH guidanceH)

theorem ay_rasg_accepted_interlock_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_rasg_conj_left guardEvidence
      (ay_rasg_conj agreementEvidence interlockGuidance)
      accepted

theorem ay_rasg_accepted_interlock_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_rasg_conj_left agreementEvidence interlockGuidance
      (ay_rasg_conj_right guardEvidence
        (ay_rasg_conj agreementEvidence interlockGuidance)
        accepted)

theorem ay_rasg_accepted_interlock_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    interlockGuidance :=
  fun accepted =>
    ay_rasg_conj_right agreementEvidence interlockGuidance
      (ay_rasg_conj_right guardEvidence
        (ay_rasg_conj agreementEvidence interlockGuidance)
        accepted)

theorem ay_rasg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rasg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rasg_conj_intro acceptedEvidence
      (ay_rasg_conj outcome formulaTruth)
      acceptedH
      (ay_rasg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rasg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rasg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_rasg_conj_left acceptedEvidence
      (ay_rasg_conj outcome formulaTruth)
      public

theorem ay_rasg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_rasg_no_claim diagnostic fallbackPublic :=
  ay_rasg_conj_intro diagnostic fallbackPublic

theorem ay_rasg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rasg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_rasg_conj_right diagnostic fallbackPublic noClaim

theorem ay_rasg_restart_mismatch_no_claim
    (restartMismatch : Prop)
    (fallbackPublic : Prop) :
    restartMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim restartMismatch fallbackPublic :=
  ay_rasg_no_claim_intro restartMismatch fallbackPublic

theorem ay_rasg_frame_mismatch_no_claim
    (frameMismatch : Prop)
    (fallbackPublic : Prop) :
    frameMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim frameMismatch fallbackPublic :=
  ay_rasg_no_claim_intro frameMismatch fallbackPublic

theorem ay_rasg_scope_mismatch_no_claim
    (scopeMismatch : Prop)
    (fallbackPublic : Prop) :
    scopeMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim scopeMismatch fallbackPublic :=
  ay_rasg_no_claim_intro scopeMismatch fallbackPublic

theorem ay_rasg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim replayMismatch fallbackPublic :=
  ay_rasg_no_claim_intro replayMismatch fallbackPublic

theorem ay_rasg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_rasg_no_claim fallbackFailure fallbackPublic :=
  ay_rasg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_rasg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim buildMismatch fallbackPublic :=
  ay_rasg_no_claim_intro buildMismatch fallbackPublic

theorem ay_rasg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_rasg_no_claim validatorRejection fallbackPublic :=
  ay_rasg_no_claim_intro validatorRejection fallbackPublic

theorem ay_rasg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_rasg_no_claim auditMismatch fallbackPublic :=
  ay_rasg_no_claim_intro auditMismatch fallbackPublic

theorem ay_rasg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_rasg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_rasg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_rasg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rasg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_rasg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_rasg_accepted_interlock_is_assumption_search_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    interlockGuidance :=
  ay_rasg_accepted_interlock_hint guardEvidence agreementEvidence
    interlockGuidance

theorem ay_rasg_accepted_interlock_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    ay_rasg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_rasg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_rasg_accepted_interlock_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_rasg_public_report
      (ay_rasg_accepted_interlock guardEvidence agreementEvidence
        interlockGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_rasg_public_report_intro
      (ay_rasg_accepted_interlock guardEvidence agreementEvidence
        interlockGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_rasg_accepted_interlock_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_rasg_public_report
      (ay_rasg_accepted_interlock guardEvidence agreementEvidence
        interlockGuidance)
      unsatOutcome
      formulaTruth :=
  ay_rasg_accepted_interlock_guides_sat guardEvidence agreementEvidence
    interlockGuidance unsatOutcome formulaTruth

theorem ay_rasg_interlock_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_rasg_accepted_interlock guardEvidence agreementEvidence
      interlockGuidance ->
    ay_rasg_equisat beforeTruth afterTruth ->
    ay_rasg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_rasg_equisat_intro afterTruth beforeTruth
      (ay_rasg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_rasg_equisat_forward beforeTruth afterTruth eqsat)
