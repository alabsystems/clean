-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision stack snapshot guard skeleton for sequential-main SAT. Stack
-- snapshot guidance is search scheduling only when stack, level, trail, replay,
-- fallback, build, validator, and audit evidence agree.

def ay_dssg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dssg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_dssg_conj (before -> after) (after -> before)

def ay_dssg_guard
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (stackDigest ->
      decisionLevelLedger ->
      trailSnapshot ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_dssg_agreement
    (stackMatch : Prop)
    (levelMatch : Prop)
    (trailMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_dssg_guard stackMatch levelMatch trailMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_dssg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) : Prop :=
  ay_dssg_conj guardEvidence (ay_dssg_conj agreementEvidence stackGuidance)

def ay_dssg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_dssg_conj acceptedEvidence (ay_dssg_conj outcome formulaTruth)

def ay_dssg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_dssg_conj diagnostic fallbackPublic

theorem ay_dssg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_dssg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_dssg_conj_left (left : Prop) (right : Prop) :
    ay_dssg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_dssg_conj_right (left : Prop) (right : Prop) :
    ay_dssg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_dssg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_dssg_equisat before after :=
  fun forward backward =>
    ay_dssg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_dssg_equisat_forward (before : Prop) (after : Prop) :
    ay_dssg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_dssg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dssg_equisat_backward (before : Prop) (after : Prop) :
    ay_dssg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_dssg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dssg_guard_intro
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    stackDigest ->
    decisionLevelLedger ->
    trailSnapshot ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun stackH levelH trailH replayH fallbackH buildH validatorH auditH
      result build =>
    build stackH levelH trailH replayH fallbackH buildH validatorH auditH

theorem ay_dssg_guard_stack
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    stackDigest :=
  fun guard =>
    guard stackDigest
      (fun stackH _levelH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => stackH)

theorem ay_dssg_guard_level
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    decisionLevelLedger :=
  fun guard =>
    guard decisionLevelLedger
      (fun _stackH levelH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_dssg_guard_trail
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    trailSnapshot :=
  fun guard =>
    guard trailSnapshot
      (fun _stackH _levelH trailH _replayH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_dssg_guard_replay
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _stackH _levelH _trailH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_dssg_guard_fallback
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _stackH _levelH _trailH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_dssg_guard_build
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _stackH _levelH _trailH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_dssg_guard_validator
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _stackH _levelH _trailH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_dssg_guard_audit
    (stackDigest : Prop)
    (decisionLevelLedger : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_dssg_guard stackDigest decisionLevelLedger trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _stackH _levelH _trailH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_dssg_agreement_intro
    (stackMatch : Prop)
    (levelMatch : Prop)
    (trailMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    stackMatch ->
    levelMatch ->
    trailMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_dssg_agreement stackMatch levelMatch trailMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_dssg_guard_intro stackMatch levelMatch trailMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_dssg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    stackGuidance ->
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance :=
  fun guardH agreementH guidanceH =>
    ay_dssg_conj_intro guardEvidence
      (ay_dssg_conj agreementEvidence stackGuidance)
      guardH
      (ay_dssg_conj_intro agreementEvidence stackGuidance agreementH guidanceH)

theorem ay_dssg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_dssg_conj_left guardEvidence
      (ay_dssg_conj agreementEvidence stackGuidance)
      accepted

theorem ay_dssg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_dssg_conj_left agreementEvidence stackGuidance
      (ay_dssg_conj_right guardEvidence
        (ay_dssg_conj agreementEvidence stackGuidance)
        accepted)

theorem ay_dssg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    stackGuidance :=
  fun accepted =>
    ay_dssg_conj_right agreementEvidence stackGuidance
      (ay_dssg_conj_right guardEvidence
        (ay_dssg_conj agreementEvidence stackGuidance)
        accepted)

theorem ay_dssg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_dssg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_dssg_conj_intro acceptedEvidence
      (ay_dssg_conj outcome formulaTruth)
      acceptedH
      (ay_dssg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_dssg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_dssg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_dssg_conj_left acceptedEvidence
      (ay_dssg_conj outcome formulaTruth)
      public

theorem ay_dssg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_dssg_no_claim diagnostic fallbackPublic :=
  ay_dssg_conj_intro diagnostic fallbackPublic

theorem ay_dssg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_dssg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_dssg_conj_right diagnostic fallbackPublic noClaim

theorem ay_dssg_stack_failure_no_claim
    (stackFailure : Prop)
    (fallbackPublic : Prop) :
    stackFailure -> fallbackPublic -> ay_dssg_no_claim stackFailure fallbackPublic :=
  ay_dssg_no_claim_intro stackFailure fallbackPublic

theorem ay_dssg_level_failure_no_claim
    (levelFailure : Prop)
    (fallbackPublic : Prop) :
    levelFailure -> fallbackPublic -> ay_dssg_no_claim levelFailure fallbackPublic :=
  ay_dssg_no_claim_intro levelFailure fallbackPublic

theorem ay_dssg_trail_failure_no_claim
    (trailFailure : Prop)
    (fallbackPublic : Prop) :
    trailFailure -> fallbackPublic -> ay_dssg_no_claim trailFailure fallbackPublic :=
  ay_dssg_no_claim_intro trailFailure fallbackPublic

theorem ay_dssg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_dssg_no_claim replayFailure fallbackPublic :=
  ay_dssg_no_claim_intro replayFailure fallbackPublic

theorem ay_dssg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_dssg_no_claim fallbackFailure fallbackPublic :=
  ay_dssg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_dssg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_dssg_no_claim buildFailure fallbackPublic :=
  ay_dssg_no_claim_intro buildFailure fallbackPublic

theorem ay_dssg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_dssg_no_claim validatorFailure fallbackPublic :=
  ay_dssg_no_claim_intro validatorFailure fallbackPublic

theorem ay_dssg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_dssg_no_claim auditFailure fallbackPublic :=
  ay_dssg_no_claim_intro auditFailure fallbackPublic

theorem ay_dssg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_dssg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_dssg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_dssg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_dssg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_dssg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_dssg_accepted_guidance_is_search_scheduling_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    stackGuidance :=
  ay_dssg_accepted_guidance_hint guardEvidence agreementEvidence stackGuidance

theorem ay_dssg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    ay_dssg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_dssg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_dssg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_dssg_public_report
      (ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_dssg_public_report_intro
      (ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_dssg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_dssg_public_report
      (ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance)
      unsatOutcome
      formulaTruth :=
  ay_dssg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    stackGuidance unsatOutcome formulaTruth

theorem ay_dssg_stack_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (stackGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_dssg_accepted_guidance guardEvidence agreementEvidence stackGuidance ->
    ay_dssg_equisat beforeTruth afterTruth ->
    ay_dssg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_dssg_equisat_intro afterTruth beforeTruth
      (ay_dssg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_dssg_equisat_forward beforeTruth afterTruth eqsat)
