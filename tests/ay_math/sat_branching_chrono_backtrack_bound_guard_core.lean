-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Chronological/backjump bound guard skeleton for sequential-main SAT. Backtrack
-- bound guidance is search scheduling only when conflict levels, targets,
-- trail snapshots, replay, fallback, build, validator, and audit evidence agree.

def ay_cbbg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cbbg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cbbg_conj (before -> after) (after -> before)

def ay_cbbg_guard
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictLevelLedger ->
      backtrackTargetDigest ->
      trailSnapshot ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cbbg_agreement
    (levelMatch : Prop)
    (targetMatch : Prop)
    (trailMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_cbbg_guard levelMatch targetMatch trailMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_cbbg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) : Prop :=
  ay_cbbg_conj guardEvidence
    (ay_cbbg_conj agreementEvidence backtrackGuidance)

def ay_cbbg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_cbbg_conj acceptedEvidence (ay_cbbg_conj outcome formulaTruth)

def ay_cbbg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_cbbg_conj diagnostic fallbackPublic

theorem ay_cbbg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_cbbg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cbbg_conj_left (left : Prop) (right : Prop) :
    ay_cbbg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cbbg_conj_right (left : Prop) (right : Prop) :
    ay_cbbg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cbbg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_cbbg_equisat before after :=
  fun forward backward =>
    ay_cbbg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cbbg_equisat_forward (before : Prop) (after : Prop) :
    ay_cbbg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cbbg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cbbg_equisat_backward (before : Prop) (after : Prop) :
    ay_cbbg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cbbg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cbbg_guard_intro
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    conflictLevelLedger ->
    backtrackTargetDigest ->
    trailSnapshot ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun levelH targetH trailH replayH fallbackH buildH validatorH auditH
      result build =>
    build levelH targetH trailH replayH fallbackH buildH validatorH auditH

theorem ay_cbbg_guard_level
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    conflictLevelLedger :=
  fun guard =>
    guard conflictLevelLedger
      (fun levelH _targetH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_cbbg_guard_target
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    backtrackTargetDigest :=
  fun guard =>
    guard backtrackTargetDigest
      (fun _levelH targetH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => targetH)

theorem ay_cbbg_guard_trail
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    trailSnapshot :=
  fun guard =>
    guard trailSnapshot
      (fun _levelH _targetH trailH _replayH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_cbbg_guard_replay
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _levelH _targetH _trailH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_cbbg_guard_fallback
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _levelH _targetH _trailH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_cbbg_guard_build
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _levelH _targetH _trailH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_cbbg_guard_validator
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _levelH _targetH _trailH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_cbbg_guard_audit
    (conflictLevelLedger : Prop)
    (backtrackTargetDigest : Prop)
    (trailSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbbg_guard conflictLevelLedger backtrackTargetDigest trailSnapshot
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _levelH _targetH _trailH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_cbbg_agreement_intro
    (levelMatch : Prop)
    (targetMatch : Prop)
    (trailMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    levelMatch ->
    targetMatch ->
    trailMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_cbbg_agreement levelMatch targetMatch trailMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_cbbg_guard_intro levelMatch targetMatch trailMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_cbbg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    backtrackGuidance ->
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance :=
  fun guardH agreementH guidanceH =>
    ay_cbbg_conj_intro guardEvidence
      (ay_cbbg_conj agreementEvidence backtrackGuidance)
      guardH
      (ay_cbbg_conj_intro agreementEvidence backtrackGuidance
        agreementH guidanceH)

theorem ay_cbbg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_cbbg_conj_left guardEvidence
      (ay_cbbg_conj agreementEvidence backtrackGuidance)
      accepted

theorem ay_cbbg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_cbbg_conj_left agreementEvidence backtrackGuidance
      (ay_cbbg_conj_right guardEvidence
        (ay_cbbg_conj agreementEvidence backtrackGuidance)
        accepted)

theorem ay_cbbg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    backtrackGuidance :=
  fun accepted =>
    ay_cbbg_conj_right agreementEvidence backtrackGuidance
      (ay_cbbg_conj_right guardEvidence
        (ay_cbbg_conj agreementEvidence backtrackGuidance)
        accepted)

theorem ay_cbbg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cbbg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cbbg_conj_intro acceptedEvidence
      (ay_cbbg_conj outcome formulaTruth)
      acceptedH
      (ay_cbbg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cbbg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_cbbg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_cbbg_conj_left acceptedEvidence
      (ay_cbbg_conj outcome formulaTruth)
      public

theorem ay_cbbg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_cbbg_no_claim diagnostic fallbackPublic :=
  ay_cbbg_conj_intro diagnostic fallbackPublic

theorem ay_cbbg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_cbbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_cbbg_conj_right diagnostic fallbackPublic noClaim

theorem ay_cbbg_level_failure_no_claim
    (levelFailure : Prop)
    (fallbackPublic : Prop) :
    levelFailure -> fallbackPublic -> ay_cbbg_no_claim levelFailure fallbackPublic :=
  ay_cbbg_no_claim_intro levelFailure fallbackPublic

theorem ay_cbbg_target_failure_no_claim
    (targetFailure : Prop)
    (fallbackPublic : Prop) :
    targetFailure ->
    fallbackPublic ->
    ay_cbbg_no_claim targetFailure fallbackPublic :=
  ay_cbbg_no_claim_intro targetFailure fallbackPublic

theorem ay_cbbg_trail_failure_no_claim
    (trailFailure : Prop)
    (fallbackPublic : Prop) :
    trailFailure -> fallbackPublic -> ay_cbbg_no_claim trailFailure fallbackPublic :=
  ay_cbbg_no_claim_intro trailFailure fallbackPublic

theorem ay_cbbg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_cbbg_no_claim replayFailure fallbackPublic :=
  ay_cbbg_no_claim_intro replayFailure fallbackPublic

theorem ay_cbbg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_cbbg_no_claim fallbackFailure fallbackPublic :=
  ay_cbbg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_cbbg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_cbbg_no_claim buildFailure fallbackPublic :=
  ay_cbbg_no_claim_intro buildFailure fallbackPublic

theorem ay_cbbg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_cbbg_no_claim validatorFailure fallbackPublic :=
  ay_cbbg_no_claim_intro validatorFailure fallbackPublic

theorem ay_cbbg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_cbbg_no_claim auditFailure fallbackPublic :=
  ay_cbbg_no_claim_intro auditFailure fallbackPublic

theorem ay_cbbg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_cbbg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_cbbg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_cbbg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_cbbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_cbbg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_cbbg_accepted_guidance_is_search_scheduling_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    backtrackGuidance :=
  ay_cbbg_accepted_guidance_hint guardEvidence agreementEvidence
    backtrackGuidance

theorem ay_cbbg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    ay_cbbg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_cbbg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_cbbg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_cbbg_public_report
      (ay_cbbg_accepted_guidance guardEvidence agreementEvidence
        backtrackGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_cbbg_public_report_intro
      (ay_cbbg_accepted_guidance guardEvidence agreementEvidence
        backtrackGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_cbbg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_cbbg_public_report
      (ay_cbbg_accepted_guidance guardEvidence agreementEvidence
        backtrackGuidance)
      unsatOutcome
      formulaTruth :=
  ay_cbbg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    backtrackGuidance unsatOutcome formulaTruth

theorem ay_cbbg_backtrack_bound_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_cbbg_accepted_guidance guardEvidence agreementEvidence
      backtrackGuidance ->
    ay_cbbg_equisat beforeTruth afterTruth ->
    ay_cbbg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_cbbg_equisat_intro afterTruth beforeTruth
      (ay_cbbg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_cbbg_equisat_forward beforeTruth afterTruth eqsat)
