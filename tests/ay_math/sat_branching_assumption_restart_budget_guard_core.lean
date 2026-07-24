-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption-scoped restart budget guard skeleton for sequential-main SAT.
-- Restart budgets under assumptions are search hints only when assumption
-- frames, budget ledgers, counters, replay, fallback, build, validator, and
-- audit evidence agree.

def ay_arbg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_arbg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_arbg_conj (before -> after) (after -> before)

def ay_arbg_guard
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionFrameManifest ->
      restartBudgetLedger ->
      conflictCounterDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_arbg_agreement
    (frameMatch : Prop)
    (budgetMatch : Prop)
    (counterMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_arbg_guard frameMatch budgetMatch counterMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_arbg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) : Prop :=
  ay_arbg_conj guardEvidence (ay_arbg_conj agreementEvidence budgetGuidance)

def ay_arbg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_arbg_conj acceptedEvidence (ay_arbg_conj outcome formulaTruth)

def ay_arbg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_arbg_conj diagnostic fallbackPublic

theorem ay_arbg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_arbg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_arbg_conj_left (left : Prop) (right : Prop) :
    ay_arbg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_arbg_conj_right (left : Prop) (right : Prop) :
    ay_arbg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_arbg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_arbg_equisat before after :=
  fun forward backward =>
    ay_arbg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_arbg_equisat_forward (before : Prop) (after : Prop) :
    ay_arbg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_arbg_conj_left (before -> after) (after -> before) eqsat

theorem ay_arbg_equisat_backward (before : Prop) (after : Prop) :
    ay_arbg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_arbg_conj_right (before -> after) (after -> before) eqsat

theorem ay_arbg_guard_intro
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    assumptionFrameManifest ->
    restartBudgetLedger ->
    conflictCounterDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun frameH budgetH counterH replayH fallbackH buildH validatorH auditH
      result build =>
    build frameH budgetH counterH replayH fallbackH buildH validatorH auditH

theorem ay_arbg_guard_frame
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    assumptionFrameManifest :=
  fun guard =>
    guard assumptionFrameManifest
      (fun frameH _budgetH _counterH _replayH _fallbackH _buildH
          _validatorH _auditH => frameH)

theorem ay_arbg_guard_budget
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    restartBudgetLedger :=
  fun guard =>
    guard restartBudgetLedger
      (fun _frameH budgetH _counterH _replayH _fallbackH _buildH
          _validatorH _auditH => budgetH)

theorem ay_arbg_guard_counter
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    conflictCounterDigest :=
  fun guard =>
    guard conflictCounterDigest
      (fun _frameH _budgetH counterH _replayH _fallbackH _buildH
          _validatorH _auditH => counterH)

theorem ay_arbg_guard_replay
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _frameH _budgetH _counterH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_arbg_guard_fallback
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _frameH _budgetH _counterH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_arbg_guard_build
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _frameH _budgetH _counterH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_arbg_guard_validator
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _frameH _budgetH _counterH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_arbg_guard_audit
    (assumptionFrameManifest : Prop)
    (restartBudgetLedger : Prop)
    (conflictCounterDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_arbg_guard assumptionFrameManifest restartBudgetLedger
      conflictCounterDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _frameH _budgetH _counterH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_arbg_agreement_intro
    (frameMatch : Prop)
    (budgetMatch : Prop)
    (counterMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    frameMatch ->
    budgetMatch ->
    counterMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_arbg_agreement frameMatch budgetMatch counterMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_arbg_guard_intro frameMatch budgetMatch counterMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_arbg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    budgetGuidance ->
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance :=
  fun guardH agreementH guidanceH =>
    ay_arbg_conj_intro guardEvidence
      (ay_arbg_conj agreementEvidence budgetGuidance)
      guardH
      (ay_arbg_conj_intro agreementEvidence budgetGuidance agreementH guidanceH)

theorem ay_arbg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_arbg_conj_left guardEvidence
      (ay_arbg_conj agreementEvidence budgetGuidance)
      accepted

theorem ay_arbg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_arbg_conj_left agreementEvidence budgetGuidance
      (ay_arbg_conj_right guardEvidence
        (ay_arbg_conj agreementEvidence budgetGuidance)
        accepted)

theorem ay_arbg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    budgetGuidance :=
  fun accepted =>
    ay_arbg_conj_right agreementEvidence budgetGuidance
      (ay_arbg_conj_right guardEvidence
        (ay_arbg_conj agreementEvidence budgetGuidance)
        accepted)

theorem ay_arbg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_arbg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_arbg_conj_intro acceptedEvidence
      (ay_arbg_conj outcome formulaTruth)
      acceptedH
      (ay_arbg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_arbg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_arbg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_arbg_conj_left acceptedEvidence
      (ay_arbg_conj outcome formulaTruth)
      public

theorem ay_arbg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_arbg_no_claim diagnostic fallbackPublic :=
  ay_arbg_conj_intro diagnostic fallbackPublic

theorem ay_arbg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_arbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_arbg_conj_right diagnostic fallbackPublic noClaim

theorem ay_arbg_frame_failure_no_claim
    (frameFailure : Prop)
    (fallbackPublic : Prop) :
    frameFailure -> fallbackPublic -> ay_arbg_no_claim frameFailure fallbackPublic :=
  ay_arbg_no_claim_intro frameFailure fallbackPublic

theorem ay_arbg_budget_failure_no_claim
    (budgetFailure : Prop)
    (fallbackPublic : Prop) :
    budgetFailure ->
    fallbackPublic ->
    ay_arbg_no_claim budgetFailure fallbackPublic :=
  ay_arbg_no_claim_intro budgetFailure fallbackPublic

theorem ay_arbg_counter_failure_no_claim
    (counterFailure : Prop)
    (fallbackPublic : Prop) :
    counterFailure ->
    fallbackPublic ->
    ay_arbg_no_claim counterFailure fallbackPublic :=
  ay_arbg_no_claim_intro counterFailure fallbackPublic

theorem ay_arbg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_arbg_no_claim replayFailure fallbackPublic :=
  ay_arbg_no_claim_intro replayFailure fallbackPublic

theorem ay_arbg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_arbg_no_claim fallbackFailure fallbackPublic :=
  ay_arbg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_arbg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_arbg_no_claim buildFailure fallbackPublic :=
  ay_arbg_no_claim_intro buildFailure fallbackPublic

theorem ay_arbg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_arbg_no_claim validatorFailure fallbackPublic :=
  ay_arbg_no_claim_intro validatorFailure fallbackPublic

theorem ay_arbg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_arbg_no_claim auditFailure fallbackPublic :=
  ay_arbg_no_claim_intro auditFailure fallbackPublic

theorem ay_arbg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_arbg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_arbg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_arbg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_arbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_arbg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_arbg_accepted_guidance_is_assumption_search_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    budgetGuidance :=
  ay_arbg_accepted_guidance_hint guardEvidence agreementEvidence budgetGuidance

theorem ay_arbg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    ay_arbg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_arbg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_arbg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_arbg_public_report
      (ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_arbg_public_report_intro
      (ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_arbg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_arbg_public_report
      (ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance)
      unsatOutcome
      formulaTruth :=
  ay_arbg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    budgetGuidance unsatOutcome formulaTruth

theorem ay_arbg_budget_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_arbg_accepted_guidance guardEvidence agreementEvidence budgetGuidance ->
    ay_arbg_equisat beforeTruth afterTruth ->
    ay_arbg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_arbg_equisat_intro afterTruth beforeTruth
      (ay_arbg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_arbg_equisat_forward beforeTruth afterTruth eqsat)
