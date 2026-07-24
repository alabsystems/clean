-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Conflict-budget cutoff guard skeleton for sequential-main SAT-COMP branching
-- and restart control. Cutoff decisions are search-control only when budget,
-- counter, checkpoint, replay, fallback, build, validator, and audit evidence
-- agree with the checked public result.

def ay_cbcg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cbcg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cbcg_conj (before -> after) (after -> before)

def ay_cbcg_guard
    (conflictBudgetManifest : Prop)
    (counterEpochLedger : Prop)
    (decisionStackCheckpoint : Prop)
    (propagationReplay : Prop)
    (fallbackBaselinePolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictBudgetManifest ->
      counterEpochLedger ->
      decisionStackCheckpoint ->
      propagationReplay ->
      fallbackBaselinePolicy ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cbcg_agreement
    (budgetMatch : Prop)
    (counterMatch : Prop)
    (checkpointMatch : Prop)
    (replayMatch : Prop)
    (fallbackPolicyMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_cbcg_guard budgetMatch counterMatch checkpointMatch replayMatch
    fallbackPolicyMatch buildMatch validatorAccepts auditMatch

def ay_cbcg_accepted_cutoff
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_cbcg_conj guardEvidence
    (ay_cbcg_conj agreementEvidence searchControlHint)

def ay_cbcg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_cbcg_conj acceptedEvidence (ay_cbcg_conj outcome formulaTruth)

def ay_cbcg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_cbcg_conj diagnostic fallbackPublic

theorem ay_cbcg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_cbcg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cbcg_conj_left (left : Prop) (right : Prop) :
    ay_cbcg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cbcg_conj_right (left : Prop) (right : Prop) :
    ay_cbcg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cbcg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_cbcg_equisat before after :=
  fun forward backward =>
    ay_cbcg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cbcg_equisat_forward (before : Prop) (after : Prop) :
    ay_cbcg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cbcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cbcg_equisat_backward (before : Prop) (after : Prop) :
    ay_cbcg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cbcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cbcg_guard_intro
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    conflictBudgetManifest ->
    counterEpochLedger ->
    decisionStackCheckpoint ->
    propagationReplay ->
    fallbackBaselinePolicy ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript :=
  fun budgetH counterH checkpointH replayH fallbackH buildH validatorH auditH
      result make =>
    make budgetH counterH checkpointH replayH fallbackH buildH validatorH
      auditH

theorem ay_cbcg_guard_budget
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    conflictBudgetManifest :=
  fun guard =>
    guard conflictBudgetManifest
      (fun budgetH _counterH _checkpointH _replayH _fallbackH _buildH
          _validatorH _auditH => budgetH)

theorem ay_cbcg_guard_counter
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    counterEpochLedger :=
  fun guard =>
    guard counterEpochLedger
      (fun _budgetH counterH _checkpointH _replayH _fallbackH _buildH
          _validatorH _auditH => counterH)

theorem ay_cbcg_guard_checkpoint
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    decisionStackCheckpoint :=
  fun guard =>
    guard decisionStackCheckpoint
      (fun _budgetH _counterH checkpointH _replayH _fallbackH _buildH
          _validatorH _auditH => checkpointH)

theorem ay_cbcg_guard_replay
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _budgetH _counterH _checkpointH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_cbcg_guard_fallback
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    fallbackBaselinePolicy :=
  fun guard =>
    guard fallbackBaselinePolicy
      (fun _budgetH _counterH _checkpointH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_cbcg_guard_build
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _budgetH _counterH _checkpointH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_cbcg_guard_validator
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _budgetH _counterH _checkpointH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_cbcg_guard_audit
    (conflictBudgetManifest counterEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaselinePolicy buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cbcg_guard conflictBudgetManifest counterEpochLedger
      decisionStackCheckpoint propagationReplay fallbackBaselinePolicy
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _budgetH _counterH _checkpointH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_cbcg_agreement_intro
    (budgetMatch counterMatch checkpointMatch replayMatch fallbackPolicyMatch
      buildMatch validatorAccepts auditMatch : Prop) :
    budgetMatch ->
    counterMatch ->
    checkpointMatch ->
    replayMatch ->
    fallbackPolicyMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_cbcg_agreement budgetMatch counterMatch checkpointMatch replayMatch
      fallbackPolicyMatch buildMatch validatorAccepts auditMatch :=
  ay_cbcg_guard_intro budgetMatch counterMatch checkpointMatch replayMatch
    fallbackPolicyMatch buildMatch validatorAccepts auditMatch

theorem ay_cbcg_accepted_cutoff_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_cbcg_conj_intro guardEvidence
      (ay_cbcg_conj agreementEvidence searchControlHint)
      guardH
      (ay_cbcg_conj_intro agreementEvidence searchControlHint agreementH
        hintH)

theorem ay_cbcg_accepted_cutoff_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_cbcg_conj_left guardEvidence
      (ay_cbcg_conj agreementEvidence searchControlHint) accepted

theorem ay_cbcg_accepted_cutoff_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_cbcg_conj_left agreementEvidence searchControlHint
      (ay_cbcg_conj_right guardEvidence
        (ay_cbcg_conj agreementEvidence searchControlHint) accepted)

theorem ay_cbcg_accepted_cutoff_hint
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_cbcg_conj_right agreementEvidence searchControlHint
      (ay_cbcg_conj_right guardEvidence
        (ay_cbcg_conj agreementEvidence searchControlHint) accepted)

theorem ay_cbcg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cbcg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cbcg_conj_intro acceptedEvidence
      (ay_cbcg_conj outcome formulaTruth)
      acceptedH (ay_cbcg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cbcg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cbcg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_cbcg_conj_left acceptedEvidence (ay_cbcg_conj outcome formulaTruth)
      report

theorem ay_cbcg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cbcg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_cbcg_conj_right outcome formulaTruth
      (ay_cbcg_conj_right acceptedEvidence
        (ay_cbcg_conj outcome formulaTruth) report)

theorem ay_cbcg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_cbcg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_cbcg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_cbcg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_cbcg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_cbcg_conj_right diagnostic fallbackPublic noClaim

theorem ay_cbcg_budget_mismatch_no_claim
    (budgetMismatch fallbackPublic : Prop) :
    budgetMismatch -> fallbackPublic ->
    ay_cbcg_no_claim budgetMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro budgetMismatch fallbackPublic

theorem ay_cbcg_counter_mismatch_no_claim
    (counterMismatch fallbackPublic : Prop) :
    counterMismatch -> fallbackPublic ->
    ay_cbcg_no_claim counterMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro counterMismatch fallbackPublic

theorem ay_cbcg_checkpoint_mismatch_no_claim
    (checkpointMismatch fallbackPublic : Prop) :
    checkpointMismatch -> fallbackPublic ->
    ay_cbcg_no_claim checkpointMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro checkpointMismatch fallbackPublic

theorem ay_cbcg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_cbcg_no_claim replayMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro replayMismatch fallbackPublic

theorem ay_cbcg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_cbcg_no_claim buildMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro buildMismatch fallbackPublic

theorem ay_cbcg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_cbcg_no_claim validatorRejection fallbackPublic :=
  ay_cbcg_no_claim_intro validatorRejection fallbackPublic

theorem ay_cbcg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_cbcg_no_claim auditMismatch fallbackPublic :=
  ay_cbcg_no_claim_intro auditMismatch fallbackPublic

theorem ay_cbcg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_cbcg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_cbcg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_cbcg_failed_cutoff_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_cbcg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_cbcg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_cbcg_accepted_cutoff_is_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  ay_cbcg_accepted_cutoff_hint guardEvidence agreementEvidence
    searchControlHint

theorem ay_cbcg_accepted_cutoff_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth
      publicSound : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_cbcg_accepted_cutoff_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      (ay_cbcg_accepted_cutoff_agreement guardEvidence agreementEvidence
        searchControlHint accepted)
      outcomeH
      truthH

theorem ay_cbcg_accepted_cutoff_guides_sat
    (guardEvidence agreementEvidence searchControlHint satOutcome
      satTruth : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_cbcg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_cbcg_public_report_intro guardEvidence satOutcome satTruth
      (ay_cbcg_accepted_cutoff_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      satH
      truthH

theorem ay_cbcg_accepted_cutoff_guides_unsat
    (guardEvidence agreementEvidence searchControlHint unsatOutcome
      unsatTruth : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_cbcg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_cbcg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_cbcg_accepted_cutoff_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      unsatH
      truthH

theorem ay_cbcg_budget_cutoff_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      searchControlHint : Prop) :
    ay_cbcg_accepted_cutoff guardEvidence agreementEvidence
      searchControlHint ->
    (searchControlHint -> formulaBefore -> formulaAfter) ->
    (searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_cbcg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_cbcg_equisat_intro formulaBefore formulaAfter
      (forward (ay_cbcg_accepted_cutoff_hint guardEvidence agreementEvidence
        searchControlHint accepted))
      (backward (ay_cbcg_accepted_cutoff_hint guardEvidence agreementEvidence
        searchControlHint accepted))
