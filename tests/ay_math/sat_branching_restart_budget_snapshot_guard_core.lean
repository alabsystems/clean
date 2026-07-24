-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart-budget snapshot guard skeleton for sequential-main SAT. Restoring a
-- restart budget snapshot is admissible performance-control reuse only when
-- budget ledgers, restart epochs, phase/trail state, activity replay, fallback,
-- build, validator, and audit evidence agree.

def ay_brsb_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brsb_equisat (before : Prop) (after : Prop) : Prop :=
  ay_brsb_conj (before -> after) (after -> before)

def ay_brsb_snapshot_guard
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (budgetLedgers ->
      restartEpochs ->
      phaseTrailState ->
      activityReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_brsb_guard_agreement
    (budgetMatch : Prop)
    (epochMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_brsb_snapshot_guard budgetMatch epochMatch phaseTrailMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brsb_accepted_snapshot
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) : Prop :=
  ay_brsb_conj guardEvidence (ay_brsb_conj agreementEvidence budgetGuidance)

def ay_brsb_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_brsb_conj acceptedEvidence (ay_brsb_conj outcome formulaTruth)

def ay_brsb_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_brsb_conj diagnostic fallbackPublic

theorem ay_brsb_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_brsb_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_brsb_conj_left (left : Prop) (right : Prop) :
    ay_brsb_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_brsb_conj_right (left : Prop) (right : Prop) :
    ay_brsb_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_brsb_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_brsb_equisat before after :=
  fun forward backward =>
    ay_brsb_conj_intro (before -> after) (after -> before) forward backward

theorem ay_brsb_equisat_forward (before : Prop) (after : Prop) :
    ay_brsb_equisat before after -> before -> after :=
  fun eqsat =>
    ay_brsb_conj_left (before -> after) (after -> before) eqsat

theorem ay_brsb_equisat_backward (before : Prop) (after : Prop) :
    ay_brsb_equisat before after -> after -> before :=
  fun eqsat =>
    ay_brsb_conj_right (before -> after) (after -> before) eqsat

theorem ay_brsb_snapshot_guard_intro
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    budgetLedgers ->
    restartEpochs ->
    phaseTrailState ->
    activityReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun budgetH epochH phaseTrailH activityH fallbackH buildH validatorH auditH
      result build =>
    build budgetH epochH phaseTrailH activityH fallbackH buildH validatorH auditH

theorem ay_brsb_snapshot_guard_budget
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    budgetLedgers :=
  fun guard =>
    guard budgetLedgers
      (fun budgetH _epochH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => budgetH)

theorem ay_brsb_snapshot_guard_epoch
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    restartEpochs :=
  fun guard =>
    guard restartEpochs
      (fun _budgetH epochH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_brsb_snapshot_guard_phase_trail
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailState :=
  fun guard =>
    guard phaseTrailState
      (fun _budgetH _epochH phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_brsb_snapshot_guard_activity
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityReplay :=
  fun guard =>
    guard activityReplay
      (fun _budgetH _epochH _phaseTrailH activityH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_brsb_snapshot_guard_fallback
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _budgetH _epochH _phaseTrailH _activityH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brsb_snapshot_guard_build
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _budgetH _epochH _phaseTrailH _activityH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brsb_snapshot_guard_validator
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _budgetH _epochH _phaseTrailH _activityH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brsb_snapshot_guard_audit
    (budgetLedgers : Prop)
    (restartEpochs : Prop)
    (phaseTrailState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brsb_snapshot_guard budgetLedgers restartEpochs phaseTrailState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _budgetH _epochH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brsb_guard_agreement_intro
    (budgetMatch : Prop)
    (epochMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    budgetMatch ->
    epochMatch ->
    phaseTrailMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brsb_guard_agreement budgetMatch epochMatch phaseTrailMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_brsb_snapshot_guard_intro budgetMatch epochMatch phaseTrailMatch
    activityMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_brsb_accepted_snapshot_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    budgetGuidance ->
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance :=
  fun guardH agreementH guidanceH =>
    ay_brsb_conj_intro guardEvidence
      (ay_brsb_conj agreementEvidence budgetGuidance)
      guardH
      (ay_brsb_conj_intro agreementEvidence budgetGuidance agreementH guidanceH)

theorem ay_brsb_accepted_snapshot_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_brsb_conj_left guardEvidence
      (ay_brsb_conj agreementEvidence budgetGuidance)
      accepted

theorem ay_brsb_accepted_snapshot_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_brsb_conj_left agreementEvidence budgetGuidance
      (ay_brsb_conj_right guardEvidence
        (ay_brsb_conj agreementEvidence budgetGuidance)
        accepted)

theorem ay_brsb_accepted_snapshot_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    budgetGuidance :=
  fun accepted =>
    ay_brsb_conj_right agreementEvidence budgetGuidance
      (ay_brsb_conj_right guardEvidence
        (ay_brsb_conj agreementEvidence budgetGuidance)
        accepted)

theorem ay_brsb_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_brsb_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_brsb_conj_intro acceptedEvidence
      (ay_brsb_conj outcome formulaTruth)
      acceptedH
      (ay_brsb_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_brsb_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_brsb_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_brsb_conj_left acceptedEvidence
      (ay_brsb_conj outcome formulaTruth)
      public

theorem ay_brsb_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_brsb_no_claim diagnostic fallbackPublic :=
  ay_brsb_conj_intro diagnostic fallbackPublic

theorem ay_brsb_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brsb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_brsb_conj_right diagnostic fallbackPublic noClaim

theorem ay_brsb_budget_drift_no_claim
    (budgetDrift : Prop)
    (fallbackPublic : Prop) :
    budgetDrift -> fallbackPublic -> ay_brsb_no_claim budgetDrift fallbackPublic :=
  ay_brsb_no_claim_intro budgetDrift fallbackPublic

theorem ay_brsb_epoch_drift_no_claim
    (epochDrift : Prop)
    (fallbackPublic : Prop) :
    epochDrift -> fallbackPublic -> ay_brsb_no_claim epochDrift fallbackPublic :=
  ay_brsb_no_claim_intro epochDrift fallbackPublic

theorem ay_brsb_phase_trail_drift_no_claim
    (phaseTrailDrift : Prop)
    (fallbackPublic : Prop) :
    phaseTrailDrift ->
    fallbackPublic ->
    ay_brsb_no_claim phaseTrailDrift fallbackPublic :=
  ay_brsb_no_claim_intro phaseTrailDrift fallbackPublic

theorem ay_brsb_activity_replay_drift_no_claim
    (activityReplayDrift : Prop)
    (fallbackPublic : Prop) :
    activityReplayDrift ->
    fallbackPublic ->
    ay_brsb_no_claim activityReplayDrift fallbackPublic :=
  ay_brsb_no_claim_intro activityReplayDrift fallbackPublic

theorem ay_brsb_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_brsb_no_claim staleBuild fallbackPublic :=
  ay_brsb_no_claim_intro staleBuild fallbackPublic

theorem ay_brsb_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_brsb_no_claim validatorRejection fallbackPublic :=
  ay_brsb_no_claim_intro validatorRejection fallbackPublic

theorem ay_brsb_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brsb_no_claim auditContradiction fallbackPublic :=
  ay_brsb_no_claim_intro auditContradiction fallbackPublic

theorem ay_brsb_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_brsb_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_brsb_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_brsb_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brsb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_brsb_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_brsb_accepted_snapshot_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_brsb_public_report
      (ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_brsb_public_report_intro
      (ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_brsb_accepted_snapshot_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_brsb_public_report
      (ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance)
      unsatOutcome
      formulaTruth :=
  ay_brsb_accepted_snapshot_guides_sat guardEvidence agreementEvidence
    budgetGuidance unsatOutcome formulaTruth

theorem ay_brsb_accepted_snapshot_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    ay_brsb_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_brsb_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_brsb_budget_restore_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (budgetGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_brsb_accepted_snapshot guardEvidence agreementEvidence budgetGuidance ->
    ay_brsb_equisat beforeTruth afterTruth ->
    ay_brsb_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_brsb_equisat_intro afterTruth beforeTruth
      (ay_brsb_equisat_backward beforeTruth afterTruth eqsat)
      (ay_brsb_equisat_forward beforeTruth afterTruth eqsat)
