-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Luby restart budget replay guard soundness skeleton for sequential-main SAT.
-- The schedule is modeled as heuristic guidance: public SAT/UNSAT publication
-- remains tied to validator, audit, fallback, build, and replay evidence.

def ay_blrb_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_blrb_equisat (before : Prop) (after : Prop) : Prop :=
  ay_blrb_conj (before -> after) (after -> before)

def ay_blrb_replay_guard
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (restartBudget ->
      lubyEpoch ->
      phaseCompatible ->
      activityRankingReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_blrb_guard_agreement
    (budgetMatch : Prop)
    (epochMatch : Prop)
    (phaseMatch : Prop)
    (rankingMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_blrb_replay_guard budgetMatch epochMatch phaseMatch rankingMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_blrb_accepted_schedule
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop) : Prop :=
  ay_blrb_conj guardEvidence (ay_blrb_conj agreementEvidence scheduleHint)

def ay_blrb_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_blrb_conj acceptedEvidence (ay_blrb_conj outcome formulaTruth)

def ay_blrb_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_blrb_conj diagnostic fallbackPublic

theorem ay_blrb_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_blrb_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_blrb_conj_left (left : Prop) (right : Prop) :
    ay_blrb_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_blrb_conj_right (left : Prop) (right : Prop) :
    ay_blrb_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_blrb_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_blrb_equisat before after :=
  fun forward backward =>
    ay_blrb_conj_intro (before -> after) (after -> before) forward backward

theorem ay_blrb_equisat_forward (before : Prop) (after : Prop) :
    ay_blrb_equisat before after -> before -> after :=
  fun eqsat =>
    ay_blrb_conj_left (before -> after) (after -> before) eqsat

theorem ay_blrb_equisat_backward (before : Prop) (after : Prop) :
    ay_blrb_equisat before after -> after -> before :=
  fun eqsat =>
    ay_blrb_conj_right (before -> after) (after -> before) eqsat

theorem ay_blrb_replay_guard_intro
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    restartBudget ->
    lubyEpoch ->
    phaseCompatible ->
    activityRankingReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence :=
  fun budgetH epochH phaseH rankingH fallbackH buildH validatorH auditH
      result build =>
    build budgetH epochH phaseH rankingH fallbackH buildH validatorH auditH

theorem ay_blrb_replay_guard_budget
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    restartBudget :=
  fun guard =>
    guard restartBudget
      (fun budgetH _epochH _phaseH _rankingH _fallbackH _buildH
          _validatorH _auditH => budgetH)

theorem ay_blrb_replay_guard_epoch
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    lubyEpoch :=
  fun guard =>
    guard lubyEpoch
      (fun _budgetH epochH _phaseH _rankingH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_blrb_replay_guard_phase
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    phaseCompatible :=
  fun guard =>
    guard phaseCompatible
      (fun _budgetH _epochH phaseH _rankingH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_blrb_replay_guard_ranking
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    activityRankingReplay :=
  fun guard =>
    guard activityRankingReplay
      (fun _budgetH _epochH _phaseH rankingH _fallbackH _buildH
          _validatorH _auditH => rankingH)

theorem ay_blrb_replay_guard_fallback
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _budgetH _epochH _phaseH _rankingH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_blrb_replay_guard_build
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _budgetH _epochH _phaseH _rankingH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_blrb_replay_guard_validator
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _budgetH _epochH _phaseH _rankingH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_blrb_replay_guard_audit
    (restartBudget : Prop)
    (lubyEpoch : Prop)
    (phaseCompatible : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_blrb_replay_guard restartBudget lubyEpoch phaseCompatible
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _budgetH _epochH _phaseH _rankingH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_blrb_guard_agreement_intro
    (budgetMatch : Prop)
    (epochMatch : Prop)
    (phaseMatch : Prop)
    (rankingMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    budgetMatch ->
    epochMatch ->
    phaseMatch ->
    rankingMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_blrb_guard_agreement budgetMatch epochMatch phaseMatch rankingMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_blrb_replay_guard_intro budgetMatch epochMatch phaseMatch rankingMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_blrb_accepted_schedule_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    scheduleHint ->
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint :=
  fun guardH agreementH hintH =>
    ay_blrb_conj_intro guardEvidence
      (ay_blrb_conj agreementEvidence scheduleHint)
      guardH
      (ay_blrb_conj_intro agreementEvidence scheduleHint agreementH hintH)

theorem ay_blrb_accepted_schedule_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    guardEvidence :=
  fun accepted =>
    ay_blrb_conj_left guardEvidence
      (ay_blrb_conj agreementEvidence scheduleHint)
      accepted

theorem ay_blrb_accepted_schedule_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    agreementEvidence :=
  fun accepted =>
    ay_blrb_conj_left agreementEvidence scheduleHint
      (ay_blrb_conj_right guardEvidence
        (ay_blrb_conj agreementEvidence scheduleHint)
        accepted)

theorem ay_blrb_accepted_schedule_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    scheduleHint :=
  fun accepted =>
    ay_blrb_conj_right agreementEvidence scheduleHint
      (ay_blrb_conj_right guardEvidence
        (ay_blrb_conj agreementEvidence scheduleHint)
        accepted)

theorem ay_blrb_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_blrb_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_blrb_conj_intro acceptedEvidence
      (ay_blrb_conj outcome formulaTruth)
      acceptedH
      (ay_blrb_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_blrb_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_blrb_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_blrb_conj_left acceptedEvidence
      (ay_blrb_conj outcome formulaTruth)
      public

theorem ay_blrb_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_blrb_no_claim diagnostic fallbackPublic :=
  ay_blrb_conj_intro diagnostic fallbackPublic

theorem ay_blrb_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_blrb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_blrb_conj_right diagnostic fallbackPublic noClaim

theorem ay_blrb_budget_drift_no_claim
    (budgetDrift : Prop)
    (fallbackPublic : Prop) :
    budgetDrift -> fallbackPublic -> ay_blrb_no_claim budgetDrift fallbackPublic :=
  ay_blrb_no_claim_intro budgetDrift fallbackPublic

theorem ay_blrb_epoch_mismatch_no_claim
    (epochMismatch : Prop)
    (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    ay_blrb_no_claim epochMismatch fallbackPublic :=
  ay_blrb_no_claim_intro epochMismatch fallbackPublic

theorem ay_blrb_phase_cache_mismatch_no_claim
    (phaseCacheMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseCacheMismatch ->
    fallbackPublic ->
    ay_blrb_no_claim phaseCacheMismatch fallbackPublic :=
  ay_blrb_no_claim_intro phaseCacheMismatch fallbackPublic

theorem ay_blrb_ranking_replay_failure_no_claim
    (rankingReplayFailure : Prop)
    (fallbackPublic : Prop) :
    rankingReplayFailure ->
    fallbackPublic ->
    ay_blrb_no_claim rankingReplayFailure fallbackPublic :=
  ay_blrb_no_claim_intro rankingReplayFailure fallbackPublic

theorem ay_blrb_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_blrb_no_claim staleBuild fallbackPublic :=
  ay_blrb_no_claim_intro staleBuild fallbackPublic

theorem ay_blrb_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_blrb_no_claim auditContradiction fallbackPublic :=
  ay_blrb_no_claim_intro auditContradiction fallbackPublic

theorem ay_blrb_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_blrb_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_blrb_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_blrb_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_blrb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_blrb_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_blrb_accepted_schedule_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    satOutcome ->
    formulaTruth ->
    ay_blrb_public_report
      (ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_blrb_public_report_intro
      (ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_blrb_accepted_schedule_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    unsatOutcome ->
    formulaTruth ->
    ay_blrb_public_report
      (ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint)
      unsatOutcome
      formulaTruth :=
  ay_blrb_accepted_schedule_guides_sat guardEvidence agreementEvidence
    scheduleHint unsatOutcome formulaTruth

theorem ay_blrb_accepted_schedule_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    ay_blrb_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_blrb_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_blrb_luby_schedule_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scheduleHint : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_blrb_accepted_schedule guardEvidence agreementEvidence scheduleHint ->
    ay_blrb_equisat beforeTruth afterTruth ->
    ay_blrb_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_blrb_equisat_intro afterTruth beforeTruth
      (ay_blrb_equisat_backward beforeTruth afterTruth eqsat)
      (ay_blrb_equisat_forward beforeTruth afterTruth eqsat)
