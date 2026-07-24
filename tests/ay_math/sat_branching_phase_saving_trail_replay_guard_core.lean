-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-saving trail replay guard skeleton for sequential-main SAT. Reused
-- phase state is admissible branching guidance only when trail snapshots,
-- decision levels, activity replay, fallback, build, validator, and audit
-- evidence agree.

def ay_bpst_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpst_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bpst_conj (before -> after) (after -> before)

def ay_bpst_replay_guard
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (phaseTrailState ->
      assignmentTrailSnapshot ->
      decisionLevels ->
      activityReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bpst_guard_agreement
    (phaseMatch : Prop)
    (trailMatch : Prop)
    (levelMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bpst_replay_guard phaseMatch trailMatch levelMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bpst_accepted_phase_reuse
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) : Prop :=
  ay_bpst_conj guardEvidence (ay_bpst_conj agreementEvidence phaseGuidance)

def ay_bpst_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bpst_conj acceptedEvidence (ay_bpst_conj outcome formulaTruth)

def ay_bpst_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bpst_conj diagnostic fallbackPublic

theorem ay_bpst_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bpst_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bpst_conj_left (left : Prop) (right : Prop) :
    ay_bpst_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bpst_conj_right (left : Prop) (right : Prop) :
    ay_bpst_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bpst_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bpst_equisat before after :=
  fun forward backward =>
    ay_bpst_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bpst_equisat_forward (before : Prop) (after : Prop) :
    ay_bpst_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bpst_conj_left (before -> after) (after -> before) eqsat

theorem ay_bpst_equisat_backward (before : Prop) (after : Prop) :
    ay_bpst_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bpst_conj_right (before -> after) (after -> before) eqsat

theorem ay_bpst_replay_guard_intro
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    phaseTrailState ->
    assignmentTrailSnapshot ->
    decisionLevels ->
    activityReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun phaseH trailH levelH activityH fallbackH buildH validatorH auditH
      result build =>
    build phaseH trailH levelH activityH fallbackH buildH validatorH auditH

theorem ay_bpst_replay_guard_phase
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailState :=
  fun guard =>
    guard phaseTrailState
      (fun phaseH _trailH _levelH _activityH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_bpst_replay_guard_trail
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    assignmentTrailSnapshot :=
  fun guard =>
    guard assignmentTrailSnapshot
      (fun _phaseH trailH _levelH _activityH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_bpst_replay_guard_levels
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    decisionLevels :=
  fun guard =>
    guard decisionLevels
      (fun _phaseH _trailH levelH _activityH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bpst_replay_guard_activity
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityReplay :=
  fun guard =>
    guard activityReplay
      (fun _phaseH _trailH _levelH activityH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bpst_replay_guard_fallback
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _phaseH _trailH _levelH _activityH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bpst_replay_guard_build
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _phaseH _trailH _levelH _activityH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bpst_replay_guard_validator
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _phaseH _trailH _levelH _activityH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bpst_replay_guard_audit
    (phaseTrailState : Prop)
    (assignmentTrailSnapshot : Prop)
    (decisionLevels : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpst_replay_guard phaseTrailState assignmentTrailSnapshot decisionLevels
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _phaseH _trailH _levelH _activityH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bpst_guard_agreement_intro
    (phaseMatch : Prop)
    (trailMatch : Prop)
    (levelMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    phaseMatch ->
    trailMatch ->
    levelMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bpst_guard_agreement phaseMatch trailMatch levelMatch activityMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bpst_replay_guard_intro phaseMatch trailMatch levelMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bpst_accepted_phase_reuse_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    phaseGuidance ->
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bpst_conj_intro guardEvidence
      (ay_bpst_conj agreementEvidence phaseGuidance)
      guardH
      (ay_bpst_conj_intro agreementEvidence phaseGuidance
        agreementH guidanceH)

theorem ay_bpst_accepted_phase_reuse_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bpst_conj_left guardEvidence
      (ay_bpst_conj agreementEvidence phaseGuidance)
      accepted

theorem ay_bpst_accepted_phase_reuse_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bpst_conj_left agreementEvidence phaseGuidance
      (ay_bpst_conj_right guardEvidence
        (ay_bpst_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpst_accepted_phase_reuse_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    phaseGuidance :=
  fun accepted =>
    ay_bpst_conj_right agreementEvidence phaseGuidance
      (ay_bpst_conj_right guardEvidence
        (ay_bpst_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpst_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bpst_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bpst_conj_intro acceptedEvidence
      (ay_bpst_conj outcome formulaTruth)
      acceptedH
      (ay_bpst_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bpst_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bpst_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bpst_conj_left acceptedEvidence
      (ay_bpst_conj outcome formulaTruth)
      public

theorem ay_bpst_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bpst_no_claim diagnostic fallbackPublic :=
  ay_bpst_conj_intro diagnostic fallbackPublic

theorem ay_bpst_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpst_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bpst_conj_right diagnostic fallbackPublic noClaim

theorem ay_bpst_phase_drift_no_claim
    (phaseDrift : Prop)
    (fallbackPublic : Prop) :
    phaseDrift -> fallbackPublic -> ay_bpst_no_claim phaseDrift fallbackPublic :=
  ay_bpst_no_claim_intro phaseDrift fallbackPublic

theorem ay_bpst_trail_mismatch_no_claim
    (trailMismatch : Prop)
    (fallbackPublic : Prop) :
    trailMismatch ->
    fallbackPublic ->
    ay_bpst_no_claim trailMismatch fallbackPublic :=
  ay_bpst_no_claim_intro trailMismatch fallbackPublic

theorem ay_bpst_decision_level_mismatch_no_claim
    (decisionLevelMismatch : Prop)
    (fallbackPublic : Prop) :
    decisionLevelMismatch ->
    fallbackPublic ->
    ay_bpst_no_claim decisionLevelMismatch fallbackPublic :=
  ay_bpst_no_claim_intro decisionLevelMismatch fallbackPublic

theorem ay_bpst_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bpst_no_claim staleBuild fallbackPublic :=
  ay_bpst_no_claim_intro staleBuild fallbackPublic

theorem ay_bpst_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bpst_no_claim auditContradiction fallbackPublic :=
  ay_bpst_no_claim_intro auditContradiction fallbackPublic

theorem ay_bpst_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bpst_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bpst_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bpst_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpst_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bpst_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bpst_accepted_phase_reuse_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bpst_public_report
      (ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bpst_public_report_intro
      (ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bpst_accepted_phase_reuse_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bpst_public_report
      (ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bpst_accepted_phase_reuse_guides_sat guardEvidence agreementEvidence
    phaseGuidance unsatOutcome formulaTruth

theorem ay_bpst_accepted_phase_reuse_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    ay_bpst_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bpst_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bpst_phase_reuse_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bpst_accepted_phase_reuse guardEvidence agreementEvidence phaseGuidance ->
    ay_bpst_equisat beforeTruth afterTruth ->
    ay_bpst_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bpst_equisat_intro afterTruth beforeTruth
      (ay_bpst_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bpst_equisat_forward beforeTruth afterTruth eqsat)
