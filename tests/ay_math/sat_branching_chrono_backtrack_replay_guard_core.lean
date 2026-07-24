-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Chronological/non-chronological backtracking replay guard skeleton for
-- sequential-main SAT. Backtracking state is admissible guidance only when the
-- replayed levels, learned assertion levels, phase/activity state, and public
-- checker gates all agree.

def ay_bchr_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bchr_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bchr_conj (before -> after) (after -> before)

def ay_bchr_replay_guard
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (backtrackLevels ->
      assertionLevels ->
      phaseState ->
      activityReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bchr_guard_agreement
    (levelMatch : Prop)
    (assertionMatch : Prop)
    (phaseMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bchr_replay_guard levelMatch assertionMatch phaseMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bchr_accepted_state
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) : Prop :=
  ay_bchr_conj guardEvidence (ay_bchr_conj agreementEvidence backtrackGuidance)

def ay_bchr_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bchr_conj acceptedEvidence (ay_bchr_conj outcome formulaTruth)

def ay_bchr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bchr_conj diagnostic fallbackPublic

theorem ay_bchr_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bchr_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bchr_conj_left (left : Prop) (right : Prop) :
    ay_bchr_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bchr_conj_right (left : Prop) (right : Prop) :
    ay_bchr_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bchr_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bchr_equisat before after :=
  fun forward backward =>
    ay_bchr_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bchr_equisat_forward (before : Prop) (after : Prop) :
    ay_bchr_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bchr_conj_left (before -> after) (after -> before) eqsat

theorem ay_bchr_equisat_backward (before : Prop) (after : Prop) :
    ay_bchr_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bchr_conj_right (before -> after) (after -> before) eqsat

theorem ay_bchr_replay_guard_intro
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    backtrackLevels ->
    assertionLevels ->
    phaseState ->
    activityReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun levelH assertionH phaseH activityH fallbackH buildH validatorH auditH
      result build =>
    build levelH assertionH phaseH activityH fallbackH buildH validatorH auditH

theorem ay_bchr_replay_guard_levels
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    backtrackLevels :=
  fun guard =>
    guard backtrackLevels
      (fun levelH _assertionH _phaseH _activityH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bchr_replay_guard_assertion
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    assertionLevels :=
  fun guard =>
    guard assertionLevels
      (fun _levelH assertionH _phaseH _activityH _fallbackH _buildH
          _validatorH _auditH => assertionH)

theorem ay_bchr_replay_guard_phase
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseState :=
  fun guard =>
    guard phaseState
      (fun _levelH _assertionH phaseH _activityH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_bchr_replay_guard_activity
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityReplay :=
  fun guard =>
    guard activityReplay
      (fun _levelH _assertionH _phaseH activityH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bchr_replay_guard_fallback
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _levelH _assertionH _phaseH _activityH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bchr_replay_guard_build
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _levelH _assertionH _phaseH _activityH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bchr_replay_guard_validator
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _levelH _assertionH _phaseH _activityH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bchr_replay_guard_audit
    (backtrackLevels : Prop)
    (assertionLevels : Prop)
    (phaseState : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bchr_replay_guard backtrackLevels assertionLevels phaseState
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _levelH _assertionH _phaseH _activityH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bchr_guard_agreement_intro
    (levelMatch : Prop)
    (assertionMatch : Prop)
    (phaseMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    levelMatch ->
    assertionMatch ->
    phaseMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bchr_guard_agreement levelMatch assertionMatch phaseMatch activityMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bchr_replay_guard_intro levelMatch assertionMatch phaseMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bchr_accepted_state_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    backtrackGuidance ->
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bchr_conj_intro guardEvidence
      (ay_bchr_conj agreementEvidence backtrackGuidance)
      guardH
      (ay_bchr_conj_intro agreementEvidence backtrackGuidance
        agreementH guidanceH)

theorem ay_bchr_accepted_state_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bchr_conj_left guardEvidence
      (ay_bchr_conj agreementEvidence backtrackGuidance)
      accepted

theorem ay_bchr_accepted_state_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bchr_conj_left agreementEvidence backtrackGuidance
      (ay_bchr_conj_right guardEvidence
        (ay_bchr_conj agreementEvidence backtrackGuidance)
        accepted)

theorem ay_bchr_accepted_state_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    backtrackGuidance :=
  fun accepted =>
    ay_bchr_conj_right agreementEvidence backtrackGuidance
      (ay_bchr_conj_right guardEvidence
        (ay_bchr_conj agreementEvidence backtrackGuidance)
        accepted)

theorem ay_bchr_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bchr_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bchr_conj_intro acceptedEvidence
      (ay_bchr_conj outcome formulaTruth)
      acceptedH
      (ay_bchr_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bchr_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bchr_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bchr_conj_left acceptedEvidence
      (ay_bchr_conj outcome formulaTruth)
      public

theorem ay_bchr_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bchr_no_claim diagnostic fallbackPublic :=
  ay_bchr_conj_intro diagnostic fallbackPublic

theorem ay_bchr_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bchr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bchr_conj_right diagnostic fallbackPublic noClaim

theorem ay_bchr_level_drift_no_claim
    (levelDrift : Prop)
    (fallbackPublic : Prop) :
    levelDrift -> fallbackPublic -> ay_bchr_no_claim levelDrift fallbackPublic :=
  ay_bchr_no_claim_intro levelDrift fallbackPublic

theorem ay_bchr_assertion_mismatch_no_claim
    (assertionMismatch : Prop)
    (fallbackPublic : Prop) :
    assertionMismatch ->
    fallbackPublic ->
    ay_bchr_no_claim assertionMismatch fallbackPublic :=
  ay_bchr_no_claim_intro assertionMismatch fallbackPublic

theorem ay_bchr_phase_mismatch_no_claim
    (phaseMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseMismatch ->
    fallbackPublic ->
    ay_bchr_no_claim phaseMismatch fallbackPublic :=
  ay_bchr_no_claim_intro phaseMismatch fallbackPublic

theorem ay_bchr_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bchr_no_claim staleBuild fallbackPublic :=
  ay_bchr_no_claim_intro staleBuild fallbackPublic

theorem ay_bchr_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bchr_no_claim auditContradiction fallbackPublic :=
  ay_bchr_no_claim_intro auditContradiction fallbackPublic

theorem ay_bchr_activity_replay_failure_no_claim
    (activityReplayFailure : Prop)
    (fallbackPublic : Prop) :
    activityReplayFailure ->
    fallbackPublic ->
    ay_bchr_no_claim activityReplayFailure fallbackPublic :=
  ay_bchr_no_claim_intro activityReplayFailure fallbackPublic

theorem ay_bchr_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bchr_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bchr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bchr_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bchr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bchr_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bchr_accepted_state_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bchr_public_report
      (ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bchr_public_report_intro
      (ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bchr_accepted_state_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bchr_public_report
      (ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bchr_accepted_state_guides_sat guardEvidence agreementEvidence
    backtrackGuidance unsatOutcome formulaTruth

theorem ay_bchr_accepted_state_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    ay_bchr_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bchr_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bchr_backtracking_state_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (backtrackGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bchr_accepted_state guardEvidence agreementEvidence backtrackGuidance ->
    ay_bchr_equisat beforeTruth afterTruth ->
    ay_bchr_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bchr_equisat_intro afterTruth beforeTruth
      (ay_bchr_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bchr_equisat_forward beforeTruth afterTruth eqsat)
