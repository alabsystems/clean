-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart/phase interaction guard soundness skeleton for ay SAT
-- solving. Restart-triggered phase reuse and reset hints may guide search only
-- when restart ledgers, phase caches, deterministic replay, activity ledgers,
-- fallback baselines, solver builds, validator gates, and audit evidence agree.

def ay_brpi_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brpi_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brpi_equisat (before : Prop) (after : Prop) :=
  ay_brpi_conj (before -> after) (after -> before)

def ay_brpi_interaction_guard
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (restartLedger -> phaseCacheLedger -> deterministicReplayEvidence ->
      activityLedger -> fallbackBaseline -> solverBuildEvidence ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_brpi_guard_agreement
    (restartMatch : Prop) (phaseMatch : Prop)
    (replayMatch : Prop) (activityMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_brpi_interaction_guard restartMatch phaseMatch replayMatch
    activityMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brpi_accepted_hint
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :=
  ay_brpi_conj guard (ay_brpi_conj agreement restartPhaseHint)

def ay_brpi_outcome (model : Prop) (conflict : Prop) :=
  ay_brpi_disj model conflict

def ay_brpi_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_brpi_conj acceptedEvidence (ay_brpi_conj outcome formula)

def ay_brpi_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_brpi_conj hintCert public

def ay_brpi_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_brpi_conj fallbackPublic diagnostic

theorem ay_brpi_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_brpi_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brpi_conj_left
    (left : Prop) (right : Prop) :
    ay_brpi_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brpi_conj_right
    (left : Prop) (right : Prop) :
    ay_brpi_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brpi_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_brpi_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brpi_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_brpi_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brpi_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_brpi_equisat before after :=
  fun forward backward =>
    ay_brpi_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brpi_equisat_forward
    (before : Prop) (after : Prop) :
    ay_brpi_equisat before after -> before -> after :=
  fun equisat =>
    ay_brpi_conj_left (before -> after) (after -> before) equisat

theorem ay_brpi_equisat_backward
    (before : Prop) (after : Prop) :
    ay_brpi_equisat before after -> after -> before :=
  fun equisat =>
    ay_brpi_conj_right (before -> after) (after -> before) equisat

theorem ay_brpi_interaction_guard_intro
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    restartLedger ->
    phaseCacheLedger ->
    deterministicReplayEvidence ->
    activityLedger ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence :=
  fun restartH phaseH replayH activityH fallbackH buildH validatorH auditH
      result build =>
    build restartH phaseH replayH activityH fallbackH buildH validatorH auditH

theorem ay_brpi_interaction_guard_restart
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    restartLedger :=
  fun guard =>
    guard restartLedger
      (fun restartH _phaseH _replayH _activityH _fallbackH _buildH
          _validatorH _auditH => restartH)

theorem ay_brpi_interaction_guard_phase
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    phaseCacheLedger :=
  fun guard =>
    guard phaseCacheLedger
      (fun _restartH phaseH _replayH _activityH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_brpi_interaction_guard_replay
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    deterministicReplayEvidence :=
  fun guard =>
    guard deterministicReplayEvidence
      (fun _restartH _phaseH replayH _activityH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_brpi_interaction_guard_activity
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    activityLedger :=
  fun guard =>
    guard activityLedger
      (fun _restartH _phaseH _replayH activityH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_brpi_interaction_guard_fallback
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _restartH _phaseH _replayH _activityH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brpi_interaction_guard_build
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _restartH _phaseH _replayH _activityH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brpi_interaction_guard_validator
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _restartH _phaseH _replayH _activityH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brpi_interaction_guard_audit
    (restartLedger : Prop) (phaseCacheLedger : Prop)
    (deterministicReplayEvidence : Prop) (activityLedger : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brpi_interaction_guard restartLedger phaseCacheLedger
      deterministicReplayEvidence activityLedger fallbackBaseline
      solverBuildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _restartH _phaseH _replayH _activityH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brpi_guard_agreement_intro
    (restartMatch : Prop) (phaseMatch : Prop)
    (replayMatch : Prop) (activityMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    restartMatch ->
    phaseMatch ->
    replayMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brpi_guard_agreement restartMatch phaseMatch replayMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun restartH phaseH replayH activityH fallbackH buildH validatorH auditH =>
    ay_brpi_interaction_guard_intro restartMatch phaseMatch replayMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch
      restartH phaseH replayH activityH fallbackH buildH validatorH auditH

theorem ay_brpi_guard_agreement_restart
    (restartMatch : Prop) (phaseMatch : Prop)
    (replayMatch : Prop) (activityMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_brpi_guard_agreement restartMatch phaseMatch replayMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    restartMatch :=
  fun agreement =>
    ay_brpi_interaction_guard_restart restartMatch phaseMatch replayMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_brpi_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    guard ->
    agreement ->
    restartPhaseHint ->
    ay_brpi_accepted_hint guard agreement restartPhaseHint :=
  fun guardH agreementH hintH =>
    ay_brpi_conj_intro guard (ay_brpi_conj agreement restartPhaseHint)
      guardH
      (ay_brpi_conj_intro agreement restartPhaseHint agreementH hintH)

theorem ay_brpi_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brpi_accepted_hint guard agreement restartPhaseHint -> guard :=
  fun accepted =>
    ay_brpi_conj_left guard (ay_brpi_conj agreement restartPhaseHint)
      accepted

theorem ay_brpi_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brpi_accepted_hint guard agreement restartPhaseHint -> agreement :=
  fun accepted =>
    ay_brpi_conj_left agreement restartPhaseHint
      (ay_brpi_conj_right guard (ay_brpi_conj agreement restartPhaseHint)
        accepted)

theorem ay_brpi_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brpi_accepted_hint guard agreement restartPhaseHint ->
    restartPhaseHint :=
  fun accepted =>
    ay_brpi_conj_right agreement restartPhaseHint
      (ay_brpi_conj_right guard (ay_brpi_conj agreement restartPhaseHint)
        accepted)

theorem ay_brpi_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_brpi_public_report acceptedEvidence
      (ay_brpi_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_brpi_conj_intro acceptedEvidence
      (ay_brpi_conj (ay_brpi_outcome model conflict) formula)
      acceptedH
      (ay_brpi_conj_intro (ay_brpi_outcome model conflict) formula
        (ay_brpi_disj_left model conflict modelH)
        formulaH)

theorem ay_brpi_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_brpi_public_report acceptedEvidence
      (ay_brpi_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_brpi_conj_intro acceptedEvidence
      (ay_brpi_conj (ay_brpi_outcome model conflict) formula)
      acceptedH
      (ay_brpi_conj_intro (ay_brpi_outcome model conflict) formula
        (ay_brpi_disj_right model conflict conflictH)
        formulaH)

theorem ay_brpi_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_brpi_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_brpi_conj_left acceptedEvidence
      (ay_brpi_conj outcome formula) public

theorem ay_brpi_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_brpi_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_brpi_conj_intro hintCert public hintH publicH

theorem ay_brpi_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_brpi_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brpi_conj_right hintCert public accepted

theorem ay_brpi_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_brpi_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_brpi_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brpi_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brpi_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brpi_conj_left fallbackPublic diagnostic noClaim

theorem ay_brpi_restart_drift_no_claim
    (restartDrift : Prop) (fallbackPublic : Prop) :
    restartDrift ->
    fallbackPublic ->
    ay_brpi_no_claim restartDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro restartDrift fallbackPublic fallbackH diagnosticH

theorem ay_brpi_phase_replay_drift_no_claim
    (phaseReplayDrift : Prop) (fallbackPublic : Prop) :
    phaseReplayDrift ->
    fallbackPublic ->
    ay_brpi_no_claim phaseReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro phaseReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_brpi_missing_restart_ledger_no_claim
    (missingRestartLedger : Prop) (fallbackPublic : Prop) :
    missingRestartLedger ->
    fallbackPublic ->
    ay_brpi_no_claim missingRestartLedger fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro missingRestartLedger fallbackPublic
      fallbackH diagnosticH

theorem ay_brpi_missing_phase_cache_no_claim
    (missingPhaseCache : Prop) (fallbackPublic : Prop) :
    missingPhaseCache ->
    fallbackPublic ->
    ay_brpi_no_claim missingPhaseCache fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro missingPhaseCache fallbackPublic
      fallbackH diagnosticH

theorem ay_brpi_replay_drift_no_claim
    (replayDrift : Prop) (fallbackPublic : Prop) :
    replayDrift ->
    fallbackPublic ->
    ay_brpi_no_claim replayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro replayDrift fallbackPublic fallbackH diagnosticH

theorem ay_brpi_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_brpi_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_brpi_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brpi_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_brpi_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_brpi_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_brpi_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_brpi_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_brpi_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brpi_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brpi_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_brpi_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brpi_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_brpi_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_brpi_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brpi_accepted_hint guard agreement restartPhaseHint ->
    model ->
    formula ->
    ay_brpi_accepted_report
      (ay_brpi_accepted_hint guard agreement restartPhaseHint)
      (ay_brpi_public_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        (ay_brpi_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_brpi_accepted_report_intro
      (ay_brpi_accepted_hint guard agreement restartPhaseHint)
      (ay_brpi_public_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        (ay_brpi_outcome model conflict) formula)
      accepted
      (ay_brpi_public_sat_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        model conflict formula accepted modelH formulaH)

theorem ay_brpi_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brpi_accepted_hint guard agreement restartPhaseHint ->
    conflict ->
    formula ->
    ay_brpi_accepted_report
      (ay_brpi_accepted_hint guard agreement restartPhaseHint)
      (ay_brpi_public_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        (ay_brpi_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_brpi_accepted_report_intro
      (ay_brpi_accepted_hint guard agreement restartPhaseHint)
      (ay_brpi_public_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        (ay_brpi_outcome model conflict) formula)
      accepted
      (ay_brpi_public_unsat_report
        (ay_brpi_accepted_hint guard agreement restartPhaseHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_brpi_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_brpi_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brpi_accepted_report_public hintCert public accepted

theorem ay_brpi_restart_phase_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_brpi_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_brpi_equisat_forward beforeHint afterHint equisat beforeH
