-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded variable activity-decay guard soundness skeleton for ay SAT solving.
-- Activity decay and phase-saving guidance may guide search only when activity
-- ledgers, conflict-window replay, decision levels, implication graph slices,
-- restart epochs, fallback baselines, solver builds, validator gates, and
-- audit evidence agree.

def ay_bvad_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bvad_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bvad_equisat (before : Prop) (after : Prop) :=
  ay_bvad_conj (before -> after) (after -> before)

def ay_bvad_decay_guard
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (activityLedger -> conflictWindowReplay -> decisionLevelSnapshot ->
      implicationGraphSlice -> restartEpoch -> fallbackBaseline ->
      solverBuildEvidence -> validatorGate -> auditEvidence -> result) ->
    result

def ay_bvad_guard_agreement
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (levelMatch : Prop) (graphSliceMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bvad_decay_guard activityMatch windowReplayMatch levelMatch
    graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bvad_accepted_hint
    (guard : Prop) (agreement : Prop) (decayHint : Prop) :=
  ay_bvad_conj guard (ay_bvad_conj agreement decayHint)

def ay_bvad_outcome (model : Prop) (conflict : Prop) :=
  ay_bvad_disj model conflict

def ay_bvad_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bvad_conj acceptedEvidence (ay_bvad_conj outcome formula)

def ay_bvad_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bvad_conj hintCert public

def ay_bvad_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bvad_conj fallbackPublic diagnostic

theorem ay_bvad_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bvad_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bvad_conj_left
    (left : Prop) (right : Prop) :
    ay_bvad_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bvad_conj_right
    (left : Prop) (right : Prop) :
    ay_bvad_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bvad_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bvad_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bvad_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bvad_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bvad_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bvad_equisat before after :=
  fun forward backward =>
    ay_bvad_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bvad_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bvad_equisat before after -> before -> after :=
  fun equisat =>
    ay_bvad_conj_left (before -> after) (after -> before) equisat

theorem ay_bvad_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bvad_equisat before after -> after -> before :=
  fun equisat =>
    ay_bvad_conj_right (before -> after) (after -> before) equisat

theorem ay_bvad_decay_guard_intro
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    activityLedger ->
    conflictWindowReplay ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    restartEpoch ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence :=
  fun activityH windowH levelH graphH epochH fallbackH buildH validatorH
      auditH result build =>
    build activityH windowH levelH graphH epochH fallbackH buildH validatorH
      auditH

theorem ay_bvad_decay_guard_activity
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    activityLedger :=
  fun guard =>
    guard activityLedger
      (fun activityH _windowH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bvad_decay_guard_window
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _activityH windowH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_bvad_decay_guard_level
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _activityH _windowH levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bvad_decay_guard_graph
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _activityH _windowH _levelH graphH _epochH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_bvad_decay_guard_epoch
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    restartEpoch :=
  fun guard =>
    guard restartEpoch
      (fun _activityH _windowH _levelH _graphH epochH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bvad_decay_guard_fallback
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _activityH _windowH _levelH _graphH _epochH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bvad_decay_guard_build
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _activityH _windowH _levelH _graphH _epochH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bvad_decay_guard_validator
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _activityH _windowH _levelH _graphH _epochH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bvad_decay_guard_audit
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvad_decay_guard activityLedger conflictWindowReplay
      decisionLevelSnapshot implicationGraphSlice restartEpoch
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _activityH _windowH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bvad_guard_agreement_intro
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (levelMatch : Prop) (graphSliceMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    activityMatch ->
    windowReplayMatch ->
    levelMatch ->
    graphSliceMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bvad_guard_agreement activityMatch windowReplayMatch levelMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  fun activityH windowH levelH graphH epochH fallbackH buildH validatorH
      auditH =>
    ay_bvad_decay_guard_intro activityMatch windowReplayMatch levelMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch activityH windowH levelH graphH epochH fallbackH buildH
      validatorH auditH

theorem ay_bvad_guard_agreement_activity
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (levelMatch : Prop) (graphSliceMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bvad_guard_agreement activityMatch windowReplayMatch levelMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch ->
    activityMatch :=
  fun agreement =>
    ay_bvad_decay_guard_activity activityMatch windowReplayMatch levelMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch agreement

theorem ay_bvad_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (decayHint : Prop) :
    guard ->
    agreement ->
    decayHint ->
    ay_bvad_accepted_hint guard agreement decayHint :=
  fun guardH agreementH hintH =>
    ay_bvad_conj_intro guard (ay_bvad_conj agreement decayHint)
      guardH
      (ay_bvad_conj_intro agreement decayHint agreementH hintH)

theorem ay_bvad_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (decayHint : Prop) :
    ay_bvad_accepted_hint guard agreement decayHint -> guard :=
  fun accepted =>
    ay_bvad_conj_left guard (ay_bvad_conj agreement decayHint) accepted

theorem ay_bvad_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (decayHint : Prop) :
    ay_bvad_accepted_hint guard agreement decayHint -> agreement :=
  fun accepted =>
    ay_bvad_conj_left agreement decayHint
      (ay_bvad_conj_right guard (ay_bvad_conj agreement decayHint)
        accepted)

theorem ay_bvad_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (decayHint : Prop) :
    ay_bvad_accepted_hint guard agreement decayHint -> decayHint :=
  fun accepted =>
    ay_bvad_conj_right agreement decayHint
      (ay_bvad_conj_right guard (ay_bvad_conj agreement decayHint)
        accepted)

theorem ay_bvad_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bvad_public_report acceptedEvidence
      (ay_bvad_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bvad_conj_intro acceptedEvidence
      (ay_bvad_conj (ay_bvad_outcome model conflict) formula)
      acceptedH
      (ay_bvad_conj_intro (ay_bvad_outcome model conflict) formula
        (ay_bvad_disj_left model conflict modelH)
        formulaH)

theorem ay_bvad_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bvad_public_report acceptedEvidence
      (ay_bvad_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bvad_conj_intro acceptedEvidence
      (ay_bvad_conj (ay_bvad_outcome model conflict) formula)
      acceptedH
      (ay_bvad_conj_intro (ay_bvad_outcome model conflict) formula
        (ay_bvad_disj_right model conflict conflictH)
        formulaH)

theorem ay_bvad_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bvad_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bvad_conj_left acceptedEvidence
      (ay_bvad_conj outcome formula) public

theorem ay_bvad_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bvad_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bvad_conj_intro hintCert public hintH publicH

theorem ay_bvad_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bvad_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bvad_conj_right hintCert public accepted

theorem ay_bvad_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bvad_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bvad_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bvad_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bvad_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bvad_conj_left fallbackPublic diagnostic noClaim

theorem ay_bvad_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bvad_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvad_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bvad_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bvad_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_bvad_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvad_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bvad_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvad_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_bvad_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvad_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bvad_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bvad_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bvad_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bvad_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bvad_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bvad_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bvad_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bvad_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bvad_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bvad_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bvad_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bvad_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (decayHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bvad_accepted_hint guard agreement decayHint ->
    model ->
    formula ->
    ay_bvad_accepted_report
      (ay_bvad_accepted_hint guard agreement decayHint)
      (ay_bvad_public_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        (ay_bvad_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bvad_accepted_report_intro
      (ay_bvad_accepted_hint guard agreement decayHint)
      (ay_bvad_public_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        (ay_bvad_outcome model conflict) formula)
      accepted
      (ay_bvad_public_sat_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bvad_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (decayHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bvad_accepted_hint guard agreement decayHint ->
    conflict ->
    formula ->
    ay_bvad_accepted_report
      (ay_bvad_accepted_hint guard agreement decayHint)
      (ay_bvad_public_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        (ay_bvad_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bvad_accepted_report_intro
      (ay_bvad_accepted_hint guard agreement decayHint)
      (ay_bvad_public_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        (ay_bvad_outcome model conflict) formula)
      accepted
      (ay_bvad_public_unsat_report
        (ay_bvad_accepted_hint guard agreement decayHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bvad_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bvad_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bvad_accepted_report_public hintCert public accepted

theorem ay_bvad_decay_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bvad_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bvad_equisat_forward beforeHint afterHint equisat beforeH
