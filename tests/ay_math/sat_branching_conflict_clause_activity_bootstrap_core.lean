-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded conflict-clause activity bootstrap guard soundness skeleton for ay.
-- Bootstrap and initial score hints may guide branching only when bootstrap
-- ledgers, variable/clause activity ledgers, conflict-window replay, decision
-- levels, implication graph slices, fallback baselines, solver builds,
-- validator gates, and audit evidence agree.

def ay_bcab_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcab_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bcab_equisat (before : Prop) (after : Prop) :=
  ay_bcab_conj (before -> after) (after -> before)

def ay_bcab_bootstrap_guard
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (bootstrapLedger -> activityLedger -> conflictWindowReplay ->
      decisionLevelSnapshot -> implicationGraphSlice -> fallbackBaseline ->
      solverBuildEvidence -> validatorGate -> auditEvidence -> result) ->
    result

def ay_bcab_guard_agreement
    (bootstrapMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bcab_bootstrap_guard bootstrapMatch activityMatch windowReplayMatch
    levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bcab_accepted_hint
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop) :=
  ay_bcab_conj guard (ay_bcab_conj agreement bootstrapHint)

def ay_bcab_outcome (model : Prop) (conflict : Prop) :=
  ay_bcab_disj model conflict

def ay_bcab_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bcab_conj acceptedEvidence (ay_bcab_conj outcome formula)

def ay_bcab_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bcab_conj hintCert public

def ay_bcab_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bcab_conj fallbackPublic diagnostic

theorem ay_bcab_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bcab_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcab_conj_left
    (left : Prop) (right : Prop) :
    ay_bcab_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcab_conj_right
    (left : Prop) (right : Prop) :
    ay_bcab_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcab_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bcab_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcab_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bcab_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcab_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcab_equisat before after :=
  fun forward backward =>
    ay_bcab_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcab_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bcab_equisat before after -> before -> after :=
  fun equisat =>
    ay_bcab_conj_left (before -> after) (after -> before) equisat

theorem ay_bcab_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bcab_equisat before after -> after -> before :=
  fun equisat =>
    ay_bcab_conj_right (before -> after) (after -> before) equisat

theorem ay_bcab_bootstrap_guard_intro
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    bootstrapLedger ->
    activityLedger ->
    conflictWindowReplay ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence :=
  fun bootstrapH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH result build =>
    build bootstrapH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH

theorem ay_bcab_bootstrap_guard_bootstrap
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    bootstrapLedger :=
  fun guard =>
    guard bootstrapLedger
      (fun bootstrapH _activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => bootstrapH)

theorem ay_bcab_bootstrap_guard_activity
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    activityLedger :=
  fun guard =>
    guard activityLedger
      (fun _bootstrapH activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bcab_bootstrap_guard_window
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _bootstrapH _activityH windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => windowH)

theorem ay_bcab_bootstrap_guard_level
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _bootstrapH _activityH _windowH levelH _graphH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_bcab_bootstrap_guard_graph
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _bootstrapH _activityH _windowH _levelH graphH _fallbackH
          _buildH _validatorH _auditH => graphH)

theorem ay_bcab_bootstrap_guard_fallback
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _bootstrapH _activityH _windowH _levelH _graphH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bcab_bootstrap_guard_build
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _bootstrapH _activityH _windowH _levelH _graphH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bcab_bootstrap_guard_validator
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _bootstrapH _activityH _windowH _levelH _graphH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bcab_bootstrap_guard_audit
    (bootstrapLedger : Prop) (activityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_bootstrap_guard bootstrapLedger activityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _bootstrapH _activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bcab_guard_agreement_intro
    (bootstrapMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    bootstrapMatch ->
    activityMatch ->
    windowReplayMatch ->
    levelMatch ->
    graphSliceMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcab_guard_agreement bootstrapMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  fun bootstrapH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH =>
    ay_bcab_bootstrap_guard_intro bootstrapMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch bootstrapH activityH windowH levelH graphH
      fallbackH buildH validatorH auditH

theorem ay_bcab_guard_agreement_bootstrap
    (bootstrapMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bcab_guard_agreement bootstrapMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch ->
    bootstrapMatch :=
  fun agreement =>
    ay_bcab_bootstrap_guard_bootstrap bootstrapMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch agreement

theorem ay_bcab_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop) :
    guard ->
    agreement ->
    bootstrapHint ->
    ay_bcab_accepted_hint guard agreement bootstrapHint :=
  fun guardH agreementH hintH =>
    ay_bcab_conj_intro guard (ay_bcab_conj agreement bootstrapHint)
      guardH
      (ay_bcab_conj_intro agreement bootstrapHint agreementH hintH)

theorem ay_bcab_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop) :
    ay_bcab_accepted_hint guard agreement bootstrapHint -> guard :=
  fun accepted =>
    ay_bcab_conj_left guard (ay_bcab_conj agreement bootstrapHint) accepted

theorem ay_bcab_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop) :
    ay_bcab_accepted_hint guard agreement bootstrapHint -> agreement :=
  fun accepted =>
    ay_bcab_conj_left agreement bootstrapHint
      (ay_bcab_conj_right guard (ay_bcab_conj agreement bootstrapHint)
        accepted)

theorem ay_bcab_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop) :
    ay_bcab_accepted_hint guard agreement bootstrapHint -> bootstrapHint :=
  fun accepted =>
    ay_bcab_conj_right agreement bootstrapHint
      (ay_bcab_conj_right guard (ay_bcab_conj agreement bootstrapHint)
        accepted)

theorem ay_bcab_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bcab_public_report acceptedEvidence
      (ay_bcab_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bcab_conj_intro acceptedEvidence
      (ay_bcab_conj (ay_bcab_outcome model conflict) formula)
      acceptedH
      (ay_bcab_conj_intro (ay_bcab_outcome model conflict) formula
        (ay_bcab_disj_left model conflict modelH)
        formulaH)

theorem ay_bcab_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bcab_public_report acceptedEvidence
      (ay_bcab_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bcab_conj_intro acceptedEvidence
      (ay_bcab_conj (ay_bcab_outcome model conflict) formula)
      acceptedH
      (ay_bcab_conj_intro (ay_bcab_outcome model conflict) formula
        (ay_bcab_disj_right model conflict conflictH)
        formulaH)

theorem ay_bcab_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bcab_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bcab_conj_left acceptedEvidence
      (ay_bcab_conj outcome formula) public

theorem ay_bcab_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bcab_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bcab_conj_intro hintCert public hintH publicH

theorem ay_bcab_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bcab_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcab_conj_right hintCert public accepted

theorem ay_bcab_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bcab_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bcab_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcab_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcab_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcab_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcab_bootstrap_drift_no_claim
    (bootstrapDrift : Prop) (fallbackPublic : Prop) :
    bootstrapDrift ->
    fallbackPublic ->
    ay_bcab_no_claim bootstrapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro bootstrapDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcab_missing_bootstrap_ledger_no_claim
    (missingBootstrapLedger : Prop) (fallbackPublic : Prop) :
    missingBootstrapLedger ->
    fallbackPublic ->
    ay_bcab_no_claim missingBootstrapLedger fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro missingBootstrapLedger fallbackPublic
      fallbackH diagnosticH

theorem ay_bcab_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bcab_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcab_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bcab_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bcab_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_bcab_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcab_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bcab_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcab_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcab_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bcab_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bcab_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcab_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bcab_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bcab_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcab_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcab_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bcab_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcab_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bcab_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bcab_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcab_accepted_hint guard agreement bootstrapHint ->
    model ->
    formula ->
    ay_bcab_accepted_report
      (ay_bcab_accepted_hint guard agreement bootstrapHint)
      (ay_bcab_public_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        (ay_bcab_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bcab_accepted_report_intro
      (ay_bcab_accepted_hint guard agreement bootstrapHint)
      (ay_bcab_public_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        (ay_bcab_outcome model conflict) formula)
      accepted
      (ay_bcab_public_sat_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bcab_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (bootstrapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcab_accepted_hint guard agreement bootstrapHint ->
    conflict ->
    formula ->
    ay_bcab_accepted_report
      (ay_bcab_accepted_hint guard agreement bootstrapHint)
      (ay_bcab_public_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        (ay_bcab_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bcab_accepted_report_intro
      (ay_bcab_accepted_hint guard agreement bootstrapHint)
      (ay_bcab_public_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        (ay_bcab_outcome model conflict) formula)
      accepted
      (ay_bcab_public_unsat_report
        (ay_bcab_accepted_hint guard agreement bootstrapHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bcab_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bcab_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcab_accepted_report_public hintCert public accepted

theorem ay_bcab_bootstrap_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bcab_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bcab_equisat_forward beforeHint afterHint equisat beforeH
