-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause-weight tie-break guard soundness skeleton for ay SAT solving.
-- Clause-weight and variable-score tie-break hints may guide branching only
-- when clause weights, variable activity, conflict-window replay, decision
-- levels, implication graph slices, fallback baselines, solver builds,
-- validator gates, and audit evidence agree.

def ay_bcwt_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcwt_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bcwt_equisat (before : Prop) (after : Prop) :=
  ay_bcwt_conj (before -> after) (after -> before)

def ay_bcwt_tiebreak_guard
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (clauseWeightLedger -> variableActivityLedger ->
      conflictWindowReplay -> decisionLevelSnapshot ->
      implicationGraphSlice -> fallbackBaseline -> solverBuildEvidence ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_bcwt_guard_agreement
    (weightMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bcwt_tiebreak_guard weightMatch activityMatch windowReplayMatch
    levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bcwt_accepted_hint
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop) :=
  ay_bcwt_conj guard (ay_bcwt_conj agreement tiebreakHint)

def ay_bcwt_outcome (model : Prop) (conflict : Prop) :=
  ay_bcwt_disj model conflict

def ay_bcwt_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bcwt_conj acceptedEvidence (ay_bcwt_conj outcome formula)

def ay_bcwt_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bcwt_conj hintCert public

def ay_bcwt_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bcwt_conj fallbackPublic diagnostic

theorem ay_bcwt_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bcwt_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcwt_conj_left
    (left : Prop) (right : Prop) :
    ay_bcwt_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcwt_conj_right
    (left : Prop) (right : Prop) :
    ay_bcwt_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcwt_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bcwt_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcwt_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bcwt_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcwt_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcwt_equisat before after :=
  fun forward backward =>
    ay_bcwt_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcwt_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bcwt_equisat before after -> before -> after :=
  fun equisat =>
    ay_bcwt_conj_left (before -> after) (after -> before) equisat

theorem ay_bcwt_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bcwt_equisat before after -> after -> before :=
  fun equisat =>
    ay_bcwt_conj_right (before -> after) (after -> before) equisat

theorem ay_bcwt_tiebreak_guard_intro
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    clauseWeightLedger ->
    variableActivityLedger ->
    conflictWindowReplay ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence :=
  fun weightH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH result build =>
    build weightH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH

theorem ay_bcwt_tiebreak_guard_weight
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    clauseWeightLedger :=
  fun guard =>
    guard clauseWeightLedger
      (fun weightH _activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => weightH)

theorem ay_bcwt_tiebreak_guard_activity
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    variableActivityLedger :=
  fun guard =>
    guard variableActivityLedger
      (fun _weightH activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bcwt_tiebreak_guard_window
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _weightH _activityH windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_bcwt_tiebreak_guard_level
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _weightH _activityH _windowH levelH _graphH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bcwt_tiebreak_guard_graph
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _weightH _activityH _windowH _levelH graphH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_bcwt_tiebreak_guard_fallback
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _weightH _activityH _windowH _levelH _graphH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bcwt_tiebreak_guard_build
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _weightH _activityH _windowH _levelH _graphH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bcwt_tiebreak_guard_validator
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _weightH _activityH _windowH _levelH _graphH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bcwt_tiebreak_guard_audit
    (clauseWeightLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcwt_tiebreak_guard clauseWeightLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _weightH _activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bcwt_guard_agreement_intro
    (weightMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    weightMatch ->
    activityMatch ->
    windowReplayMatch ->
    levelMatch ->
    graphSliceMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcwt_guard_agreement weightMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  fun weightH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH =>
    ay_bcwt_tiebreak_guard_intro weightMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch weightH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH

theorem ay_bcwt_guard_agreement_weight
    (weightMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bcwt_guard_agreement weightMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch ->
    weightMatch :=
  fun agreement =>
    ay_bcwt_tiebreak_guard_weight weightMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch agreement

theorem ay_bcwt_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop) :
    guard ->
    agreement ->
    tiebreakHint ->
    ay_bcwt_accepted_hint guard agreement tiebreakHint :=
  fun guardH agreementH hintH =>
    ay_bcwt_conj_intro guard (ay_bcwt_conj agreement tiebreakHint)
      guardH
      (ay_bcwt_conj_intro agreement tiebreakHint agreementH hintH)

theorem ay_bcwt_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop) :
    ay_bcwt_accepted_hint guard agreement tiebreakHint -> guard :=
  fun accepted =>
    ay_bcwt_conj_left guard (ay_bcwt_conj agreement tiebreakHint) accepted

theorem ay_bcwt_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop) :
    ay_bcwt_accepted_hint guard agreement tiebreakHint -> agreement :=
  fun accepted =>
    ay_bcwt_conj_left agreement tiebreakHint
      (ay_bcwt_conj_right guard (ay_bcwt_conj agreement tiebreakHint)
        accepted)

theorem ay_bcwt_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop) :
    ay_bcwt_accepted_hint guard agreement tiebreakHint -> tiebreakHint :=
  fun accepted =>
    ay_bcwt_conj_right agreement tiebreakHint
      (ay_bcwt_conj_right guard (ay_bcwt_conj agreement tiebreakHint)
        accepted)

theorem ay_bcwt_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bcwt_public_report acceptedEvidence
      (ay_bcwt_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bcwt_conj_intro acceptedEvidence
      (ay_bcwt_conj (ay_bcwt_outcome model conflict) formula)
      acceptedH
      (ay_bcwt_conj_intro (ay_bcwt_outcome model conflict) formula
        (ay_bcwt_disj_left model conflict modelH)
        formulaH)

theorem ay_bcwt_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bcwt_public_report acceptedEvidence
      (ay_bcwt_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bcwt_conj_intro acceptedEvidence
      (ay_bcwt_conj (ay_bcwt_outcome model conflict) formula)
      acceptedH
      (ay_bcwt_conj_intro (ay_bcwt_outcome model conflict) formula
        (ay_bcwt_disj_right model conflict conflictH)
        formulaH)

theorem ay_bcwt_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bcwt_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bcwt_conj_left acceptedEvidence
      (ay_bcwt_conj outcome formula) public

theorem ay_bcwt_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bcwt_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bcwt_conj_intro hintCert public hintH publicH

theorem ay_bcwt_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bcwt_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcwt_conj_right hintCert public accepted

theorem ay_bcwt_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bcwt_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bcwt_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcwt_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcwt_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcwt_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcwt_weight_drift_no_claim
    (weightDrift : Prop) (fallbackPublic : Prop) :
    weightDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim weightDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro weightDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bcwt_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcwt_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bcwt_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcwt_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bcwt_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bcwt_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcwt_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcwt_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bcwt_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcwt_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bcwt_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bcwt_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcwt_accepted_hint guard agreement tiebreakHint ->
    model ->
    formula ->
    ay_bcwt_accepted_report
      (ay_bcwt_accepted_hint guard agreement tiebreakHint)
      (ay_bcwt_public_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        (ay_bcwt_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bcwt_accepted_report_intro
      (ay_bcwt_accepted_hint guard agreement tiebreakHint)
      (ay_bcwt_public_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        (ay_bcwt_outcome model conflict) formula)
      accepted
      (ay_bcwt_public_sat_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bcwt_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (tiebreakHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcwt_accepted_hint guard agreement tiebreakHint ->
    conflict ->
    formula ->
    ay_bcwt_accepted_report
      (ay_bcwt_accepted_hint guard agreement tiebreakHint)
      (ay_bcwt_public_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        (ay_bcwt_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bcwt_accepted_report_intro
      (ay_bcwt_accepted_hint guard agreement tiebreakHint)
      (ay_bcwt_public_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        (ay_bcwt_outcome model conflict) formula)
      accepted
      (ay_bcwt_public_unsat_report
        (ay_bcwt_accepted_hint guard agreement tiebreakHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bcwt_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bcwt_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcwt_accepted_report_public hintCert public accepted

theorem ay_bcwt_tiebreak_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bcwt_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bcwt_equisat_forward beforeHint afterHint equisat beforeH
