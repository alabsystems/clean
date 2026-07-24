-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded phase-saving cache guard soundness skeleton for ay SAT solving.
-- Phase-saving cache and polarity replay hints may guide branching only when
-- phase cache ledgers, variable activity, conflict-window replay, decision
-- levels, implication graph slices, fallback baselines, solver builds,
-- validator gates, and audit evidence agree.

def ay_bpsc_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpsc_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bpsc_equisat (before : Prop) (after : Prop) :=
  ay_bpsc_conj (before -> after) (after -> before)

def ay_bpsc_phase_guard
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (phaseCacheLedger -> variableActivityLedger -> conflictWindowReplay ->
      decisionLevelSnapshot -> implicationGraphSlice -> fallbackBaseline ->
      solverBuildEvidence -> validatorGate -> auditEvidence -> result) ->
    result

def ay_bpsc_guard_agreement
    (phaseMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bpsc_phase_guard phaseMatch activityMatch windowReplayMatch levelMatch
    graphSliceMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bpsc_accepted_hint
    (guard : Prop) (agreement : Prop) (phaseHint : Prop) :=
  ay_bpsc_conj guard (ay_bpsc_conj agreement phaseHint)

def ay_bpsc_outcome (model : Prop) (conflict : Prop) :=
  ay_bpsc_disj model conflict

def ay_bpsc_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bpsc_conj acceptedEvidence (ay_bpsc_conj outcome formula)

def ay_bpsc_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bpsc_conj hintCert public

def ay_bpsc_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bpsc_conj fallbackPublic diagnostic

theorem ay_bpsc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bpsc_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bpsc_conj_left
    (left : Prop) (right : Prop) :
    ay_bpsc_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bpsc_conj_right
    (left : Prop) (right : Prop) :
    ay_bpsc_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bpsc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bpsc_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bpsc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bpsc_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bpsc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bpsc_equisat before after :=
  fun forward backward =>
    ay_bpsc_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bpsc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bpsc_equisat before after -> before -> after :=
  fun equisat =>
    ay_bpsc_conj_left (before -> after) (after -> before) equisat

theorem ay_bpsc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bpsc_equisat before after -> after -> before :=
  fun equisat =>
    ay_bpsc_conj_right (before -> after) (after -> before) equisat

theorem ay_bpsc_phase_guard_intro
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    phaseCacheLedger ->
    variableActivityLedger ->
    conflictWindowReplay ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence :=
  fun phaseH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH result build =>
    build phaseH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH

theorem ay_bpsc_phase_guard_phase
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    phaseCacheLedger :=
  fun guard =>
    guard phaseCacheLedger
      (fun phaseH _activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_bpsc_phase_guard_activity
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    variableActivityLedger :=
  fun guard =>
    guard variableActivityLedger
      (fun _phaseH activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bpsc_phase_guard_window
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _phaseH _activityH windowH _levelH _graphH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_bpsc_phase_guard_level
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _phaseH _activityH _windowH levelH _graphH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bpsc_phase_guard_graph
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _phaseH _activityH _windowH _levelH graphH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_bpsc_phase_guard_fallback
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _phaseH _activityH _windowH _levelH _graphH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bpsc_phase_guard_build
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _phaseH _activityH _windowH _levelH _graphH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bpsc_phase_guard_validator
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _phaseH _activityH _windowH _levelH _graphH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bpsc_phase_guard_audit
    (phaseCacheLedger : Prop) (variableActivityLedger : Prop)
    (conflictWindowReplay : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpsc_phase_guard phaseCacheLedger variableActivityLedger
      conflictWindowReplay decisionLevelSnapshot implicationGraphSlice
      fallbackBaseline solverBuildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _phaseH _activityH _windowH _levelH _graphH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bpsc_guard_agreement_intro
    (phaseMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    phaseMatch ->
    activityMatch ->
    windowReplayMatch ->
    levelMatch ->
    graphSliceMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bpsc_guard_agreement phaseMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  fun phaseH activityH windowH levelH graphH fallbackH buildH validatorH
      auditH =>
    ay_bpsc_phase_guard_intro phaseMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch phaseH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH

theorem ay_bpsc_guard_agreement_phase
    (phaseMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bpsc_guard_agreement phaseMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch ->
    phaseMatch :=
  fun agreement =>
    ay_bpsc_phase_guard_phase phaseMatch activityMatch windowReplayMatch
      levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
      auditMatch agreement

theorem ay_bpsc_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (phaseHint : Prop) :
    guard ->
    agreement ->
    phaseHint ->
    ay_bpsc_accepted_hint guard agreement phaseHint :=
  fun guardH agreementH hintH =>
    ay_bpsc_conj_intro guard (ay_bpsc_conj agreement phaseHint)
      guardH
      (ay_bpsc_conj_intro agreement phaseHint agreementH hintH)

theorem ay_bpsc_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (phaseHint : Prop) :
    ay_bpsc_accepted_hint guard agreement phaseHint -> guard :=
  fun accepted =>
    ay_bpsc_conj_left guard (ay_bpsc_conj agreement phaseHint) accepted

theorem ay_bpsc_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (phaseHint : Prop) :
    ay_bpsc_accepted_hint guard agreement phaseHint -> agreement :=
  fun accepted =>
    ay_bpsc_conj_left agreement phaseHint
      (ay_bpsc_conj_right guard (ay_bpsc_conj agreement phaseHint)
        accepted)

theorem ay_bpsc_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (phaseHint : Prop) :
    ay_bpsc_accepted_hint guard agreement phaseHint -> phaseHint :=
  fun accepted =>
    ay_bpsc_conj_right agreement phaseHint
      (ay_bpsc_conj_right guard (ay_bpsc_conj agreement phaseHint)
        accepted)

theorem ay_bpsc_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bpsc_public_report acceptedEvidence
      (ay_bpsc_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bpsc_conj_intro acceptedEvidence
      (ay_bpsc_conj (ay_bpsc_outcome model conflict) formula)
      acceptedH
      (ay_bpsc_conj_intro (ay_bpsc_outcome model conflict) formula
        (ay_bpsc_disj_left model conflict modelH)
        formulaH)

theorem ay_bpsc_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bpsc_public_report acceptedEvidence
      (ay_bpsc_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bpsc_conj_intro acceptedEvidence
      (ay_bpsc_conj (ay_bpsc_outcome model conflict) formula)
      acceptedH
      (ay_bpsc_conj_intro (ay_bpsc_outcome model conflict) formula
        (ay_bpsc_disj_right model conflict conflictH)
        formulaH)

theorem ay_bpsc_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bpsc_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bpsc_conj_left acceptedEvidence
      (ay_bpsc_conj outcome formula) public

theorem ay_bpsc_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bpsc_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bpsc_conj_intro hintCert public hintH publicH

theorem ay_bpsc_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bpsc_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpsc_conj_right hintCert public accepted

theorem ay_bpsc_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bpsc_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bpsc_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bpsc_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpsc_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bpsc_conj_left fallbackPublic diagnostic noClaim

theorem ay_bpsc_phase_cache_drift_no_claim
    (phaseCacheDrift : Prop) (fallbackPublic : Prop) :
    phaseCacheDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim phaseCacheDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro phaseCacheDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsc_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsc_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsc_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsc_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsc_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bpsc_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bpsc_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bpsc_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpsc_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bpsc_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsc_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bpsc_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpsc_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bpsc_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpsc_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bpsc_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bpsc_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (phaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpsc_accepted_hint guard agreement phaseHint ->
    model ->
    formula ->
    ay_bpsc_accepted_report
      (ay_bpsc_accepted_hint guard agreement phaseHint)
      (ay_bpsc_public_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        (ay_bpsc_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bpsc_accepted_report_intro
      (ay_bpsc_accepted_hint guard agreement phaseHint)
      (ay_bpsc_public_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        (ay_bpsc_outcome model conflict) formula)
      accepted
      (ay_bpsc_public_sat_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bpsc_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (phaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpsc_accepted_hint guard agreement phaseHint ->
    conflict ->
    formula ->
    ay_bpsc_accepted_report
      (ay_bpsc_accepted_hint guard agreement phaseHint)
      (ay_bpsc_public_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        (ay_bpsc_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bpsc_accepted_report_intro
      (ay_bpsc_accepted_hint guard agreement phaseHint)
      (ay_bpsc_public_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        (ay_bpsc_outcome model conflict) formula)
      accepted
      (ay_bpsc_public_unsat_report
        (ay_bpsc_accepted_hint guard agreement phaseHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bpsc_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bpsc_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpsc_accepted_report_public hintCert public accepted

theorem ay_bpsc_phase_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bpsc_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bpsc_equisat_forward beforeHint afterHint equisat beforeH

-- Refined phase-saving polarity cache guard for sequential-main SAT-COMP
-- branching. Cache use is search-control only when polarity cache, assignment
-- epoch, domain, replay, fallback policy, build, validator, and audit evidence
-- agree with the checked public result.

def ay_pscg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pscg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pscg_conj (before -> after) (after -> before)

def ay_pscg_guard
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (polarityCacheDigest ->
      assignmentEpochLedger ->
      variableDomainManifest ->
      decisionLevelReplay ->
      tieBreakFallbackPolicy ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pscg_agreement
    (cacheMatch : Prop)
    (assignmentEpochMatch : Prop)
    (domainMatch : Prop)
    (replayMatch : Prop)
    (fallbackPolicyMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_pscg_guard cacheMatch assignmentEpochMatch domainMatch replayMatch
    fallbackPolicyMatch buildMatch validatorAccepts auditMatch

def ay_pscg_accepted_cache_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_pscg_conj guardEvidence
    (ay_pscg_conj agreementEvidence searchControlHint)

def ay_pscg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_pscg_conj acceptedEvidence (ay_pscg_conj outcome formulaTruth)

def ay_pscg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_pscg_conj diagnostic fallbackPublic

theorem ay_pscg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_pscg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pscg_conj_left (left : Prop) (right : Prop) :
    ay_pscg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pscg_conj_right (left : Prop) (right : Prop) :
    ay_pscg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pscg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_pscg_equisat before after :=
  fun forward backward =>
    ay_pscg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pscg_equisat_forward (before : Prop) (after : Prop) :
    ay_pscg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pscg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pscg_equisat_backward (before : Prop) (after : Prop) :
    ay_pscg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pscg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pscg_guard_intro
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    polarityCacheDigest ->
    assignmentEpochLedger ->
    variableDomainManifest ->
    decisionLevelReplay ->
    tieBreakFallbackPolicy ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript :=
  fun cacheH epochH domainH replayH policyH buildH validatorH auditH
      result make =>
    make cacheH epochH domainH replayH policyH buildH validatorH auditH

theorem ay_pscg_guard_cache
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    polarityCacheDigest :=
  fun guard =>
    guard polarityCacheDigest
      (fun cacheH _epochH _domainH _replayH _policyH _buildH _validatorH
          _auditH => cacheH)

theorem ay_pscg_guard_assignment_epoch
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    assignmentEpochLedger :=
  fun guard =>
    guard assignmentEpochLedger
      (fun _cacheH epochH _domainH _replayH _policyH _buildH _validatorH
          _auditH => epochH)

theorem ay_pscg_guard_domain
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _cacheH _epochH domainH _replayH _policyH _buildH _validatorH
          _auditH => domainH)

theorem ay_pscg_guard_replay
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    decisionLevelReplay :=
  fun guard =>
    guard decisionLevelReplay
      (fun _cacheH _epochH _domainH replayH _policyH _buildH _validatorH
          _auditH => replayH)

theorem ay_pscg_guard_policy
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    tieBreakFallbackPolicy :=
  fun guard =>
    guard tieBreakFallbackPolicy
      (fun _cacheH _epochH _domainH _replayH policyH _buildH _validatorH
          _auditH => policyH)

theorem ay_pscg_guard_build
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _cacheH _epochH _domainH _replayH _policyH buildH _validatorH
          _auditH => buildH)

theorem ay_pscg_guard_validator
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _cacheH _epochH _domainH _replayH _policyH _buildH validatorH
          _auditH => validatorH)

theorem ay_pscg_guard_audit
    (polarityCacheDigest : Prop)
    (assignmentEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (decisionLevelReplay : Prop)
    (tieBreakFallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_pscg_guard polarityCacheDigest assignmentEpochLedger
      variableDomainManifest decisionLevelReplay tieBreakFallbackPolicy
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _cacheH _epochH _domainH _replayH _policyH _buildH _validatorH
          auditH => auditH)

theorem ay_pscg_agreement_intro
    (cacheMatch : Prop)
    (assignmentEpochMatch : Prop)
    (domainMatch : Prop)
    (replayMatch : Prop)
    (fallbackPolicyMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    cacheMatch ->
    assignmentEpochMatch ->
    domainMatch ->
    replayMatch ->
    fallbackPolicyMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_pscg_agreement cacheMatch assignmentEpochMatch domainMatch replayMatch
      fallbackPolicyMatch buildMatch validatorAccepts auditMatch :=
  ay_pscg_guard_intro cacheMatch assignmentEpochMatch domainMatch replayMatch
    fallbackPolicyMatch buildMatch validatorAccepts auditMatch

theorem ay_pscg_accepted_cache_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_pscg_conj_intro guardEvidence
      (ay_pscg_conj agreementEvidence searchControlHint)
      guardH
      (ay_pscg_conj_intro agreementEvidence searchControlHint agreementH
        hintH)

theorem ay_pscg_accepted_cache_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_pscg_conj_left guardEvidence
      (ay_pscg_conj agreementEvidence searchControlHint) accepted

theorem ay_pscg_accepted_cache_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_pscg_conj_left agreementEvidence searchControlHint
      (ay_pscg_conj_right guardEvidence
        (ay_pscg_conj agreementEvidence searchControlHint) accepted)

theorem ay_pscg_accepted_cache_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_pscg_conj_right agreementEvidence searchControlHint
      (ay_pscg_conj_right guardEvidence
        (ay_pscg_conj agreementEvidence searchControlHint) accepted)

theorem ay_pscg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pscg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pscg_conj_intro acceptedEvidence
      (ay_pscg_conj outcome formulaTruth)
      acceptedH (ay_pscg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pscg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_pscg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pscg_conj_left acceptedEvidence (ay_pscg_conj outcome formulaTruth)
      report

theorem ay_pscg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_pscg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pscg_conj_right outcome formulaTruth
      (ay_pscg_conj_right acceptedEvidence
        (ay_pscg_conj outcome formulaTruth) report)

theorem ay_pscg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_pscg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_pscg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_pscg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_pscg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_pscg_conj_right diagnostic fallbackPublic noClaim

theorem ay_pscg_stale_cache_no_claim
    (staleCache : Prop)
    (fallbackPublic : Prop) :
    staleCache -> fallbackPublic ->
    ay_pscg_no_claim staleCache fallbackPublic :=
  ay_pscg_no_claim_intro staleCache fallbackPublic

theorem ay_pscg_assignment_epoch_mismatch_no_claim
    (assignmentEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    assignmentEpochMismatch -> fallbackPublic ->
    ay_pscg_no_claim assignmentEpochMismatch fallbackPublic :=
  ay_pscg_no_claim_intro assignmentEpochMismatch fallbackPublic

theorem ay_pscg_domain_mismatch_no_claim
    (domainMismatch : Prop)
    (fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_pscg_no_claim domainMismatch fallbackPublic :=
  ay_pscg_no_claim_intro domainMismatch fallbackPublic

theorem ay_pscg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_pscg_no_claim replayMismatch fallbackPublic :=
  ay_pscg_no_claim_intro replayMismatch fallbackPublic

theorem ay_pscg_policy_mismatch_no_claim
    (policyMismatch : Prop)
    (fallbackPublic : Prop) :
    policyMismatch -> fallbackPublic ->
    ay_pscg_no_claim policyMismatch fallbackPublic :=
  ay_pscg_no_claim_intro policyMismatch fallbackPublic

theorem ay_pscg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_pscg_no_claim buildMismatch fallbackPublic :=
  ay_pscg_no_claim_intro buildMismatch fallbackPublic

theorem ay_pscg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_pscg_no_claim validatorRejection fallbackPublic :=
  ay_pscg_no_claim_intro validatorRejection fallbackPublic

theorem ay_pscg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_pscg_no_claim auditMismatch fallbackPublic :=
  ay_pscg_no_claim_intro auditMismatch fallbackPublic

theorem ay_pscg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_pscg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_pscg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_pscg_failed_cache_guard_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_pscg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_pscg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_pscg_accepted_cache_is_search_control
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  ay_pscg_accepted_cache_hint_hint guardEvidence agreementEvidence
    searchControlHint

theorem ay_pscg_accepted_cache_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_pscg_accepted_cache_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      (ay_pscg_accepted_cache_hint_agreement guardEvidence agreementEvidence
        searchControlHint accepted)
      outcomeH
      truthH

theorem ay_pscg_accepted_cache_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_pscg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_pscg_public_report_intro guardEvidence satOutcome satTruth
      (ay_pscg_accepted_cache_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      satH
      truthH

theorem ay_pscg_accepted_cache_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_pscg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_pscg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_pscg_accepted_cache_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      unsatH
      truthH

theorem ay_pscg_phase_cache_preserves_formula_truth
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_pscg_accepted_cache_hint guardEvidence agreementEvidence
      searchControlHint ->
    (searchControlHint -> formulaBefore -> formulaAfter) ->
    (searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_pscg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_pscg_equisat_intro formulaBefore formulaAfter
      (forward (ay_pscg_accepted_cache_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))
      (backward (ay_pscg_accepted_cache_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))
