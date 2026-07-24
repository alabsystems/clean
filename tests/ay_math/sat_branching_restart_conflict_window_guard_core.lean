-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart conflict-window guard soundness skeleton for ay SAT solving.
-- Conflict-window histograms and phase-saving hints may guide branching and
-- restart policy only when conflict-window ledgers, decision levels,
-- implication graph slices, restart epochs, fallback baselines, solver builds,
-- validator gates, and audit evidence agree.

def ay_brcw_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brcw_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brcw_equisat (before : Prop) (after : Prop) :=
  ay_brcw_conj (before -> after) (after -> before)

def ay_brcw_window_guard
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (conflictWindowLedger -> decisionLevelSnapshot ->
      implicationGraphSlice -> restartEpoch -> fallbackBaseline ->
      solverBuildEvidence -> validatorGate -> auditEvidence -> result) ->
    result

def ay_brcw_guard_agreement
    (windowMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_brcw_window_guard windowMatch levelMatch graphSliceMatch epochMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brcw_accepted_hint
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :=
  ay_brcw_conj guard (ay_brcw_conj agreement restartPhaseHint)

def ay_brcw_outcome (model : Prop) (conflict : Prop) :=
  ay_brcw_disj model conflict

def ay_brcw_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_brcw_conj acceptedEvidence (ay_brcw_conj outcome formula)

def ay_brcw_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_brcw_conj hintCert public

def ay_brcw_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_brcw_conj fallbackPublic diagnostic

theorem ay_brcw_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_brcw_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brcw_conj_left
    (left : Prop) (right : Prop) :
    ay_brcw_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brcw_conj_right
    (left : Prop) (right : Prop) :
    ay_brcw_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brcw_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_brcw_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brcw_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_brcw_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brcw_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_brcw_equisat before after :=
  fun forward backward =>
    ay_brcw_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brcw_equisat_forward
    (before : Prop) (after : Prop) :
    ay_brcw_equisat before after -> before -> after :=
  fun equisat =>
    ay_brcw_conj_left (before -> after) (after -> before) equisat

theorem ay_brcw_equisat_backward
    (before : Prop) (after : Prop) :
    ay_brcw_equisat before after -> after -> before :=
  fun equisat =>
    ay_brcw_conj_right (before -> after) (after -> before) equisat

theorem ay_brcw_window_guard_intro
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    conflictWindowLedger ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    restartEpoch ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence :=
  fun windowH levelH graphH epochH fallbackH buildH validatorH auditH
      result build =>
    build windowH levelH graphH epochH fallbackH buildH validatorH auditH

theorem ay_brcw_window_guard_ledger
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    conflictWindowLedger :=
  fun guard =>
    guard conflictWindowLedger
      (fun windowH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_brcw_window_guard_level
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _windowH levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_brcw_window_guard_graph
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _windowH _levelH graphH _epochH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_brcw_window_guard_epoch
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    restartEpoch :=
  fun guard =>
    guard restartEpoch
      (fun _windowH _levelH _graphH epochH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_brcw_window_guard_fallback
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _windowH _levelH _graphH _epochH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brcw_window_guard_build
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _windowH _levelH _graphH _epochH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brcw_window_guard_validator
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _windowH _levelH _graphH _epochH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brcw_window_guard_audit
    (conflictWindowLedger : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (restartEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brcw_window_guard conflictWindowLedger decisionLevelSnapshot
      implicationGraphSlice restartEpoch fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _windowH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brcw_guard_agreement_intro
    (windowMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    windowMatch ->
    levelMatch ->
    graphSliceMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brcw_guard_agreement windowMatch levelMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun windowH levelH graphH epochH fallbackH buildH validatorH auditH =>
    ay_brcw_window_guard_intro windowMatch levelMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      windowH levelH graphH epochH fallbackH buildH validatorH auditH

theorem ay_brcw_guard_agreement_ledger
    (windowMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_brcw_guard_agreement windowMatch levelMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    windowMatch :=
  fun agreement =>
    ay_brcw_window_guard_ledger windowMatch levelMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_brcw_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    guard ->
    agreement ->
    restartPhaseHint ->
    ay_brcw_accepted_hint guard agreement restartPhaseHint :=
  fun guardH agreementH hintH =>
    ay_brcw_conj_intro guard (ay_brcw_conj agreement restartPhaseHint)
      guardH
      (ay_brcw_conj_intro agreement restartPhaseHint agreementH hintH)

theorem ay_brcw_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brcw_accepted_hint guard agreement restartPhaseHint -> guard :=
  fun accepted =>
    ay_brcw_conj_left guard (ay_brcw_conj agreement restartPhaseHint)
      accepted

theorem ay_brcw_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brcw_accepted_hint guard agreement restartPhaseHint -> agreement :=
  fun accepted =>
    ay_brcw_conj_left agreement restartPhaseHint
      (ay_brcw_conj_right guard (ay_brcw_conj agreement restartPhaseHint)
        accepted)

theorem ay_brcw_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop) :
    ay_brcw_accepted_hint guard agreement restartPhaseHint ->
    restartPhaseHint :=
  fun accepted =>
    ay_brcw_conj_right agreement restartPhaseHint
      (ay_brcw_conj_right guard (ay_brcw_conj agreement restartPhaseHint)
        accepted)

theorem ay_brcw_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_brcw_public_report acceptedEvidence
      (ay_brcw_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_brcw_conj_intro acceptedEvidence
      (ay_brcw_conj (ay_brcw_outcome model conflict) formula)
      acceptedH
      (ay_brcw_conj_intro (ay_brcw_outcome model conflict) formula
        (ay_brcw_disj_left model conflict modelH)
        formulaH)

theorem ay_brcw_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_brcw_public_report acceptedEvidence
      (ay_brcw_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_brcw_conj_intro acceptedEvidence
      (ay_brcw_conj (ay_brcw_outcome model conflict) formula)
      acceptedH
      (ay_brcw_conj_intro (ay_brcw_outcome model conflict) formula
        (ay_brcw_disj_right model conflict conflictH)
        formulaH)

theorem ay_brcw_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_brcw_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_brcw_conj_left acceptedEvidence
      (ay_brcw_conj outcome formula) public

theorem ay_brcw_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_brcw_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_brcw_conj_intro hintCert public hintH publicH

theorem ay_brcw_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_brcw_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brcw_conj_right hintCert public accepted

theorem ay_brcw_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_brcw_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_brcw_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brcw_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brcw_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brcw_conj_left fallbackPublic diagnostic noClaim

theorem ay_brcw_window_drift_no_claim
    (windowDrift : Prop) (fallbackPublic : Prop) :
    windowDrift ->
    fallbackPublic ->
    ay_brcw_no_claim windowDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro windowDrift fallbackPublic fallbackH diagnosticH

theorem ay_brcw_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_brcw_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_brcw_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_brcw_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_brcw_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_brcw_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_brcw_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brcw_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_brcw_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_brcw_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_brcw_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_brcw_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_brcw_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brcw_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brcw_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_brcw_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brcw_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_brcw_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_brcw_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brcw_accepted_hint guard agreement restartPhaseHint ->
    model ->
    formula ->
    ay_brcw_accepted_report
      (ay_brcw_accepted_hint guard agreement restartPhaseHint)
      (ay_brcw_public_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        (ay_brcw_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_brcw_accepted_report_intro
      (ay_brcw_accepted_hint guard agreement restartPhaseHint)
      (ay_brcw_public_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        (ay_brcw_outcome model conflict) formula)
      accepted
      (ay_brcw_public_sat_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        model conflict formula accepted modelH formulaH)

theorem ay_brcw_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (restartPhaseHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brcw_accepted_hint guard agreement restartPhaseHint ->
    conflict ->
    formula ->
    ay_brcw_accepted_report
      (ay_brcw_accepted_hint guard agreement restartPhaseHint)
      (ay_brcw_public_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        (ay_brcw_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_brcw_accepted_report_intro
      (ay_brcw_accepted_hint guard agreement restartPhaseHint)
      (ay_brcw_public_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        (ay_brcw_outcome model conflict) formula)
      accepted
      (ay_brcw_public_unsat_report
        (ay_brcw_accepted_hint guard agreement restartPhaseHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_brcw_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_brcw_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brcw_accepted_report_public hintCert public accepted

theorem ay_brcw_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_brcw_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_brcw_equisat_forward beforeHint afterHint equisat beforeH
