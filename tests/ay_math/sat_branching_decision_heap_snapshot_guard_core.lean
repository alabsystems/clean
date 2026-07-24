-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded decision-heap snapshot guard soundness skeleton for ay SAT solving.
-- Decision heap snapshots and lazy heap repair hints may guide branching only
-- when heap ledgers, repair evidence, variable activity, conflict-window
-- replay, decision levels, implication graph slices, fallback baselines,
-- solver builds, validator gates, and audit evidence agree.

def ay_bdhs_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bdhs_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bdhs_equisat (before : Prop) (after : Prop) :=
  ay_bdhs_conj (before -> after) (after -> before)

def ay_bdhs_heap_guard
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (heapSnapshotLedger -> lazyRepairEvidence -> variableActivityLedger ->
      conflictWindowReplay -> decisionLevelSnapshot -> implicationGraphSlice ->
      fallbackBaseline -> solverBuildEvidence -> validatorGate ->
      auditEvidence -> result) ->
    result

def ay_bdhs_guard_agreement
    (heapMatch : Prop) (repairMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bdhs_heap_guard heapMatch repairMatch activityMatch windowReplayMatch
    levelMatch graphSliceMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bdhs_accepted_hint
    (guard : Prop) (agreement : Prop) (heapHint : Prop) :=
  ay_bdhs_conj guard (ay_bdhs_conj agreement heapHint)

def ay_bdhs_outcome (model : Prop) (conflict : Prop) :=
  ay_bdhs_disj model conflict

def ay_bdhs_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bdhs_conj acceptedEvidence (ay_bdhs_conj outcome formula)

def ay_bdhs_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bdhs_conj hintCert public

def ay_bdhs_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bdhs_conj fallbackPublic diagnostic

theorem ay_bdhs_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bdhs_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bdhs_conj_left
    (left : Prop) (right : Prop) :
    ay_bdhs_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bdhs_conj_right
    (left : Prop) (right : Prop) :
    ay_bdhs_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bdhs_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bdhs_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bdhs_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bdhs_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bdhs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bdhs_equisat before after :=
  fun forward backward =>
    ay_bdhs_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bdhs_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bdhs_equisat before after -> before -> after :=
  fun equisat =>
    ay_bdhs_conj_left (before -> after) (after -> before) equisat

theorem ay_bdhs_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bdhs_equisat before after -> after -> before :=
  fun equisat =>
    ay_bdhs_conj_right (before -> after) (after -> before) equisat

theorem ay_bdhs_heap_guard_intro
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    heapSnapshotLedger ->
    lazyRepairEvidence ->
    variableActivityLedger ->
    conflictWindowReplay ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence :=
  fun heapH repairH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH result build =>
    build heapH repairH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH

theorem ay_bdhs_heap_guard_heap
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    heapSnapshotLedger :=
  fun guard =>
    guard heapSnapshotLedger
      (fun heapH _repairH _activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => heapH)

theorem ay_bdhs_heap_guard_repair
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    lazyRepairEvidence :=
  fun guard =>
    guard lazyRepairEvidence
      (fun _heapH repairH _activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => repairH)

theorem ay_bdhs_heap_guard_activity
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    variableActivityLedger :=
  fun guard =>
    guard variableActivityLedger
      (fun _heapH _repairH activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bdhs_heap_guard_window
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _heapH _repairH _activityH windowH _levelH _graphH _fallbackH
          _buildH _validatorH _auditH => windowH)

theorem ay_bdhs_heap_guard_level
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _heapH _repairH _activityH _windowH levelH _graphH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_bdhs_heap_guard_graph
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _heapH _repairH _activityH _windowH _levelH graphH _fallbackH
          _buildH _validatorH _auditH => graphH)

theorem ay_bdhs_heap_guard_fallback
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _heapH _repairH _activityH _windowH _levelH _graphH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bdhs_heap_guard_build
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _heapH _repairH _activityH _windowH _levelH _graphH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bdhs_heap_guard_validator
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _heapH _repairH _activityH _windowH _levelH _graphH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bdhs_heap_guard_audit
    (heapSnapshotLedger : Prop) (lazyRepairEvidence : Prop)
    (variableActivityLedger : Prop) (conflictWindowReplay : Prop)
    (decisionLevelSnapshot : Prop) (implicationGraphSlice : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bdhs_heap_guard heapSnapshotLedger lazyRepairEvidence
      variableActivityLedger conflictWindowReplay decisionLevelSnapshot
      implicationGraphSlice fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _heapH _repairH _activityH _windowH _levelH _graphH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bdhs_guard_agreement_intro
    (heapMatch : Prop) (repairMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    heapMatch ->
    repairMatch ->
    activityMatch ->
    windowReplayMatch ->
    levelMatch ->
    graphSliceMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bdhs_guard_agreement heapMatch repairMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  fun heapH repairH activityH windowH levelH graphH fallbackH buildH
      validatorH auditH =>
    ay_bdhs_heap_guard_intro heapMatch repairMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch heapH repairH activityH windowH levelH
      graphH fallbackH buildH validatorH auditH

theorem ay_bdhs_guard_agreement_heap
    (heapMatch : Prop) (repairMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bdhs_guard_agreement heapMatch repairMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch ->
    heapMatch :=
  fun agreement =>
    ay_bdhs_heap_guard_heap heapMatch repairMatch activityMatch
      windowReplayMatch levelMatch graphSliceMatch fallbackMatch buildMatch
      validatorAccepts auditMatch agreement

theorem ay_bdhs_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (heapHint : Prop) :
    guard ->
    agreement ->
    heapHint ->
    ay_bdhs_accepted_hint guard agreement heapHint :=
  fun guardH agreementH hintH =>
    ay_bdhs_conj_intro guard (ay_bdhs_conj agreement heapHint)
      guardH
      (ay_bdhs_conj_intro agreement heapHint agreementH hintH)

theorem ay_bdhs_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (heapHint : Prop) :
    ay_bdhs_accepted_hint guard agreement heapHint -> guard :=
  fun accepted =>
    ay_bdhs_conj_left guard (ay_bdhs_conj agreement heapHint) accepted

theorem ay_bdhs_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (heapHint : Prop) :
    ay_bdhs_accepted_hint guard agreement heapHint -> agreement :=
  fun accepted =>
    ay_bdhs_conj_left agreement heapHint
      (ay_bdhs_conj_right guard (ay_bdhs_conj agreement heapHint)
        accepted)

theorem ay_bdhs_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (heapHint : Prop) :
    ay_bdhs_accepted_hint guard agreement heapHint -> heapHint :=
  fun accepted =>
    ay_bdhs_conj_right agreement heapHint
      (ay_bdhs_conj_right guard (ay_bdhs_conj agreement heapHint)
        accepted)

theorem ay_bdhs_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bdhs_public_report acceptedEvidence
      (ay_bdhs_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bdhs_conj_intro acceptedEvidence
      (ay_bdhs_conj (ay_bdhs_outcome model conflict) formula)
      acceptedH
      (ay_bdhs_conj_intro (ay_bdhs_outcome model conflict) formula
        (ay_bdhs_disj_left model conflict modelH)
        formulaH)

theorem ay_bdhs_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bdhs_public_report acceptedEvidence
      (ay_bdhs_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bdhs_conj_intro acceptedEvidence
      (ay_bdhs_conj (ay_bdhs_outcome model conflict) formula)
      acceptedH
      (ay_bdhs_conj_intro (ay_bdhs_outcome model conflict) formula
        (ay_bdhs_disj_right model conflict conflictH)
        formulaH)

theorem ay_bdhs_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bdhs_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bdhs_conj_left acceptedEvidence
      (ay_bdhs_conj outcome formula) public

theorem ay_bdhs_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bdhs_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bdhs_conj_intro hintCert public hintH publicH

theorem ay_bdhs_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bdhs_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bdhs_conj_right hintCert public accepted

theorem ay_bdhs_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bdhs_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bdhs_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bdhs_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bdhs_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bdhs_conj_left fallbackPublic diagnostic noClaim

theorem ay_bdhs_heap_drift_no_claim
    (heapDrift : Prop) (fallbackPublic : Prop) :
    heapDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim heapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro heapDrift fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_missing_repair_no_claim
    (missingRepair : Prop) (fallbackPublic : Prop) :
    missingRepair ->
    fallbackPublic ->
    ay_bdhs_no_claim missingRepair fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro missingRepair fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bdhs_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bdhs_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bdhs_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bdhs_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bdhs_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bdhs_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bdhs_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bdhs_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bdhs_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bdhs_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bdhs_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bdhs_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (heapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bdhs_accepted_hint guard agreement heapHint ->
    model ->
    formula ->
    ay_bdhs_accepted_report
      (ay_bdhs_accepted_hint guard agreement heapHint)
      (ay_bdhs_public_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        (ay_bdhs_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bdhs_accepted_report_intro
      (ay_bdhs_accepted_hint guard agreement heapHint)
      (ay_bdhs_public_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        (ay_bdhs_outcome model conflict) formula)
      accepted
      (ay_bdhs_public_sat_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bdhs_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (heapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bdhs_accepted_hint guard agreement heapHint ->
    conflict ->
    formula ->
    ay_bdhs_accepted_report
      (ay_bdhs_accepted_hint guard agreement heapHint)
      (ay_bdhs_public_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        (ay_bdhs_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bdhs_accepted_report_intro
      (ay_bdhs_accepted_hint guard agreement heapHint)
      (ay_bdhs_public_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        (ay_bdhs_outcome model conflict) formula)
      accepted
      (ay_bdhs_public_unsat_report
        (ay_bdhs_accepted_hint guard agreement heapHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bdhs_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bdhs_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bdhs_accepted_report_public hintCert public accepted

theorem ay_bdhs_heap_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bdhs_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bdhs_equisat_forward beforeHint afterHint equisat beforeH
