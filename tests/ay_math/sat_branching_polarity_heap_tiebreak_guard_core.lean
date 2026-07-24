-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded polarity-aware heap tie-break guard soundness skeleton for ay SAT
-- solving. Polarity-aware heap tie-breaks may guide branching only when
-- polarity ledgers, heap snapshots, variable/clause activity, conflict-window
-- replay, fallback baselines, solver builds, validator gates, and audit
-- evidence agree.

def ay_bpht_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpht_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bpht_equisat (before : Prop) (after : Prop) :=
  ay_bpht_conj (before -> after) (after -> before)

def ay_bpht_tiebreak_guard
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (polarityLedger -> heapSnapshotLedger -> activityLedger ->
      conflictWindowReplay -> fallbackBaseline -> solverBuildEvidence ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_bpht_guard_agreement
    (polarityMatch : Prop) (heapMatch : Prop)
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_bpht_tiebreak_guard polarityMatch heapMatch activityMatch
    windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bpht_accepted_hint
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop) :=
  ay_bpht_conj guard (ay_bpht_conj agreement polarityHeapHint)

def ay_bpht_outcome (model : Prop) (conflict : Prop) :=
  ay_bpht_disj model conflict

def ay_bpht_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_bpht_conj acceptedEvidence (ay_bpht_conj outcome formula)

def ay_bpht_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bpht_conj hintCert public

def ay_bpht_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bpht_conj fallbackPublic diagnostic

theorem ay_bpht_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bpht_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bpht_conj_left
    (left : Prop) (right : Prop) :
    ay_bpht_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bpht_conj_right
    (left : Prop) (right : Prop) :
    ay_bpht_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bpht_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bpht_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bpht_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bpht_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bpht_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bpht_equisat before after :=
  fun forward backward =>
    ay_bpht_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bpht_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bpht_equisat before after -> before -> after :=
  fun equisat =>
    ay_bpht_conj_left (before -> after) (after -> before) equisat

theorem ay_bpht_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bpht_equisat before after -> after -> before :=
  fun equisat =>
    ay_bpht_conj_right (before -> after) (after -> before) equisat

theorem ay_bpht_tiebreak_guard_intro
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    polarityLedger ->
    heapSnapshotLedger ->
    activityLedger ->
    conflictWindowReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence :=
  fun polarityH heapH activityH windowH fallbackH buildH validatorH auditH
      result build =>
    build polarityH heapH activityH windowH fallbackH buildH validatorH auditH

theorem ay_bpht_tiebreak_guard_polarity
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    polarityLedger :=
  fun guard =>
    guard polarityLedger
      (fun polarityH _heapH _activityH _windowH _fallbackH _buildH
          _validatorH _auditH => polarityH)

theorem ay_bpht_tiebreak_guard_heap
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    heapSnapshotLedger :=
  fun guard =>
    guard heapSnapshotLedger
      (fun _polarityH heapH _activityH _windowH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_bpht_tiebreak_guard_activity
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    activityLedger :=
  fun guard =>
    guard activityLedger
      (fun _polarityH _heapH activityH _windowH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bpht_tiebreak_guard_window
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _polarityH _heapH _activityH windowH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_bpht_tiebreak_guard_fallback
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _polarityH _heapH _activityH _windowH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bpht_tiebreak_guard_build
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _polarityH _heapH _activityH _windowH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bpht_tiebreak_guard_validator
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _polarityH _heapH _activityH _windowH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bpht_tiebreak_guard_audit
    (polarityLedger : Prop) (heapSnapshotLedger : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bpht_tiebreak_guard polarityLedger heapSnapshotLedger
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _polarityH _heapH _activityH _windowH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bpht_guard_agreement_intro
    (polarityMatch : Prop) (heapMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) (auditMatch : Prop) :
    polarityMatch ->
    heapMatch ->
    activityMatch ->
    windowReplayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bpht_guard_agreement polarityMatch heapMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun polarityH heapH activityH windowH fallbackH buildH validatorH auditH =>
    ay_bpht_tiebreak_guard_intro polarityMatch heapMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch
      polarityH heapH activityH windowH fallbackH buildH validatorH auditH

theorem ay_bpht_guard_agreement_polarity
    (polarityMatch : Prop) (heapMatch : Prop) (activityMatch : Prop)
    (windowReplayMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_bpht_guard_agreement polarityMatch heapMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    polarityMatch :=
  fun agreement =>
    ay_bpht_tiebreak_guard_polarity polarityMatch heapMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_bpht_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop) :
    guard ->
    agreement ->
    polarityHeapHint ->
    ay_bpht_accepted_hint guard agreement polarityHeapHint :=
  fun guardH agreementH hintH =>
    ay_bpht_conj_intro guard (ay_bpht_conj agreement polarityHeapHint)
      guardH
      (ay_bpht_conj_intro agreement polarityHeapHint agreementH hintH)

theorem ay_bpht_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop) :
    ay_bpht_accepted_hint guard agreement polarityHeapHint -> guard :=
  fun accepted =>
    ay_bpht_conj_left guard (ay_bpht_conj agreement polarityHeapHint)
      accepted

theorem ay_bpht_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop) :
    ay_bpht_accepted_hint guard agreement polarityHeapHint -> agreement :=
  fun accepted =>
    ay_bpht_conj_left agreement polarityHeapHint
      (ay_bpht_conj_right guard (ay_bpht_conj agreement polarityHeapHint)
        accepted)

theorem ay_bpht_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop) :
    ay_bpht_accepted_hint guard agreement polarityHeapHint ->
    polarityHeapHint :=
  fun accepted =>
    ay_bpht_conj_right agreement polarityHeapHint
      (ay_bpht_conj_right guard (ay_bpht_conj agreement polarityHeapHint)
        accepted)

theorem ay_bpht_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_bpht_public_report acceptedEvidence
      (ay_bpht_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_bpht_conj_intro acceptedEvidence
      (ay_bpht_conj (ay_bpht_outcome model conflict) formula)
      acceptedH
      (ay_bpht_conj_intro (ay_bpht_outcome model conflict) formula
        (ay_bpht_disj_left model conflict modelH)
        formulaH)

theorem ay_bpht_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_bpht_public_report acceptedEvidence
      (ay_bpht_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_bpht_conj_intro acceptedEvidence
      (ay_bpht_conj (ay_bpht_outcome model conflict) formula)
      acceptedH
      (ay_bpht_conj_intro (ay_bpht_outcome model conflict) formula
        (ay_bpht_disj_right model conflict conflictH)
        formulaH)

theorem ay_bpht_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_bpht_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_bpht_conj_left acceptedEvidence
      (ay_bpht_conj outcome formula) public

theorem ay_bpht_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bpht_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bpht_conj_intro hintCert public hintH publicH

theorem ay_bpht_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bpht_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpht_conj_right hintCert public accepted

theorem ay_bpht_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bpht_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bpht_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bpht_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpht_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bpht_conj_left fallbackPublic diagnostic noClaim

theorem ay_bpht_polarity_drift_no_claim
    (polarityDrift : Prop) (fallbackPublic : Prop) :
    polarityDrift ->
    fallbackPublic ->
    ay_bpht_no_claim polarityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro polarityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpht_heap_drift_no_claim
    (heapDrift : Prop) (fallbackPublic : Prop) :
    heapDrift ->
    fallbackPublic ->
    ay_bpht_no_claim heapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro heapDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpht_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_bpht_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpht_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_bpht_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bpht_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bpht_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bpht_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bpht_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bpht_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bpht_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bpht_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bpht_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bpht_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bpht_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bpht_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bpht_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bpht_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpht_accepted_hint guard agreement polarityHeapHint ->
    model ->
    formula ->
    ay_bpht_accepted_report
      (ay_bpht_accepted_hint guard agreement polarityHeapHint)
      (ay_bpht_public_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        (ay_bpht_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bpht_accepted_report_intro
      (ay_bpht_accepted_hint guard agreement polarityHeapHint)
      (ay_bpht_public_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        (ay_bpht_outcome model conflict) formula)
      accepted
      (ay_bpht_public_sat_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        model conflict formula accepted modelH formulaH)

theorem ay_bpht_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (polarityHeapHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bpht_accepted_hint guard agreement polarityHeapHint ->
    conflict ->
    formula ->
    ay_bpht_accepted_report
      (ay_bpht_accepted_hint guard agreement polarityHeapHint)
      (ay_bpht_public_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        (ay_bpht_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bpht_accepted_report_intro
      (ay_bpht_accepted_hint guard agreement polarityHeapHint)
      (ay_bpht_public_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        (ay_bpht_outcome model conflict) formula)
      accepted
      (ay_bpht_public_unsat_report
        (ay_bpht_accepted_hint guard agreement polarityHeapHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_bpht_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bpht_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bpht_accepted_report_public hintCert public accepted

theorem ay_bpht_polarity_heap_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bpht_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bpht_equisat_forward beforeHint afterHint equisat beforeH
