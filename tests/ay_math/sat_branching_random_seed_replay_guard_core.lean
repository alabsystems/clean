-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded random-seed replay guard soundness skeleton for ay SAT solving.
-- Randomized or shuffled branching tie-breaks may guide search only when seed
-- ledgers, deterministic replay, variable/clause activity, conflict-window
-- replay, fallback baselines, solver builds, validator gates, and audit
-- evidence agree.

def ay_brsr_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brsr_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brsr_equisat (before : Prop) (after : Prop) :=
  ay_brsr_conj (before -> after) (after -> before)

def ay_brsr_seed_guard
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (seedLedger -> deterministicReplayEvidence -> activityLedger ->
      conflictWindowReplay -> fallbackBaseline -> solverBuildEvidence ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_brsr_guard_agreement
    (seedMatch : Prop) (replayMatch : Prop)
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_brsr_seed_guard seedMatch replayMatch activityMatch windowReplayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brsr_accepted_hint
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop) :=
  ay_brsr_conj guard (ay_brsr_conj agreement seedReplayHint)

def ay_brsr_outcome (model : Prop) (conflict : Prop) :=
  ay_brsr_disj model conflict

def ay_brsr_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_brsr_conj acceptedEvidence (ay_brsr_conj outcome formula)

def ay_brsr_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_brsr_conj hintCert public

def ay_brsr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_brsr_conj fallbackPublic diagnostic

theorem ay_brsr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_brsr_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brsr_conj_left
    (left : Prop) (right : Prop) :
    ay_brsr_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brsr_conj_right
    (left : Prop) (right : Prop) :
    ay_brsr_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brsr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_brsr_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brsr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_brsr_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brsr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_brsr_equisat before after :=
  fun forward backward =>
    ay_brsr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brsr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_brsr_equisat before after -> before -> after :=
  fun equisat =>
    ay_brsr_conj_left (before -> after) (after -> before) equisat

theorem ay_brsr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_brsr_equisat before after -> after -> before :=
  fun equisat =>
    ay_brsr_conj_right (before -> after) (after -> before) equisat

theorem ay_brsr_seed_guard_intro
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    seedLedger ->
    deterministicReplayEvidence ->
    activityLedger ->
    conflictWindowReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence :=
  fun seedH replayH activityH windowH fallbackH buildH validatorH auditH
      result build =>
    build seedH replayH activityH windowH fallbackH buildH validatorH auditH

theorem ay_brsr_seed_guard_seed
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    seedLedger :=
  fun guard =>
    guard seedLedger
      (fun seedH _replayH _activityH _windowH _fallbackH _buildH
          _validatorH _auditH => seedH)

theorem ay_brsr_seed_guard_replay
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    deterministicReplayEvidence :=
  fun guard =>
    guard deterministicReplayEvidence
      (fun _seedH replayH _activityH _windowH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_brsr_seed_guard_activity
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    activityLedger :=
  fun guard =>
    guard activityLedger
      (fun _seedH _replayH activityH _windowH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_brsr_seed_guard_window
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _seedH _replayH _activityH windowH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_brsr_seed_guard_fallback
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _seedH _replayH _activityH _windowH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brsr_seed_guard_build
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _seedH _replayH _activityH _windowH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brsr_seed_guard_validator
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _seedH _replayH _activityH _windowH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brsr_seed_guard_audit
    (seedLedger : Prop) (deterministicReplayEvidence : Prop)
    (activityLedger : Prop) (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop) (solverBuildEvidence : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brsr_seed_guard seedLedger deterministicReplayEvidence
      activityLedger conflictWindowReplay fallbackBaseline solverBuildEvidence
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _seedH _replayH _activityH _windowH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brsr_guard_agreement_intro
    (seedMatch : Prop) (replayMatch : Prop)
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    seedMatch ->
    replayMatch ->
    activityMatch ->
    windowReplayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brsr_guard_agreement seedMatch replayMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun seedH replayH activityH windowH fallbackH buildH validatorH auditH =>
    ay_brsr_seed_guard_intro seedMatch replayMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch
      seedH replayH activityH windowH fallbackH buildH validatorH auditH

theorem ay_brsr_guard_agreement_seed
    (seedMatch : Prop) (replayMatch : Prop)
    (activityMatch : Prop) (windowReplayMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_brsr_guard_agreement seedMatch replayMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    seedMatch :=
  fun agreement =>
    ay_brsr_seed_guard_seed seedMatch replayMatch activityMatch
      windowReplayMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_brsr_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop) :
    guard ->
    agreement ->
    seedReplayHint ->
    ay_brsr_accepted_hint guard agreement seedReplayHint :=
  fun guardH agreementH hintH =>
    ay_brsr_conj_intro guard (ay_brsr_conj agreement seedReplayHint)
      guardH
      (ay_brsr_conj_intro agreement seedReplayHint agreementH hintH)

theorem ay_brsr_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop) :
    ay_brsr_accepted_hint guard agreement seedReplayHint -> guard :=
  fun accepted =>
    ay_brsr_conj_left guard (ay_brsr_conj agreement seedReplayHint)
      accepted

theorem ay_brsr_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop) :
    ay_brsr_accepted_hint guard agreement seedReplayHint -> agreement :=
  fun accepted =>
    ay_brsr_conj_left agreement seedReplayHint
      (ay_brsr_conj_right guard (ay_brsr_conj agreement seedReplayHint)
        accepted)

theorem ay_brsr_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop) :
    ay_brsr_accepted_hint guard agreement seedReplayHint ->
    seedReplayHint :=
  fun accepted =>
    ay_brsr_conj_right agreement seedReplayHint
      (ay_brsr_conj_right guard (ay_brsr_conj agreement seedReplayHint)
        accepted)

theorem ay_brsr_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_brsr_public_report acceptedEvidence
      (ay_brsr_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_brsr_conj_intro acceptedEvidence
      (ay_brsr_conj (ay_brsr_outcome model conflict) formula)
      acceptedH
      (ay_brsr_conj_intro (ay_brsr_outcome model conflict) formula
        (ay_brsr_disj_left model conflict modelH)
        formulaH)

theorem ay_brsr_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_brsr_public_report acceptedEvidence
      (ay_brsr_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_brsr_conj_intro acceptedEvidence
      (ay_brsr_conj (ay_brsr_outcome model conflict) formula)
      acceptedH
      (ay_brsr_conj_intro (ay_brsr_outcome model conflict) formula
        (ay_brsr_disj_right model conflict conflictH)
        formulaH)

theorem ay_brsr_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_brsr_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_brsr_conj_left acceptedEvidence
      (ay_brsr_conj outcome formula) public

theorem ay_brsr_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_brsr_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_brsr_conj_intro hintCert public hintH publicH

theorem ay_brsr_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_brsr_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brsr_conj_right hintCert public accepted

theorem ay_brsr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_brsr_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_brsr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brsr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brsr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brsr_conj_left fallbackPublic diagnostic noClaim

theorem ay_brsr_seed_drift_no_claim
    (seedDrift : Prop) (fallbackPublic : Prop) :
    seedDrift ->
    fallbackPublic ->
    ay_brsr_no_claim seedDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro seedDrift fallbackPublic fallbackH diagnosticH

theorem ay_brsr_replay_drift_no_claim
    (replayDrift : Prop) (fallbackPublic : Prop) :
    replayDrift ->
    fallbackPublic ->
    ay_brsr_no_claim replayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro replayDrift fallbackPublic fallbackH diagnosticH

theorem ay_brsr_activity_drift_no_claim
    (activityDrift : Prop) (fallbackPublic : Prop) :
    activityDrift ->
    fallbackPublic ->
    ay_brsr_no_claim activityDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro activityDrift fallbackPublic fallbackH diagnosticH

theorem ay_brsr_window_replay_drift_no_claim
    (windowReplayDrift : Prop) (fallbackPublic : Prop) :
    windowReplayDrift ->
    fallbackPublic ->
    ay_brsr_no_claim windowReplayDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro windowReplayDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_brsr_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brsr_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_brsr_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_brsr_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_brsr_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_brsr_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_brsr_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brsr_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brsr_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_brsr_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brsr_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_brsr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_brsr_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brsr_accepted_hint guard agreement seedReplayHint ->
    model ->
    formula ->
    ay_brsr_accepted_report
      (ay_brsr_accepted_hint guard agreement seedReplayHint)
      (ay_brsr_public_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        (ay_brsr_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_brsr_accepted_report_intro
      (ay_brsr_accepted_hint guard agreement seedReplayHint)
      (ay_brsr_public_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        (ay_brsr_outcome model conflict) formula)
      accepted
      (ay_brsr_public_sat_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        model conflict formula accepted modelH formulaH)

theorem ay_brsr_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (seedReplayHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brsr_accepted_hint guard agreement seedReplayHint ->
    conflict ->
    formula ->
    ay_brsr_accepted_report
      (ay_brsr_accepted_hint guard agreement seedReplayHint)
      (ay_brsr_public_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        (ay_brsr_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_brsr_accepted_report_intro
      (ay_brsr_accepted_hint guard agreement seedReplayHint)
      (ay_brsr_public_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        (ay_brsr_outcome model conflict) formula)
      accepted
      (ay_brsr_public_unsat_report
        (ay_brsr_accepted_hint guard agreement seedReplayHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_brsr_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_brsr_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brsr_accepted_report_public hintCert public accepted

theorem ay_brsr_seed_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_brsr_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_brsr_equisat_forward beforeHint afterHint equisat beforeH

-- Refined random-seed replay guard for sequential-main SAT-COMP branching.
-- Randomized guidance is a branching-order hint only when seed, stream, heap,
-- replay, deterministic fallback, build, validator, and audit evidence agree.

def ay_seed_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_seed_equisat (before : Prop) (after : Prop) : Prop :=
  ay_seed_conj (before -> after) (after -> before)

def ay_seed_guard
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (seedManifest ->
      streamDigest ->
      decisionHeapSnapshot ->
      propagationReplay ->
      fallbackDeterministicBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_seed_agreement
    (seedMatch : Prop)
    (streamMatch : Prop)
    (heapMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_seed_guard seedMatch streamMatch heapMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_seed_accepted_random_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_seed_conj guardEvidence
    (ay_seed_conj agreementEvidence branchingOrderHint)

def ay_seed_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_seed_conj acceptedEvidence (ay_seed_conj outcome formulaTruth)

def ay_seed_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_seed_conj diagnostic fallbackPublic

theorem ay_seed_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_seed_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_seed_conj_left (left : Prop) (right : Prop) :
    ay_seed_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_seed_conj_right (left : Prop) (right : Prop) :
    ay_seed_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_seed_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_seed_equisat before after :=
  fun forward backward =>
    ay_seed_conj_intro (before -> after) (after -> before) forward backward

theorem ay_seed_equisat_forward (before : Prop) (after : Prop) :
    ay_seed_equisat before after -> before -> after :=
  fun eqsat =>
    ay_seed_conj_left (before -> after) (after -> before) eqsat

theorem ay_seed_equisat_backward (before : Prop) (after : Prop) :
    ay_seed_equisat before after -> after -> before :=
  fun eqsat =>
    ay_seed_conj_right (before -> after) (after -> before) eqsat

theorem ay_seed_guard_intro
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    seedManifest ->
    streamDigest ->
    decisionHeapSnapshot ->
    propagationReplay ->
    fallbackDeterministicBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript :=
  fun seedH streamH heapH replayH fallbackH buildH validatorH auditH
      result make =>
    make seedH streamH heapH replayH fallbackH buildH validatorH auditH

theorem ay_seed_guard_seed
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    seedManifest :=
  fun guard =>
    guard seedManifest
      (fun seedH _streamH _heapH _replayH _fallbackH _buildH _validatorH
          _auditH => seedH)

theorem ay_seed_guard_stream
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    streamDigest :=
  fun guard =>
    guard streamDigest
      (fun _seedH streamH _heapH _replayH _fallbackH _buildH _validatorH
          _auditH => streamH)

theorem ay_seed_guard_heap
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionHeapSnapshot :=
  fun guard =>
    guard decisionHeapSnapshot
      (fun _seedH _streamH heapH _replayH _fallbackH _buildH _validatorH
          _auditH => heapH)

theorem ay_seed_guard_replay
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _seedH _streamH _heapH replayH _fallbackH _buildH _validatorH
          _auditH => replayH)

theorem ay_seed_guard_fallback
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackDeterministicBaseline :=
  fun guard =>
    guard fallbackDeterministicBaseline
      (fun _seedH _streamH _heapH _replayH fallbackH _buildH _validatorH
          _auditH => fallbackH)

theorem ay_seed_guard_build
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _seedH _streamH _heapH _replayH _fallbackH buildH _validatorH
          _auditH => buildH)

theorem ay_seed_guard_validator
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _seedH _streamH _heapH _replayH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_seed_guard_audit
    (seedManifest : Prop)
    (streamDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackDeterministicBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_seed_guard seedManifest streamDigest decisionHeapSnapshot
      propagationReplay fallbackDeterministicBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _seedH _streamH _heapH _replayH _fallbackH _buildH _validatorH
          auditH => auditH)

theorem ay_seed_agreement_intro
    (seedMatch : Prop)
    (streamMatch : Prop)
    (heapMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    seedMatch ->
    streamMatch ->
    heapMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_seed_agreement seedMatch streamMatch heapMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_seed_guard_intro seedMatch streamMatch heapMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_seed_accepted_random_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingOrderHint ->
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint :=
  fun guardH agreementH hintH =>
    ay_seed_conj_intro guardEvidence
      (ay_seed_conj agreementEvidence branchingOrderHint)
      guardH
      (ay_seed_conj_intro agreementEvidence branchingOrderHint agreementH
        hintH)

theorem ay_seed_accepted_random_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_seed_conj_left guardEvidence
      (ay_seed_conj agreementEvidence branchingOrderHint) accepted

theorem ay_seed_accepted_random_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_seed_conj_left agreementEvidence branchingOrderHint
      (ay_seed_conj_right guardEvidence
        (ay_seed_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_seed_accepted_random_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_seed_conj_right agreementEvidence branchingOrderHint
      (ay_seed_conj_right guardEvidence
        (ay_seed_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_seed_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_seed_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_seed_conj_intro acceptedEvidence
      (ay_seed_conj outcome formulaTruth)
      acceptedH (ay_seed_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_seed_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_seed_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_seed_conj_left acceptedEvidence (ay_seed_conj outcome formulaTruth)
      report

theorem ay_seed_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_seed_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_seed_conj_right outcome formulaTruth
      (ay_seed_conj_right acceptedEvidence
        (ay_seed_conj outcome formulaTruth) report)

theorem ay_seed_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_seed_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_seed_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_seed_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_seed_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_seed_conj_right diagnostic fallbackPublic noClaim

theorem ay_seed_seed_mismatch_no_claim
    (seedMismatch : Prop)
    (fallbackPublic : Prop) :
    seedMismatch -> fallbackPublic ->
    ay_seed_no_claim seedMismatch fallbackPublic :=
  ay_seed_no_claim_intro seedMismatch fallbackPublic

theorem ay_seed_stream_mismatch_no_claim
    (streamMismatch : Prop)
    (fallbackPublic : Prop) :
    streamMismatch -> fallbackPublic ->
    ay_seed_no_claim streamMismatch fallbackPublic :=
  ay_seed_no_claim_intro streamMismatch fallbackPublic

theorem ay_seed_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_seed_no_claim heapMismatch fallbackPublic :=
  ay_seed_no_claim_intro heapMismatch fallbackPublic

theorem ay_seed_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_seed_no_claim replayMismatch fallbackPublic :=
  ay_seed_no_claim_intro replayMismatch fallbackPublic

theorem ay_seed_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_seed_no_claim fallbackFailure fallbackPublic :=
  ay_seed_no_claim_intro fallbackFailure fallbackPublic

theorem ay_seed_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_seed_no_claim buildMismatch fallbackPublic :=
  ay_seed_no_claim_intro buildMismatch fallbackPublic

theorem ay_seed_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_seed_no_claim validatorRejection fallbackPublic :=
  ay_seed_no_claim_intro validatorRejection fallbackPublic

theorem ay_seed_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_seed_no_claim auditMismatch fallbackPublic :=
  ay_seed_no_claim_intro auditMismatch fallbackPublic

theorem ay_seed_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_seed_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_seed_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_seed_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_seed_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_seed_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_seed_accepted_random_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  ay_seed_accepted_random_hint_hint guardEvidence agreementEvidence
    branchingOrderHint

theorem ay_seed_accepted_random_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_seed_accepted_random_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      (ay_seed_accepted_random_hint_agreement guardEvidence agreementEvidence
        branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_seed_accepted_random_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_seed_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_seed_public_report_intro guardEvidence satOutcome satTruth
      (ay_seed_accepted_random_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      satH
      truthH

theorem ay_seed_accepted_random_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_seed_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_seed_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_seed_accepted_random_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_seed_randomized_guidance_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_seed_accepted_random_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_seed_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_seed_equisat_intro formulaBefore formulaAfter
      (forward (ay_seed_accepted_random_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
      (backward (ay_seed_accepted_random_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
