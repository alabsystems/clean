-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Luby/restart-schedule guard skeleton for sequential-main SAT-COMP restart
-- policy. Schedule replay is a search-control hint only when the schedule
-- ledger, counters, replay, fallback, build, validator, and audit evidence
-- agree with the public SAT/UNSAT certificate path.

def ay_luby_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_luby_equisat (before : Prop) (after : Prop) : Prop :=
  ay_luby_conj (before -> after) (after -> before)

def ay_luby_guard
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (scheduleEpochLedger ->
      conflictCounterDigest ->
      levelScopeDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_luby_agreement
    (scheduleEpochMatch : Prop)
    (conflictCounterMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_luby_guard scheduleEpochMatch conflictCounterMatch levelScopeMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_luby_accepted_schedule_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_luby_conj guardEvidence
    (ay_luby_conj agreementEvidence searchControlHint)

def ay_luby_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_luby_conj acceptedEvidence (ay_luby_conj outcome formulaTruth)

def ay_luby_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_luby_conj diagnostic fallbackPublic

theorem ay_luby_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_luby_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_luby_conj_left (left : Prop) (right : Prop) :
    ay_luby_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_luby_conj_right (left : Prop) (right : Prop) :
    ay_luby_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_luby_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_luby_equisat before after :=
  fun forward backward =>
    ay_luby_conj_intro (before -> after) (after -> before) forward backward

theorem ay_luby_equisat_forward (before : Prop) (after : Prop) :
    ay_luby_equisat before after -> before -> after :=
  fun eqsat =>
    ay_luby_conj_left (before -> after) (after -> before) eqsat

theorem ay_luby_equisat_backward (before : Prop) (after : Prop) :
    ay_luby_equisat before after -> after -> before :=
  fun eqsat =>
    ay_luby_conj_right (before -> after) (after -> before) eqsat

theorem ay_luby_guard_intro
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    scheduleEpochLedger ->
    conflictCounterDigest ->
    levelScopeDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun scheduleH counterH levelH replayH fallbackH buildH validatorH auditH
      result make =>
    make scheduleH counterH levelH replayH fallbackH buildH validatorH auditH

theorem ay_luby_guard_schedule
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    scheduleEpochLedger :=
  fun guard =>
    guard scheduleEpochLedger
      (fun scheduleH _counterH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => scheduleH)

theorem ay_luby_guard_conflict_counter
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    conflictCounterDigest :=
  fun guard =>
    guard conflictCounterDigest
      (fun _scheduleH counterH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => counterH)

theorem ay_luby_guard_level_scope
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _scheduleH _counterH levelH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_luby_guard_replay
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _scheduleH _counterH _levelH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_luby_guard_fallback
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _scheduleH _counterH _levelH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_luby_guard_build
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _scheduleH _counterH _levelH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_luby_guard_validator
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _scheduleH _counterH _levelH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_luby_guard_audit
    (scheduleEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_luby_guard scheduleEpochLedger conflictCounterDigest
      levelScopeDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _scheduleH _counterH _levelH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_luby_agreement_intro
    (scheduleEpochMatch : Prop)
    (conflictCounterMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    scheduleEpochMatch ->
    conflictCounterMatch ->
    levelScopeMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_luby_agreement scheduleEpochMatch conflictCounterMatch levelScopeMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_luby_guard_intro scheduleEpochMatch conflictCounterMatch levelScopeMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_luby_accepted_schedule_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_luby_conj_intro guardEvidence
      (ay_luby_conj agreementEvidence searchControlHint)
      guardH
      (ay_luby_conj_intro agreementEvidence searchControlHint agreementH
        hintH)

theorem ay_luby_accepted_schedule_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_luby_conj_left guardEvidence
      (ay_luby_conj agreementEvidence searchControlHint) accepted

theorem ay_luby_accepted_schedule_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_luby_conj_left agreementEvidence searchControlHint
      (ay_luby_conj_right guardEvidence
        (ay_luby_conj agreementEvidence searchControlHint) accepted)

theorem ay_luby_accepted_schedule_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_luby_conj_right agreementEvidence searchControlHint
      (ay_luby_conj_right guardEvidence
        (ay_luby_conj agreementEvidence searchControlHint) accepted)

theorem ay_luby_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_luby_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_luby_conj_intro acceptedEvidence
      (ay_luby_conj outcome formulaTruth)
      acceptedH (ay_luby_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_luby_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_luby_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_luby_conj_left acceptedEvidence (ay_luby_conj outcome formulaTruth)
      report

theorem ay_luby_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_luby_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_luby_conj_right outcome formulaTruth
      (ay_luby_conj_right acceptedEvidence
        (ay_luby_conj outcome formulaTruth) report)

theorem ay_luby_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_luby_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_luby_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_luby_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_luby_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_luby_conj_right diagnostic fallbackPublic noClaim

theorem ay_luby_schedule_epoch_mismatch_no_claim
    (scheduleEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    scheduleEpochMismatch -> fallbackPublic ->
    ay_luby_no_claim scheduleEpochMismatch fallbackPublic :=
  ay_luby_no_claim_intro scheduleEpochMismatch fallbackPublic

theorem ay_luby_conflict_counter_mismatch_no_claim
    (conflictCounterMismatch : Prop)
    (fallbackPublic : Prop) :
    conflictCounterMismatch -> fallbackPublic ->
    ay_luby_no_claim conflictCounterMismatch fallbackPublic :=
  ay_luby_no_claim_intro conflictCounterMismatch fallbackPublic

theorem ay_luby_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_luby_no_claim levelScopeMismatch fallbackPublic :=
  ay_luby_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_luby_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_luby_no_claim replayMismatch fallbackPublic :=
  ay_luby_no_claim_intro replayMismatch fallbackPublic

theorem ay_luby_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_luby_no_claim fallbackFailure fallbackPublic :=
  ay_luby_no_claim_intro fallbackFailure fallbackPublic

theorem ay_luby_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_luby_no_claim buildMismatch fallbackPublic :=
  ay_luby_no_claim_intro buildMismatch fallbackPublic

theorem ay_luby_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_luby_no_claim validatorRejection fallbackPublic :=
  ay_luby_no_claim_intro validatorRejection fallbackPublic

theorem ay_luby_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_luby_no_claim auditMismatch fallbackPublic :=
  ay_luby_no_claim_intro auditMismatch fallbackPublic

theorem ay_luby_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_luby_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_luby_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_luby_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_luby_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_luby_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_luby_accepted_schedule_is_search_control_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  ay_luby_accepted_schedule_hint_hint guardEvidence agreementEvidence
    searchControlHint

theorem ay_luby_accepted_schedule_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_luby_accepted_schedule_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      (ay_luby_accepted_schedule_hint_agreement guardEvidence agreementEvidence
        searchControlHint accepted)
      outcomeH
      truthH

theorem ay_luby_accepted_schedule_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_luby_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_luby_public_report_intro guardEvidence satOutcome satTruth
      (ay_luby_accepted_schedule_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      satH
      truthH

theorem ay_luby_accepted_schedule_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_luby_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_luby_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_luby_accepted_schedule_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      unsatH
      truthH

theorem ay_luby_restart_schedule_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_luby_accepted_schedule_hint guardEvidence agreementEvidence
      searchControlHint ->
    (searchControlHint -> formulaBefore -> formulaAfter) ->
    (searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_luby_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_luby_equisat_intro formulaBefore formulaAfter
      (forward (ay_luby_accepted_schedule_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))
      (backward (ay_luby_accepted_schedule_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))

-- Updated Luby restart schedule guard package with ay_lrsg_ prefix. Restart
-- scheduling remains search-control only when conflict counters, Luby index,
-- restart bounds, stack reset, replay, tiebreak, fallback, build, validator,
-- and audit evidence agree.

def ay_lrsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lrsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_lrsg_conj (before -> after) (after -> before)

def ay_lrsg_guard
    (conflictCounterDigest : Prop)
    (lubyIndexLedger : Prop)
    (restartBoundManifest : Prop)
    (decisionStackResetWitness : Prop)
    (propagationReplay : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictCounterDigest ->
      lubyIndexLedger ->
      restartBoundManifest ->
      decisionStackResetWitness ->
      propagationReplay ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_lrsg_agreement
    (conflictMatch : Prop)
    (indexMatch : Prop)
    (boundMatch : Prop)
    (resetMatch : Prop)
    (replayMatch : Prop)
    (tiebreakMatch : Prop)
    (baselineMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_lrsg_guard conflictMatch indexMatch boundMatch resetMatch replayMatch
    tiebreakMatch baselineMatch buildMatch validatorAccepts auditMatch

def ay_lrsg_accepted_restart_schedule
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_lrsg_conj guardEvidence
    (ay_lrsg_conj agreementEvidence
      (ay_lrsg_conj deterministicBranchOrder searchControlHint))

def ay_lrsg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_lrsg_conj acceptedEvidence (ay_lrsg_conj outcome formulaTruth)

def ay_lrsg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_lrsg_conj diagnostic fallbackPublic

theorem ay_lrsg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_lrsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_lrsg_conj_left (left : Prop) (right : Prop) :
    ay_lrsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_lrsg_conj_right (left : Prop) (right : Prop) :
    ay_lrsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_lrsg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_lrsg_equisat before after :=
  fun forward backward =>
    ay_lrsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_lrsg_equisat_forward (before : Prop) (after : Prop) :
    ay_lrsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_lrsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_lrsg_equisat_backward (before : Prop) (after : Prop) :
    ay_lrsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_lrsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_lrsg_guard_intro
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    conflictCounterDigest ->
    lubyIndexLedger ->
    restartBoundManifest ->
    decisionStackResetWitness ->
    propagationReplay ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun conflictH indexH boundH resetH replayH tiebreakH baselineH buildH
      validatorH auditH result make =>
    make conflictH indexH boundH resetH replayH tiebreakH baselineH buildH
      validatorH auditH

theorem ay_lrsg_guard_conflict
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    conflictCounterDigest :=
  fun guard =>
    guard conflictCounterDigest
      (fun conflictH _indexH _boundH _resetH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => conflictH)

theorem ay_lrsg_guard_index
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    lubyIndexLedger :=
  fun guard =>
    guard lubyIndexLedger
      (fun _conflictH indexH _boundH _resetH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => indexH)

theorem ay_lrsg_guard_bound
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    restartBoundManifest :=
  fun guard =>
    guard restartBoundManifest
      (fun _conflictH _indexH boundH _resetH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => boundH)

theorem ay_lrsg_guard_reset
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionStackResetWitness :=
  fun guard =>
    guard decisionStackResetWitness
      (fun _conflictH _indexH _boundH resetH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => resetH)

theorem ay_lrsg_guard_replay
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _conflictH _indexH _boundH _resetH replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => replayH)

theorem ay_lrsg_guard_tiebreak
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _conflictH _indexH _boundH _resetH _replayH tiebreakH _baselineH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_lrsg_guard_baseline
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _conflictH _indexH _boundH _resetH _replayH _tiebreakH baselineH
          _buildH _validatorH _auditH => baselineH)

theorem ay_lrsg_guard_build
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _conflictH _indexH _boundH _resetH _replayH _tiebreakH _baselineH
          buildH _validatorH _auditH => buildH)

theorem ay_lrsg_guard_validator
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _conflictH _indexH _boundH _resetH _replayH _tiebreakH _baselineH
          _buildH validatorH _auditH => validatorH)

theorem ay_lrsg_guard_audit
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_lrsg_guard conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _conflictH _indexH _boundH _resetH _replayH _tiebreakH _baselineH
          _buildH _validatorH auditH => auditH)

theorem ay_lrsg_agreement_intro
    (conflictMatch indexMatch boundMatch resetMatch replayMatch tiebreakMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) :
    conflictMatch ->
    indexMatch ->
    boundMatch ->
    resetMatch ->
    replayMatch ->
    tiebreakMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_lrsg_agreement conflictMatch indexMatch boundMatch resetMatch
      replayMatch tiebreakMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_lrsg_guard_intro conflictMatch indexMatch boundMatch resetMatch replayMatch
    tiebreakMatch baselineMatch buildMatch validatorAccepts auditMatch

theorem ay_lrsg_accepted_restart_schedule_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_lrsg_conj_intro guardEvidence
      (ay_lrsg_conj agreementEvidence
        (ay_lrsg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_lrsg_conj_intro agreementEvidence
        (ay_lrsg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_lrsg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_lrsg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_lrsg_conj_left guardEvidence
    (ay_lrsg_conj agreementEvidence
      (ay_lrsg_conj deterministicBranchOrder searchControlHint))

theorem ay_lrsg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_lrsg_conj_left agreementEvidence
      (ay_lrsg_conj deterministicBranchOrder searchControlHint)
      (ay_lrsg_conj_right guardEvidence
        (ay_lrsg_conj agreementEvidence
          (ay_lrsg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_lrsg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_lrsg_conj_left deterministicBranchOrder searchControlHint
      (ay_lrsg_conj_right agreementEvidence
        (ay_lrsg_conj deterministicBranchOrder searchControlHint)
        (ay_lrsg_conj_right guardEvidence
          (ay_lrsg_conj agreementEvidence
            (ay_lrsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_lrsg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_lrsg_conj_right deterministicBranchOrder searchControlHint
      (ay_lrsg_conj_right agreementEvidence
        (ay_lrsg_conj deterministicBranchOrder searchControlHint)
        (ay_lrsg_conj_right guardEvidence
          (ay_lrsg_conj agreementEvidence
            (ay_lrsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_lrsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_lrsg_conj_intro acceptedEvidence (ay_lrsg_conj outcome formulaTruth)
      acceptedH (ay_lrsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_lrsg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_lrsg_conj_left acceptedEvidence (ay_lrsg_conj outcome formulaTruth)

theorem ay_lrsg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_lrsg_conj_left outcome formulaTruth
      (ay_lrsg_conj_right acceptedEvidence
        (ay_lrsg_conj outcome formulaTruth) report)

theorem ay_lrsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_lrsg_conj_right outcome formulaTruth
      (ay_lrsg_conj_right acceptedEvidence
        (ay_lrsg_conj outcome formulaTruth) report)

theorem ay_lrsg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_lrsg_no_claim diagnostic fallbackPublic :=
  ay_lrsg_conj_intro diagnostic fallbackPublic

theorem ay_lrsg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_lrsg_conj_left diagnostic fallbackPublic

theorem ay_lrsg_no_claim_preserves_fallback (diagnostic fallbackPublic : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_lrsg_conj_right diagnostic fallbackPublic

theorem ay_lrsg_restart_schedule_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_lrsg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_lrsg_equisat_forward beforeFormula afterFormula

theorem ay_lrsg_restart_schedule_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_lrsg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_lrsg_equisat_backward beforeFormula afterFormula

theorem ay_lrsg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    ay_lrsg_conj outcome formulaTruth :=
  fun report =>
    ay_lrsg_conj_right acceptedEvidence (ay_lrsg_conj outcome formulaTruth)
      report

theorem ay_lrsg_accepted_guides_restart_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_lrsg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_lrsg_conj_right agreementEvidence
      (ay_lrsg_conj deterministicBranchOrder searchControlHint)
      (ay_lrsg_conj_right guardEvidence
        (ay_lrsg_conj agreementEvidence
          (ay_lrsg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_lrsg_conflict_mismatch_no_claim
    (conflictMismatch fallbackPublic : Prop) :
    conflictMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim conflictMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro conflictMismatch fallbackPublic

theorem ay_lrsg_index_mismatch_no_claim
    (indexMismatch fallbackPublic : Prop) :
    indexMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim indexMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro indexMismatch fallbackPublic

theorem ay_lrsg_bound_mismatch_no_claim
    (boundMismatch fallbackPublic : Prop) :
    boundMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim boundMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro boundMismatch fallbackPublic

theorem ay_lrsg_reset_mismatch_no_claim
    (resetMismatch fallbackPublic : Prop) :
    resetMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim resetMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro resetMismatch fallbackPublic

theorem ay_lrsg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim replayMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_lrsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim tiebreakMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_lrsg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim baselineMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_lrsg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim buildMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_lrsg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_lrsg_no_claim validatorRejects fallbackPublic :=
  ay_lrsg_no_claim_intro validatorRejects fallbackPublic

theorem ay_lrsg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_lrsg_no_claim auditMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_lrsg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_lrsg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_lrsg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_lrsg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_lrsg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_lrsg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_lrsg_public_report
      (ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_lrsg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_lrsg_public_report_accepted
        (ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_lrsg_publication_requires_validator
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_lrsg_public_report
      (ay_lrsg_accepted_restart_schedule
        (ay_lrsg_guard conflictCounterDigest lubyIndexLedger
          restartBoundManifest decisionStackResetWitness propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_lrsg_guard_validator conflictCounterDigest lubyIndexLedger
      restartBoundManifest decisionStackResetWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_lrsg_publication_requires_accepted_guard
        (ay_lrsg_guard conflictCounterDigest lubyIndexLedger
          restartBoundManifest decisionStackResetWitness propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_lrsg_publication_requires_audit
    (conflictCounterDigest lubyIndexLedger restartBoundManifest
      decisionStackResetWitness propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_lrsg_public_report
      (ay_lrsg_accepted_restart_schedule
        (ay_lrsg_guard conflictCounterDigest lubyIndexLedger
          restartBoundManifest decisionStackResetWitness propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_lrsg_guard_audit conflictCounterDigest lubyIndexLedger
      restartBoundManifest decisionStackResetWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_lrsg_publication_requires_accepted_guard
        (ay_lrsg_guard conflictCounterDigest lubyIndexLedger
          restartBoundManifest decisionStackResetWitness propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_lrsg_luby_restart_scheduling_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_lrsg_equisat beforeFormula afterFormula ->
    ay_lrsg_accepted_restart_schedule guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_lrsg_conj (beforeFormula -> afterFormula)
      (ay_lrsg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_lrsg_conj_intro (beforeFormula -> afterFormula)
      (ay_lrsg_conj deterministicBranchOrder searchControlHint)
      (ay_lrsg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_lrsg_accepted_guides_restart_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_lrsg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_lrsg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_lrsg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_lrsg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_lrsg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_lrsg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
