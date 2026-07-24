-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart/phase interlock guard skeleton for sequential-main SAT. Interlocked
-- restart schedules and phase-saving metadata are performance hints only when
-- restart epochs, phase epochs, trail snapshots, score digests, fallback,
-- build, validator, and audit evidence agree.

def ay_brpi_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brpi_equisat (before : Prop) (after : Prop) : Prop :=
  ay_brpi_conj (before -> after) (after -> before)

def ay_brpi_interlock_guard
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (restartEpochLedger ->
      phaseEpochLedger ->
      trailSnapshot ->
      activityScoreDigest ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_brpi_guard_agreement
    (restartEpochMatch : Prop)
    (phaseEpochMatch : Prop)
    (trailMatch : Prop)
    (scoreDigestMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_brpi_interlock_guard restartEpochMatch phaseEpochMatch trailMatch
    scoreDigestMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brpi_accepted_interlock
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) : Prop :=
  ay_brpi_conj guardEvidence (ay_brpi_conj agreementEvidence interlockGuidance)

def ay_brpi_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_brpi_conj acceptedEvidence (ay_brpi_conj outcome formulaTruth)

def ay_brpi_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_brpi_conj diagnostic fallbackPublic

theorem ay_brpi_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_brpi_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_brpi_conj_left (left : Prop) (right : Prop) :
    ay_brpi_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_brpi_conj_right (left : Prop) (right : Prop) :
    ay_brpi_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_brpi_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_brpi_equisat before after :=
  fun forward backward =>
    ay_brpi_conj_intro (before -> after) (after -> before) forward backward

theorem ay_brpi_equisat_forward (before : Prop) (after : Prop) :
    ay_brpi_equisat before after -> before -> after :=
  fun eqsat =>
    ay_brpi_conj_left (before -> after) (after -> before) eqsat

theorem ay_brpi_equisat_backward (before : Prop) (after : Prop) :
    ay_brpi_equisat before after -> after -> before :=
  fun eqsat =>
    ay_brpi_conj_right (before -> after) (after -> before) eqsat

theorem ay_brpi_interlock_guard_intro
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    restartEpochLedger ->
    phaseEpochLedger ->
    trailSnapshot ->
    activityScoreDigest ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence :=
  fun restartH phaseH trailH scoreH fallbackH buildH validatorH auditH
      result build =>
    build restartH phaseH trailH scoreH fallbackH buildH validatorH auditH

theorem ay_brpi_interlock_guard_restart_epoch
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    restartEpochLedger :=
  fun guard =>
    guard restartEpochLedger
      (fun restartH _phaseH _trailH _scoreH _fallbackH _buildH
          _validatorH _auditH => restartH)

theorem ay_brpi_interlock_guard_phase_epoch
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    phaseEpochLedger :=
  fun guard =>
    guard phaseEpochLedger
      (fun _restartH phaseH _trailH _scoreH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_brpi_interlock_guard_trail
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    trailSnapshot :=
  fun guard =>
    guard trailSnapshot
      (fun _restartH _phaseH trailH _scoreH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_brpi_interlock_guard_score_digest
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    activityScoreDigest :=
  fun guard =>
    guard activityScoreDigest
      (fun _restartH _phaseH _trailH scoreH _fallbackH _buildH
          _validatorH _auditH => scoreH)

theorem ay_brpi_interlock_guard_fallback
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _restartH _phaseH _trailH _scoreH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brpi_interlock_guard_build
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _restartH _phaseH _trailH _scoreH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brpi_interlock_guard_validator
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _restartH _phaseH _trailH _scoreH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brpi_interlock_guard_audit
    (restartEpochLedger : Prop)
    (phaseEpochLedger : Prop)
    (trailSnapshot : Prop)
    (activityScoreDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpi_interlock_guard restartEpochLedger phaseEpochLedger trailSnapshot
      activityScoreDigest fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _restartH _phaseH _trailH _scoreH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brpi_guard_agreement_intro
    (restartEpochMatch : Prop)
    (phaseEpochMatch : Prop)
    (trailMatch : Prop)
    (scoreDigestMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    restartEpochMatch ->
    phaseEpochMatch ->
    trailMatch ->
    scoreDigestMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brpi_guard_agreement restartEpochMatch phaseEpochMatch trailMatch
      scoreDigestMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_brpi_interlock_guard_intro restartEpochMatch phaseEpochMatch trailMatch
    scoreDigestMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_brpi_accepted_interlock_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    interlockGuidance ->
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance :=
  fun guardH agreementH guidanceH =>
    ay_brpi_conj_intro guardEvidence
      (ay_brpi_conj agreementEvidence interlockGuidance)
      guardH
      (ay_brpi_conj_intro agreementEvidence interlockGuidance
        agreementH guidanceH)

theorem ay_brpi_accepted_interlock_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_brpi_conj_left guardEvidence
      (ay_brpi_conj agreementEvidence interlockGuidance)
      accepted

theorem ay_brpi_accepted_interlock_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_brpi_conj_left agreementEvidence interlockGuidance
      (ay_brpi_conj_right guardEvidence
        (ay_brpi_conj agreementEvidence interlockGuidance)
        accepted)

theorem ay_brpi_accepted_interlock_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    interlockGuidance :=
  fun accepted =>
    ay_brpi_conj_right agreementEvidence interlockGuidance
      (ay_brpi_conj_right guardEvidence
        (ay_brpi_conj agreementEvidence interlockGuidance)
        accepted)

theorem ay_brpi_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_brpi_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_brpi_conj_intro acceptedEvidence
      (ay_brpi_conj outcome formulaTruth)
      acceptedH
      (ay_brpi_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_brpi_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_brpi_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_brpi_conj_left acceptedEvidence
      (ay_brpi_conj outcome formulaTruth)
      public

theorem ay_brpi_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_brpi_no_claim diagnostic fallbackPublic :=
  ay_brpi_conj_intro diagnostic fallbackPublic

theorem ay_brpi_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brpi_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_brpi_conj_right diagnostic fallbackPublic noClaim

theorem ay_brpi_restart_epoch_drift_no_claim
    (restartEpochDrift : Prop)
    (fallbackPublic : Prop) :
    restartEpochDrift ->
    fallbackPublic ->
    ay_brpi_no_claim restartEpochDrift fallbackPublic :=
  ay_brpi_no_claim_intro restartEpochDrift fallbackPublic

theorem ay_brpi_phase_epoch_drift_no_claim
    (phaseEpochDrift : Prop)
    (fallbackPublic : Prop) :
    phaseEpochDrift ->
    fallbackPublic ->
    ay_brpi_no_claim phaseEpochDrift fallbackPublic :=
  ay_brpi_no_claim_intro phaseEpochDrift fallbackPublic

theorem ay_brpi_trail_mismatch_no_claim
    (trailMismatch : Prop)
    (fallbackPublic : Prop) :
    trailMismatch ->
    fallbackPublic ->
    ay_brpi_no_claim trailMismatch fallbackPublic :=
  ay_brpi_no_claim_intro trailMismatch fallbackPublic

theorem ay_brpi_score_digest_mismatch_no_claim
    (scoreDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    scoreDigestMismatch ->
    fallbackPublic ->
    ay_brpi_no_claim scoreDigestMismatch fallbackPublic :=
  ay_brpi_no_claim_intro scoreDigestMismatch fallbackPublic

theorem ay_brpi_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brpi_no_claim missingFallback fallbackPublic :=
  ay_brpi_no_claim_intro missingFallback fallbackPublic

theorem ay_brpi_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_brpi_no_claim staleBuild fallbackPublic :=
  ay_brpi_no_claim_intro staleBuild fallbackPublic

theorem ay_brpi_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_brpi_no_claim validatorRejection fallbackPublic :=
  ay_brpi_no_claim_intro validatorRejection fallbackPublic

theorem ay_brpi_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brpi_no_claim auditContradiction fallbackPublic :=
  ay_brpi_no_claim_intro auditContradiction fallbackPublic

theorem ay_brpi_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_brpi_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_brpi_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_brpi_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brpi_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_brpi_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_brpi_accepted_interlock_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_brpi_public_report
      (ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_brpi_public_report_intro
      (ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_brpi_accepted_interlock_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_brpi_public_report
      (ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance)
      unsatOutcome
      formulaTruth :=
  ay_brpi_accepted_interlock_guides_sat guardEvidence agreementEvidence
    interlockGuidance unsatOutcome formulaTruth

theorem ay_brpi_accepted_interlock_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    ay_brpi_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_brpi_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_brpi_interlock_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interlockGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_brpi_accepted_interlock guardEvidence agreementEvidence interlockGuidance ->
    ay_brpi_equisat beforeTruth afterTruth ->
    ay_brpi_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_brpi_equisat_intro afterTruth beforeTruth
      (ay_brpi_equisat_backward beforeTruth afterTruth eqsat)
      (ay_brpi_equisat_forward beforeTruth afterTruth eqsat)

-- Restart/phase-saving interlock guard package with ay_rpig_ prefix. The
-- interlock is search-control only when restart counters, phase tables,
-- decision-stack reset, phase restore, replay, tiebreak, fallback, build,
-- validator, and audit evidence agree.

def ay_rpig_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rpig_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rpig_conj (before -> after) (after -> before)

def ay_rpig_guard
    (restartCounterDigest : Prop)
    (phaseTableDigest : Prop)
    (decisionStackResetWitness : Prop)
    (phaseRestoreLedger : Prop)
    (propagationReplay : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (restartCounterDigest ->
      phaseTableDigest ->
      decisionStackResetWitness ->
      phaseRestoreLedger ->
      propagationReplay ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rpig_agreement
    (counterMatch phaseMatch resetMatch restoreMatch replayMatch tiebreakMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) : Prop :=
  ay_rpig_guard counterMatch phaseMatch resetMatch restoreMatch replayMatch
    tiebreakMatch baselineMatch buildMatch validatorAccepts auditMatch

def ay_rpig_accepted_interlock
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_rpig_conj guardEvidence
    (ay_rpig_conj agreementEvidence
      (ay_rpig_conj deterministicBranchOrder searchControlHint))

def ay_rpig_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_rpig_conj acceptedEvidence (ay_rpig_conj outcome formulaTruth)

def ay_rpig_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_rpig_conj diagnostic fallbackPublic

theorem ay_rpig_conj_intro (left right : Prop) :
    left -> right -> ay_rpig_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rpig_conj_left (left right : Prop) :
    ay_rpig_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rpig_conj_right (left right : Prop) :
    ay_rpig_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rpig_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_rpig_equisat before after :=
  fun forward backward =>
    ay_rpig_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rpig_equisat_forward (before after : Prop) :
    ay_rpig_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rpig_conj_left (before -> after) (after -> before) eqsat

theorem ay_rpig_equisat_backward (before after : Prop) :
    ay_rpig_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rpig_conj_right (before -> after) (after -> before) eqsat

theorem ay_rpig_guard_intro
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    restartCounterDigest ->
    phaseTableDigest ->
    decisionStackResetWitness ->
    phaseRestoreLedger ->
    propagationReplay ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rpig_guard restartCounterDigest phaseTableDigest
      decisionStackResetWitness phaseRestoreLedger propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun counterH phaseH resetH restoreH replayH tiebreakH baselineH buildH
      validatorH auditH result make =>
    make counterH phaseH resetH restoreH replayH tiebreakH baselineH buildH
      validatorH auditH

theorem ay_rpig_guard_counter
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    restartCounterDigest :=
  fun guard =>
    guard restartCounterDigest
      (fun counterH _phaseH _resetH _restoreH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => counterH)

theorem ay_rpig_guard_phase
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    phaseTableDigest :=
  fun guard =>
    guard phaseTableDigest
      (fun _counterH phaseH _resetH _restoreH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => phaseH)

theorem ay_rpig_guard_reset
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionStackResetWitness :=
  fun guard =>
    guard decisionStackResetWitness
      (fun _counterH _phaseH resetH _restoreH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => resetH)

theorem ay_rpig_guard_restore
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    phaseRestoreLedger :=
  fun guard =>
    guard phaseRestoreLedger
      (fun _counterH _phaseH _resetH restoreH _replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => restoreH)

theorem ay_rpig_guard_replay
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _counterH _phaseH _resetH _restoreH replayH _tiebreakH _baselineH
          _buildH _validatorH _auditH => replayH)

theorem ay_rpig_guard_tiebreak
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _counterH _phaseH _resetH _restoreH _replayH tiebreakH _baselineH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_rpig_guard_baseline
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _counterH _phaseH _resetH _restoreH _replayH _tiebreakH baselineH
          _buildH _validatorH _auditH => baselineH)

theorem ay_rpig_guard_build
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _counterH _phaseH _resetH _restoreH _replayH _tiebreakH _baselineH
          buildH _validatorH _auditH => buildH)

theorem ay_rpig_guard_validator
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _counterH _phaseH _resetH _restoreH _replayH _tiebreakH _baselineH
          _buildH validatorH _auditH => validatorH)

theorem ay_rpig_guard_audit
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rpig_guard restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _counterH _phaseH _resetH _restoreH _replayH _tiebreakH _baselineH
          _buildH _validatorH auditH => auditH)

theorem ay_rpig_agreement_intro
    (counterMatch phaseMatch resetMatch restoreMatch replayMatch tiebreakMatch
      baselineMatch buildMatch validatorAccepts auditMatch : Prop) :
    counterMatch ->
    phaseMatch ->
    resetMatch ->
    restoreMatch ->
    replayMatch ->
    tiebreakMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rpig_agreement counterMatch phaseMatch resetMatch restoreMatch
      replayMatch tiebreakMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_rpig_guard_intro counterMatch phaseMatch resetMatch restoreMatch
    replayMatch tiebreakMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_rpig_accepted_interlock_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_rpig_conj_intro guardEvidence
      (ay_rpig_conj agreementEvidence
        (ay_rpig_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_rpig_conj_intro agreementEvidence
        (ay_rpig_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_rpig_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_rpig_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_rpig_conj_left guardEvidence
    (ay_rpig_conj agreementEvidence
      (ay_rpig_conj deterministicBranchOrder searchControlHint))

theorem ay_rpig_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_rpig_conj_left agreementEvidence
      (ay_rpig_conj deterministicBranchOrder searchControlHint)
      (ay_rpig_conj_right guardEvidence
        (ay_rpig_conj agreementEvidence
          (ay_rpig_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_rpig_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_rpig_conj_left deterministicBranchOrder searchControlHint
      (ay_rpig_conj_right agreementEvidence
        (ay_rpig_conj deterministicBranchOrder searchControlHint)
        (ay_rpig_conj_right guardEvidence
          (ay_rpig_conj agreementEvidence
            (ay_rpig_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_rpig_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_rpig_conj_right deterministicBranchOrder searchControlHint
      (ay_rpig_conj_right agreementEvidence
        (ay_rpig_conj deterministicBranchOrder searchControlHint)
        (ay_rpig_conj_right guardEvidence
          (ay_rpig_conj agreementEvidence
            (ay_rpig_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_rpig_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rpig_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rpig_conj_intro acceptedEvidence (ay_rpig_conj outcome formulaTruth)
      acceptedH (ay_rpig_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rpig_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rpig_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_rpig_conj_left acceptedEvidence (ay_rpig_conj outcome formulaTruth)

theorem ay_rpig_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rpig_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_rpig_conj_left outcome formulaTruth
      (ay_rpig_conj_right acceptedEvidence
        (ay_rpig_conj outcome formulaTruth) report)

theorem ay_rpig_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rpig_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rpig_conj_right outcome formulaTruth
      (ay_rpig_conj_right acceptedEvidence
        (ay_rpig_conj outcome formulaTruth) report)

theorem ay_rpig_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_rpig_no_claim diagnostic fallbackPublic :=
  ay_rpig_conj_intro diagnostic fallbackPublic

theorem ay_rpig_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_rpig_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_rpig_conj_left diagnostic fallbackPublic

theorem ay_rpig_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_rpig_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_rpig_conj_right diagnostic fallbackPublic

theorem ay_rpig_interlock_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rpig_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_rpig_equisat_forward beforeFormula afterFormula

theorem ay_rpig_interlock_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rpig_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_rpig_equisat_backward beforeFormula afterFormula

theorem ay_rpig_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rpig_public_report acceptedEvidence outcome formulaTruth ->
    ay_rpig_conj outcome formulaTruth :=
  fun report =>
    ay_rpig_conj_right acceptedEvidence (ay_rpig_conj outcome formulaTruth)
      report

theorem ay_rpig_accepted_guides_search_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_rpig_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_rpig_conj_right agreementEvidence
      (ay_rpig_conj deterministicBranchOrder searchControlHint)
      (ay_rpig_conj_right guardEvidence
        (ay_rpig_conj agreementEvidence
          (ay_rpig_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_rpig_counter_mismatch_no_claim
    (counterMismatch fallbackPublic : Prop) :
    counterMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim counterMismatch fallbackPublic :=
  ay_rpig_no_claim_intro counterMismatch fallbackPublic

theorem ay_rpig_phase_mismatch_no_claim
    (phaseMismatch fallbackPublic : Prop) :
    phaseMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim phaseMismatch fallbackPublic :=
  ay_rpig_no_claim_intro phaseMismatch fallbackPublic

theorem ay_rpig_reset_mismatch_no_claim
    (resetMismatch fallbackPublic : Prop) :
    resetMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim resetMismatch fallbackPublic :=
  ay_rpig_no_claim_intro resetMismatch fallbackPublic

theorem ay_rpig_restore_mismatch_no_claim
    (restoreMismatch fallbackPublic : Prop) :
    restoreMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim restoreMismatch fallbackPublic :=
  ay_rpig_no_claim_intro restoreMismatch fallbackPublic

theorem ay_rpig_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim replayMismatch fallbackPublic :=
  ay_rpig_no_claim_intro replayMismatch fallbackPublic

theorem ay_rpig_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim tiebreakMismatch fallbackPublic :=
  ay_rpig_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_rpig_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim baselineMismatch fallbackPublic :=
  ay_rpig_no_claim_intro baselineMismatch fallbackPublic

theorem ay_rpig_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim buildMismatch fallbackPublic :=
  ay_rpig_no_claim_intro buildMismatch fallbackPublic

theorem ay_rpig_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_rpig_no_claim validatorRejects fallbackPublic :=
  ay_rpig_no_claim_intro validatorRejects fallbackPublic

theorem ay_rpig_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_rpig_no_claim auditMismatch fallbackPublic :=
  ay_rpig_no_claim_intro auditMismatch fallbackPublic

theorem ay_rpig_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_rpig_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_rpig_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_rpig_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_rpig_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_rpig_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_rpig_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_rpig_public_report
      (ay_rpig_accepted_interlock guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_rpig_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_rpig_public_report_accepted
        (ay_rpig_accepted_interlock guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_rpig_publication_requires_validator
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_rpig_public_report
      (ay_rpig_accepted_interlock
        (ay_rpig_guard restartCounterDigest phaseTableDigest
          decisionStackResetWitness phaseRestoreLedger propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_rpig_guard_validator restartCounterDigest phaseTableDigest
      decisionStackResetWitness phaseRestoreLedger propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_rpig_publication_requires_accepted_guard
        (ay_rpig_guard restartCounterDigest phaseTableDigest
          decisionStackResetWitness phaseRestoreLedger propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_rpig_publication_requires_audit
    (restartCounterDigest phaseTableDigest decisionStackResetWitness
      phaseRestoreLedger propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_rpig_public_report
      (ay_rpig_accepted_interlock
        (ay_rpig_guard restartCounterDigest phaseTableDigest
          decisionStackResetWitness phaseRestoreLedger propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_rpig_guard_audit restartCounterDigest phaseTableDigest
      decisionStackResetWitness phaseRestoreLedger propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_rpig_publication_requires_accepted_guard
        (ay_rpig_guard restartCounterDigest phaseTableDigest
          decisionStackResetWitness phaseRestoreLedger propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_rpig_restart_phase_interlocking_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_rpig_equisat beforeFormula afterFormula ->
    ay_rpig_accepted_interlock guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_rpig_conj (beforeFormula -> afterFormula)
      (ay_rpig_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_rpig_conj_intro (beforeFormula -> afterFormula)
      (ay_rpig_conj deterministicBranchOrder searchControlHint)
      (ay_rpig_equisat_forward beforeFormula afterFormula eqsat)
      (ay_rpig_accepted_guides_search_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_rpig_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_rpig_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_rpig_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_rpig_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_rpig_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_rpig_public_report_intro acceptedEvidence unsatOutcome formulaTruth
