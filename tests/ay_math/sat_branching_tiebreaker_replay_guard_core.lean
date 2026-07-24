-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Deterministic tiebreaker replay guard skeleton for sequential-main SAT-COMP
-- branching. Tiebreak replay is a branching-order hint only when ledgers,
-- digests, replay, fallback, build, validator, and audit evidence agree.

def ay_tbrg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_tbrg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_tbrg_conj (before -> after) (after -> before)

def ay_tbrg_guard
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (tiebreakEpochLedger ->
      variableActivityDigest ->
      decisionHeapSnapshot ->
      randomFallbackDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_tbrg_agreement
    (tiebreakEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (heapSnapshotMatch : Prop)
    (randomFallbackMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_tbrg_guard tiebreakEpochMatch activityDigestMatch heapSnapshotMatch
    randomFallbackMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_tbrg_accepted_tiebreak_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_tbrg_conj guardEvidence
    (ay_tbrg_conj agreementEvidence branchingOrderHint)

def ay_tbrg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_tbrg_conj acceptedEvidence (ay_tbrg_conj outcome formulaTruth)

def ay_tbrg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_tbrg_conj diagnostic fallbackPublic

theorem ay_tbrg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_tbrg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_tbrg_conj_left (left : Prop) (right : Prop) :
    ay_tbrg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_tbrg_conj_right (left : Prop) (right : Prop) :
    ay_tbrg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_tbrg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_tbrg_equisat before after :=
  fun forward backward =>
    ay_tbrg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_tbrg_equisat_forward (before : Prop) (after : Prop) :
    ay_tbrg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_tbrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_tbrg_equisat_backward (before : Prop) (after : Prop) :
    ay_tbrg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_tbrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_tbrg_guard_intro
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    tiebreakEpochLedger ->
    variableActivityDigest ->
    decisionHeapSnapshot ->
    randomFallbackDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript :=
  fun epochH activityH heapH randomH replayH fallbackH buildH validatorH
      auditH result make =>
    make epochH activityH heapH randomH replayH fallbackH buildH validatorH
      auditH

theorem ay_tbrg_guard_epoch
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    tiebreakEpochLedger :=
  fun guard =>
    guard tiebreakEpochLedger
      (fun epochH _activityH _heapH _randomH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_tbrg_guard_activity
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    variableActivityDigest :=
  fun guard =>
    guard variableActivityDigest
      (fun _epochH activityH _heapH _randomH _replayH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_tbrg_guard_heap
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    decisionHeapSnapshot :=
  fun guard =>
    guard decisionHeapSnapshot
      (fun _epochH _activityH heapH _randomH _replayH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_tbrg_guard_random_fallback
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    randomFallbackDigest :=
  fun guard =>
    guard randomFallbackDigest
      (fun _epochH _activityH _heapH randomH _replayH _fallbackH _buildH
          _validatorH _auditH => randomH)

theorem ay_tbrg_guard_replay
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _activityH _heapH _randomH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_tbrg_guard_fallback
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _activityH _heapH _randomH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_tbrg_guard_build
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _activityH _heapH _randomH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_tbrg_guard_validator
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _activityH _heapH _randomH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_tbrg_guard_audit
    (tiebreakEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (randomFallbackDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_tbrg_guard tiebreakEpochLedger variableActivityDigest
      decisionHeapSnapshot randomFallbackDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _activityH _heapH _randomH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_tbrg_agreement_intro
    (tiebreakEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (heapSnapshotMatch : Prop)
    (randomFallbackMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    tiebreakEpochMatch ->
    activityDigestMatch ->
    heapSnapshotMatch ->
    randomFallbackMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_tbrg_agreement tiebreakEpochMatch activityDigestMatch
      heapSnapshotMatch randomFallbackMatch replayMatch fallbackMatch
      buildMatch validatorAccepts auditMatch :=
  ay_tbrg_guard_intro tiebreakEpochMatch activityDigestMatch heapSnapshotMatch
    randomFallbackMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_tbrg_accepted_tiebreak_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingOrderHint ->
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint :=
  fun guardH agreementH hintH =>
    ay_tbrg_conj_intro guardEvidence
      (ay_tbrg_conj agreementEvidence branchingOrderHint)
      guardH
      (ay_tbrg_conj_intro agreementEvidence branchingOrderHint agreementH
        hintH)

theorem ay_tbrg_accepted_tiebreak_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_tbrg_conj_left guardEvidence
      (ay_tbrg_conj agreementEvidence branchingOrderHint) accepted

theorem ay_tbrg_accepted_tiebreak_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_tbrg_conj_left agreementEvidence branchingOrderHint
      (ay_tbrg_conj_right guardEvidence
        (ay_tbrg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_tbrg_accepted_tiebreak_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_tbrg_conj_right agreementEvidence branchingOrderHint
      (ay_tbrg_conj_right guardEvidence
        (ay_tbrg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_tbrg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_tbrg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_tbrg_conj_intro acceptedEvidence
      (ay_tbrg_conj outcome formulaTruth)
      acceptedH (ay_tbrg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_tbrg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_tbrg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_tbrg_conj_left acceptedEvidence (ay_tbrg_conj outcome formulaTruth)
      report

theorem ay_tbrg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_tbrg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_tbrg_conj_right outcome formulaTruth
      (ay_tbrg_conj_right acceptedEvidence
        (ay_tbrg_conj outcome formulaTruth) report)

theorem ay_tbrg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_tbrg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_tbrg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_tbrg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_tbrg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_tbrg_conj_right diagnostic fallbackPublic noClaim

theorem ay_tbrg_epoch_mismatch_no_claim
    (epochMismatch : Prop)
    (fallbackPublic : Prop) :
    epochMismatch -> fallbackPublic ->
    ay_tbrg_no_claim epochMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro epochMismatch fallbackPublic

theorem ay_tbrg_activity_mismatch_no_claim
    (activityMismatch : Prop)
    (fallbackPublic : Prop) :
    activityMismatch -> fallbackPublic ->
    ay_tbrg_no_claim activityMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro activityMismatch fallbackPublic

theorem ay_tbrg_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_tbrg_no_claim heapMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro heapMismatch fallbackPublic

theorem ay_tbrg_random_fallback_mismatch_no_claim
    (randomFallbackMismatch : Prop)
    (fallbackPublic : Prop) :
    randomFallbackMismatch -> fallbackPublic ->
    ay_tbrg_no_claim randomFallbackMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro randomFallbackMismatch fallbackPublic

theorem ay_tbrg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_tbrg_no_claim replayMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro replayMismatch fallbackPublic

theorem ay_tbrg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_tbrg_no_claim fallbackFailure fallbackPublic :=
  ay_tbrg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_tbrg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_tbrg_no_claim buildMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro buildMismatch fallbackPublic

theorem ay_tbrg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_tbrg_no_claim validatorRejection fallbackPublic :=
  ay_tbrg_no_claim_intro validatorRejection fallbackPublic

theorem ay_tbrg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_tbrg_no_claim auditMismatch fallbackPublic :=
  ay_tbrg_no_claim_intro auditMismatch fallbackPublic

theorem ay_tbrg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_tbrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_tbrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_tbrg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_tbrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_tbrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_tbrg_accepted_tiebreak_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  ay_tbrg_accepted_tiebreak_hint_hint guardEvidence agreementEvidence
    branchingOrderHint

theorem ay_tbrg_accepted_tiebreak_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_tbrg_accepted_tiebreak_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      (ay_tbrg_accepted_tiebreak_hint_agreement guardEvidence agreementEvidence
        branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_tbrg_accepted_tiebreak_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_tbrg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_tbrg_public_report_intro guardEvidence satOutcome satTruth
      (ay_tbrg_accepted_tiebreak_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      satH
      truthH

theorem ay_tbrg_accepted_tiebreak_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_tbrg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_tbrg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_tbrg_accepted_tiebreak_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_tbrg_tiebreaking_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_tbrg_accepted_tiebreak_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_tbrg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_tbrg_equisat_intro formulaBefore formulaAfter
      (forward (ay_tbrg_accepted_tiebreak_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
      (backward (ay_tbrg_accepted_tiebreak_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
