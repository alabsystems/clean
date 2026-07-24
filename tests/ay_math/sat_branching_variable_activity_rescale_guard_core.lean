-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-activity rescale guard skeleton for sequential-main SAT-COMP
-- branching. Activity rescaling is a branching-order hint only when activity,
-- heap, replay, fallback, build, validator, and audit evidence agree.

def ay_varg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_varg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_varg_conj (before -> after) (after -> before)

def ay_varg_guard
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (activityEpochLedger ->
      variableActivityDigest ->
      decisionHeapSnapshot ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_varg_agreement
    (activityEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_varg_guard activityEpochMatch activityDigestMatch heapSnapshotMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_varg_accepted_rescale_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_varg_conj guardEvidence
    (ay_varg_conj agreementEvidence branchingOrderHint)

def ay_varg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_varg_conj acceptedEvidence (ay_varg_conj outcome formulaTruth)

def ay_varg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_varg_conj diagnostic fallbackPublic

theorem ay_varg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_varg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_varg_conj_left (left : Prop) (right : Prop) :
    ay_varg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_varg_conj_right (left : Prop) (right : Prop) :
    ay_varg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_varg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_varg_equisat before after :=
  fun forward backward =>
    ay_varg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_varg_equisat_forward (before : Prop) (after : Prop) :
    ay_varg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_varg_conj_left (before -> after) (after -> before) eqsat

theorem ay_varg_equisat_backward (before : Prop) (after : Prop) :
    ay_varg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_varg_conj_right (before -> after) (after -> before) eqsat

theorem ay_varg_guard_intro
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    activityEpochLedger ->
    variableActivityDigest ->
    decisionHeapSnapshot ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun epochH activityH heapH replayH fallbackH buildH validatorH auditH
      result make =>
    make epochH activityH heapH replayH fallbackH buildH validatorH auditH

theorem ay_varg_guard_activity_epoch
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    activityEpochLedger :=
  fun guard =>
    guard activityEpochLedger
      (fun epochH _activityH _heapH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_varg_guard_activity_digest
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    variableActivityDigest :=
  fun guard =>
    guard variableActivityDigest
      (fun _epochH activityH _heapH _replayH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_varg_guard_heap_snapshot
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionHeapSnapshot :=
  fun guard =>
    guard decisionHeapSnapshot
      (fun _epochH _activityH heapH _replayH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_varg_guard_replay
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _activityH _heapH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_varg_guard_fallback
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _activityH _heapH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_varg_guard_build
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _activityH _heapH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_varg_guard_validator
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _activityH _heapH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_varg_guard_audit
    (activityEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_varg_guard activityEpochLedger variableActivityDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _activityH _heapH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_varg_agreement_intro
    (activityEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    activityEpochMatch ->
    activityDigestMatch ->
    heapSnapshotMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_varg_agreement activityEpochMatch activityDigestMatch heapSnapshotMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_varg_guard_intro activityEpochMatch activityDigestMatch heapSnapshotMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_varg_accepted_rescale_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingOrderHint ->
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint :=
  fun guardH agreementH hintH =>
    ay_varg_conj_intro guardEvidence
      (ay_varg_conj agreementEvidence branchingOrderHint)
      guardH
      (ay_varg_conj_intro agreementEvidence branchingOrderHint agreementH
        hintH)

theorem ay_varg_accepted_rescale_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_varg_conj_left guardEvidence
      (ay_varg_conj agreementEvidence branchingOrderHint) accepted

theorem ay_varg_accepted_rescale_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_varg_conj_left agreementEvidence branchingOrderHint
      (ay_varg_conj_right guardEvidence
        (ay_varg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_varg_accepted_rescale_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_varg_conj_right agreementEvidence branchingOrderHint
      (ay_varg_conj_right guardEvidence
        (ay_varg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_varg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_varg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_varg_conj_intro acceptedEvidence
      (ay_varg_conj outcome formulaTruth)
      acceptedH (ay_varg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_varg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_varg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_varg_conj_left acceptedEvidence (ay_varg_conj outcome formulaTruth)
      report

theorem ay_varg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_varg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_varg_conj_right outcome formulaTruth
      (ay_varg_conj_right acceptedEvidence
        (ay_varg_conj outcome formulaTruth) report)

theorem ay_varg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_varg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_varg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_varg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_varg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_varg_conj_right diagnostic fallbackPublic noClaim

theorem ay_varg_activity_epoch_mismatch_no_claim
    (activityEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    activityEpochMismatch -> fallbackPublic ->
    ay_varg_no_claim activityEpochMismatch fallbackPublic :=
  ay_varg_no_claim_intro activityEpochMismatch fallbackPublic

theorem ay_varg_activity_digest_mismatch_no_claim
    (activityDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    activityDigestMismatch -> fallbackPublic ->
    ay_varg_no_claim activityDigestMismatch fallbackPublic :=
  ay_varg_no_claim_intro activityDigestMismatch fallbackPublic

theorem ay_varg_heap_snapshot_mismatch_no_claim
    (heapSnapshotMismatch : Prop)
    (fallbackPublic : Prop) :
    heapSnapshotMismatch -> fallbackPublic ->
    ay_varg_no_claim heapSnapshotMismatch fallbackPublic :=
  ay_varg_no_claim_intro heapSnapshotMismatch fallbackPublic

theorem ay_varg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_varg_no_claim replayMismatch fallbackPublic :=
  ay_varg_no_claim_intro replayMismatch fallbackPublic

theorem ay_varg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_varg_no_claim fallbackFailure fallbackPublic :=
  ay_varg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_varg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_varg_no_claim buildMismatch fallbackPublic :=
  ay_varg_no_claim_intro buildMismatch fallbackPublic

theorem ay_varg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_varg_no_claim validatorRejection fallbackPublic :=
  ay_varg_no_claim_intro validatorRejection fallbackPublic

theorem ay_varg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_varg_no_claim auditMismatch fallbackPublic :=
  ay_varg_no_claim_intro auditMismatch fallbackPublic

theorem ay_varg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_varg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_varg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_varg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_varg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_varg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_varg_accepted_rescale_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  ay_varg_accepted_rescale_hint_hint guardEvidence agreementEvidence
    branchingOrderHint

theorem ay_varg_accepted_rescale_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_varg_accepted_rescale_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      (ay_varg_accepted_rescale_hint_agreement guardEvidence agreementEvidence
        branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_varg_accepted_rescale_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_varg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_varg_public_report_intro guardEvidence satOutcome satTruth
      (ay_varg_accepted_rescale_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      satH
      truthH

theorem ay_varg_accepted_rescale_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_varg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_varg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_varg_accepted_rescale_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_varg_rescaling_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_varg_accepted_rescale_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_varg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_varg_equisat_intro formulaBefore formulaAfter
      (forward (ay_varg_accepted_rescale_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
      (backward (ay_varg_accepted_rescale_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
