-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Heap persistence snapshot guard skeleton for sequential-main SAT-COMP
-- branching. Restored heap state is a branching-order hint only when
-- persistence, heap, activity, scope, replay, fallback, build, validator, and
-- audit evidence agree with the checked public outcome path.

def ay_hpsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_hpsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_hpsg_conj (before -> after) (after -> before)

def ay_hpsg_guard
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (persistenceEpochLedger ->
      heapSnapshotDigest ->
      variableActivityDigest ->
      levelScopeDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_hpsg_agreement
    (persistenceEpochMatch : Prop)
    (heapSnapshotMatch : Prop)
    (activityDigestMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_hpsg_guard persistenceEpochMatch heapSnapshotMatch activityDigestMatch
    levelScopeMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_hpsg_accepted_heap_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_hpsg_conj guardEvidence
    (ay_hpsg_conj agreementEvidence branchingOrderHint)

def ay_hpsg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_hpsg_conj acceptedEvidence (ay_hpsg_conj outcome formulaTruth)

def ay_hpsg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_hpsg_conj diagnostic fallbackPublic

theorem ay_hpsg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_hpsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_hpsg_conj_left (left : Prop) (right : Prop) :
    ay_hpsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_hpsg_conj_right (left : Prop) (right : Prop) :
    ay_hpsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_hpsg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_hpsg_equisat before after :=
  fun forward backward =>
    ay_hpsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_hpsg_equisat_forward (before : Prop) (after : Prop) :
    ay_hpsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_hpsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_hpsg_equisat_backward (before : Prop) (after : Prop) :
    ay_hpsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_hpsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_hpsg_guard_intro
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    persistenceEpochLedger ->
    heapSnapshotDigest ->
    variableActivityDigest ->
    levelScopeDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript :=
  fun epochH heapH activityH levelH replayH fallbackH buildH validatorH
      auditH result make =>
    make epochH heapH activityH levelH replayH fallbackH buildH validatorH
      auditH

theorem ay_hpsg_guard_persistence_epoch
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    persistenceEpochLedger :=
  fun guard =>
    guard persistenceEpochLedger
      (fun epochH _heapH _activityH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_hpsg_guard_heap_snapshot
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    heapSnapshotDigest :=
  fun guard =>
    guard heapSnapshotDigest
      (fun _epochH heapH _activityH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_hpsg_guard_activity_digest
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    variableActivityDigest :=
  fun guard =>
    guard variableActivityDigest
      (fun _epochH _heapH activityH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_hpsg_guard_level_scope
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _epochH _heapH _activityH levelH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_hpsg_guard_replay
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _heapH _activityH _levelH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_hpsg_guard_fallback
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _heapH _activityH _levelH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_hpsg_guard_build
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _heapH _activityH _levelH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_hpsg_guard_validator
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _heapH _activityH _levelH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_hpsg_guard_audit
    (persistenceEpochLedger : Prop)
    (heapSnapshotDigest : Prop)
    (variableActivityDigest : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hpsg_guard persistenceEpochLedger heapSnapshotDigest
      variableActivityDigest levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _heapH _activityH _levelH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_hpsg_agreement_intro
    (persistenceEpochMatch : Prop)
    (heapSnapshotMatch : Prop)
    (activityDigestMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    persistenceEpochMatch ->
    heapSnapshotMatch ->
    activityDigestMatch ->
    levelScopeMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_hpsg_agreement persistenceEpochMatch heapSnapshotMatch
      activityDigestMatch levelScopeMatch replayMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  ay_hpsg_guard_intro persistenceEpochMatch heapSnapshotMatch
    activityDigestMatch levelScopeMatch replayMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_hpsg_accepted_heap_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingOrderHint ->
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint :=
  fun guardH agreementH hintH =>
    ay_hpsg_conj_intro guardEvidence
      (ay_hpsg_conj agreementEvidence branchingOrderHint)
      guardH
      (ay_hpsg_conj_intro agreementEvidence branchingOrderHint agreementH
        hintH)

theorem ay_hpsg_accepted_heap_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_hpsg_conj_left guardEvidence
      (ay_hpsg_conj agreementEvidence branchingOrderHint) accepted

theorem ay_hpsg_accepted_heap_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_hpsg_conj_left agreementEvidence branchingOrderHint
      (ay_hpsg_conj_right guardEvidence
        (ay_hpsg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_hpsg_accepted_heap_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_hpsg_conj_right agreementEvidence branchingOrderHint
      (ay_hpsg_conj_right guardEvidence
        (ay_hpsg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_hpsg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_hpsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_hpsg_conj_intro acceptedEvidence
      (ay_hpsg_conj outcome formulaTruth)
      acceptedH (ay_hpsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_hpsg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_hpsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_hpsg_conj_left acceptedEvidence (ay_hpsg_conj outcome formulaTruth)
      report

theorem ay_hpsg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_hpsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_hpsg_conj_right outcome formulaTruth
      (ay_hpsg_conj_right acceptedEvidence
        (ay_hpsg_conj outcome formulaTruth) report)

theorem ay_hpsg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_hpsg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_hpsg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_hpsg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_hpsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_hpsg_conj_right diagnostic fallbackPublic noClaim

theorem ay_hpsg_persistence_epoch_mismatch_no_claim
    (persistenceEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    persistenceEpochMismatch -> fallbackPublic ->
    ay_hpsg_no_claim persistenceEpochMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro persistenceEpochMismatch fallbackPublic

theorem ay_hpsg_heap_snapshot_mismatch_no_claim
    (heapSnapshotMismatch : Prop)
    (fallbackPublic : Prop) :
    heapSnapshotMismatch -> fallbackPublic ->
    ay_hpsg_no_claim heapSnapshotMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro heapSnapshotMismatch fallbackPublic

theorem ay_hpsg_activity_digest_mismatch_no_claim
    (activityDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    activityDigestMismatch -> fallbackPublic ->
    ay_hpsg_no_claim activityDigestMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro activityDigestMismatch fallbackPublic

theorem ay_hpsg_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_hpsg_no_claim levelScopeMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_hpsg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_hpsg_no_claim replayMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_hpsg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_hpsg_no_claim fallbackFailure fallbackPublic :=
  ay_hpsg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_hpsg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_hpsg_no_claim buildMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_hpsg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_hpsg_no_claim validatorRejection fallbackPublic :=
  ay_hpsg_no_claim_intro validatorRejection fallbackPublic

theorem ay_hpsg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_hpsg_no_claim auditMismatch fallbackPublic :=
  ay_hpsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_hpsg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_hpsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_hpsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_hpsg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_hpsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_hpsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_hpsg_accepted_heap_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  ay_hpsg_accepted_heap_hint_hint guardEvidence agreementEvidence
    branchingOrderHint

theorem ay_hpsg_accepted_heap_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_hpsg_accepted_heap_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      (ay_hpsg_accepted_heap_hint_agreement guardEvidence agreementEvidence
        branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_hpsg_accepted_heap_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_hpsg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_hpsg_public_report_intro guardEvidence satOutcome satTruth
      (ay_hpsg_accepted_heap_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      satH
      truthH

theorem ay_hpsg_accepted_heap_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_hpsg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_hpsg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_hpsg_accepted_heap_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_hpsg_restored_heap_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hpsg_accepted_heap_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_hpsg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_hpsg_equisat_intro formulaBefore formulaAfter
      (forward (ay_hpsg_accepted_heap_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
      (backward (ay_hpsg_accepted_heap_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
