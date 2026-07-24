-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-heap rebuild consistency guard skeleton for sequential-main
-- SAT-COMP branching. Heap rebuilds are branching-order hints only when heap,
-- activity, scope, replay, fallback, build, validator, and audit evidence
-- agree with the checked public outcome path.

def ay_hbrg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_hbrg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_hbrg_conj (before -> after) (after -> before)

def ay_hbrg_guard
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (heapEpochLedger ->
      variableActivityDigest ->
      heapMembershipSnapshot ->
      levelScopeDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_hbrg_agreement
    (heapEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (membershipSnapshotMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_hbrg_guard heapEpochMatch activityDigestMatch membershipSnapshotMatch
    levelScopeMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_hbrg_accepted_rebuild_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_hbrg_conj guardEvidence
    (ay_hbrg_conj agreementEvidence branchingOrderHint)

def ay_hbrg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_hbrg_conj acceptedEvidence (ay_hbrg_conj outcome formulaTruth)

def ay_hbrg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_hbrg_conj diagnostic fallbackPublic

theorem ay_hbrg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_hbrg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_hbrg_conj_left (left : Prop) (right : Prop) :
    ay_hbrg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_hbrg_conj_right (left : Prop) (right : Prop) :
    ay_hbrg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_hbrg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_hbrg_equisat before after :=
  fun forward backward =>
    ay_hbrg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_hbrg_equisat_forward (before : Prop) (after : Prop) :
    ay_hbrg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_hbrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_hbrg_equisat_backward (before : Prop) (after : Prop) :
    ay_hbrg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_hbrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_hbrg_guard_intro
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    heapEpochLedger ->
    variableActivityDigest ->
    heapMembershipSnapshot ->
    levelScopeDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript :=
  fun heapH activityH membershipH levelH replayH fallbackH buildH validatorH
      auditH result make =>
    make heapH activityH membershipH levelH replayH fallbackH buildH
      validatorH auditH

theorem ay_hbrg_guard_heap_epoch
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    heapEpochLedger :=
  fun guard =>
    guard heapEpochLedger
      (fun heapH _activityH _membershipH _levelH _replayH _fallbackH
          _buildH _validatorH _auditH => heapH)

theorem ay_hbrg_guard_activity_digest
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    variableActivityDigest :=
  fun guard =>
    guard variableActivityDigest
      (fun _heapH activityH _membershipH _levelH _replayH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_hbrg_guard_membership_snapshot
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    heapMembershipSnapshot :=
  fun guard =>
    guard heapMembershipSnapshot
      (fun _heapH _activityH membershipH _levelH _replayH _fallbackH
          _buildH _validatorH _auditH => membershipH)

theorem ay_hbrg_guard_level_scope
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _heapH _activityH _membershipH levelH _replayH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_hbrg_guard_replay
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _heapH _activityH _membershipH _levelH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_hbrg_guard_fallback
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _heapH _activityH _membershipH _levelH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_hbrg_guard_build
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _heapH _activityH _membershipH _levelH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_hbrg_guard_validator
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _heapH _activityH _membershipH _levelH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_hbrg_guard_audit
    (heapEpochLedger : Prop)
    (variableActivityDigest : Prop)
    (heapMembershipSnapshot : Prop)
    (levelScopeDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_hbrg_guard heapEpochLedger variableActivityDigest
      heapMembershipSnapshot levelScopeDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _heapH _activityH _membershipH _levelH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_hbrg_agreement_intro
    (heapEpochMatch : Prop)
    (activityDigestMatch : Prop)
    (membershipSnapshotMatch : Prop)
    (levelScopeMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    heapEpochMatch ->
    activityDigestMatch ->
    membershipSnapshotMatch ->
    levelScopeMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_hbrg_agreement heapEpochMatch activityDigestMatch
      membershipSnapshotMatch levelScopeMatch replayMatch fallbackMatch
      buildMatch validatorAccepts auditMatch :=
  ay_hbrg_guard_intro heapEpochMatch activityDigestMatch
    membershipSnapshotMatch levelScopeMatch replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

theorem ay_hbrg_accepted_rebuild_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingOrderHint ->
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint :=
  fun guardH agreementH hintH =>
    ay_hbrg_conj_intro guardEvidence
      (ay_hbrg_conj agreementEvidence branchingOrderHint)
      guardH
      (ay_hbrg_conj_intro agreementEvidence branchingOrderHint agreementH
        hintH)

theorem ay_hbrg_accepted_rebuild_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_hbrg_conj_left guardEvidence
      (ay_hbrg_conj agreementEvidence branchingOrderHint) accepted

theorem ay_hbrg_accepted_rebuild_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_hbrg_conj_left agreementEvidence branchingOrderHint
      (ay_hbrg_conj_right guardEvidence
        (ay_hbrg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_hbrg_accepted_rebuild_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_hbrg_conj_right agreementEvidence branchingOrderHint
      (ay_hbrg_conj_right guardEvidence
        (ay_hbrg_conj agreementEvidence branchingOrderHint) accepted)

theorem ay_hbrg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_hbrg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_hbrg_conj_intro acceptedEvidence
      (ay_hbrg_conj outcome formulaTruth)
      acceptedH (ay_hbrg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_hbrg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_hbrg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_hbrg_conj_left acceptedEvidence (ay_hbrg_conj outcome formulaTruth)
      report

theorem ay_hbrg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_hbrg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_hbrg_conj_right outcome formulaTruth
      (ay_hbrg_conj_right acceptedEvidence
        (ay_hbrg_conj outcome formulaTruth) report)

theorem ay_hbrg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_hbrg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_hbrg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_hbrg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_hbrg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_hbrg_conj_right diagnostic fallbackPublic noClaim

theorem ay_hbrg_heap_epoch_mismatch_no_claim
    (heapEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    heapEpochMismatch -> fallbackPublic ->
    ay_hbrg_no_claim heapEpochMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro heapEpochMismatch fallbackPublic

theorem ay_hbrg_activity_digest_mismatch_no_claim
    (activityDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    activityDigestMismatch -> fallbackPublic ->
    ay_hbrg_no_claim activityDigestMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro activityDigestMismatch fallbackPublic

theorem ay_hbrg_membership_snapshot_mismatch_no_claim
    (membershipSnapshotMismatch : Prop)
    (fallbackPublic : Prop) :
    membershipSnapshotMismatch -> fallbackPublic ->
    ay_hbrg_no_claim membershipSnapshotMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro membershipSnapshotMismatch fallbackPublic

theorem ay_hbrg_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_hbrg_no_claim levelScopeMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_hbrg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_hbrg_no_claim replayMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro replayMismatch fallbackPublic

theorem ay_hbrg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_hbrg_no_claim fallbackFailure fallbackPublic :=
  ay_hbrg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_hbrg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_hbrg_no_claim buildMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro buildMismatch fallbackPublic

theorem ay_hbrg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_hbrg_no_claim validatorRejection fallbackPublic :=
  ay_hbrg_no_claim_intro validatorRejection fallbackPublic

theorem ay_hbrg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_hbrg_no_claim auditMismatch fallbackPublic :=
  ay_hbrg_no_claim_intro auditMismatch fallbackPublic

theorem ay_hbrg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_hbrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_hbrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_hbrg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_hbrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_hbrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_hbrg_accepted_rebuild_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    branchingOrderHint :=
  ay_hbrg_accepted_rebuild_hint_hint guardEvidence agreementEvidence
    branchingOrderHint

theorem ay_hbrg_accepted_rebuild_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_hbrg_accepted_rebuild_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      (ay_hbrg_accepted_rebuild_hint_agreement guardEvidence agreementEvidence
        branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_hbrg_accepted_rebuild_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_hbrg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_hbrg_public_report_intro guardEvidence satOutcome satTruth
      (ay_hbrg_accepted_rebuild_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      satH
      truthH

theorem ay_hbrg_accepted_rebuild_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_hbrg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_hbrg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_hbrg_accepted_rebuild_hint_guard guardEvidence agreementEvidence
        branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_hbrg_heap_rebuild_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingOrderHint : Prop) :
    ay_hbrg_accepted_rebuild_hint guardEvidence agreementEvidence
      branchingOrderHint ->
    (branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_hbrg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_hbrg_equisat_intro formulaBefore formulaAfter
      (forward (ay_hbrg_accepted_rebuild_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
      (backward (ay_hbrg_accepted_rebuild_hint_hint guardEvidence
        agreementEvidence branchingOrderHint accepted))
