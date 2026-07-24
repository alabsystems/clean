-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-heap snapshot/restore guard skeleton for sequential-main SAT-COMP
-- branching. Heap restore is search-control only when heap, domain, activity,
-- epoch, checkpoint, replay, fallback, build, validator, and audit evidence
-- agree with the checked public result.

def ay_dhrg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dhrg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_dhrg_conj (before -> after) (after -> before)

def ay_dhrg_guard
    (heapSnapshotDigest : Prop)
    (liveVariableDomainManifest : Prop)
    (activityTiebreakManifest : Prop)
    (restoreEpochLedger : Prop)
    (decisionStackCheckpoint : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (heapSnapshotDigest ->
      liveVariableDomainManifest ->
      activityTiebreakManifest ->
      restoreEpochLedger ->
      decisionStackCheckpoint ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_dhrg_agreement
    (heapDigestMatch : Prop)
    (domainMatch : Prop)
    (activityTiebreakMatch : Prop)
    (epochMatch : Prop)
    (checkpointMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_dhrg_guard heapDigestMatch domainMatch activityTiebreakMatch epochMatch
    checkpointMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_dhrg_accepted_restore
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_dhrg_conj guardEvidence
    (ay_dhrg_conj agreementEvidence
      (ay_dhrg_conj branchOrderRelation searchControlHint))

def ay_dhrg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_dhrg_conj acceptedEvidence (ay_dhrg_conj outcome formulaTruth)

def ay_dhrg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_dhrg_conj diagnostic fallbackPublic

theorem ay_dhrg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_dhrg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_dhrg_conj_left (left : Prop) (right : Prop) :
    ay_dhrg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_dhrg_conj_right (left : Prop) (right : Prop) :
    ay_dhrg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_dhrg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_dhrg_equisat before after :=
  fun forward backward =>
    ay_dhrg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_dhrg_equisat_forward (before : Prop) (after : Prop) :
    ay_dhrg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_dhrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dhrg_equisat_backward (before : Prop) (after : Prop) :
    ay_dhrg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_dhrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dhrg_guard_intro
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    heapSnapshotDigest ->
    liveVariableDomainManifest ->
    activityTiebreakManifest ->
    restoreEpochLedger ->
    decisionStackCheckpoint ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun heapH domainH activityH epochH checkpointH replayH fallbackH buildH
      validatorH auditH result make =>
    make heapH domainH activityH epochH checkpointH replayH fallbackH buildH
      validatorH auditH

theorem ay_dhrg_guard_heap
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    heapSnapshotDigest :=
  fun guard =>
    guard heapSnapshotDigest
      (fun heapH _domainH _activityH _epochH _checkpointH _replayH
          _fallbackH _buildH _validatorH _auditH => heapH)

theorem ay_dhrg_guard_domain
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    liveVariableDomainManifest :=
  fun guard =>
    guard liveVariableDomainManifest
      (fun _heapH domainH _activityH _epochH _checkpointH _replayH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_dhrg_guard_activity
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    activityTiebreakManifest :=
  fun guard =>
    guard activityTiebreakManifest
      (fun _heapH _domainH activityH _epochH _checkpointH _replayH
          _fallbackH _buildH _validatorH _auditH => activityH)

theorem ay_dhrg_guard_epoch
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    restoreEpochLedger :=
  fun guard =>
    guard restoreEpochLedger
      (fun _heapH _domainH _activityH epochH _checkpointH _replayH
          _fallbackH _buildH _validatorH _auditH => epochH)

theorem ay_dhrg_guard_checkpoint
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    decisionStackCheckpoint :=
  fun guard =>
    guard decisionStackCheckpoint
      (fun _heapH _domainH _activityH _epochH checkpointH _replayH
          _fallbackH _buildH _validatorH _auditH => checkpointH)

theorem ay_dhrg_guard_replay
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _heapH _domainH _activityH _epochH _checkpointH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_dhrg_guard_fallback
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _heapH _domainH _activityH _epochH _checkpointH _replayH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_dhrg_guard_build
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _heapH _domainH _activityH _epochH _checkpointH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_dhrg_guard_validator
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _heapH _domainH _activityH _epochH _checkpointH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_dhrg_guard_audit
    (heapSnapshotDigest liveVariableDomainManifest activityTiebreakManifest
      restoreEpochLedger decisionStackCheckpoint propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard heapSnapshotDigest liveVariableDomainManifest
      activityTiebreakManifest restoreEpochLedger decisionStackCheckpoint
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _heapH _domainH _activityH _epochH _checkpointH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_dhrg_agreement_intro
    (heapDigestMatch domainMatch activityTiebreakMatch epochMatch
      checkpointMatch replayMatch fallbackMatch buildMatch validatorAccepts
      auditMatch : Prop) :
    heapDigestMatch ->
    domainMatch ->
    activityTiebreakMatch ->
    epochMatch ->
    checkpointMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_dhrg_agreement heapDigestMatch domainMatch activityTiebreakMatch
      epochMatch checkpointMatch replayMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  ay_dhrg_guard_intro heapDigestMatch domainMatch activityTiebreakMatch
    epochMatch checkpointMatch replayMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_dhrg_accepted_restore_intro
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchOrderRelation ->
    searchControlHint ->
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_dhrg_conj_intro guardEvidence
      (ay_dhrg_conj agreementEvidence
        (ay_dhrg_conj branchOrderRelation searchControlHint))
      guardH
      (ay_dhrg_conj_intro agreementEvidence
        (ay_dhrg_conj branchOrderRelation searchControlHint)
        agreementH
        (ay_dhrg_conj_intro branchOrderRelation searchControlHint orderH
          hintH))

theorem ay_dhrg_accepted_restore_guard
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_dhrg_conj_left guardEvidence
      (ay_dhrg_conj agreementEvidence
        (ay_dhrg_conj branchOrderRelation searchControlHint))
      accepted

theorem ay_dhrg_accepted_restore_agreement
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_dhrg_conj_left agreementEvidence
      (ay_dhrg_conj branchOrderRelation searchControlHint)
      (ay_dhrg_conj_right guardEvidence
        (ay_dhrg_conj agreementEvidence
          (ay_dhrg_conj branchOrderRelation searchControlHint))
        accepted)

theorem ay_dhrg_accepted_restore_order
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  fun accepted =>
    ay_dhrg_conj_left branchOrderRelation searchControlHint
      (ay_dhrg_conj_right agreementEvidence
        (ay_dhrg_conj branchOrderRelation searchControlHint)
        (ay_dhrg_conj_right guardEvidence
          (ay_dhrg_conj agreementEvidence
            (ay_dhrg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_dhrg_accepted_restore_hint
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_dhrg_conj_right branchOrderRelation searchControlHint
      (ay_dhrg_conj_right agreementEvidence
        (ay_dhrg_conj branchOrderRelation searchControlHint)
        (ay_dhrg_conj_right guardEvidence
          (ay_dhrg_conj agreementEvidence
            (ay_dhrg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_dhrg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_dhrg_conj_intro acceptedEvidence
      (ay_dhrg_conj outcome formulaTruth)
      acceptedH (ay_dhrg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_dhrg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_dhrg_conj_left acceptedEvidence (ay_dhrg_conj outcome formulaTruth)
      report

theorem ay_dhrg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_dhrg_conj_right outcome formulaTruth
      (ay_dhrg_conj_right acceptedEvidence
        (ay_dhrg_conj outcome formulaTruth) report)

theorem ay_dhrg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_dhrg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_dhrg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_dhrg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_dhrg_conj_right diagnostic fallbackPublic noClaim

theorem ay_dhrg_digest_mismatch_no_claim
    (digestMismatch fallbackPublic : Prop) :
    digestMismatch -> fallbackPublic ->
    ay_dhrg_no_claim digestMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro digestMismatch fallbackPublic

theorem ay_dhrg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_dhrg_no_claim domainMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro domainMismatch fallbackPublic

theorem ay_dhrg_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch -> fallbackPublic ->
    ay_dhrg_no_claim activityMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro activityMismatch fallbackPublic

theorem ay_dhrg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch -> fallbackPublic ->
    ay_dhrg_no_claim epochMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro epochMismatch fallbackPublic

theorem ay_dhrg_checkpoint_mismatch_no_claim
    (checkpointMismatch fallbackPublic : Prop) :
    checkpointMismatch -> fallbackPublic ->
    ay_dhrg_no_claim checkpointMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro checkpointMismatch fallbackPublic

theorem ay_dhrg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_dhrg_no_claim replayMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro replayMismatch fallbackPublic

theorem ay_dhrg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_dhrg_no_claim buildMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro buildMismatch fallbackPublic

theorem ay_dhrg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_dhrg_no_claim validatorRejection fallbackPublic :=
  ay_dhrg_no_claim_intro validatorRejection fallbackPublic

theorem ay_dhrg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_dhrg_no_claim auditMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro auditMismatch fallbackPublic

theorem ay_dhrg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_dhrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_dhrg_failed_restore_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_dhrg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_dhrg_accepted_restore_is_search_control
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  ay_dhrg_accepted_restore_hint guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_dhrg_accepted_restore_preserves_branch_order
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  ay_dhrg_accepted_restore_order guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_dhrg_accepted_restore_preserves_public_soundness
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (guardEvidence -> agreementEvidence -> branchOrderRelation -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_dhrg_accepted_restore_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_dhrg_accepted_restore_agreement guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_dhrg_accepted_restore_order guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      outcomeH
      truthH

theorem ay_dhrg_accepted_restore_guides_sat
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      satOutcome satTruth : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_dhrg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_dhrg_public_report_intro guardEvidence satOutcome satTruth
      (ay_dhrg_accepted_restore_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      satH
      truthH

theorem ay_dhrg_accepted_restore_guides_unsat
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_dhrg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_dhrg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_dhrg_accepted_restore_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      unsatH
      truthH

theorem ay_dhrg_heap_restore_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      branchOrderRelation searchControlHint : Prop) :
    ay_dhrg_accepted_restore guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (searchControlHint -> branchOrderRelation -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> branchOrderRelation -> formulaAfter ->
      formulaBefore) ->
    ay_dhrg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_dhrg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_dhrg_accepted_restore_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_dhrg_accepted_restore_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
      (backward
        (ay_dhrg_accepted_restore_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_dhrg_accepted_restore_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
