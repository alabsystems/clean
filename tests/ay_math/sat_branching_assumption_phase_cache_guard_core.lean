-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption phase-cache guard skeleton for sequential-main SAT-COMP
-- branching. Cached phases are branching-order hints under the same
-- assumption frame only when replay and publication evidence agree.

def ay_aphg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_aphg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_aphg_conj (before -> after) (after -> before)

def ay_aphg_guard
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionFrameLedger ->
      phaseCacheDigest ->
      decisionHeapSnapshot ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_aphg_agreement
    (assumptionFrameMatch : Prop)
    (phaseCacheMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_aphg_guard assumptionFrameMatch phaseCacheMatch heapSnapshotMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_aphg_accepted_cache_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) : Prop :=
  ay_aphg_conj guardEvidence
    (ay_aphg_conj agreementEvidence
      (ay_aphg_conj sameAssumptions branchingOrderHint))

def ay_aphg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_aphg_conj acceptedEvidence (ay_aphg_conj outcome formulaTruth)

def ay_aphg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_aphg_conj diagnostic fallbackPublic

theorem ay_aphg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_aphg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_aphg_conj_left (left : Prop) (right : Prop) :
    ay_aphg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_aphg_conj_right (left : Prop) (right : Prop) :
    ay_aphg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_aphg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_aphg_equisat before after :=
  fun forward backward =>
    ay_aphg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_aphg_equisat_forward (before : Prop) (after : Prop) :
    ay_aphg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_aphg_conj_left (before -> after) (after -> before) eqsat

theorem ay_aphg_equisat_backward (before : Prop) (after : Prop) :
    ay_aphg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_aphg_conj_right (before -> after) (after -> before) eqsat

theorem ay_aphg_guard_intro
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    assumptionFrameLedger ->
    phaseCacheDigest ->
    decisionHeapSnapshot ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun frameH cacheH heapH replayH fallbackH buildH validatorH auditH
      result make =>
    make frameH cacheH heapH replayH fallbackH buildH validatorH auditH

theorem ay_aphg_guard_assumption_frame
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    assumptionFrameLedger :=
  fun guard =>
    guard assumptionFrameLedger
      (fun frameH _cacheH _heapH _replayH _fallbackH _buildH _validatorH
          _auditH => frameH)

theorem ay_aphg_guard_phase_cache
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    phaseCacheDigest :=
  fun guard =>
    guard phaseCacheDigest
      (fun _frameH cacheH _heapH _replayH _fallbackH _buildH _validatorH
          _auditH => cacheH)

theorem ay_aphg_guard_heap
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionHeapSnapshot :=
  fun guard =>
    guard decisionHeapSnapshot
      (fun _frameH _cacheH heapH _replayH _fallbackH _buildH _validatorH
          _auditH => heapH)

theorem ay_aphg_guard_replay
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _frameH _cacheH _heapH replayH _fallbackH _buildH _validatorH
          _auditH => replayH)

theorem ay_aphg_guard_fallback
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _frameH _cacheH _heapH _replayH fallbackH _buildH _validatorH
          _auditH => fallbackH)

theorem ay_aphg_guard_build
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _frameH _cacheH _heapH _replayH _fallbackH buildH _validatorH
          _auditH => buildH)

theorem ay_aphg_guard_validator
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _frameH _cacheH _heapH _replayH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_aphg_guard_audit
    (assumptionFrameLedger : Prop)
    (phaseCacheDigest : Prop)
    (decisionHeapSnapshot : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_aphg_guard assumptionFrameLedger phaseCacheDigest
      decisionHeapSnapshot propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _frameH _cacheH _heapH _replayH _fallbackH _buildH _validatorH
          auditH => auditH)

theorem ay_aphg_agreement_intro
    (assumptionFrameMatch : Prop)
    (phaseCacheMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    assumptionFrameMatch ->
    phaseCacheMatch ->
    heapSnapshotMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_aphg_agreement assumptionFrameMatch phaseCacheMatch heapSnapshotMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_aphg_guard_intro assumptionFrameMatch phaseCacheMatch heapSnapshotMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_aphg_accepted_cache_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    sameAssumptions ->
    branchingOrderHint ->
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint :=
  fun guardH agreementH assumptionsH hintH =>
    ay_aphg_conj_intro guardEvidence
      (ay_aphg_conj agreementEvidence
        (ay_aphg_conj sameAssumptions branchingOrderHint))
      guardH
      (ay_aphg_conj_intro agreementEvidence
        (ay_aphg_conj sameAssumptions branchingOrderHint)
        agreementH
        (ay_aphg_conj_intro sameAssumptions branchingOrderHint
          assumptionsH hintH))

theorem ay_aphg_accepted_cache_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    guardEvidence :=
  fun accepted =>
    ay_aphg_conj_left guardEvidence
      (ay_aphg_conj agreementEvidence
        (ay_aphg_conj sameAssumptions branchingOrderHint))
      accepted

theorem ay_aphg_accepted_cache_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    agreementEvidence :=
  fun accepted =>
    ay_aphg_conj_left agreementEvidence
      (ay_aphg_conj sameAssumptions branchingOrderHint)
      (ay_aphg_conj_right guardEvidence
        (ay_aphg_conj agreementEvidence
          (ay_aphg_conj sameAssumptions branchingOrderHint))
        accepted)

theorem ay_aphg_accepted_cache_hint_same_assumptions
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    sameAssumptions :=
  fun accepted =>
    ay_aphg_conj_left sameAssumptions branchingOrderHint
      (ay_aphg_conj_right agreementEvidence
        (ay_aphg_conj sameAssumptions branchingOrderHint)
        (ay_aphg_conj_right guardEvidence
          (ay_aphg_conj agreementEvidence
            (ay_aphg_conj sameAssumptions branchingOrderHint))
          accepted))

theorem ay_aphg_accepted_cache_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    branchingOrderHint :=
  fun accepted =>
    ay_aphg_conj_right sameAssumptions branchingOrderHint
      (ay_aphg_conj_right agreementEvidence
        (ay_aphg_conj sameAssumptions branchingOrderHint)
        (ay_aphg_conj_right guardEvidence
          (ay_aphg_conj agreementEvidence
            (ay_aphg_conj sameAssumptions branchingOrderHint))
          accepted))

theorem ay_aphg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_aphg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_aphg_conj_intro acceptedEvidence
      (ay_aphg_conj outcome formulaTruth)
      acceptedH (ay_aphg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_aphg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_aphg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_aphg_conj_left acceptedEvidence (ay_aphg_conj outcome formulaTruth)
      report

theorem ay_aphg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_aphg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_aphg_conj_right outcome formulaTruth
      (ay_aphg_conj_right acceptedEvidence
        (ay_aphg_conj outcome formulaTruth) report)

theorem ay_aphg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_aphg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_aphg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_aphg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_aphg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_aphg_conj_right diagnostic fallbackPublic noClaim

theorem ay_aphg_assumption_frame_mismatch_no_claim
    (assumptionFrameMismatch : Prop)
    (fallbackPublic : Prop) :
    assumptionFrameMismatch -> fallbackPublic ->
    ay_aphg_no_claim assumptionFrameMismatch fallbackPublic :=
  ay_aphg_no_claim_intro assumptionFrameMismatch fallbackPublic

theorem ay_aphg_phase_cache_mismatch_no_claim
    (phaseCacheMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseCacheMismatch -> fallbackPublic ->
    ay_aphg_no_claim phaseCacheMismatch fallbackPublic :=
  ay_aphg_no_claim_intro phaseCacheMismatch fallbackPublic

theorem ay_aphg_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_aphg_no_claim heapMismatch fallbackPublic :=
  ay_aphg_no_claim_intro heapMismatch fallbackPublic

theorem ay_aphg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_aphg_no_claim replayMismatch fallbackPublic :=
  ay_aphg_no_claim_intro replayMismatch fallbackPublic

theorem ay_aphg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_aphg_no_claim fallbackFailure fallbackPublic :=
  ay_aphg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_aphg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_aphg_no_claim buildMismatch fallbackPublic :=
  ay_aphg_no_claim_intro buildMismatch fallbackPublic

theorem ay_aphg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_aphg_no_claim validatorRejection fallbackPublic :=
  ay_aphg_no_claim_intro validatorRejection fallbackPublic

theorem ay_aphg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_aphg_no_claim auditMismatch fallbackPublic :=
  ay_aphg_no_claim_intro auditMismatch fallbackPublic

theorem ay_aphg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_aphg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_aphg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_aphg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_aphg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_aphg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_aphg_accepted_cache_is_branching_order_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    branchingOrderHint :=
  ay_aphg_accepted_cache_hint_hint guardEvidence agreementEvidence
    sameAssumptions branchingOrderHint

theorem ay_aphg_accepted_cache_under_same_assumptions
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    sameAssumptions :=
  ay_aphg_accepted_cache_hint_same_assumptions guardEvidence agreementEvidence
    sameAssumptions branchingOrderHint

theorem ay_aphg_accepted_cache_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    (guardEvidence -> agreementEvidence -> sameAssumptions -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_aphg_accepted_cache_hint_guard guardEvidence agreementEvidence
        sameAssumptions branchingOrderHint accepted)
      (ay_aphg_accepted_cache_hint_agreement guardEvidence agreementEvidence
        sameAssumptions branchingOrderHint accepted)
      (ay_aphg_accepted_cache_hint_same_assumptions guardEvidence
        agreementEvidence sameAssumptions branchingOrderHint accepted)
      outcomeH
      truthH

theorem ay_aphg_accepted_cache_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    satOutcome ->
    satTruth ->
    ay_aphg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_aphg_public_report_intro guardEvidence satOutcome satTruth
      (ay_aphg_accepted_cache_hint_guard guardEvidence agreementEvidence
        sameAssumptions branchingOrderHint accepted)
      satH
      truthH

theorem ay_aphg_accepted_cache_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_aphg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_aphg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_aphg_accepted_cache_hint_guard guardEvidence agreementEvidence
        sameAssumptions branchingOrderHint accepted)
      unsatH
      truthH

theorem ay_aphg_phase_cache_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (sameAssumptions : Prop)
    (branchingOrderHint : Prop) :
    ay_aphg_accepted_cache_hint guardEvidence agreementEvidence
      sameAssumptions branchingOrderHint ->
    (sameAssumptions -> branchingOrderHint -> formulaBefore -> formulaAfter) ->
    (sameAssumptions -> branchingOrderHint -> formulaAfter -> formulaBefore) ->
    ay_aphg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_aphg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_aphg_accepted_cache_hint_same_assumptions guardEvidence
          agreementEvidence sameAssumptions branchingOrderHint accepted)
        (ay_aphg_accepted_cache_hint_hint guardEvidence agreementEvidence
          sameAssumptions branchingOrderHint accepted))
      (backward
        (ay_aphg_accepted_cache_hint_same_assumptions guardEvidence
          agreementEvidence sameAssumptions branchingOrderHint accepted)
        (ay_aphg_accepted_cache_hint_hint guardEvidence agreementEvidence
          sameAssumptions branchingOrderHint accepted))
