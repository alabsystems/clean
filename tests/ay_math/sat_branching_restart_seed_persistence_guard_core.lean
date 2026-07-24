-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart-seed persistence guard skeleton for sequential-main SAT-COMP
-- branching/restart persistence. Restored seed state is a branching/restart
-- ordering hint only when restart, seed, stream, heap, replay, fallback,
-- build, validator, and audit evidence agree with the checked public result.

def ay_rspg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rspg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rspg_conj (before -> after) (after -> before)

def ay_rspg_guard
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (restartEpochLedger ->
      seedManifest ->
      streamDigest ->
      heapSnapshotDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rspg_agreement
    (restartEpochMatch : Prop)
    (seedMatch : Prop)
    (streamMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_rspg_guard restartEpochMatch seedMatch streamMatch heapSnapshotMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_rspg_accepted_seed_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) : Prop :=
  ay_rspg_conj guardEvidence
    (ay_rspg_conj agreementEvidence branchingRestartHint)

def ay_rspg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_rspg_conj acceptedEvidence (ay_rspg_conj outcome formulaTruth)

def ay_rspg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_rspg_conj diagnostic fallbackPublic

theorem ay_rspg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_rspg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rspg_conj_left (left : Prop) (right : Prop) :
    ay_rspg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rspg_conj_right (left : Prop) (right : Prop) :
    ay_rspg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rspg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_rspg_equisat before after :=
  fun forward backward =>
    ay_rspg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rspg_equisat_forward (before : Prop) (after : Prop) :
    ay_rspg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rspg_conj_left (before -> after) (after -> before) eqsat

theorem ay_rspg_equisat_backward (before : Prop) (after : Prop) :
    ay_rspg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rspg_conj_right (before -> after) (after -> before) eqsat

theorem ay_rspg_guard_intro
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    restartEpochLedger ->
    seedManifest ->
    streamDigest ->
    heapSnapshotDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun restartH seedH streamH heapH replayH fallbackH buildH validatorH
      auditH result make =>
    make restartH seedH streamH heapH replayH fallbackH buildH validatorH
      auditH

theorem ay_rspg_guard_restart
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    restartEpochLedger :=
  fun guard =>
    guard restartEpochLedger
      (fun restartH _seedH _streamH _heapH _replayH _fallbackH _buildH
          _validatorH _auditH => restartH)

theorem ay_rspg_guard_seed
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    seedManifest :=
  fun guard =>
    guard seedManifest
      (fun _restartH seedH _streamH _heapH _replayH _fallbackH _buildH
          _validatorH _auditH => seedH)

theorem ay_rspg_guard_stream
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    streamDigest :=
  fun guard =>
    guard streamDigest
      (fun _restartH _seedH streamH _heapH _replayH _fallbackH _buildH
          _validatorH _auditH => streamH)

theorem ay_rspg_guard_heap
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    heapSnapshotDigest :=
  fun guard =>
    guard heapSnapshotDigest
      (fun _restartH _seedH _streamH heapH _replayH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_rspg_guard_replay
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _restartH _seedH _streamH _heapH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_rspg_guard_fallback
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _restartH _seedH _streamH _heapH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_rspg_guard_build
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _restartH _seedH _streamH _heapH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_rspg_guard_validator
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _restartH _seedH _streamH _heapH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_rspg_guard_audit
    (restartEpochLedger : Prop)
    (seedManifest : Prop)
    (streamDigest : Prop)
    (heapSnapshotDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rspg_guard restartEpochLedger seedManifest streamDigest
      heapSnapshotDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _restartH _seedH _streamH _heapH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_rspg_agreement_intro
    (restartEpochMatch : Prop)
    (seedMatch : Prop)
    (streamMatch : Prop)
    (heapSnapshotMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    restartEpochMatch ->
    seedMatch ->
    streamMatch ->
    heapSnapshotMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rspg_agreement restartEpochMatch seedMatch streamMatch
      heapSnapshotMatch replayMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_rspg_guard_intro restartEpochMatch seedMatch streamMatch
    heapSnapshotMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_rspg_accepted_seed_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingRestartHint ->
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint :=
  fun guardH agreementH hintH =>
    ay_rspg_conj_intro guardEvidence
      (ay_rspg_conj agreementEvidence branchingRestartHint)
      guardH
      (ay_rspg_conj_intro agreementEvidence branchingRestartHint agreementH
        hintH)

theorem ay_rspg_accepted_seed_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    guardEvidence :=
  fun accepted =>
    ay_rspg_conj_left guardEvidence
      (ay_rspg_conj agreementEvidence branchingRestartHint) accepted

theorem ay_rspg_accepted_seed_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    agreementEvidence :=
  fun accepted =>
    ay_rspg_conj_left agreementEvidence branchingRestartHint
      (ay_rspg_conj_right guardEvidence
        (ay_rspg_conj agreementEvidence branchingRestartHint) accepted)

theorem ay_rspg_accepted_seed_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    branchingRestartHint :=
  fun accepted =>
    ay_rspg_conj_right agreementEvidence branchingRestartHint
      (ay_rspg_conj_right guardEvidence
        (ay_rspg_conj agreementEvidence branchingRestartHint) accepted)

theorem ay_rspg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rspg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rspg_conj_intro acceptedEvidence
      (ay_rspg_conj outcome formulaTruth)
      acceptedH (ay_rspg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rspg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rspg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_rspg_conj_left acceptedEvidence (ay_rspg_conj outcome formulaTruth)
      report

theorem ay_rspg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rspg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rspg_conj_right outcome formulaTruth
      (ay_rspg_conj_right acceptedEvidence
        (ay_rspg_conj outcome formulaTruth) report)

theorem ay_rspg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_rspg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_rspg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_rspg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rspg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_rspg_conj_right diagnostic fallbackPublic noClaim

theorem ay_rspg_restart_epoch_mismatch_no_claim
    (restartEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    restartEpochMismatch -> fallbackPublic ->
    ay_rspg_no_claim restartEpochMismatch fallbackPublic :=
  ay_rspg_no_claim_intro restartEpochMismatch fallbackPublic

theorem ay_rspg_seed_mismatch_no_claim
    (seedMismatch : Prop)
    (fallbackPublic : Prop) :
    seedMismatch -> fallbackPublic ->
    ay_rspg_no_claim seedMismatch fallbackPublic :=
  ay_rspg_no_claim_intro seedMismatch fallbackPublic

theorem ay_rspg_stream_mismatch_no_claim
    (streamMismatch : Prop)
    (fallbackPublic : Prop) :
    streamMismatch -> fallbackPublic ->
    ay_rspg_no_claim streamMismatch fallbackPublic :=
  ay_rspg_no_claim_intro streamMismatch fallbackPublic

theorem ay_rspg_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_rspg_no_claim heapMismatch fallbackPublic :=
  ay_rspg_no_claim_intro heapMismatch fallbackPublic

theorem ay_rspg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_rspg_no_claim replayMismatch fallbackPublic :=
  ay_rspg_no_claim_intro replayMismatch fallbackPublic

theorem ay_rspg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_rspg_no_claim fallbackFailure fallbackPublic :=
  ay_rspg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_rspg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_rspg_no_claim buildMismatch fallbackPublic :=
  ay_rspg_no_claim_intro buildMismatch fallbackPublic

theorem ay_rspg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_rspg_no_claim validatorRejection fallbackPublic :=
  ay_rspg_no_claim_intro validatorRejection fallbackPublic

theorem ay_rspg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_rspg_no_claim auditMismatch fallbackPublic :=
  ay_rspg_no_claim_intro auditMismatch fallbackPublic

theorem ay_rspg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_rspg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_rspg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_rspg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_rspg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_rspg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_rspg_accepted_seed_is_branching_restart_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    branchingRestartHint :=
  ay_rspg_accepted_seed_hint_hint guardEvidence agreementEvidence
    branchingRestartHint

theorem ay_rspg_accepted_seed_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_rspg_accepted_seed_hint_guard guardEvidence agreementEvidence
        branchingRestartHint accepted)
      (ay_rspg_accepted_seed_hint_agreement guardEvidence agreementEvidence
        branchingRestartHint accepted)
      outcomeH
      truthH

theorem ay_rspg_accepted_seed_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    satOutcome ->
    satTruth ->
    ay_rspg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_rspg_public_report_intro guardEvidence satOutcome satTruth
      (ay_rspg_accepted_seed_hint_guard guardEvidence agreementEvidence
        branchingRestartHint accepted)
      satH
      truthH

theorem ay_rspg_accepted_seed_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_rspg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_rspg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_rspg_accepted_seed_hint_guard guardEvidence agreementEvidence
        branchingRestartHint accepted)
      unsatH
      truthH

theorem ay_rspg_restored_seed_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingRestartHint : Prop) :
    ay_rspg_accepted_seed_hint guardEvidence agreementEvidence
      branchingRestartHint ->
    (branchingRestartHint -> formulaBefore -> formulaAfter) ->
    (branchingRestartHint -> formulaAfter -> formulaBefore) ->
    ay_rspg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_rspg_equisat_intro formulaBefore formulaAfter
      (forward (ay_rspg_accepted_seed_hint_hint guardEvidence
        agreementEvidence branchingRestartHint accepted))
      (backward (ay_rspg_accepted_seed_hint_hint guardEvidence
        agreementEvidence branchingRestartHint accepted))
