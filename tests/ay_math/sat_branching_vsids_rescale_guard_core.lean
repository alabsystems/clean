-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- VSIDS/activity rescale guard skeleton for sequential-main SAT-COMP
-- branching. Rescaling is search-control only when activity digests,
-- live-variable ordering, tiebreaks, restart epoch, replay, fallback, build,
-- validator, and audit evidence agree with the checked public result.

def ay_vrsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_vrsg_conj (before -> after) (after -> before)

def ay_vrsg_guard
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (activityBeforeDigest ->
      activityAfterDigest ->
      orderPreservationWitness ->
      tiebreakManifest ->
      restartEpoch ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_vrsg_agreement
    (beforeDigestMatch : Prop)
    (afterDigestMatch : Prop)
    (orderPreserved : Prop)
    (tiebreakMatch : Prop)
    (restartEpochMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_vrsg_guard beforeDigestMatch afterDigestMatch orderPreserved
    tiebreakMatch restartEpochMatch replayMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

def ay_vrsg_accepted_rescale
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_vrsg_conj guardEvidence
    (ay_vrsg_conj agreementEvidence
      (ay_vrsg_conj branchOrderRelation searchControlHint))

def ay_vrsg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_vrsg_conj acceptedEvidence (ay_vrsg_conj outcome formulaTruth)

def ay_vrsg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_vrsg_conj diagnostic fallbackPublic

theorem ay_vrsg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_vrsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_vrsg_conj_left (left : Prop) (right : Prop) :
    ay_vrsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_vrsg_conj_right (left : Prop) (right : Prop) :
    ay_vrsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_vrsg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_vrsg_equisat before after :=
  fun forward backward =>
    ay_vrsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_vrsg_equisat_forward (before : Prop) (after : Prop) :
    ay_vrsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_vrsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_vrsg_equisat_backward (before : Prop) (after : Prop) :
    ay_vrsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_vrsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_vrsg_guard_intro
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    activityBeforeDigest ->
    activityAfterDigest ->
    orderPreservationWitness ->
    tiebreakManifest ->
    restartEpoch ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun beforeH afterH orderH tiebreakH epochH replayH fallbackH buildH
      validatorH auditH result make =>
    make beforeH afterH orderH tiebreakH epochH replayH fallbackH buildH
      validatorH auditH

theorem ay_vrsg_guard_before_digest
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    activityBeforeDigest :=
  fun guard =>
    guard activityBeforeDigest
      (fun beforeH _afterH _orderH _tieH _epochH _replayH _fallbackH
          _buildH _validatorH _auditH => beforeH)

theorem ay_vrsg_guard_after_digest
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    activityAfterDigest :=
  fun guard =>
    guard activityAfterDigest
      (fun _beforeH afterH _orderH _tieH _epochH _replayH _fallbackH
          _buildH _validatorH _auditH => afterH)

theorem ay_vrsg_guard_order
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    orderPreservationWitness :=
  fun guard =>
    guard orderPreservationWitness
      (fun _beforeH _afterH orderH _tieH _epochH _replayH _fallbackH
          _buildH _validatorH _auditH => orderH)

theorem ay_vrsg_guard_tiebreak
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _beforeH _afterH _orderH tieH _epochH _replayH _fallbackH
          _buildH _validatorH _auditH => tieH)

theorem ay_vrsg_guard_restart_epoch
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    restartEpoch :=
  fun guard =>
    guard restartEpoch
      (fun _beforeH _afterH _orderH _tieH epochH _replayH _fallbackH
          _buildH _validatorH _auditH => epochH)

theorem ay_vrsg_guard_replay
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _beforeH _afterH _orderH _tieH _epochH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_vrsg_guard_fallback
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _beforeH _afterH _orderH _tieH _epochH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_vrsg_guard_build
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _beforeH _afterH _orderH _tieH _epochH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_vrsg_guard_validator
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _beforeH _afterH _orderH _tieH _epochH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_vrsg_guard_audit
    (activityBeforeDigest : Prop)
    (activityAfterDigest : Prop)
    (orderPreservationWitness : Prop)
    (tiebreakManifest : Prop)
    (restartEpoch : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vrsg_guard activityBeforeDigest activityAfterDigest
      orderPreservationWitness tiebreakManifest restartEpoch
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _beforeH _afterH _orderH _tieH _epochH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_vrsg_agreement_intro
    (beforeDigestMatch : Prop)
    (afterDigestMatch : Prop)
    (orderPreserved : Prop)
    (tiebreakMatch : Prop)
    (restartEpochMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    beforeDigestMatch ->
    afterDigestMatch ->
    orderPreserved ->
    tiebreakMatch ->
    restartEpochMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_vrsg_agreement beforeDigestMatch afterDigestMatch orderPreserved
      tiebreakMatch restartEpochMatch replayMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  ay_vrsg_guard_intro beforeDigestMatch afterDigestMatch orderPreserved
    tiebreakMatch restartEpochMatch replayMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_vrsg_accepted_rescale_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchOrderRelation ->
    searchControlHint ->
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_vrsg_conj_intro guardEvidence
      (ay_vrsg_conj agreementEvidence
        (ay_vrsg_conj branchOrderRelation searchControlHint))
      guardH
      (ay_vrsg_conj_intro agreementEvidence
        (ay_vrsg_conj branchOrderRelation searchControlHint)
        agreementH
        (ay_vrsg_conj_intro branchOrderRelation searchControlHint orderH
          hintH))

theorem ay_vrsg_accepted_rescale_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_vrsg_conj_left guardEvidence
      (ay_vrsg_conj agreementEvidence
        (ay_vrsg_conj branchOrderRelation searchControlHint))
      accepted

theorem ay_vrsg_accepted_rescale_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_vrsg_conj_left agreementEvidence
      (ay_vrsg_conj branchOrderRelation searchControlHint)
      (ay_vrsg_conj_right guardEvidence
        (ay_vrsg_conj agreementEvidence
          (ay_vrsg_conj branchOrderRelation searchControlHint))
        accepted)

theorem ay_vrsg_accepted_rescale_order
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  fun accepted =>
    ay_vrsg_conj_left branchOrderRelation searchControlHint
      (ay_vrsg_conj_right agreementEvidence
        (ay_vrsg_conj branchOrderRelation searchControlHint)
        (ay_vrsg_conj_right guardEvidence
          (ay_vrsg_conj agreementEvidence
            (ay_vrsg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_vrsg_accepted_rescale_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_vrsg_conj_right branchOrderRelation searchControlHint
      (ay_vrsg_conj_right agreementEvidence
        (ay_vrsg_conj branchOrderRelation searchControlHint)
        (ay_vrsg_conj_right guardEvidence
          (ay_vrsg_conj agreementEvidence
            (ay_vrsg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_vrsg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_vrsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_vrsg_conj_intro acceptedEvidence
      (ay_vrsg_conj outcome formulaTruth)
      acceptedH (ay_vrsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_vrsg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_vrsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_vrsg_conj_left acceptedEvidence (ay_vrsg_conj outcome formulaTruth)
      report

theorem ay_vrsg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_vrsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_vrsg_conj_right outcome formulaTruth
      (ay_vrsg_conj_right acceptedEvidence
        (ay_vrsg_conj outcome formulaTruth) report)

theorem ay_vrsg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_vrsg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_vrsg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_vrsg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_vrsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_vrsg_conj_right diagnostic fallbackPublic noClaim

theorem ay_vrsg_before_digest_mismatch_no_claim
    (beforeDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    beforeDigestMismatch -> fallbackPublic ->
    ay_vrsg_no_claim beforeDigestMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro beforeDigestMismatch fallbackPublic

theorem ay_vrsg_after_digest_mismatch_no_claim
    (afterDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    afterDigestMismatch -> fallbackPublic ->
    ay_vrsg_no_claim afterDigestMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro afterDigestMismatch fallbackPublic

theorem ay_vrsg_order_mismatch_no_claim
    (orderMismatch : Prop)
    (fallbackPublic : Prop) :
    orderMismatch -> fallbackPublic ->
    ay_vrsg_no_claim orderMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro orderMismatch fallbackPublic

theorem ay_vrsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch : Prop)
    (fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_vrsg_no_claim tiebreakMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_vrsg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_vrsg_no_claim replayMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_vrsg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_vrsg_no_claim buildMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_vrsg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_vrsg_no_claim validatorRejection fallbackPublic :=
  ay_vrsg_no_claim_intro validatorRejection fallbackPublic

theorem ay_vrsg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_vrsg_no_claim auditMismatch fallbackPublic :=
  ay_vrsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_vrsg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_vrsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_vrsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_vrsg_failed_rescale_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_vrsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_vrsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_vrsg_accepted_rescale_is_search_control
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  ay_vrsg_accepted_rescale_hint guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_vrsg_accepted_rescale_preserves_branch_order
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  ay_vrsg_accepted_rescale_order guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_vrsg_accepted_rescale_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (guardEvidence -> agreementEvidence -> branchOrderRelation -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_vrsg_accepted_rescale_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_vrsg_accepted_rescale_agreement guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_vrsg_accepted_rescale_order guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      outcomeH
      truthH

theorem ay_vrsg_accepted_rescale_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_vrsg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_vrsg_public_report_intro guardEvidence satOutcome satTruth
      (ay_vrsg_accepted_rescale_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      satH
      truthH

theorem ay_vrsg_accepted_rescale_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_vrsg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_vrsg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_vrsg_accepted_rescale_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      unsatH
      truthH

theorem ay_vrsg_rescale_preserves_formula_truth
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) :
    ay_vrsg_accepted_rescale guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (searchControlHint -> branchOrderRelation -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> branchOrderRelation -> formulaAfter ->
      formulaBefore) ->
    ay_vrsg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_vrsg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_vrsg_accepted_rescale_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_vrsg_accepted_rescale_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
      (backward
        (ay_vrsg_accepted_rescale_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_vrsg_accepted_rescale_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
