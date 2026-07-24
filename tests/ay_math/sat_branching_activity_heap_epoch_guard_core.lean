-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Activity-heap epoch guard skeleton for sequential-main SAT. Activity heap
-- reuse is a performance hint only when heap epoch, score digest, domain,
-- heap order, phase/trail, fallback, build, validator, and audit evidence
-- agree.

def ay_bahe_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bahe_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bahe_conj (before -> after) (after -> before)

def ay_bahe_heap_guard
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (heapEpochLedger ->
      activityScoresDigest ->
      variableDomainManifest ->
      heapOrderEvidence ->
      phaseTrailSnapshot ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bahe_guard_agreement
    (epochMatch : Prop)
    (scoreDigestMatch : Prop)
    (domainMatch : Prop)
    (heapOrderMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bahe_heap_guard epochMatch scoreDigestMatch domainMatch heapOrderMatch
    phaseTrailMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bahe_accepted_heap
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) : Prop :=
  ay_bahe_conj guardEvidence (ay_bahe_conj agreementEvidence heapGuidance)

def ay_bahe_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bahe_conj acceptedEvidence (ay_bahe_conj outcome formulaTruth)

def ay_bahe_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bahe_conj diagnostic fallbackPublic

theorem ay_bahe_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bahe_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bahe_conj_left (left : Prop) (right : Prop) :
    ay_bahe_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bahe_conj_right (left : Prop) (right : Prop) :
    ay_bahe_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bahe_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bahe_equisat before after :=
  fun forward backward =>
    ay_bahe_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bahe_equisat_forward (before : Prop) (after : Prop) :
    ay_bahe_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bahe_conj_left (before -> after) (after -> before) eqsat

theorem ay_bahe_equisat_backward (before : Prop) (after : Prop) :
    ay_bahe_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bahe_conj_right (before -> after) (after -> before) eqsat

theorem ay_bahe_heap_guard_intro
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    heapEpochLedger ->
    activityScoresDigest ->
    variableDomainManifest ->
    heapOrderEvidence ->
    phaseTrailSnapshot ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun epochH scoreH domainH orderH phaseTrailH fallbackH buildH validatorH
      auditH result build =>
    build epochH scoreH domainH orderH phaseTrailH fallbackH buildH validatorH
      auditH

theorem ay_bahe_heap_guard_epoch
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    heapEpochLedger :=
  fun guard =>
    guard heapEpochLedger
      (fun epochH _scoreH _domainH _orderH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bahe_heap_guard_score_digest
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityScoresDigest :=
  fun guard =>
    guard activityScoresDigest
      (fun _epochH scoreH _domainH _orderH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => scoreH)

theorem ay_bahe_heap_guard_domain
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _epochH _scoreH domainH _orderH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_bahe_heap_guard_order
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    heapOrderEvidence :=
  fun guard =>
    guard heapOrderEvidence
      (fun _epochH _scoreH _domainH orderH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => orderH)

theorem ay_bahe_heap_guard_phase_trail
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailSnapshot :=
  fun guard =>
    guard phaseTrailSnapshot
      (fun _epochH _scoreH _domainH _orderH phaseTrailH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_bahe_heap_guard_fallback
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _scoreH _domainH _orderH _phaseTrailH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bahe_heap_guard_build
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _scoreH _domainH _orderH _phaseTrailH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bahe_heap_guard_validator
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _scoreH _domainH _orderH _phaseTrailH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bahe_heap_guard_audit
    (heapEpochLedger : Prop)
    (activityScoresDigest : Prop)
    (variableDomainManifest : Prop)
    (heapOrderEvidence : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahe_heap_guard heapEpochLedger activityScoresDigest
      variableDomainManifest heapOrderEvidence phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _scoreH _domainH _orderH _phaseTrailH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bahe_guard_agreement_intro
    (epochMatch : Prop)
    (scoreDigestMatch : Prop)
    (domainMatch : Prop)
    (heapOrderMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    scoreDigestMatch ->
    domainMatch ->
    heapOrderMatch ->
    phaseTrailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bahe_guard_agreement epochMatch scoreDigestMatch domainMatch
      heapOrderMatch phaseTrailMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_bahe_heap_guard_intro epochMatch scoreDigestMatch domainMatch
    heapOrderMatch phaseTrailMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_bahe_accepted_heap_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    heapGuidance ->
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bahe_conj_intro guardEvidence
      (ay_bahe_conj agreementEvidence heapGuidance)
      guardH
      (ay_bahe_conj_intro agreementEvidence heapGuidance agreementH guidanceH)

theorem ay_bahe_accepted_heap_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bahe_conj_left guardEvidence
      (ay_bahe_conj agreementEvidence heapGuidance)
      accepted

theorem ay_bahe_accepted_heap_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bahe_conj_left agreementEvidence heapGuidance
      (ay_bahe_conj_right guardEvidence
        (ay_bahe_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_bahe_accepted_heap_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    heapGuidance :=
  fun accepted =>
    ay_bahe_conj_right agreementEvidence heapGuidance
      (ay_bahe_conj_right guardEvidence
        (ay_bahe_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_bahe_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bahe_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bahe_conj_intro acceptedEvidence
      (ay_bahe_conj outcome formulaTruth)
      acceptedH
      (ay_bahe_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bahe_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bahe_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bahe_conj_left acceptedEvidence
      (ay_bahe_conj outcome formulaTruth)
      public

theorem ay_bahe_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bahe_no_claim diagnostic fallbackPublic :=
  ay_bahe_conj_intro diagnostic fallbackPublic

theorem ay_bahe_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bahe_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bahe_conj_right diagnostic fallbackPublic noClaim

theorem ay_bahe_epoch_drift_no_claim
    (epochDrift : Prop)
    (fallbackPublic : Prop) :
    epochDrift -> fallbackPublic -> ay_bahe_no_claim epochDrift fallbackPublic :=
  ay_bahe_no_claim_intro epochDrift fallbackPublic

theorem ay_bahe_score_digest_mismatch_no_claim
    (scoreDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    scoreDigestMismatch ->
    fallbackPublic ->
    ay_bahe_no_claim scoreDigestMismatch fallbackPublic :=
  ay_bahe_no_claim_intro scoreDigestMismatch fallbackPublic

theorem ay_bahe_domain_mismatch_no_claim
    (domainMismatch : Prop)
    (fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_bahe_no_claim domainMismatch fallbackPublic :=
  ay_bahe_no_claim_intro domainMismatch fallbackPublic

theorem ay_bahe_heap_order_mismatch_no_claim
    (heapOrderMismatch : Prop)
    (fallbackPublic : Prop) :
    heapOrderMismatch ->
    fallbackPublic ->
    ay_bahe_no_claim heapOrderMismatch fallbackPublic :=
  ay_bahe_no_claim_intro heapOrderMismatch fallbackPublic

theorem ay_bahe_phase_trail_mismatch_no_claim
    (phaseTrailMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseTrailMismatch ->
    fallbackPublic ->
    ay_bahe_no_claim phaseTrailMismatch fallbackPublic :=
  ay_bahe_no_claim_intro phaseTrailMismatch fallbackPublic

theorem ay_bahe_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bahe_no_claim missingFallback fallbackPublic :=
  ay_bahe_no_claim_intro missingFallback fallbackPublic

theorem ay_bahe_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bahe_no_claim staleBuild fallbackPublic :=
  ay_bahe_no_claim_intro staleBuild fallbackPublic

theorem ay_bahe_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bahe_no_claim validatorRejection fallbackPublic :=
  ay_bahe_no_claim_intro validatorRejection fallbackPublic

theorem ay_bahe_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bahe_no_claim auditContradiction fallbackPublic :=
  ay_bahe_no_claim_intro auditContradiction fallbackPublic

theorem ay_bahe_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bahe_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bahe_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bahe_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bahe_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bahe_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bahe_accepted_heap_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bahe_public_report
      (ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bahe_public_report_intro
      (ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bahe_accepted_heap_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bahe_public_report
      (ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bahe_accepted_heap_guides_sat guardEvidence agreementEvidence
    heapGuidance unsatOutcome formulaTruth

theorem ay_bahe_accepted_heap_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    ay_bahe_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bahe_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bahe_activity_heap_reuse_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bahe_accepted_heap guardEvidence agreementEvidence heapGuidance ->
    ay_bahe_equisat beforeTruth afterTruth ->
    ay_bahe_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bahe_equisat_intro afterTruth beforeTruth
      (ay_bahe_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bahe_equisat_forward beforeTruth afterTruth eqsat)
