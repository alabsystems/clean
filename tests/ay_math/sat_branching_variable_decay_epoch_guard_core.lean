-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-decay epoch guard skeleton for sequential-main SAT. Variable
-- activity decay metadata is a performance hint only when decay epochs, score
-- digests, heap snapshots, domain manifests, phase/trail snapshots, fallback,
-- build, validator, and audit evidence agree.

def ay_bvde_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bvde_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bvde_conj (before -> after) (after -> before)

def ay_bvde_decay_guard
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (decayEpochLedger ->
      scoreDigest ->
      heapSnapshot ->
      variableDomainManifest ->
      phaseTrailSnapshot ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bvde_guard_agreement
    (decayEpochMatch : Prop)
    (scoreDigestMatch : Prop)
    (heapMatch : Prop)
    (domainMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bvde_decay_guard decayEpochMatch scoreDigestMatch heapMatch domainMatch
    phaseTrailMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bvde_accepted_decay
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) : Prop :=
  ay_bvde_conj guardEvidence (ay_bvde_conj agreementEvidence decayGuidance)

def ay_bvde_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bvde_conj acceptedEvidence (ay_bvde_conj outcome formulaTruth)

def ay_bvde_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bvde_conj diagnostic fallbackPublic

theorem ay_bvde_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bvde_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bvde_conj_left (left : Prop) (right : Prop) :
    ay_bvde_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bvde_conj_right (left : Prop) (right : Prop) :
    ay_bvde_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bvde_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bvde_equisat before after :=
  fun forward backward =>
    ay_bvde_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bvde_equisat_forward (before : Prop) (after : Prop) :
    ay_bvde_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bvde_conj_left (before -> after) (after -> before) eqsat

theorem ay_bvde_equisat_backward (before : Prop) (after : Prop) :
    ay_bvde_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bvde_conj_right (before -> after) (after -> before) eqsat

theorem ay_bvde_decay_guard_intro
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    decayEpochLedger ->
    scoreDigest ->
    heapSnapshot ->
    variableDomainManifest ->
    phaseTrailSnapshot ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence :=
  fun decayH scoreH heapH domainH phaseTrailH fallbackH buildH validatorH auditH
      result build =>
    build decayH scoreH heapH domainH phaseTrailH fallbackH buildH validatorH
      auditH

theorem ay_bvde_decay_guard_epoch
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    decayEpochLedger :=
  fun guard =>
    guard decayEpochLedger
      (fun decayH _scoreH _heapH _domainH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => decayH)

theorem ay_bvde_decay_guard_score_digest
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    scoreDigest :=
  fun guard =>
    guard scoreDigest
      (fun _decayH scoreH _heapH _domainH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => scoreH)

theorem ay_bvde_decay_guard_heap
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    heapSnapshot :=
  fun guard =>
    guard heapSnapshot
      (fun _decayH _scoreH heapH _domainH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_bvde_decay_guard_domain
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _decayH _scoreH _heapH domainH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_bvde_decay_guard_phase_trail
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    phaseTrailSnapshot :=
  fun guard =>
    guard phaseTrailSnapshot
      (fun _decayH _scoreH _heapH _domainH phaseTrailH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_bvde_decay_guard_fallback
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _decayH _scoreH _heapH _domainH _phaseTrailH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bvde_decay_guard_build
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _decayH _scoreH _heapH _domainH _phaseTrailH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bvde_decay_guard_validator
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _decayH _scoreH _heapH _domainH _phaseTrailH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bvde_decay_guard_audit
    (decayEpochLedger : Prop)
    (scoreDigest : Prop)
    (heapSnapshot : Prop)
    (variableDomainManifest : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bvde_decay_guard decayEpochLedger scoreDigest heapSnapshot
      variableDomainManifest phaseTrailSnapshot fallbackBaseline buildEvidence
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _decayH _scoreH _heapH _domainH _phaseTrailH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bvde_guard_agreement_intro
    (decayEpochMatch : Prop)
    (scoreDigestMatch : Prop)
    (heapMatch : Prop)
    (domainMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    decayEpochMatch ->
    scoreDigestMatch ->
    heapMatch ->
    domainMatch ->
    phaseTrailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bvde_guard_agreement decayEpochMatch scoreDigestMatch heapMatch
      domainMatch phaseTrailMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_bvde_decay_guard_intro decayEpochMatch scoreDigestMatch heapMatch
    domainMatch phaseTrailMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_bvde_accepted_decay_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    decayGuidance ->
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bvde_conj_intro guardEvidence
      (ay_bvde_conj agreementEvidence decayGuidance)
      guardH
      (ay_bvde_conj_intro agreementEvidence decayGuidance agreementH guidanceH)

theorem ay_bvde_accepted_decay_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bvde_conj_left guardEvidence
      (ay_bvde_conj agreementEvidence decayGuidance)
      accepted

theorem ay_bvde_accepted_decay_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bvde_conj_left agreementEvidence decayGuidance
      (ay_bvde_conj_right guardEvidence
        (ay_bvde_conj agreementEvidence decayGuidance)
        accepted)

theorem ay_bvde_accepted_decay_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    decayGuidance :=
  fun accepted =>
    ay_bvde_conj_right agreementEvidence decayGuidance
      (ay_bvde_conj_right guardEvidence
        (ay_bvde_conj agreementEvidence decayGuidance)
        accepted)

theorem ay_bvde_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bvde_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bvde_conj_intro acceptedEvidence
      (ay_bvde_conj outcome formulaTruth)
      acceptedH
      (ay_bvde_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bvde_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bvde_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bvde_conj_left acceptedEvidence
      (ay_bvde_conj outcome formulaTruth)
      public

theorem ay_bvde_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bvde_no_claim diagnostic fallbackPublic :=
  ay_bvde_conj_intro diagnostic fallbackPublic

theorem ay_bvde_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bvde_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bvde_conj_right diagnostic fallbackPublic noClaim

theorem ay_bvde_decay_epoch_drift_no_claim
    (decayEpochDrift : Prop)
    (fallbackPublic : Prop) :
    decayEpochDrift ->
    fallbackPublic ->
    ay_bvde_no_claim decayEpochDrift fallbackPublic :=
  ay_bvde_no_claim_intro decayEpochDrift fallbackPublic

theorem ay_bvde_score_digest_mismatch_no_claim
    (scoreDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    scoreDigestMismatch ->
    fallbackPublic ->
    ay_bvde_no_claim scoreDigestMismatch fallbackPublic :=
  ay_bvde_no_claim_intro scoreDigestMismatch fallbackPublic

theorem ay_bvde_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic -> ay_bvde_no_claim heapMismatch fallbackPublic :=
  ay_bvde_no_claim_intro heapMismatch fallbackPublic

theorem ay_bvde_domain_mismatch_no_claim
    (domainMismatch : Prop)
    (fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_bvde_no_claim domainMismatch fallbackPublic :=
  ay_bvde_no_claim_intro domainMismatch fallbackPublic

theorem ay_bvde_phase_trail_mismatch_no_claim
    (phaseTrailMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseTrailMismatch ->
    fallbackPublic ->
    ay_bvde_no_claim phaseTrailMismatch fallbackPublic :=
  ay_bvde_no_claim_intro phaseTrailMismatch fallbackPublic

theorem ay_bvde_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bvde_no_claim missingFallback fallbackPublic :=
  ay_bvde_no_claim_intro missingFallback fallbackPublic

theorem ay_bvde_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bvde_no_claim staleBuild fallbackPublic :=
  ay_bvde_no_claim_intro staleBuild fallbackPublic

theorem ay_bvde_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bvde_no_claim validatorRejection fallbackPublic :=
  ay_bvde_no_claim_intro validatorRejection fallbackPublic

theorem ay_bvde_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bvde_no_claim auditContradiction fallbackPublic :=
  ay_bvde_no_claim_intro auditContradiction fallbackPublic

theorem ay_bvde_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bvde_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bvde_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bvde_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bvde_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bvde_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bvde_accepted_decay_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bvde_public_report
      (ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bvde_public_report_intro
      (ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bvde_accepted_decay_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bvde_public_report
      (ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bvde_accepted_decay_guides_sat guardEvidence agreementEvidence
    decayGuidance unsatOutcome formulaTruth

theorem ay_bvde_accepted_decay_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    ay_bvde_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bvde_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bvde_variable_decay_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bvde_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    ay_bvde_equisat beforeTruth afterTruth ->
    ay_bvde_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bvde_equisat_intro afterTruth beforeTruth
      (ay_bvde_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bvde_equisat_forward beforeTruth afterTruth eqsat)
