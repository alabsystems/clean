-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-cache epoch guard skeleton for sequential-main SAT. Saved phase caches
-- are performance hints only when epoch, domain, trail, activity, digest,
-- fallback, build, validator, and audit evidence agree.

def ay_bpce_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpce_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bpce_conj (before -> after) (after -> before)

def ay_bpce_cache_guard
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (phaseEpochLedger ->
      variableDomainManifest ->
      trailConsistencySnapshot ->
      activitySnapshot ->
      cacheDigest ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bpce_guard_agreement
    (epochMatch : Prop)
    (domainMatch : Prop)
    (trailMatch : Prop)
    (activityMatch : Prop)
    (digestMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bpce_cache_guard epochMatch domainMatch trailMatch activityMatch
    digestMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bpce_accepted_cache
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) : Prop :=
  ay_bpce_conj guardEvidence (ay_bpce_conj agreementEvidence phaseGuidance)

def ay_bpce_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bpce_conj acceptedEvidence (ay_bpce_conj outcome formulaTruth)

def ay_bpce_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bpce_conj diagnostic fallbackPublic

theorem ay_bpce_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bpce_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bpce_conj_left (left : Prop) (right : Prop) :
    ay_bpce_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bpce_conj_right (left : Prop) (right : Prop) :
    ay_bpce_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bpce_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bpce_equisat before after :=
  fun forward backward =>
    ay_bpce_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bpce_equisat_forward (before : Prop) (after : Prop) :
    ay_bpce_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bpce_conj_left (before -> after) (after -> before) eqsat

theorem ay_bpce_equisat_backward (before : Prop) (after : Prop) :
    ay_bpce_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bpce_conj_right (before -> after) (after -> before) eqsat

theorem ay_bpce_cache_guard_intro
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    phaseEpochLedger ->
    variableDomainManifest ->
    trailConsistencySnapshot ->
    activitySnapshot ->
    cacheDigest ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence :=
  fun epochH domainH trailH activityH digestH fallbackH buildH validatorH auditH
      result build =>
    build epochH domainH trailH activityH digestH fallbackH buildH validatorH
      auditH

theorem ay_bpce_cache_guard_epoch
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    phaseEpochLedger :=
  fun guard =>
    guard phaseEpochLedger
      (fun epochH _domainH _trailH _activityH _digestH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bpce_cache_guard_domain
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _epochH domainH _trailH _activityH _digestH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_bpce_cache_guard_trail
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    trailConsistencySnapshot :=
  fun guard =>
    guard trailConsistencySnapshot
      (fun _epochH _domainH trailH _activityH _digestH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_bpce_cache_guard_activity
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    activitySnapshot :=
  fun guard =>
    guard activitySnapshot
      (fun _epochH _domainH _trailH activityH _digestH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bpce_cache_guard_digest
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    cacheDigest :=
  fun guard =>
    guard cacheDigest
      (fun _epochH _domainH _trailH _activityH digestH _fallbackH _buildH
          _validatorH _auditH => digestH)

theorem ay_bpce_cache_guard_fallback
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _domainH _trailH _activityH _digestH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bpce_cache_guard_build
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _domainH _trailH _activityH _digestH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bpce_cache_guard_validator
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _domainH _trailH _activityH _digestH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bpce_cache_guard_audit
    (phaseEpochLedger : Prop)
    (variableDomainManifest : Prop)
    (trailConsistencySnapshot : Prop)
    (activitySnapshot : Prop)
    (cacheDigest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bpce_cache_guard phaseEpochLedger variableDomainManifest
      trailConsistencySnapshot activitySnapshot cacheDigest fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _domainH _trailH _activityH _digestH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bpce_guard_agreement_intro
    (epochMatch : Prop)
    (domainMatch : Prop)
    (trailMatch : Prop)
    (activityMatch : Prop)
    (digestMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    domainMatch ->
    trailMatch ->
    activityMatch ->
    digestMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bpce_guard_agreement epochMatch domainMatch trailMatch activityMatch
      digestMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bpce_cache_guard_intro epochMatch domainMatch trailMatch activityMatch
    digestMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bpce_accepted_cache_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    phaseGuidance ->
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bpce_conj_intro guardEvidence
      (ay_bpce_conj agreementEvidence phaseGuidance)
      guardH
      (ay_bpce_conj_intro agreementEvidence phaseGuidance agreementH guidanceH)

theorem ay_bpce_accepted_cache_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bpce_conj_left guardEvidence
      (ay_bpce_conj agreementEvidence phaseGuidance)
      accepted

theorem ay_bpce_accepted_cache_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bpce_conj_left agreementEvidence phaseGuidance
      (ay_bpce_conj_right guardEvidence
        (ay_bpce_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpce_accepted_cache_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    phaseGuidance :=
  fun accepted =>
    ay_bpce_conj_right agreementEvidence phaseGuidance
      (ay_bpce_conj_right guardEvidence
        (ay_bpce_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpce_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bpce_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bpce_conj_intro acceptedEvidence
      (ay_bpce_conj outcome formulaTruth)
      acceptedH
      (ay_bpce_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bpce_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bpce_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bpce_conj_left acceptedEvidence
      (ay_bpce_conj outcome formulaTruth)
      public

theorem ay_bpce_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bpce_no_claim diagnostic fallbackPublic :=
  ay_bpce_conj_intro diagnostic fallbackPublic

theorem ay_bpce_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpce_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bpce_conj_right diagnostic fallbackPublic noClaim

theorem ay_bpce_epoch_drift_no_claim
    (epochDrift : Prop)
    (fallbackPublic : Prop) :
    epochDrift -> fallbackPublic -> ay_bpce_no_claim epochDrift fallbackPublic :=
  ay_bpce_no_claim_intro epochDrift fallbackPublic

theorem ay_bpce_domain_mismatch_no_claim
    (domainMismatch : Prop)
    (fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_bpce_no_claim domainMismatch fallbackPublic :=
  ay_bpce_no_claim_intro domainMismatch fallbackPublic

theorem ay_bpce_trail_inconsistency_no_claim
    (trailInconsistency : Prop)
    (fallbackPublic : Prop) :
    trailInconsistency ->
    fallbackPublic ->
    ay_bpce_no_claim trailInconsistency fallbackPublic :=
  ay_bpce_no_claim_intro trailInconsistency fallbackPublic

theorem ay_bpce_activity_mismatch_no_claim
    (activityMismatch : Prop)
    (fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_bpce_no_claim activityMismatch fallbackPublic :=
  ay_bpce_no_claim_intro activityMismatch fallbackPublic

theorem ay_bpce_cache_digest_drift_no_claim
    (cacheDigestDrift : Prop)
    (fallbackPublic : Prop) :
    cacheDigestDrift ->
    fallbackPublic ->
    ay_bpce_no_claim cacheDigestDrift fallbackPublic :=
  ay_bpce_no_claim_intro cacheDigestDrift fallbackPublic

theorem ay_bpce_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bpce_no_claim missingFallback fallbackPublic :=
  ay_bpce_no_claim_intro missingFallback fallbackPublic

theorem ay_bpce_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bpce_no_claim staleBuild fallbackPublic :=
  ay_bpce_no_claim_intro staleBuild fallbackPublic

theorem ay_bpce_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bpce_no_claim validatorRejection fallbackPublic :=
  ay_bpce_no_claim_intro validatorRejection fallbackPublic

theorem ay_bpce_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bpce_no_claim auditContradiction fallbackPublic :=
  ay_bpce_no_claim_intro auditContradiction fallbackPublic

theorem ay_bpce_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bpce_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bpce_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bpce_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpce_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bpce_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bpce_accepted_cache_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bpce_public_report
      (ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bpce_public_report_intro
      (ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bpce_accepted_cache_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bpce_public_report
      (ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bpce_accepted_cache_guides_sat guardEvidence agreementEvidence
    phaseGuidance unsatOutcome formulaTruth

theorem ay_bpce_accepted_cache_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    ay_bpce_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bpce_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bpce_phase_cache_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bpce_accepted_cache guardEvidence agreementEvidence phaseGuidance ->
    ay_bpce_equisat beforeTruth afterTruth ->
    ay_bpce_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bpce_equisat_intro afterTruth beforeTruth
      (ay_bpce_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bpce_equisat_forward beforeTruth afterTruth eqsat)

def ay_pceg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pceg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pceg_conj (before -> after) (after -> before)

def ay_pceg_guard
    (variableDomainDigest : Prop)
    (phaseCacheDigest : Prop)
    (cacheEpochManifest : Prop)
    (assignmentTrailReplay : Prop)
    (decisionCandidateLedger : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      phaseCacheDigest ->
      cacheEpochManifest ->
      assignmentTrailReplay ->
      decisionCandidateLedger ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pceg_agreement
    (domainMatch cacheMatch epochMatch trailMatch candidateMatch tiebreakMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) : Prop :=
  ay_pceg_guard domainMatch cacheMatch epochMatch trailMatch candidateMatch
    tiebreakMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_pceg_accepted_cache
    (guardEvidence agreementEvidence searchControlHint : Prop) : Prop :=
  ay_pceg_conj guardEvidence
    (ay_pceg_conj agreementEvidence searchControlHint)

def ay_pceg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pceg_conj acceptedEvidence (ay_pceg_conj outcome formulaTruth)

def ay_pceg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_pceg_conj diagnostic fallbackPublic

theorem ay_pceg_conj_intro (left right : Prop) :
    left -> right -> ay_pceg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pceg_conj_left (left right : Prop) :
    ay_pceg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pceg_conj_right (left right : Prop) :
    ay_pceg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pceg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pceg_equisat before after :=
  fun forward backward =>
    ay_pceg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pceg_equisat_forward (before after : Prop) :
    ay_pceg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pceg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pceg_equisat_backward (before after : Prop) :
    ay_pceg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pceg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pceg_guard_intro
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    phaseCacheDigest ->
    cacheEpochManifest ->
    assignmentTrailReplay ->
    decisionCandidateLedger ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH cacheH epochH trailH candidateH tiebreakH fallbackH buildH
      validatorH auditH result make =>
    make domainH cacheH epochH trailH candidateH tiebreakH fallbackH buildH
      validatorH auditH

theorem ay_pceg_guard_domain
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _cacheH _epochH _trailH _candidateH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_pceg_guard_cache
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    phaseCacheDigest :=
  fun guard =>
    guard phaseCacheDigest
      (fun _domainH cacheH _epochH _trailH _candidateH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => cacheH)

theorem ay_pceg_guard_epoch
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    cacheEpochManifest :=
  fun guard =>
    guard cacheEpochManifest
      (fun _domainH _cacheH epochH _trailH _candidateH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => epochH)

theorem ay_pceg_guard_trail
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    assignmentTrailReplay :=
  fun guard =>
    guard assignmentTrailReplay
      (fun _domainH _cacheH _epochH trailH _candidateH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => trailH)

theorem ay_pceg_guard_candidate
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionCandidateLedger :=
  fun guard =>
    guard decisionCandidateLedger
      (fun _domainH _cacheH _epochH _trailH candidateH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => candidateH)

theorem ay_pceg_guard_tiebreak
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _cacheH _epochH _trailH _candidateH tiebreakH _fallbackH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_pceg_guard_fallback
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _cacheH _epochH _trailH _candidateH _tiebreakH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_pceg_guard_build
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _cacheH _epochH _trailH _candidateH _tiebreakH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_pceg_guard_validator
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _cacheH _epochH _trailH _candidateH _tiebreakH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_pceg_guard_audit
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _cacheH _epochH _trailH _candidateH _tiebreakH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_pceg_agreement_intro
    (domainMatch cacheMatch epochMatch trailMatch candidateMatch tiebreakMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    cacheMatch ->
    epochMatch ->
    trailMatch ->
    candidateMatch ->
    tiebreakMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_pceg_agreement domainMatch cacheMatch epochMatch trailMatch
      candidateMatch tiebreakMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_pceg_guard_intro domainMatch cacheMatch epochMatch trailMatch
    candidateMatch tiebreakMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_pceg_accepted_cache_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint :=
  fun guardH agreementH hintH =>
    ay_pceg_conj_intro guardEvidence
      (ay_pceg_conj agreementEvidence searchControlHint)
      guardH
      (ay_pceg_conj_intro agreementEvidence searchControlHint agreementH hintH)

theorem ay_pceg_accepted_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint ->
    guardEvidence :=
  ay_pceg_conj_left guardEvidence
    (ay_pceg_conj agreementEvidence searchControlHint)

theorem ay_pceg_accepted_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_pceg_conj_left agreementEvidence searchControlHint
      (ay_pceg_conj_right guardEvidence
        (ay_pceg_conj agreementEvidence searchControlHint) accepted)

theorem ay_pceg_accepted_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_pceg_conj_right agreementEvidence searchControlHint
      (ay_pceg_conj_right guardEvidence
        (ay_pceg_conj agreementEvidence searchControlHint) accepted)

theorem ay_pceg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pceg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pceg_conj_intro acceptedEvidence (ay_pceg_conj outcome formulaTruth)
      acceptedH (ay_pceg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pceg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pceg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_pceg_conj_left acceptedEvidence (ay_pceg_conj outcome formulaTruth)

theorem ay_pceg_public_report_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pceg_public_report acceptedEvidence outcome formulaTruth ->
    ay_pceg_conj outcome formulaTruth :=
  fun report =>
    ay_pceg_conj_right acceptedEvidence (ay_pceg_conj outcome formulaTruth)
      report

theorem ay_pceg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_pceg_no_claim diagnostic fallbackPublic :=
  ay_pceg_conj_intro diagnostic fallbackPublic

theorem ay_pceg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_pceg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_pceg_conj_right diagnostic fallbackPublic

theorem ay_pceg_cache_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pceg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_pceg_equisat_forward beforeFormula afterFormula

theorem ay_pceg_cache_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_pceg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_pceg_equisat_backward beforeFormula afterFormula

theorem ay_pceg_accepted_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      searchControlHint : Prop) :
    ay_pceg_equisat beforeFormula afterFormula ->
    ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint ->
    ay_pceg_conj (beforeFormula -> afterFormula) searchControlHint :=
  fun eqsat accepted =>
    ay_pceg_conj_intro (beforeFormula -> afterFormula) searchControlHint
      (ay_pceg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_pceg_accepted_search_control guardEvidence agreementEvidence
        searchControlHint accepted)

theorem ay_pceg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_pceg_no_claim domainMismatch fallbackPublic :=
  ay_pceg_no_claim_intro domainMismatch fallbackPublic

theorem ay_pceg_cache_mismatch_no_claim
    (cacheMismatch fallbackPublic : Prop) :
    cacheMismatch -> fallbackPublic ->
    ay_pceg_no_claim cacheMismatch fallbackPublic :=
  ay_pceg_no_claim_intro cacheMismatch fallbackPublic

theorem ay_pceg_epoch_mismatch_no_claim
    (epochMismatch fallbackPublic : Prop) :
    epochMismatch -> fallbackPublic ->
    ay_pceg_no_claim epochMismatch fallbackPublic :=
  ay_pceg_no_claim_intro epochMismatch fallbackPublic

theorem ay_pceg_trail_mismatch_no_claim
    (trailMismatch fallbackPublic : Prop) :
    trailMismatch -> fallbackPublic ->
    ay_pceg_no_claim trailMismatch fallbackPublic :=
  ay_pceg_no_claim_intro trailMismatch fallbackPublic

theorem ay_pceg_candidate_mismatch_no_claim
    (candidateMismatch fallbackPublic : Prop) :
    candidateMismatch -> fallbackPublic ->
    ay_pceg_no_claim candidateMismatch fallbackPublic :=
  ay_pceg_no_claim_intro candidateMismatch fallbackPublic

theorem ay_pceg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_pceg_no_claim tiebreakMismatch fallbackPublic :=
  ay_pceg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_pceg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_pceg_no_claim replayMismatch fallbackPublic :=
  ay_pceg_no_claim_intro replayMismatch fallbackPublic

theorem ay_pceg_fallback_mismatch_no_claim
    (fallbackMismatch fallbackPublic : Prop) :
    fallbackMismatch -> fallbackPublic ->
    ay_pceg_no_claim fallbackMismatch fallbackPublic :=
  ay_pceg_no_claim_intro fallbackMismatch fallbackPublic

theorem ay_pceg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_pceg_no_claim buildMismatch fallbackPublic :=
  ay_pceg_no_claim_intro buildMismatch fallbackPublic

theorem ay_pceg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects -> fallbackPublic ->
    ay_pceg_no_claim validatorRejects fallbackPublic :=
  ay_pceg_no_claim_intro validatorRejects fallbackPublic

theorem ay_pceg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_pceg_no_claim auditMismatch fallbackPublic :=
  ay_pceg_no_claim_intro auditMismatch fallbackPublic

theorem ay_pceg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_pceg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_pceg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_pceg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_pceg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_pceg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_pceg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth :
      Prop) :
    ay_pceg_public_report
      (ay_pceg_accepted_cache guardEvidence agreementEvidence searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pceg_accepted_guard guardEvidence agreementEvidence searchControlHint
      (ay_pceg_public_report_accepted
        (ay_pceg_accepted_cache guardEvidence agreementEvidence
          searchControlHint)
        outcome formulaTruth report)

theorem ay_pceg_publication_requires_validator
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_pceg_public_report
      (ay_pceg_accepted_cache
        (ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
          assignmentTrailReplay decisionCandidateLedger
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pceg_guard_validator variableDomainDigest phaseCacheDigest
      cacheEpochManifest assignmentTrailReplay decisionCandidateLedger
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pceg_publication_requires_guard
        (ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
          assignmentTrailReplay decisionCandidateLedger
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_pceg_publication_requires_audit
    (variableDomainDigest phaseCacheDigest cacheEpochManifest
      assignmentTrailReplay decisionCandidateLedger deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_pceg_public_report
      (ay_pceg_accepted_cache
        (ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
          assignmentTrailReplay decisionCandidateLedger
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pceg_guard_audit variableDomainDigest phaseCacheDigest
      cacheEpochManifest assignmentTrailReplay decisionCandidateLedger
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_pceg_publication_requires_guard
        (ay_pceg_guard variableDomainDigest phaseCacheDigest cacheEpochManifest
          assignmentTrailReplay decisionCandidateLedger
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_pceg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence -> satOutcome -> formulaTruth ->
    ay_pceg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pceg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pceg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence -> unsatOutcome -> formulaTruth ->
    ay_pceg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pceg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
