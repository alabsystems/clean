-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-epoch digest guard skeleton for sequential-main SAT. Decision order
-- metadata may guide branching only when epoch ledgers, digests, snapshots,
-- fallback, build, validator, and audit evidence agree.

def ay_bded_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bded_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bded_conj (before -> after) (after -> before)

def ay_bded_digest_guard
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (decisionEpochLedger ->
      digestEvidence ->
      phaseTrailSnapshots ->
      activitySnapshot ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bded_guard_agreement
    (epochMatch : Prop)
    (digestMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bded_digest_guard epochMatch digestMatch phaseTrailMatch activityMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bded_accepted_metadata
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop) : Prop :=
  ay_bded_conj guardEvidence (ay_bded_conj agreementEvidence decisionGuidance)

def ay_bded_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bded_conj acceptedEvidence (ay_bded_conj outcome formulaTruth)

def ay_bded_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bded_conj diagnostic fallbackPublic

theorem ay_bded_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bded_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bded_conj_left (left : Prop) (right : Prop) :
    ay_bded_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bded_conj_right (left : Prop) (right : Prop) :
    ay_bded_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bded_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bded_equisat before after :=
  fun forward backward =>
    ay_bded_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bded_equisat_forward (before : Prop) (after : Prop) :
    ay_bded_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bded_conj_left (before -> after) (after -> before) eqsat

theorem ay_bded_equisat_backward (before : Prop) (after : Prop) :
    ay_bded_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bded_conj_right (before -> after) (after -> before) eqsat

theorem ay_bded_digest_guard_intro
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    decisionEpochLedger ->
    digestEvidence ->
    phaseTrailSnapshots ->
    activitySnapshot ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun epochH digestH phaseTrailH activityH fallbackH buildH validatorH auditH
      result build =>
    build epochH digestH phaseTrailH activityH fallbackH buildH validatorH auditH

theorem ay_bded_digest_guard_epoch
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    decisionEpochLedger :=
  fun guard =>
    guard decisionEpochLedger
      (fun epochH _digestH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bded_digest_guard_digest
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    digestEvidence :=
  fun guard =>
    guard digestEvidence
      (fun _epochH digestH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => digestH)

theorem ay_bded_digest_guard_phase_trail
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailSnapshots :=
  fun guard =>
    guard phaseTrailSnapshots
      (fun _epochH _digestH phaseTrailH _activityH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_bded_digest_guard_activity
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activitySnapshot :=
  fun guard =>
    guard activitySnapshot
      (fun _epochH _digestH _phaseTrailH activityH _fallbackH _buildH
          _validatorH _auditH => activityH)

theorem ay_bded_digest_guard_fallback
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _digestH _phaseTrailH _activityH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bded_digest_guard_build
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _digestH _phaseTrailH _activityH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bded_digest_guard_validator
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _digestH _phaseTrailH _activityH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bded_digest_guard_audit
    (decisionEpochLedger : Prop)
    (digestEvidence : Prop)
    (phaseTrailSnapshots : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bded_digest_guard decisionEpochLedger digestEvidence phaseTrailSnapshots
      activitySnapshot fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _digestH _phaseTrailH _activityH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bded_guard_agreement_intro
    (epochMatch : Prop)
    (digestMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    digestMatch ->
    phaseTrailMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bded_guard_agreement epochMatch digestMatch phaseTrailMatch
      activityMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bded_digest_guard_intro epochMatch digestMatch phaseTrailMatch
    activityMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bded_accepted_metadata_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    decisionGuidance ->
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bded_conj_intro guardEvidence
      (ay_bded_conj agreementEvidence decisionGuidance)
      guardH
      (ay_bded_conj_intro agreementEvidence decisionGuidance agreementH guidanceH)

theorem ay_bded_accepted_metadata_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bded_conj_left guardEvidence
      (ay_bded_conj agreementEvidence decisionGuidance)
      accepted

theorem ay_bded_accepted_metadata_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bded_conj_left agreementEvidence decisionGuidance
      (ay_bded_conj_right guardEvidence
        (ay_bded_conj agreementEvidence decisionGuidance)
        accepted)

theorem ay_bded_accepted_metadata_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    decisionGuidance :=
  fun accepted =>
    ay_bded_conj_right agreementEvidence decisionGuidance
      (ay_bded_conj_right guardEvidence
        (ay_bded_conj agreementEvidence decisionGuidance)
        accepted)

theorem ay_bded_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bded_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bded_conj_intro acceptedEvidence
      (ay_bded_conj outcome formulaTruth)
      acceptedH
      (ay_bded_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bded_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bded_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bded_conj_left acceptedEvidence
      (ay_bded_conj outcome formulaTruth)
      public

theorem ay_bded_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bded_no_claim diagnostic fallbackPublic :=
  ay_bded_conj_intro diagnostic fallbackPublic

theorem ay_bded_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bded_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bded_conj_right diagnostic fallbackPublic noClaim

theorem ay_bded_epoch_drift_no_claim
    (epochDrift : Prop)
    (fallbackPublic : Prop) :
    epochDrift -> fallbackPublic -> ay_bded_no_claim epochDrift fallbackPublic :=
  ay_bded_no_claim_intro epochDrift fallbackPublic

theorem ay_bded_digest_mismatch_no_claim
    (digestMismatch : Prop)
    (fallbackPublic : Prop) :
    digestMismatch ->
    fallbackPublic ->
    ay_bded_no_claim digestMismatch fallbackPublic :=
  ay_bded_no_claim_intro digestMismatch fallbackPublic

theorem ay_bded_stale_phase_trail_no_claim
    (stalePhaseTrail : Prop)
    (fallbackPublic : Prop) :
    stalePhaseTrail ->
    fallbackPublic ->
    ay_bded_no_claim stalePhaseTrail fallbackPublic :=
  ay_bded_no_claim_intro stalePhaseTrail fallbackPublic

theorem ay_bded_activity_mismatch_no_claim
    (activityMismatch : Prop)
    (fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_bded_no_claim activityMismatch fallbackPublic :=
  ay_bded_no_claim_intro activityMismatch fallbackPublic

theorem ay_bded_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bded_no_claim missingFallback fallbackPublic :=
  ay_bded_no_claim_intro missingFallback fallbackPublic

theorem ay_bded_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bded_no_claim staleBuild fallbackPublic :=
  ay_bded_no_claim_intro staleBuild fallbackPublic

theorem ay_bded_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bded_no_claim validatorRejection fallbackPublic :=
  ay_bded_no_claim_intro validatorRejection fallbackPublic

theorem ay_bded_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bded_no_claim auditContradiction fallbackPublic :=
  ay_bded_no_claim_intro auditContradiction fallbackPublic

theorem ay_bded_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bded_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bded_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bded_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bded_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bded_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bded_accepted_metadata_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bded_public_report
      (ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bded_public_report_intro
      (ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bded_accepted_metadata_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bded_public_report
      (ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bded_accepted_metadata_guides_sat guardEvidence agreementEvidence
    decisionGuidance unsatOutcome formulaTruth

theorem ay_bded_accepted_metadata_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    ay_bded_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bded_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bded_decision_metadata_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decisionGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bded_accepted_metadata guardEvidence agreementEvidence decisionGuidance ->
    ay_bded_equisat beforeTruth afterTruth ->
    ay_bded_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bded_equisat_intro afterTruth beforeTruth
      (ay_bded_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bded_equisat_forward beforeTruth afterTruth eqsat)
