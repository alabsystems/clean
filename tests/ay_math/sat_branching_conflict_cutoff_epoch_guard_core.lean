-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Conflict-cutoff epoch guard skeleton for sequential-main SAT. Conflict
-- cutoff metadata is a performance hint only when epoch, counter digest,
-- restart budget, phase/trail, activity, fallback, build, validator, and audit
-- evidence agree.

def ay_bcce_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcce_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bcce_conj (before -> after) (after -> before)

def ay_bcce_cutoff_guard
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (cutoffEpochLedger ->
      conflictCounterDigest ->
      restartBudgetSnapshot ->
      phaseTrailSnapshot ->
      activitySnapshot ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bcce_guard_agreement
    (epochMatch : Prop)
    (counterDigestMatch : Prop)
    (restartBudgetMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bcce_cutoff_guard epochMatch counterDigestMatch restartBudgetMatch
    phaseTrailMatch activityMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bcce_accepted_cutoff
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop) : Prop :=
  ay_bcce_conj guardEvidence (ay_bcce_conj agreementEvidence cutoffGuidance)

def ay_bcce_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bcce_conj acceptedEvidence (ay_bcce_conj outcome formulaTruth)

def ay_bcce_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bcce_conj diagnostic fallbackPublic

theorem ay_bcce_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bcce_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bcce_conj_left (left : Prop) (right : Prop) :
    ay_bcce_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bcce_conj_right (left : Prop) (right : Prop) :
    ay_bcce_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bcce_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bcce_equisat before after :=
  fun forward backward =>
    ay_bcce_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bcce_equisat_forward (before : Prop) (after : Prop) :
    ay_bcce_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bcce_conj_left (before -> after) (after -> before) eqsat

theorem ay_bcce_equisat_backward (before : Prop) (after : Prop) :
    ay_bcce_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bcce_conj_right (before -> after) (after -> before) eqsat

theorem ay_bcce_cutoff_guard_intro
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    cutoffEpochLedger ->
    conflictCounterDigest ->
    restartBudgetSnapshot ->
    phaseTrailSnapshot ->
    activitySnapshot ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence :=
  fun epochH counterH restartH phaseTrailH activityH fallbackH buildH
      validatorH auditH result build =>
    build epochH counterH restartH phaseTrailH activityH fallbackH buildH
      validatorH auditH

theorem ay_bcce_cutoff_guard_epoch
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    cutoffEpochLedger :=
  fun guard =>
    guard cutoffEpochLedger
      (fun epochH _counterH _restartH _phaseTrailH _activityH _fallbackH
          _buildH _validatorH _auditH => epochH)

theorem ay_bcce_cutoff_guard_counter
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    conflictCounterDigest :=
  fun guard =>
    guard conflictCounterDigest
      (fun _epochH counterH _restartH _phaseTrailH _activityH _fallbackH
          _buildH _validatorH _auditH => counterH)

theorem ay_bcce_cutoff_guard_restart_budget
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    restartBudgetSnapshot :=
  fun guard =>
    guard restartBudgetSnapshot
      (fun _epochH _counterH restartH _phaseTrailH _activityH _fallbackH
          _buildH _validatorH _auditH => restartH)

theorem ay_bcce_cutoff_guard_phase_trail
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    phaseTrailSnapshot :=
  fun guard =>
    guard phaseTrailSnapshot
      (fun _epochH _counterH _restartH phaseTrailH _activityH _fallbackH
          _buildH _validatorH _auditH => phaseTrailH)

theorem ay_bcce_cutoff_guard_activity
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    activitySnapshot :=
  fun guard =>
    guard activitySnapshot
      (fun _epochH _counterH _restartH _phaseTrailH activityH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bcce_cutoff_guard_fallback
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _counterH _restartH _phaseTrailH _activityH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bcce_cutoff_guard_build
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _counterH _restartH _phaseTrailH _activityH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bcce_cutoff_guard_validator
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _counterH _restartH _phaseTrailH _activityH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bcce_cutoff_guard_audit
    (cutoffEpochLedger : Prop)
    (conflictCounterDigest : Prop)
    (restartBudgetSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (activitySnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcce_cutoff_guard cutoffEpochLedger conflictCounterDigest
      restartBudgetSnapshot phaseTrailSnapshot activitySnapshot fallbackBaseline
      buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _counterH _restartH _phaseTrailH _activityH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bcce_guard_agreement_intro
    (epochMatch : Prop)
    (counterDigestMatch : Prop)
    (restartBudgetMatch : Prop)
    (phaseTrailMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    counterDigestMatch ->
    restartBudgetMatch ->
    phaseTrailMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcce_guard_agreement epochMatch counterDigestMatch restartBudgetMatch
      phaseTrailMatch activityMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_bcce_cutoff_guard_intro epochMatch counterDigestMatch restartBudgetMatch
    phaseTrailMatch activityMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_bcce_accepted_cutoff_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    cutoffGuidance ->
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bcce_conj_intro guardEvidence
      (ay_bcce_conj agreementEvidence cutoffGuidance)
      guardH
      (ay_bcce_conj_intro agreementEvidence cutoffGuidance agreementH guidanceH)

theorem ay_bcce_accepted_cutoff_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bcce_conj_left guardEvidence
      (ay_bcce_conj agreementEvidence cutoffGuidance)
      accepted

theorem ay_bcce_accepted_cutoff_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bcce_conj_left agreementEvidence cutoffGuidance
      (ay_bcce_conj_right guardEvidence
        (ay_bcce_conj agreementEvidence cutoffGuidance)
        accepted)

theorem ay_bcce_accepted_cutoff_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    cutoffGuidance :=
  fun accepted =>
    ay_bcce_conj_right agreementEvidence cutoffGuidance
      (ay_bcce_conj_right guardEvidence
        (ay_bcce_conj agreementEvidence cutoffGuidance)
        accepted)

theorem ay_bcce_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bcce_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bcce_conj_intro acceptedEvidence
      (ay_bcce_conj outcome formulaTruth)
      acceptedH
      (ay_bcce_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bcce_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bcce_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bcce_conj_left acceptedEvidence
      (ay_bcce_conj outcome formulaTruth)
      public

theorem ay_bcce_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bcce_no_claim diagnostic fallbackPublic :=
  ay_bcce_conj_intro diagnostic fallbackPublic

theorem ay_bcce_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcce_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bcce_conj_right diagnostic fallbackPublic noClaim

theorem ay_bcce_epoch_drift_no_claim
    (epochDrift : Prop)
    (fallbackPublic : Prop) :
    epochDrift -> fallbackPublic -> ay_bcce_no_claim epochDrift fallbackPublic :=
  ay_bcce_no_claim_intro epochDrift fallbackPublic

theorem ay_bcce_counter_digest_mismatch_no_claim
    (counterDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    counterDigestMismatch ->
    fallbackPublic ->
    ay_bcce_no_claim counterDigestMismatch fallbackPublic :=
  ay_bcce_no_claim_intro counterDigestMismatch fallbackPublic

theorem ay_bcce_restart_budget_mismatch_no_claim
    (restartBudgetMismatch : Prop)
    (fallbackPublic : Prop) :
    restartBudgetMismatch ->
    fallbackPublic ->
    ay_bcce_no_claim restartBudgetMismatch fallbackPublic :=
  ay_bcce_no_claim_intro restartBudgetMismatch fallbackPublic

theorem ay_bcce_phase_trail_mismatch_no_claim
    (phaseTrailMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseTrailMismatch ->
    fallbackPublic ->
    ay_bcce_no_claim phaseTrailMismatch fallbackPublic :=
  ay_bcce_no_claim_intro phaseTrailMismatch fallbackPublic

theorem ay_bcce_activity_mismatch_no_claim
    (activityMismatch : Prop)
    (fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_bcce_no_claim activityMismatch fallbackPublic :=
  ay_bcce_no_claim_intro activityMismatch fallbackPublic

theorem ay_bcce_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcce_no_claim missingFallback fallbackPublic :=
  ay_bcce_no_claim_intro missingFallback fallbackPublic

theorem ay_bcce_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bcce_no_claim staleBuild fallbackPublic :=
  ay_bcce_no_claim_intro staleBuild fallbackPublic

theorem ay_bcce_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bcce_no_claim validatorRejection fallbackPublic :=
  ay_bcce_no_claim_intro validatorRejection fallbackPublic

theorem ay_bcce_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcce_no_claim auditContradiction fallbackPublic :=
  ay_bcce_no_claim_intro auditContradiction fallbackPublic

theorem ay_bcce_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bcce_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bcce_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bcce_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcce_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bcce_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bcce_accepted_cutoff_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bcce_public_report
      (ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bcce_public_report_intro
      (ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bcce_accepted_cutoff_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bcce_public_report
      (ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bcce_accepted_cutoff_guides_sat guardEvidence agreementEvidence
    cutoffGuidance unsatOutcome formulaTruth

theorem ay_bcce_accepted_cutoff_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    ay_bcce_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bcce_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bcce_conflict_cutoff_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (cutoffGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bcce_accepted_cutoff guardEvidence agreementEvidence cutoffGuidance ->
    ay_bcce_equisat beforeTruth afterTruth ->
    ay_bcce_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bcce_equisat_intro afterTruth beforeTruth
      (ay_bcce_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bcce_equisat_forward beforeTruth afterTruth eqsat)
