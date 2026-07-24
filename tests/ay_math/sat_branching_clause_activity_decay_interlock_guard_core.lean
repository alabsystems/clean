-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-activity/decay interlock guard skeleton for sequential-main SAT.
-- Clause activity decay metadata is a performance hint only when activity
-- epochs, decay schedules, clause activity digests, learned-clause coverage,
-- restart/phase snapshots, fallback, build, validator, and audit evidence agree.

def ay_bcad_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcad_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bcad_conj (before -> after) (after -> before)

def ay_bcad_interlock_guard
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (activityEpochLedger ->
      decayScheduleDigest ->
      clauseActivityDigest ->
      learnedClauseCoverage ->
      restartPhaseSnapshots ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bcad_guard_agreement
    (activityEpochMatch : Prop)
    (decayDigestMatch : Prop)
    (clauseActivityMatch : Prop)
    (coverageMatch : Prop)
    (restartPhaseMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bcad_interlock_guard activityEpochMatch decayDigestMatch
    clauseActivityMatch coverageMatch restartPhaseMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_bcad_accepted_decay
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) : Prop :=
  ay_bcad_conj guardEvidence (ay_bcad_conj agreementEvidence decayGuidance)

def ay_bcad_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bcad_conj acceptedEvidence (ay_bcad_conj outcome formulaTruth)

def ay_bcad_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bcad_conj diagnostic fallbackPublic

theorem ay_bcad_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bcad_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bcad_conj_left (left : Prop) (right : Prop) :
    ay_bcad_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bcad_conj_right (left : Prop) (right : Prop) :
    ay_bcad_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bcad_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bcad_equisat before after :=
  fun forward backward =>
    ay_bcad_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bcad_equisat_forward (before : Prop) (after : Prop) :
    ay_bcad_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bcad_conj_left (before -> after) (after -> before) eqsat

theorem ay_bcad_equisat_backward (before : Prop) (after : Prop) :
    ay_bcad_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bcad_conj_right (before -> after) (after -> before) eqsat

theorem ay_bcad_interlock_guard_intro
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    activityEpochLedger ->
    decayScheduleDigest ->
    clauseActivityDigest ->
    learnedClauseCoverage ->
    restartPhaseSnapshots ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun epochH decayH activityH coverageH restartPhaseH fallbackH buildH
      validatorH auditH result build =>
    build epochH decayH activityH coverageH restartPhaseH fallbackH buildH
      validatorH auditH

theorem ay_bcad_interlock_guard_activity_epoch
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityEpochLedger :=
  fun guard =>
    guard activityEpochLedger
      (fun epochH _decayH _activityH _coverageH _restartPhaseH _fallbackH
          _buildH _validatorH _auditH => epochH)

theorem ay_bcad_interlock_guard_decay_digest
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    decayScheduleDigest :=
  fun guard =>
    guard decayScheduleDigest
      (fun _epochH decayH _activityH _coverageH _restartPhaseH _fallbackH
          _buildH _validatorH _auditH => decayH)

theorem ay_bcad_interlock_guard_clause_activity
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    clauseActivityDigest :=
  fun guard =>
    guard clauseActivityDigest
      (fun _epochH _decayH activityH _coverageH _restartPhaseH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bcad_interlock_guard_coverage
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    learnedClauseCoverage :=
  fun guard =>
    guard learnedClauseCoverage
      (fun _epochH _decayH _activityH coverageH _restartPhaseH _fallbackH
          _buildH _validatorH _auditH => coverageH)

theorem ay_bcad_interlock_guard_restart_phase
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    restartPhaseSnapshots :=
  fun guard =>
    guard restartPhaseSnapshots
      (fun _epochH _decayH _activityH _coverageH restartPhaseH _fallbackH
          _buildH _validatorH _auditH => restartPhaseH)

theorem ay_bcad_interlock_guard_fallback
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _decayH _activityH _coverageH _restartPhaseH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bcad_interlock_guard_build
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _decayH _activityH _coverageH _restartPhaseH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bcad_interlock_guard_validator
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _decayH _activityH _coverageH _restartPhaseH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bcad_interlock_guard_audit
    (activityEpochLedger : Prop)
    (decayScheduleDigest : Prop)
    (clauseActivityDigest : Prop)
    (learnedClauseCoverage : Prop)
    (restartPhaseSnapshots : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcad_interlock_guard activityEpochLedger decayScheduleDigest
      clauseActivityDigest learnedClauseCoverage restartPhaseSnapshots
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _decayH _activityH _coverageH _restartPhaseH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bcad_guard_agreement_intro
    (activityEpochMatch : Prop)
    (decayDigestMatch : Prop)
    (clauseActivityMatch : Prop)
    (coverageMatch : Prop)
    (restartPhaseMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    activityEpochMatch ->
    decayDigestMatch ->
    clauseActivityMatch ->
    coverageMatch ->
    restartPhaseMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcad_guard_agreement activityEpochMatch decayDigestMatch
      clauseActivityMatch coverageMatch restartPhaseMatch fallbackMatch
      buildMatch validatorAccepts auditMatch :=
  ay_bcad_interlock_guard_intro activityEpochMatch decayDigestMatch
    clauseActivityMatch coverageMatch restartPhaseMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_bcad_accepted_decay_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    decayGuidance ->
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bcad_conj_intro guardEvidence
      (ay_bcad_conj agreementEvidence decayGuidance)
      guardH
      (ay_bcad_conj_intro agreementEvidence decayGuidance agreementH guidanceH)

theorem ay_bcad_accepted_decay_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bcad_conj_left guardEvidence
      (ay_bcad_conj agreementEvidence decayGuidance)
      accepted

theorem ay_bcad_accepted_decay_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bcad_conj_left agreementEvidence decayGuidance
      (ay_bcad_conj_right guardEvidence
        (ay_bcad_conj agreementEvidence decayGuidance)
        accepted)

theorem ay_bcad_accepted_decay_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    decayGuidance :=
  fun accepted =>
    ay_bcad_conj_right agreementEvidence decayGuidance
      (ay_bcad_conj_right guardEvidence
        (ay_bcad_conj agreementEvidence decayGuidance)
        accepted)

theorem ay_bcad_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bcad_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bcad_conj_intro acceptedEvidence
      (ay_bcad_conj outcome formulaTruth)
      acceptedH
      (ay_bcad_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bcad_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bcad_conj_left acceptedEvidence
      (ay_bcad_conj outcome formulaTruth)
      public

theorem ay_bcad_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bcad_no_claim diagnostic fallbackPublic :=
  ay_bcad_conj_intro diagnostic fallbackPublic

theorem ay_bcad_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcad_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bcad_conj_right diagnostic fallbackPublic noClaim

theorem ay_bcad_activity_epoch_drift_no_claim
    (activityEpochDrift : Prop)
    (fallbackPublic : Prop) :
    activityEpochDrift ->
    fallbackPublic ->
    ay_bcad_no_claim activityEpochDrift fallbackPublic :=
  ay_bcad_no_claim_intro activityEpochDrift fallbackPublic

theorem ay_bcad_decay_digest_mismatch_no_claim
    (decayDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    decayDigestMismatch ->
    fallbackPublic ->
    ay_bcad_no_claim decayDigestMismatch fallbackPublic :=
  ay_bcad_no_claim_intro decayDigestMismatch fallbackPublic

theorem ay_bcad_clause_activity_digest_mismatch_no_claim
    (clauseActivityDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    clauseActivityDigestMismatch ->
    fallbackPublic ->
    ay_bcad_no_claim clauseActivityDigestMismatch fallbackPublic :=
  ay_bcad_no_claim_intro clauseActivityDigestMismatch fallbackPublic

theorem ay_bcad_coverage_gap_no_claim
    (coverageGap : Prop)
    (fallbackPublic : Prop) :
    coverageGap -> fallbackPublic -> ay_bcad_no_claim coverageGap fallbackPublic :=
  ay_bcad_no_claim_intro coverageGap fallbackPublic

theorem ay_bcad_restart_phase_mismatch_no_claim
    (restartPhaseMismatch : Prop)
    (fallbackPublic : Prop) :
    restartPhaseMismatch ->
    fallbackPublic ->
    ay_bcad_no_claim restartPhaseMismatch fallbackPublic :=
  ay_bcad_no_claim_intro restartPhaseMismatch fallbackPublic

theorem ay_bcad_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcad_no_claim missingFallback fallbackPublic :=
  ay_bcad_no_claim_intro missingFallback fallbackPublic

theorem ay_bcad_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bcad_no_claim staleBuild fallbackPublic :=
  ay_bcad_no_claim_intro staleBuild fallbackPublic

theorem ay_bcad_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_bcad_no_claim validatorRejection fallbackPublic :=
  ay_bcad_no_claim_intro validatorRejection fallbackPublic

theorem ay_bcad_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcad_no_claim auditContradiction fallbackPublic :=
  ay_bcad_no_claim_intro auditContradiction fallbackPublic

theorem ay_bcad_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bcad_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bcad_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bcad_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcad_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bcad_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bcad_accepted_decay_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bcad_public_report
      (ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bcad_public_report_intro
      (ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bcad_accepted_decay_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bcad_public_report
      (ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bcad_accepted_decay_guides_sat guardEvidence agreementEvidence
    decayGuidance unsatOutcome formulaTruth

theorem ay_bcad_accepted_decay_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    ay_bcad_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bcad_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bcad_clause_activity_decay_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bcad_accepted_decay guardEvidence agreementEvidence decayGuidance ->
    ay_bcad_equisat beforeTruth afterTruth ->
    ay_bcad_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bcad_equisat_intro afterTruth beforeTruth
      (ay_bcad_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bcad_equisat_forward beforeTruth afterTruth eqsat)
