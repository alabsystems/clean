-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-saving epoch replay guard skeleton for sequential-main SAT. Reused
-- phase assignments are branching hints only when epoch, assignment, level,
-- replay, fallback, build, validator, and audit evidence agree.

def ay_bpse_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bpse_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bpse_conj (before -> after) (after -> before)

def ay_bpse_replay_guard
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (phaseEpochLedger ->
      savedAssignmentDigest ->
      decisionLevelBoundary ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_bpse_guard_agreement
    (epochMatch : Prop)
    (digestMatch : Prop)
    (levelMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bpse_replay_guard epochMatch digestMatch levelMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bpse_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) : Prop :=
  ay_bpse_conj guardEvidence (ay_bpse_conj agreementEvidence phaseGuidance)

def ay_bpse_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bpse_conj acceptedEvidence (ay_bpse_conj outcome formulaTruth)

def ay_bpse_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bpse_conj diagnostic fallbackPublic

theorem ay_bpse_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bpse_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bpse_conj_left (left : Prop) (right : Prop) :
    ay_bpse_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bpse_conj_right (left : Prop) (right : Prop) :
    ay_bpse_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bpse_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bpse_equisat before after :=
  fun forward backward =>
    ay_bpse_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bpse_equisat_forward (before : Prop) (after : Prop) :
    ay_bpse_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bpse_conj_left (before -> after) (after -> before) eqsat

theorem ay_bpse_equisat_backward (before : Prop) (after : Prop) :
    ay_bpse_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bpse_conj_right (before -> after) (after -> before) eqsat

theorem ay_bpse_replay_guard_intro
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    phaseEpochLedger ->
    savedAssignmentDigest ->
    decisionLevelBoundary ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun epochH digestH levelH replayH fallbackH buildH validatorH auditH
      result build =>
    build epochH digestH levelH replayH fallbackH buildH validatorH auditH

theorem ay_bpse_replay_guard_epoch
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    phaseEpochLedger :=
  fun guard =>
    guard phaseEpochLedger
      (fun epochH _digestH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bpse_replay_guard_digest
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    savedAssignmentDigest :=
  fun guard =>
    guard savedAssignmentDigest
      (fun _epochH digestH _levelH _replayH _fallbackH _buildH
          _validatorH _auditH => digestH)

theorem ay_bpse_replay_guard_level
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionLevelBoundary :=
  fun guard =>
    guard decisionLevelBoundary
      (fun _epochH _digestH levelH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bpse_replay_guard_replay
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _digestH _levelH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_bpse_replay_guard_fallback
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _digestH _levelH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bpse_replay_guard_build
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _digestH _levelH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bpse_replay_guard_validator
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _digestH _levelH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bpse_replay_guard_audit
    (phaseEpochLedger : Prop)
    (savedAssignmentDigest : Prop)
    (decisionLevelBoundary : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bpse_replay_guard phaseEpochLedger savedAssignmentDigest
      decisionLevelBoundary propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _digestH _levelH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bpse_guard_agreement_intro
    (epochMatch : Prop)
    (digestMatch : Prop)
    (levelMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    digestMatch ->
    levelMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bpse_guard_agreement epochMatch digestMatch levelMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bpse_replay_guard_intro epochMatch digestMatch levelMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bpse_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    phaseGuidance ->
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bpse_conj_intro guardEvidence
      (ay_bpse_conj agreementEvidence phaseGuidance)
      guardH
      (ay_bpse_conj_intro agreementEvidence phaseGuidance agreementH guidanceH)

theorem ay_bpse_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bpse_conj_left guardEvidence
      (ay_bpse_conj agreementEvidence phaseGuidance)
      accepted

theorem ay_bpse_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bpse_conj_left agreementEvidence phaseGuidance
      (ay_bpse_conj_right guardEvidence
        (ay_bpse_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpse_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    phaseGuidance :=
  fun accepted =>
    ay_bpse_conj_right agreementEvidence phaseGuidance
      (ay_bpse_conj_right guardEvidence
        (ay_bpse_conj agreementEvidence phaseGuidance)
        accepted)

theorem ay_bpse_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bpse_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bpse_conj_intro acceptedEvidence
      (ay_bpse_conj outcome formulaTruth)
      acceptedH
      (ay_bpse_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bpse_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bpse_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bpse_conj_left acceptedEvidence
      (ay_bpse_conj outcome formulaTruth)
      public

theorem ay_bpse_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bpse_no_claim diagnostic fallbackPublic :=
  ay_bpse_conj_intro diagnostic fallbackPublic

theorem ay_bpse_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpse_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bpse_conj_right diagnostic fallbackPublic noClaim

theorem ay_bpse_epoch_failure_no_claim
    (epochFailure : Prop)
    (fallbackPublic : Prop) :
    epochFailure -> fallbackPublic -> ay_bpse_no_claim epochFailure fallbackPublic :=
  ay_bpse_no_claim_intro epochFailure fallbackPublic

theorem ay_bpse_digest_failure_no_claim
    (digestFailure : Prop)
    (fallbackPublic : Prop) :
    digestFailure ->
    fallbackPublic ->
    ay_bpse_no_claim digestFailure fallbackPublic :=
  ay_bpse_no_claim_intro digestFailure fallbackPublic

theorem ay_bpse_level_failure_no_claim
    (levelFailure : Prop)
    (fallbackPublic : Prop) :
    levelFailure -> fallbackPublic -> ay_bpse_no_claim levelFailure fallbackPublic :=
  ay_bpse_no_claim_intro levelFailure fallbackPublic

theorem ay_bpse_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_bpse_no_claim replayFailure fallbackPublic :=
  ay_bpse_no_claim_intro replayFailure fallbackPublic

theorem ay_bpse_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_bpse_no_claim fallbackFailure fallbackPublic :=
  ay_bpse_no_claim_intro fallbackFailure fallbackPublic

theorem ay_bpse_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_bpse_no_claim buildFailure fallbackPublic :=
  ay_bpse_no_claim_intro buildFailure fallbackPublic

theorem ay_bpse_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_bpse_no_claim validatorFailure fallbackPublic :=
  ay_bpse_no_claim_intro validatorFailure fallbackPublic

theorem ay_bpse_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_bpse_no_claim auditFailure fallbackPublic :=
  ay_bpse_no_claim_intro auditFailure fallbackPublic

theorem ay_bpse_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bpse_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bpse_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bpse_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bpse_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bpse_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bpse_accepted_guidance_is_branching_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    phaseGuidance :=
  ay_bpse_accepted_guidance_hint guardEvidence agreementEvidence phaseGuidance

theorem ay_bpse_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    ay_bpse_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bpse_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bpse_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bpse_public_report
      (ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bpse_public_report_intro
      (ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bpse_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bpse_public_report
      (ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bpse_accepted_guidance_guides_sat guardEvidence agreementEvidence
    phaseGuidance unsatOutcome formulaTruth

theorem ay_bpse_phase_saving_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (phaseGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bpse_accepted_guidance guardEvidence agreementEvidence phaseGuidance ->
    ay_bpse_equisat beforeTruth afterTruth ->
    ay_bpse_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bpse_equisat_intro afterTruth beforeTruth
      (ay_bpse_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bpse_equisat_forward beforeTruth afterTruth eqsat)
