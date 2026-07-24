-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption stack scope guard skeleton for sequential-main SAT. Scoped
-- assumption-stack guidance is a branching/search hint only when frame, scope,
-- candidate, replay, fallback, build, validator, and audit evidence agree.

def ay_assg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_assg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_assg_conj (before -> after) (after -> before)

def ay_assg_guard
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionFrameManifest ->
      scopedStackDigest ->
      decisionCandidateSet ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_assg_agreement
    (frameMatch : Prop)
    (scopeMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_assg_guard frameMatch scopeMatch candidateMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_assg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) : Prop :=
  ay_assg_conj guardEvidence (ay_assg_conj agreementEvidence scopeGuidance)

def ay_assg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_assg_conj acceptedEvidence (ay_assg_conj outcome formulaTruth)

def ay_assg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_assg_conj diagnostic fallbackPublic

theorem ay_assg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_assg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_assg_conj_left (left : Prop) (right : Prop) :
    ay_assg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_assg_conj_right (left : Prop) (right : Prop) :
    ay_assg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_assg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_assg_equisat before after :=
  fun forward backward =>
    ay_assg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_assg_equisat_forward (before : Prop) (after : Prop) :
    ay_assg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_assg_conj_left (before -> after) (after -> before) eqsat

theorem ay_assg_equisat_backward (before : Prop) (after : Prop) :
    ay_assg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_assg_conj_right (before -> after) (after -> before) eqsat

theorem ay_assg_guard_intro
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    assumptionFrameManifest ->
    scopedStackDigest ->
    decisionCandidateSet ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun frameH scopeH candidateH replayH fallbackH buildH validatorH auditH
      result build =>
    build frameH scopeH candidateH replayH fallbackH buildH validatorH auditH

theorem ay_assg_guard_frame
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    assumptionFrameManifest :=
  fun guard =>
    guard assumptionFrameManifest
      (fun frameH _scopeH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => frameH)

theorem ay_assg_guard_scope
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    scopedStackDigest :=
  fun guard =>
    guard scopedStackDigest
      (fun _frameH scopeH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => scopeH)

theorem ay_assg_guard_candidate
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionCandidateSet :=
  fun guard =>
    guard decisionCandidateSet
      (fun _frameH _scopeH candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => candidateH)

theorem ay_assg_guard_replay
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _frameH _scopeH _candidateH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_assg_guard_fallback
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _frameH _scopeH _candidateH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_assg_guard_build
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _frameH _scopeH _candidateH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_assg_guard_validator
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _frameH _scopeH _candidateH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_assg_guard_audit
    (assumptionFrameManifest : Prop)
    (scopedStackDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_assg_guard assumptionFrameManifest scopedStackDigest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _frameH _scopeH _candidateH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_assg_agreement_intro
    (frameMatch : Prop)
    (scopeMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    frameMatch ->
    scopeMatch ->
    candidateMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_assg_agreement frameMatch scopeMatch candidateMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_assg_guard_intro frameMatch scopeMatch candidateMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_assg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    scopeGuidance ->
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance :=
  fun guardH agreementH guidanceH =>
    ay_assg_conj_intro guardEvidence
      (ay_assg_conj agreementEvidence scopeGuidance)
      guardH
      (ay_assg_conj_intro agreementEvidence scopeGuidance agreementH guidanceH)

theorem ay_assg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_assg_conj_left guardEvidence
      (ay_assg_conj agreementEvidence scopeGuidance)
      accepted

theorem ay_assg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_assg_conj_left agreementEvidence scopeGuidance
      (ay_assg_conj_right guardEvidence
        (ay_assg_conj agreementEvidence scopeGuidance)
        accepted)

theorem ay_assg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    scopeGuidance :=
  fun accepted =>
    ay_assg_conj_right agreementEvidence scopeGuidance
      (ay_assg_conj_right guardEvidence
        (ay_assg_conj agreementEvidence scopeGuidance)
        accepted)

theorem ay_assg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_assg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_assg_conj_intro acceptedEvidence
      (ay_assg_conj outcome formulaTruth)
      acceptedH
      (ay_assg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_assg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_assg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_assg_conj_left acceptedEvidence
      (ay_assg_conj outcome formulaTruth)
      public

theorem ay_assg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_assg_no_claim diagnostic fallbackPublic :=
  ay_assg_conj_intro diagnostic fallbackPublic

theorem ay_assg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_assg_conj_right diagnostic fallbackPublic noClaim

theorem ay_assg_frame_failure_no_claim
    (frameFailure : Prop)
    (fallbackPublic : Prop) :
    frameFailure -> fallbackPublic -> ay_assg_no_claim frameFailure fallbackPublic :=
  ay_assg_no_claim_intro frameFailure fallbackPublic

theorem ay_assg_scope_failure_no_claim
    (scopeFailure : Prop)
    (fallbackPublic : Prop) :
    scopeFailure -> fallbackPublic -> ay_assg_no_claim scopeFailure fallbackPublic :=
  ay_assg_no_claim_intro scopeFailure fallbackPublic

theorem ay_assg_candidate_failure_no_claim
    (candidateFailure : Prop)
    (fallbackPublic : Prop) :
    candidateFailure ->
    fallbackPublic ->
    ay_assg_no_claim candidateFailure fallbackPublic :=
  ay_assg_no_claim_intro candidateFailure fallbackPublic

theorem ay_assg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_assg_no_claim replayFailure fallbackPublic :=
  ay_assg_no_claim_intro replayFailure fallbackPublic

theorem ay_assg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_assg_no_claim fallbackFailure fallbackPublic :=
  ay_assg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_assg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_assg_no_claim buildFailure fallbackPublic :=
  ay_assg_no_claim_intro buildFailure fallbackPublic

theorem ay_assg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_assg_no_claim validatorFailure fallbackPublic :=
  ay_assg_no_claim_intro validatorFailure fallbackPublic

theorem ay_assg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_assg_no_claim auditFailure fallbackPublic :=
  ay_assg_no_claim_intro auditFailure fallbackPublic

theorem ay_assg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_assg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_assg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_assg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_assg_accepted_guidance_is_assumption_search_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    scopeGuidance :=
  ay_assg_accepted_guidance_hint guardEvidence agreementEvidence scopeGuidance

theorem ay_assg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    ay_assg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_assg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_assg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_assg_public_report
      (ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_assg_public_report_intro
      (ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_assg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_assg_public_report
      (ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance)
      unsatOutcome
      formulaTruth :=
  ay_assg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    scopeGuidance unsatOutcome formulaTruth

theorem ay_assg_scope_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (scopeGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_assg_accepted_guidance guardEvidence agreementEvidence scopeGuidance ->
    ay_assg_equisat beforeTruth afterTruth ->
    ay_assg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_assg_equisat_intro afterTruth beforeTruth
      (ay_assg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_assg_equisat_forward beforeTruth afterTruth eqsat)
