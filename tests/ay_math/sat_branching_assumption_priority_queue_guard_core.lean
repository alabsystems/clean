-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption-priority queue guard skeleton for sequential-main SAT. Priority
-- queue guidance under assumptions is a branching hint only when assumption,
-- queue, candidate, replay, fallback, build, validator, and audit evidence agree.

def ay_apqg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_apqg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_apqg_conj (before -> after) (after -> before)

def ay_apqg_guard
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionManifest ->
      priorityQueueDigest ->
      decisionCandidateSet ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_apqg_agreement
    (assumptionMatch : Prop)
    (queueMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_apqg_guard assumptionMatch queueMatch candidateMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_apqg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) : Prop :=
  ay_apqg_conj guardEvidence
    (ay_apqg_conj agreementEvidence priorityGuidance)

def ay_apqg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_apqg_conj acceptedEvidence (ay_apqg_conj outcome formulaTruth)

def ay_apqg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_apqg_conj diagnostic fallbackPublic

theorem ay_apqg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_apqg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_apqg_conj_left (left : Prop) (right : Prop) :
    ay_apqg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_apqg_conj_right (left : Prop) (right : Prop) :
    ay_apqg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_apqg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_apqg_equisat before after :=
  fun forward backward =>
    ay_apqg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_apqg_equisat_forward (before : Prop) (after : Prop) :
    ay_apqg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_apqg_conj_left (before -> after) (after -> before) eqsat

theorem ay_apqg_equisat_backward (before : Prop) (after : Prop) :
    ay_apqg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_apqg_conj_right (before -> after) (after -> before) eqsat

theorem ay_apqg_guard_intro
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    assumptionManifest ->
    priorityQueueDigest ->
    decisionCandidateSet ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun assumptionH queueH candidateH replayH fallbackH buildH validatorH auditH
      result build =>
    build assumptionH queueH candidateH replayH fallbackH buildH validatorH
      auditH

theorem ay_apqg_guard_assumption
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    assumptionManifest :=
  fun guard =>
    guard assumptionManifest
      (fun assumptionH _queueH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => assumptionH)

theorem ay_apqg_guard_queue
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    priorityQueueDigest :=
  fun guard =>
    guard priorityQueueDigest
      (fun _assumptionH queueH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => queueH)

theorem ay_apqg_guard_candidate
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    decisionCandidateSet :=
  fun guard =>
    guard decisionCandidateSet
      (fun _assumptionH _queueH candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => candidateH)

theorem ay_apqg_guard_replay
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _assumptionH _queueH _candidateH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_apqg_guard_fallback
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _assumptionH _queueH _candidateH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_apqg_guard_build
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _assumptionH _queueH _candidateH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_apqg_guard_validator
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _assumptionH _queueH _candidateH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_apqg_guard_audit
    (assumptionManifest : Prop)
    (priorityQueueDigest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_apqg_guard assumptionManifest priorityQueueDigest decisionCandidateSet
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _assumptionH _queueH _candidateH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_apqg_agreement_intro
    (assumptionMatch : Prop)
    (queueMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    assumptionMatch ->
    queueMatch ->
    candidateMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_apqg_agreement assumptionMatch queueMatch candidateMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_apqg_guard_intro assumptionMatch queueMatch candidateMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_apqg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    priorityGuidance ->
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance :=
  fun guardH agreementH guidanceH =>
    ay_apqg_conj_intro guardEvidence
      (ay_apqg_conj agreementEvidence priorityGuidance)
      guardH
      (ay_apqg_conj_intro agreementEvidence priorityGuidance
        agreementH guidanceH)

theorem ay_apqg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_apqg_conj_left guardEvidence
      (ay_apqg_conj agreementEvidence priorityGuidance)
      accepted

theorem ay_apqg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_apqg_conj_left agreementEvidence priorityGuidance
      (ay_apqg_conj_right guardEvidence
        (ay_apqg_conj agreementEvidence priorityGuidance)
        accepted)

theorem ay_apqg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    priorityGuidance :=
  fun accepted =>
    ay_apqg_conj_right agreementEvidence priorityGuidance
      (ay_apqg_conj_right guardEvidence
        (ay_apqg_conj agreementEvidence priorityGuidance)
        accepted)

theorem ay_apqg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_apqg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_apqg_conj_intro acceptedEvidence
      (ay_apqg_conj outcome formulaTruth)
      acceptedH
      (ay_apqg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_apqg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_apqg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_apqg_conj_left acceptedEvidence
      (ay_apqg_conj outcome formulaTruth)
      public

theorem ay_apqg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_apqg_no_claim diagnostic fallbackPublic :=
  ay_apqg_conj_intro diagnostic fallbackPublic

theorem ay_apqg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_apqg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_apqg_conj_right diagnostic fallbackPublic noClaim

theorem ay_apqg_assumption_failure_no_claim
    (assumptionFailure : Prop)
    (fallbackPublic : Prop) :
    assumptionFailure ->
    fallbackPublic ->
    ay_apqg_no_claim assumptionFailure fallbackPublic :=
  ay_apqg_no_claim_intro assumptionFailure fallbackPublic

theorem ay_apqg_queue_failure_no_claim
    (queueFailure : Prop)
    (fallbackPublic : Prop) :
    queueFailure -> fallbackPublic -> ay_apqg_no_claim queueFailure fallbackPublic :=
  ay_apqg_no_claim_intro queueFailure fallbackPublic

theorem ay_apqg_candidate_failure_no_claim
    (candidateFailure : Prop)
    (fallbackPublic : Prop) :
    candidateFailure ->
    fallbackPublic ->
    ay_apqg_no_claim candidateFailure fallbackPublic :=
  ay_apqg_no_claim_intro candidateFailure fallbackPublic

theorem ay_apqg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_apqg_no_claim replayFailure fallbackPublic :=
  ay_apqg_no_claim_intro replayFailure fallbackPublic

theorem ay_apqg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_apqg_no_claim fallbackFailure fallbackPublic :=
  ay_apqg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_apqg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_apqg_no_claim buildFailure fallbackPublic :=
  ay_apqg_no_claim_intro buildFailure fallbackPublic

theorem ay_apqg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_apqg_no_claim validatorFailure fallbackPublic :=
  ay_apqg_no_claim_intro validatorFailure fallbackPublic

theorem ay_apqg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_apqg_no_claim auditFailure fallbackPublic :=
  ay_apqg_no_claim_intro auditFailure fallbackPublic

theorem ay_apqg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_apqg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_apqg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_apqg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_apqg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_apqg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_apqg_accepted_guidance_is_assumption_branching_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    priorityGuidance :=
  ay_apqg_accepted_guidance_hint guardEvidence agreementEvidence
    priorityGuidance

theorem ay_apqg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    ay_apqg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_apqg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_apqg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_apqg_public_report
      (ay_apqg_accepted_guidance guardEvidence agreementEvidence
        priorityGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_apqg_public_report_intro
      (ay_apqg_accepted_guidance guardEvidence agreementEvidence
        priorityGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_apqg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_apqg_public_report
      (ay_apqg_accepted_guidance guardEvidence agreementEvidence
        priorityGuidance)
      unsatOutcome
      formulaTruth :=
  ay_apqg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    priorityGuidance unsatOutcome formulaTruth

theorem ay_apqg_priority_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (priorityGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_apqg_accepted_guidance guardEvidence agreementEvidence
      priorityGuidance ->
    ay_apqg_equisat beforeTruth afterTruth ->
    ay_apqg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_apqg_equisat_intro afterTruth beforeTruth
      (ay_apqg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_apqg_equisat_forward beforeTruth afterTruth eqsat)
