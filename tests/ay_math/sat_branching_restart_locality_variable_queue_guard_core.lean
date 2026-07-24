-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart-locality variable queue guard skeleton for sequential-main SAT.
-- Variable queue locality after restarts is a branching hint only when restart
-- epochs, queue digests, locality windows, candidate sets, propagation replay,
-- fallback, build, validator, and audit evidence agree.

def ay_rlvq_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rlvq_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rlvq_conj (before -> after) (after -> before)

def ay_rlvq_guard
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (restartEpochLedger ->
      queueDigest ->
      localityWindowManifest ->
      decisionCandidateSet ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rlvq_agreement
    (epochMatch : Prop)
    (queueMatch : Prop)
    (windowMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_rlvq_guard epochMatch queueMatch windowMatch candidateMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_rlvq_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) : Prop :=
  ay_rlvq_conj guardEvidence (ay_rlvq_conj agreementEvidence queueGuidance)

def ay_rlvq_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_rlvq_conj acceptedEvidence (ay_rlvq_conj outcome formulaTruth)

def ay_rlvq_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_rlvq_conj diagnostic fallbackPublic

theorem ay_rlvq_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_rlvq_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rlvq_conj_left (left : Prop) (right : Prop) :
    ay_rlvq_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rlvq_conj_right (left : Prop) (right : Prop) :
    ay_rlvq_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rlvq_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_rlvq_equisat before after :=
  fun forward backward =>
    ay_rlvq_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rlvq_equisat_forward (before : Prop) (after : Prop) :
    ay_rlvq_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rlvq_conj_left (before -> after) (after -> before) eqsat

theorem ay_rlvq_equisat_backward (before : Prop) (after : Prop) :
    ay_rlvq_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rlvq_conj_right (before -> after) (after -> before) eqsat

theorem ay_rlvq_guard_intro
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    restartEpochLedger ->
    queueDigest ->
    localityWindowManifest ->
    decisionCandidateSet ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun epochH queueH windowH candidateH replayH fallbackH buildH validatorH
      auditH result build =>
    build epochH queueH windowH candidateH replayH fallbackH buildH validatorH
      auditH

theorem ay_rlvq_guard_epoch
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    restartEpochLedger :=
  fun guard =>
    guard restartEpochLedger
      (fun epochH _queueH _windowH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_rlvq_guard_queue
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    queueDigest :=
  fun guard =>
    guard queueDigest
      (fun _epochH queueH _windowH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => queueH)

theorem ay_rlvq_guard_window
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    localityWindowManifest :=
  fun guard =>
    guard localityWindowManifest
      (fun _epochH _queueH windowH _candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_rlvq_guard_candidate
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionCandidateSet :=
  fun guard =>
    guard decisionCandidateSet
      (fun _epochH _queueH _windowH candidateH _replayH _fallbackH _buildH
          _validatorH _auditH => candidateH)

theorem ay_rlvq_guard_replay
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _queueH _windowH _candidateH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_rlvq_guard_fallback
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _queueH _windowH _candidateH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_rlvq_guard_build
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _queueH _windowH _candidateH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_rlvq_guard_validator
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _queueH _windowH _candidateH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_rlvq_guard_audit
    (restartEpochLedger : Prop)
    (queueDigest : Prop)
    (localityWindowManifest : Prop)
    (decisionCandidateSet : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rlvq_guard restartEpochLedger queueDigest localityWindowManifest
      decisionCandidateSet propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _queueH _windowH _candidateH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_rlvq_agreement_intro
    (epochMatch : Prop)
    (queueMatch : Prop)
    (windowMatch : Prop)
    (candidateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    queueMatch ->
    windowMatch ->
    candidateMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rlvq_agreement epochMatch queueMatch windowMatch candidateMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_rlvq_guard_intro epochMatch queueMatch windowMatch candidateMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_rlvq_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    queueGuidance ->
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance :=
  fun guardH agreementH guidanceH =>
    ay_rlvq_conj_intro guardEvidence
      (ay_rlvq_conj agreementEvidence queueGuidance)
      guardH
      (ay_rlvq_conj_intro agreementEvidence queueGuidance agreementH guidanceH)

theorem ay_rlvq_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_rlvq_conj_left guardEvidence
      (ay_rlvq_conj agreementEvidence queueGuidance)
      accepted

theorem ay_rlvq_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_rlvq_conj_left agreementEvidence queueGuidance
      (ay_rlvq_conj_right guardEvidence
        (ay_rlvq_conj agreementEvidence queueGuidance)
        accepted)

theorem ay_rlvq_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    queueGuidance :=
  fun accepted =>
    ay_rlvq_conj_right agreementEvidence queueGuidance
      (ay_rlvq_conj_right guardEvidence
        (ay_rlvq_conj agreementEvidence queueGuidance)
        accepted)

theorem ay_rlvq_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rlvq_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rlvq_conj_intro acceptedEvidence
      (ay_rlvq_conj outcome formulaTruth)
      acceptedH
      (ay_rlvq_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rlvq_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rlvq_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_rlvq_conj_left acceptedEvidence
      (ay_rlvq_conj outcome formulaTruth)
      public

theorem ay_rlvq_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_rlvq_no_claim diagnostic fallbackPublic :=
  ay_rlvq_conj_intro diagnostic fallbackPublic

theorem ay_rlvq_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rlvq_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_rlvq_conj_right diagnostic fallbackPublic noClaim

theorem ay_rlvq_epoch_failure_no_claim
    (epochFailure : Prop)
    (fallbackPublic : Prop) :
    epochFailure -> fallbackPublic -> ay_rlvq_no_claim epochFailure fallbackPublic :=
  ay_rlvq_no_claim_intro epochFailure fallbackPublic

theorem ay_rlvq_queue_failure_no_claim
    (queueFailure : Prop)
    (fallbackPublic : Prop) :
    queueFailure -> fallbackPublic -> ay_rlvq_no_claim queueFailure fallbackPublic :=
  ay_rlvq_no_claim_intro queueFailure fallbackPublic

theorem ay_rlvq_window_failure_no_claim
    (windowFailure : Prop)
    (fallbackPublic : Prop) :
    windowFailure ->
    fallbackPublic ->
    ay_rlvq_no_claim windowFailure fallbackPublic :=
  ay_rlvq_no_claim_intro windowFailure fallbackPublic

theorem ay_rlvq_candidate_failure_no_claim
    (candidateFailure : Prop)
    (fallbackPublic : Prop) :
    candidateFailure ->
    fallbackPublic ->
    ay_rlvq_no_claim candidateFailure fallbackPublic :=
  ay_rlvq_no_claim_intro candidateFailure fallbackPublic

theorem ay_rlvq_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_rlvq_no_claim replayFailure fallbackPublic :=
  ay_rlvq_no_claim_intro replayFailure fallbackPublic

theorem ay_rlvq_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_rlvq_no_claim fallbackFailure fallbackPublic :=
  ay_rlvq_no_claim_intro fallbackFailure fallbackPublic

theorem ay_rlvq_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_rlvq_no_claim buildFailure fallbackPublic :=
  ay_rlvq_no_claim_intro buildFailure fallbackPublic

theorem ay_rlvq_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_rlvq_no_claim validatorFailure fallbackPublic :=
  ay_rlvq_no_claim_intro validatorFailure fallbackPublic

theorem ay_rlvq_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_rlvq_no_claim auditFailure fallbackPublic :=
  ay_rlvq_no_claim_intro auditFailure fallbackPublic

theorem ay_rlvq_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_rlvq_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_rlvq_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_rlvq_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rlvq_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_rlvq_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_rlvq_accepted_guidance_is_branching_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    queueGuidance :=
  ay_rlvq_accepted_guidance_hint guardEvidence agreementEvidence queueGuidance

theorem ay_rlvq_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    ay_rlvq_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_rlvq_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_rlvq_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_rlvq_public_report
      (ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_rlvq_public_report_intro
      (ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_rlvq_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_rlvq_public_report
      (ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance)
      unsatOutcome
      formulaTruth :=
  ay_rlvq_accepted_guidance_guides_sat guardEvidence agreementEvidence
    queueGuidance unsatOutcome formulaTruth

theorem ay_rlvq_queue_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (queueGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_rlvq_accepted_guidance guardEvidence agreementEvidence queueGuidance ->
    ay_rlvq_equisat beforeTruth afterTruth ->
    ay_rlvq_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_rlvq_equisat_intro afterTruth beforeTruth
      (ay_rlvq_equisat_backward beforeTruth afterTruth eqsat)
      (ay_rlvq_equisat_forward beforeTruth afterTruth eqsat)
