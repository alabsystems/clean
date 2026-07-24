-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-activity decay-window guard skeleton for sequential-main SAT. Decay
-- window hints are performance guidance only when epoch, activity, candidate,
-- VSIDS/EVSIDS, propagation replay, fallback, build, validator, and audit
-- evidence agree.

def ay_bcad_window_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcad_window_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bcad_window_conj (before -> after) (after -> before)

def ay_bcad_window_guard
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (decayEpochLedger ->
      clauseActivityDigest ->
      candidateClauseSet ->
      vsidsStateDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_bcad_window_agreement
    (epochMatch : Prop)
    (activityDigestMatch : Prop)
    (candidateSetMatch : Prop)
    (vsidsDigestMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bcad_window_guard epochMatch activityDigestMatch candidateSetMatch
    vsidsDigestMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_bcad_window_accepted
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop) : Prop :=
  ay_bcad_window_conj guardEvidence
    (ay_bcad_window_conj agreementEvidence decayWindowGuidance)

def ay_bcad_window_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bcad_window_conj acceptedEvidence
    (ay_bcad_window_conj outcome formulaTruth)

def ay_bcad_window_no_claim
    (diagnostic : Prop)
    (fallbackPublic : Prop) : Prop :=
  ay_bcad_window_conj diagnostic fallbackPublic

theorem ay_bcad_window_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bcad_window_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bcad_window_conj_left (left : Prop) (right : Prop) :
    ay_bcad_window_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bcad_window_conj_right (left : Prop) (right : Prop) :
    ay_bcad_window_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bcad_window_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcad_window_equisat before after :=
  fun forward backward =>
    ay_bcad_window_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcad_window_equisat_forward (before : Prop) (after : Prop) :
    ay_bcad_window_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bcad_window_conj_left (before -> after) (after -> before) eqsat

theorem ay_bcad_window_equisat_backward (before : Prop) (after : Prop) :
    ay_bcad_window_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bcad_window_conj_right (before -> after) (after -> before) eqsat

theorem ay_bcad_window_guard_intro
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    decayEpochLedger ->
    clauseActivityDigest ->
    candidateClauseSet ->
    vsidsStateDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript :=
  fun epochH activityH candidateH vsidsH replayH fallbackH buildH
      validatorH auditH result build =>
    build epochH activityH candidateH vsidsH replayH fallbackH buildH
      validatorH auditH

theorem ay_bcad_window_guard_epoch
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    decayEpochLedger :=
  fun guard =>
    guard decayEpochLedger
      (fun epochH _activityH _candidateH _vsidsH _replayH _fallbackH
          _buildH _validatorH _auditH => epochH)

theorem ay_bcad_window_guard_activity
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    clauseActivityDigest :=
  fun guard =>
    guard clauseActivityDigest
      (fun _epochH activityH _candidateH _vsidsH _replayH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bcad_window_guard_candidate
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    candidateClauseSet :=
  fun guard =>
    guard candidateClauseSet
      (fun _epochH _activityH candidateH _vsidsH _replayH _fallbackH
          _buildH _validatorH _auditH => candidateH)

theorem ay_bcad_window_guard_vsids
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    vsidsStateDigest :=
  fun guard =>
    guard vsidsStateDigest
      (fun _epochH _activityH _candidateH vsidsH _replayH _fallbackH
          _buildH _validatorH _auditH => vsidsH)

theorem ay_bcad_window_guard_replay
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _activityH _candidateH _vsidsH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_bcad_window_guard_fallback
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _activityH _candidateH _vsidsH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bcad_window_guard_build
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _activityH _candidateH _vsidsH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bcad_window_guard_validator
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _activityH _candidateH _vsidsH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bcad_window_guard_audit
    (decayEpochLedger : Prop)
    (clauseActivityDigest : Prop)
    (candidateClauseSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_bcad_window_guard decayEpochLedger clauseActivityDigest
      candidateClauseSet vsidsStateDigest propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _activityH _candidateH _vsidsH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bcad_window_agreement_intro
    (epochMatch : Prop)
    (activityDigestMatch : Prop)
    (candidateSetMatch : Prop)
    (vsidsDigestMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    activityDigestMatch ->
    candidateSetMatch ->
    vsidsDigestMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcad_window_agreement epochMatch activityDigestMatch candidateSetMatch
      vsidsDigestMatch replayMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_bcad_window_guard_intro epochMatch activityDigestMatch candidateSetMatch
    vsidsDigestMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_bcad_window_accepted_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    decayWindowGuidance ->
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bcad_window_conj_intro guardEvidence
      (ay_bcad_window_conj agreementEvidence decayWindowGuidance)
      guardH
      (ay_bcad_window_conj_intro agreementEvidence decayWindowGuidance
        agreementH guidanceH)

theorem ay_bcad_window_accepted_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bcad_window_conj_left guardEvidence
      (ay_bcad_window_conj agreementEvidence decayWindowGuidance)
      accepted

theorem ay_bcad_window_accepted_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bcad_window_conj_left agreementEvidence decayWindowGuidance
      (ay_bcad_window_conj_right guardEvidence
        (ay_bcad_window_conj agreementEvidence decayWindowGuidance)
        accepted)

theorem ay_bcad_window_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    decayWindowGuidance :=
  fun accepted =>
    ay_bcad_window_conj_right agreementEvidence decayWindowGuidance
      (ay_bcad_window_conj_right guardEvidence
        (ay_bcad_window_conj agreementEvidence decayWindowGuidance)
        accepted)

theorem ay_bcad_window_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bcad_window_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bcad_window_conj_intro acceptedEvidence
      (ay_bcad_window_conj outcome formulaTruth)
      acceptedH
      (ay_bcad_window_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bcad_window_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_window_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bcad_window_conj_left acceptedEvidence
      (ay_bcad_window_conj outcome formulaTruth)
      public

theorem ay_bcad_window_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_bcad_window_no_claim diagnostic fallbackPublic :=
  ay_bcad_window_conj_intro diagnostic fallbackPublic

theorem ay_bcad_window_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcad_window_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bcad_window_conj_right diagnostic fallbackPublic noClaim

theorem ay_bcad_window_epoch_failure_no_claim
    (epochFailure : Prop)
    (fallbackPublic : Prop) :
    epochFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim epochFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro epochFailure fallbackPublic

theorem ay_bcad_window_digest_failure_no_claim
    (digestFailure : Prop)
    (fallbackPublic : Prop) :
    digestFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim digestFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro digestFailure fallbackPublic

theorem ay_bcad_window_candidate_failure_no_claim
    (candidateFailure : Prop)
    (fallbackPublic : Prop) :
    candidateFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim candidateFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro candidateFailure fallbackPublic

theorem ay_bcad_window_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim replayFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro replayFailure fallbackPublic

theorem ay_bcad_window_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim fallbackFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro fallbackFailure fallbackPublic

theorem ay_bcad_window_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim buildFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro buildFailure fallbackPublic

theorem ay_bcad_window_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim validatorFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro validatorFailure fallbackPublic

theorem ay_bcad_window_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure ->
    fallbackPublic ->
    ay_bcad_window_no_claim auditFailure fallbackPublic :=
  ay_bcad_window_no_claim_intro auditFailure fallbackPublic

theorem ay_bcad_window_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bcad_window_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute
      (ay_bcad_window_no_claim_preserves_fallback diagnostic fallbackPublic
        noClaim)

theorem ay_bcad_window_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcad_window_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bcad_window_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bcad_window_accepted_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bcad_window_public_report
      (ay_bcad_window_accepted guardEvidence agreementEvidence
        decayWindowGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bcad_window_public_report_intro
      (ay_bcad_window_accepted guardEvidence agreementEvidence
        decayWindowGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bcad_window_accepted_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bcad_window_public_report
      (ay_bcad_window_accepted guardEvidence agreementEvidence
        decayWindowGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bcad_window_accepted_guides_sat guardEvidence agreementEvidence
    decayWindowGuidance unsatOutcome formulaTruth

theorem ay_bcad_window_accepted_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    ay_bcad_window_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bcad_window_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bcad_window_guidance_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bcad_window_accepted guardEvidence agreementEvidence
      decayWindowGuidance ->
    ay_bcad_window_equisat beforeTruth afterTruth ->
    ay_bcad_window_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bcad_window_equisat_intro afterTruth beforeTruth
      (ay_bcad_window_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bcad_window_equisat_forward beforeTruth afterTruth eqsat)
