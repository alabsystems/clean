-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-bump heap digest guard skeleton for sequential-main SAT. Heap
-- reorder guidance is a branching hint only when bump ledgers, heap digests,
-- candidate sets, VSIDS state, propagation replay, fallback, build, validator,
-- and audit evidence agree.

def ay_vbhg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vbhg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_vbhg_conj (before -> after) (after -> before)

def ay_vbhg_digest_guard
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (bumpEventLedger ->
      heapDigest ->
      decisionCandidateSet ->
      vsidsStateDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_vbhg_guard_agreement
    (ledgerMatch : Prop)
    (heapMatch : Prop)
    (candidateMatch : Prop)
    (stateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_vbhg_digest_guard ledgerMatch heapMatch candidateMatch stateMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_vbhg_accepted_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) : Prop :=
  ay_vbhg_conj guardEvidence (ay_vbhg_conj agreementEvidence heapGuidance)

def ay_vbhg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_vbhg_conj acceptedEvidence (ay_vbhg_conj outcome formulaTruth)

def ay_vbhg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_vbhg_conj diagnostic fallbackPublic

theorem ay_vbhg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_vbhg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_vbhg_conj_left (left : Prop) (right : Prop) :
    ay_vbhg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_vbhg_conj_right (left : Prop) (right : Prop) :
    ay_vbhg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_vbhg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_vbhg_equisat before after :=
  fun forward backward =>
    ay_vbhg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_vbhg_equisat_forward (before : Prop) (after : Prop) :
    ay_vbhg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_vbhg_conj_left (before -> after) (after -> before) eqsat

theorem ay_vbhg_equisat_backward (before : Prop) (after : Prop) :
    ay_vbhg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_vbhg_conj_right (before -> after) (after -> before) eqsat

theorem ay_vbhg_digest_guard_intro
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    bumpEventLedger ->
    heapDigest ->
    decisionCandidateSet ->
    vsidsStateDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun ledgerH heapH candidateH stateH replayH fallbackH buildH validatorH
      auditH result build =>
    build ledgerH heapH candidateH stateH replayH fallbackH buildH validatorH
      auditH

theorem ay_vbhg_digest_guard_ledger
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    bumpEventLedger :=
  fun guard =>
    guard bumpEventLedger
      (fun ledgerH _heapH _candidateH _stateH _replayH _fallbackH _buildH
          _validatorH _auditH => ledgerH)

theorem ay_vbhg_digest_guard_heap
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    heapDigest :=
  fun guard =>
    guard heapDigest
      (fun _ledgerH heapH _candidateH _stateH _replayH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_vbhg_digest_guard_candidate
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionCandidateSet :=
  fun guard =>
    guard decisionCandidateSet
      (fun _ledgerH _heapH candidateH _stateH _replayH _fallbackH _buildH
          _validatorH _auditH => candidateH)

theorem ay_vbhg_digest_guard_state
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    vsidsStateDigest :=
  fun guard =>
    guard vsidsStateDigest
      (fun _ledgerH _heapH _candidateH stateH _replayH _fallbackH _buildH
          _validatorH _auditH => stateH)

theorem ay_vbhg_digest_guard_replay
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _ledgerH _heapH _candidateH _stateH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_vbhg_digest_guard_fallback
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _ledgerH _heapH _candidateH _stateH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_vbhg_digest_guard_build
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _ledgerH _heapH _candidateH _stateH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_vbhg_digest_guard_validator
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _ledgerH _heapH _candidateH _stateH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_vbhg_digest_guard_audit
    (bumpEventLedger : Prop)
    (heapDigest : Prop)
    (decisionCandidateSet : Prop)
    (vsidsStateDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_vbhg_digest_guard bumpEventLedger heapDigest decisionCandidateSet
      vsidsStateDigest propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _ledgerH _heapH _candidateH _stateH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_vbhg_guard_agreement_intro
    (ledgerMatch : Prop)
    (heapMatch : Prop)
    (candidateMatch : Prop)
    (stateMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ledgerMatch ->
    heapMatch ->
    candidateMatch ->
    stateMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_vbhg_guard_agreement ledgerMatch heapMatch candidateMatch stateMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_vbhg_digest_guard_intro ledgerMatch heapMatch candidateMatch stateMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_vbhg_accepted_guidance_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    heapGuidance ->
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance :=
  fun guardH agreementH guidanceH =>
    ay_vbhg_conj_intro guardEvidence
      (ay_vbhg_conj agreementEvidence heapGuidance)
      guardH
      (ay_vbhg_conj_intro agreementEvidence heapGuidance agreementH guidanceH)

theorem ay_vbhg_accepted_guidance_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_vbhg_conj_left guardEvidence
      (ay_vbhg_conj agreementEvidence heapGuidance)
      accepted

theorem ay_vbhg_accepted_guidance_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_vbhg_conj_left agreementEvidence heapGuidance
      (ay_vbhg_conj_right guardEvidence
        (ay_vbhg_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_vbhg_accepted_guidance_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    heapGuidance :=
  fun accepted =>
    ay_vbhg_conj_right agreementEvidence heapGuidance
      (ay_vbhg_conj_right guardEvidence
        (ay_vbhg_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_vbhg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_vbhg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_vbhg_conj_intro acceptedEvidence
      (ay_vbhg_conj outcome formulaTruth)
      acceptedH
      (ay_vbhg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_vbhg_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_vbhg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_vbhg_conj_left acceptedEvidence
      (ay_vbhg_conj outcome formulaTruth)
      public

theorem ay_vbhg_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_vbhg_no_claim diagnostic fallbackPublic :=
  ay_vbhg_conj_intro diagnostic fallbackPublic

theorem ay_vbhg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_vbhg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_vbhg_conj_right diagnostic fallbackPublic noClaim

theorem ay_vbhg_ledger_failure_no_claim
    (ledgerFailure : Prop)
    (fallbackPublic : Prop) :
    ledgerFailure ->
    fallbackPublic ->
    ay_vbhg_no_claim ledgerFailure fallbackPublic :=
  ay_vbhg_no_claim_intro ledgerFailure fallbackPublic

theorem ay_vbhg_heap_failure_no_claim
    (heapFailure : Prop)
    (fallbackPublic : Prop) :
    heapFailure -> fallbackPublic -> ay_vbhg_no_claim heapFailure fallbackPublic :=
  ay_vbhg_no_claim_intro heapFailure fallbackPublic

theorem ay_vbhg_candidate_failure_no_claim
    (candidateFailure : Prop)
    (fallbackPublic : Prop) :
    candidateFailure ->
    fallbackPublic ->
    ay_vbhg_no_claim candidateFailure fallbackPublic :=
  ay_vbhg_no_claim_intro candidateFailure fallbackPublic

theorem ay_vbhg_state_failure_no_claim
    (stateFailure : Prop)
    (fallbackPublic : Prop) :
    stateFailure -> fallbackPublic -> ay_vbhg_no_claim stateFailure fallbackPublic :=
  ay_vbhg_no_claim_intro stateFailure fallbackPublic

theorem ay_vbhg_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_vbhg_no_claim replayFailure fallbackPublic :=
  ay_vbhg_no_claim_intro replayFailure fallbackPublic

theorem ay_vbhg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_vbhg_no_claim fallbackFailure fallbackPublic :=
  ay_vbhg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_vbhg_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_vbhg_no_claim buildFailure fallbackPublic :=
  ay_vbhg_no_claim_intro buildFailure fallbackPublic

theorem ay_vbhg_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_vbhg_no_claim validatorFailure fallbackPublic :=
  ay_vbhg_no_claim_intro validatorFailure fallbackPublic

theorem ay_vbhg_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_vbhg_no_claim auditFailure fallbackPublic :=
  ay_vbhg_no_claim_intro auditFailure fallbackPublic

theorem ay_vbhg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_vbhg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_vbhg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_vbhg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_vbhg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_vbhg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_vbhg_accepted_guidance_is_branching_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    heapGuidance :=
  ay_vbhg_accepted_guidance_hint guardEvidence agreementEvidence heapGuidance

theorem ay_vbhg_accepted_guidance_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    ay_vbhg_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_vbhg_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_vbhg_accepted_guidance_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_vbhg_public_report
      (ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_vbhg_public_report_intro
      (ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_vbhg_accepted_guidance_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_vbhg_public_report
      (ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance)
      unsatOutcome
      formulaTruth :=
  ay_vbhg_accepted_guidance_guides_sat guardEvidence agreementEvidence
    heapGuidance unsatOutcome formulaTruth

theorem ay_vbhg_heap_guidance_does_not_change_satisfiability
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_vbhg_accepted_guidance guardEvidence agreementEvidence heapGuidance ->
    ay_vbhg_equisat beforeTruth afterTruth ->
    ay_vbhg_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_vbhg_equisat_intro afterTruth beforeTruth
      (ay_vbhg_equisat_backward beforeTruth afterTruth eqsat)
      (ay_vbhg_equisat_forward beforeTruth afterTruth eqsat)
