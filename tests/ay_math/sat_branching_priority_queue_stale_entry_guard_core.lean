-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Stale-entry guard for branching priority queues in sequential main-track CDCL.
-- Stale entries are harmless only when freshness, candidate legality, replay,
-- fallback, build, validator, and audit evidence agree.

def ay_pqsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pqsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pqsg_conj (before -> after) (after -> before)

def ay_pqsg_guard
    (variableDomainDigest : Prop)
    (activityVectorDigest : Prop)
    (priorityQueueDigest : Prop)
    (staleEntryLedger : Prop)
    (freshnessWitness : Prop)
    (tiebreakManifest : Prop)
    (candidateLegalityWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorDigest ->
      priorityQueueDigest ->
      staleEntryLedger ->
      freshnessWitness ->
      tiebreakManifest ->
      candidateLegalityWitness ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pqsg_agreement
    (originalFormulaTruth extractedRunTruth publicSoundness : Prop) : Prop :=
  ay_pqsg_conj
    (ay_pqsg_equisat originalFormulaTruth extractedRunTruth)
    publicSoundness

def ay_pqsg_accepted_extraction
    (guardEvidence agreementEvidence searchControlOnly : Prop) : Prop :=
  ay_pqsg_conj guardEvidence
    (ay_pqsg_conj agreementEvidence searchControlOnly)

def ay_pqsg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pqsg_conj acceptedEvidence
    (ay_pqsg_conj outcome formulaTruth)

def ay_pqsg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_pqsg_conj diagnostic fallbackOrRecompute

theorem ay_pqsg_conj_intro (left right : Prop) :
    left -> right -> ay_pqsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pqsg_conj_left (left right : Prop) :
    ay_pqsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pqsg_conj_right (left right : Prop) :
    ay_pqsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pqsg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pqsg_equisat before after :=
  fun forward backward =>
    ay_pqsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pqsg_equisat_forward (before after : Prop) :
    ay_pqsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pqsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pqsg_equisat_backward (before after : Prop) :
    ay_pqsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pqsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pqsg_guard_intro
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityVectorDigest ->
    priorityQueueDigest ->
    staleEntryLedger ->
    freshnessWitness ->
    tiebreakManifest ->
    candidateLegalityWitness ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH activityH queueH staleH freshH tieH candidateH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH activityH queueH staleH freshH tieH candidateH replayH
      fallbackH buildH validatorH auditH

theorem ay_pqsg_guard_domain
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_pqsg_guard_activity
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    activityVectorDigest :=
  fun guard =>
    guard activityVectorDigest
      (fun _domainH activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => activityH)

theorem ay_pqsg_guard_queue
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    priorityQueueDigest :=
  fun guard =>
    guard priorityQueueDigest
      (fun _domainH _activityH queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => queueH)

theorem ay_pqsg_guard_stale
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    staleEntryLedger :=
  fun guard =>
    guard staleEntryLedger
      (fun _domainH _activityH _queueH staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => staleH)

theorem ay_pqsg_guard_freshness
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    freshnessWitness :=
  fun guard =>
    guard freshnessWitness
      (fun _domainH _activityH _queueH _staleH freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => freshH)

theorem ay_pqsg_guard_tiebreak
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _activityH _queueH _staleH _freshH tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_pqsg_guard_candidate
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    candidateLegalityWitness :=
  fun guard =>
    guard candidateLegalityWitness
      (fun _domainH _activityH _queueH _staleH _freshH _tieH candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_pqsg_guard_replay
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_pqsg_guard_fallback
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_pqsg_guard_build
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_pqsg_guard_validator
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_pqsg_guard_audit
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqsg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _queueH _staleH _freshH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_pqsg_agreement_intro
    (originalFormulaTruth extractedRunTruth publicSoundness : Prop) :
    ay_pqsg_equisat originalFormulaTruth extractedRunTruth ->
    publicSoundness ->
    ay_pqsg_agreement originalFormulaTruth extractedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_pqsg_conj_intro
      (ay_pqsg_equisat originalFormulaTruth extractedRunTruth)
      publicSoundness eqsat sound

theorem ay_pqsg_accepted_extraction_intro
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlOnly ->
    ay_pqsg_accepted_extraction guardEvidence agreementEvidence searchControlOnly :=
  fun guardH agreementH searchH =>
    ay_pqsg_conj_intro guardEvidence
      (ay_pqsg_conj agreementEvidence searchControlOnly) guardH
      (ay_pqsg_conj_intro agreementEvidence searchControlOnly agreementH searchH)

theorem ay_pqsg_accepted_guard
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqsg_accepted_extraction guardEvidence agreementEvidence searchControlOnly ->
    guardEvidence :=
  fun accepted =>
    ay_pqsg_conj_left guardEvidence
      (ay_pqsg_conj agreementEvidence searchControlOnly) accepted

theorem ay_pqsg_accepted_agreement
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqsg_accepted_extraction guardEvidence agreementEvidence searchControlOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_pqsg_conj_left agreementEvidence searchControlOnly
      (ay_pqsg_conj_right guardEvidence
        (ay_pqsg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_pqsg_accepted_search_control
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqsg_accepted_extraction guardEvidence agreementEvidence searchControlOnly ->
    searchControlOnly :=
  fun accepted =>
    ay_pqsg_conj_right agreementEvidence searchControlOnly
      (ay_pqsg_conj_right guardEvidence
        (ay_pqsg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_pqsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pqsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pqsg_conj_intro acceptedEvidence (ay_pqsg_conj outcome formulaTruth)
      acceptedH (ay_pqsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pqsg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pqsg_conj_left acceptedEvidence (ay_pqsg_conj outcome formulaTruth)
      report

theorem ay_pqsg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqsg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pqsg_conj_left outcome formulaTruth
      (ay_pqsg_conj_right acceptedEvidence
        (ay_pqsg_conj outcome formulaTruth) report)

theorem ay_pqsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pqsg_conj_right outcome formulaTruth
      (ay_pqsg_conj_right acceptedEvidence
        (ay_pqsg_conj outcome formulaTruth) report)

theorem ay_pqsg_preserves_formula_truth
    (originalFormulaTruth extractedRunTruth : Prop) :
    ay_pqsg_equisat originalFormulaTruth extractedRunTruth ->
    originalFormulaTruth ->
    extractedRunTruth :=
  fun eqsat truth =>
    ay_pqsg_equisat_forward originalFormulaTruth extractedRunTruth eqsat truth

theorem ay_pqsg_reflects_formula_truth
    (originalFormulaTruth extractedRunTruth : Prop) :
    ay_pqsg_equisat originalFormulaTruth extractedRunTruth ->
    extractedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_pqsg_equisat_backward originalFormulaTruth extractedRunTruth eqsat truth

theorem ay_pqsg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlOnly publicSoundness : Prop) :
    ay_pqsg_accepted_extraction guardEvidence agreementEvidence searchControlOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_pqsg_accepted_agreement guardEvidence agreementEvidence
        searchControlOnly accepted)

theorem ay_pqsg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim diagnostic fallbackOrRecompute :=
  ay_pqsg_conj_intro diagnostic fallbackOrRecompute

theorem ay_pqsg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_pqsg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_pqsg_conj_right diagnostic fallbackOrRecompute

theorem ay_pqsg_stale_mismatch_no_claim
    (staleMismatch fallbackOrRecompute : Prop) :
    staleMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim staleMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro staleMismatch fallbackOrRecompute

theorem ay_pqsg_freshness_mismatch_no_claim
    (freshnessMismatch fallbackOrRecompute : Prop) :
    freshnessMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim freshnessMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro freshnessMismatch fallbackOrRecompute

theorem ay_pqsg_order_mismatch_no_claim
    (orderMismatch fallbackOrRecompute : Prop) :
    orderMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim orderMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro orderMismatch fallbackOrRecompute

theorem ay_pqsg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_pqsg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim replayMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_pqsg_queue_mismatch_no_claim
    (queueMismatch fallbackOrRecompute : Prop) :
    queueMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim queueMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro queueMismatch fallbackOrRecompute

theorem ay_pqsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackOrRecompute : Prop) :
    tiebreakMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim tiebreakMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro tiebreakMismatch fallbackOrRecompute

theorem ay_pqsg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim buildMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_pqsg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_pqsg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_pqsg_no_claim auditMismatch fallbackOrRecompute :=
  ay_pqsg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_pqsg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_pqsg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_pqsg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_pqsg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_pqsg_public_report
      (ay_pqsg_accepted_extraction guardEvidence agreementEvidence
        searchControlOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pqsg_accepted_guard guardEvidence agreementEvidence searchControlOnly
      (ay_pqsg_public_report_accepted
        (ay_pqsg_accepted_extraction guardEvidence agreementEvidence
          searchControlOnly)
        outcome formulaTruth report)

theorem ay_pqsg_publication_requires_validator
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      searchControlOnly outcome formulaTruth : Prop) :
    ay_pqsg_public_report
      (ay_pqsg_accepted_extraction
        (ay_pqsg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pqsg_guard_validator variableDomainDigest activityVectorDigest
      priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_pqsg_publication_requires_guard
        (ay_pqsg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_pqsg_publication_requires_audit
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      searchControlOnly outcome formulaTruth : Prop) :
    ay_pqsg_public_report
      (ay_pqsg_accepted_extraction
        (ay_pqsg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pqsg_guard_audit variableDomainDigest activityVectorDigest
      priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_pqsg_publication_requires_guard
        (ay_pqsg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest staleEntryLedger freshnessWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_pqsg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pqsg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pqsg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pqsg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pqsg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pqsg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
