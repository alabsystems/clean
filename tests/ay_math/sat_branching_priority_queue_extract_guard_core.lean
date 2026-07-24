-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching priority-queue extract guard for sequential main-track CDCL.
-- Queue extraction is search-control only when queue, heuristic order,
-- tie-break, candidate legality, replay, fallback, build, validator, and audit
-- evidence agree.

def ay_pqeg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pqeg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pqeg_conj (before -> after) (after -> before)

def ay_pqeg_guard
    (variableDomainDigest : Prop)
    (assignmentTrailDigest : Prop)
    (priorityQueueDigest : Prop)
    (extractOrderWitness : Prop)
    (tiebreakManifest : Prop)
    (candidateLegalityWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      assignmentTrailDigest ->
      priorityQueueDigest ->
      extractOrderWitness ->
      tiebreakManifest ->
      candidateLegalityWitness ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pqeg_agreement
    (originalFormulaTruth extractedRunTruth publicSoundness : Prop) : Prop :=
  ay_pqeg_conj
    (ay_pqeg_equisat originalFormulaTruth extractedRunTruth)
    publicSoundness

def ay_pqeg_accepted_extract
    (guardEvidence agreementEvidence searchControlOnly : Prop) : Prop :=
  ay_pqeg_conj guardEvidence
    (ay_pqeg_conj agreementEvidence searchControlOnly)

def ay_pqeg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pqeg_conj acceptedEvidence
    (ay_pqeg_conj outcome formulaTruth)

def ay_pqeg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_pqeg_conj diagnostic fallbackOrRecompute

theorem ay_pqeg_conj_intro (left right : Prop) :
    left -> right -> ay_pqeg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pqeg_conj_left (left right : Prop) :
    ay_pqeg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pqeg_conj_right (left right : Prop) :
    ay_pqeg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pqeg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pqeg_equisat before after :=
  fun forward backward =>
    ay_pqeg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pqeg_equisat_forward (before after : Prop) :
    ay_pqeg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pqeg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pqeg_equisat_backward (before after : Prop) :
    ay_pqeg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pqeg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pqeg_guard_intro
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    assignmentTrailDigest ->
    priorityQueueDigest ->
    extractOrderWitness ->
    tiebreakManifest ->
    candidateLegalityWitness ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH trailH queueH orderH tiebreakH candidateH replayH fallbackH
      buildH validatorH auditH result make =>
    make domainH trailH queueH orderH tiebreakH candidateH replayH fallbackH
      buildH validatorH auditH

theorem ay_pqeg_guard_domain
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _trailH _queueH _orderH _tieH _candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_pqeg_guard_trail
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    assignmentTrailDigest :=
  fun guard =>
    guard assignmentTrailDigest
      (fun _domainH trailH _queueH _orderH _tieH _candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => trailH)

theorem ay_pqeg_guard_queue
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    priorityQueueDigest :=
  fun guard =>
    guard priorityQueueDigest
      (fun _domainH _trailH queueH _orderH _tieH _candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => queueH)

theorem ay_pqeg_guard_order
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    extractOrderWitness :=
  fun guard =>
    guard extractOrderWitness
      (fun _domainH _trailH _queueH orderH _tieH _candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => orderH)

theorem ay_pqeg_guard_tiebreak
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _trailH _queueH _orderH tieH _candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_pqeg_guard_candidate
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    candidateLegalityWitness :=
  fun guard =>
    guard candidateLegalityWitness
      (fun _domainH _trailH _queueH _orderH _tieH candidateH _replayH
          _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_pqeg_guard_replay
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _trailH _queueH _orderH _tieH _candidateH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_pqeg_guard_fallback
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _trailH _queueH _orderH _tieH _candidateH _replayH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_pqeg_guard_build
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _trailH _queueH _orderH _tieH _candidateH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_pqeg_guard_validator
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _trailH _queueH _orderH _tieH _candidateH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_pqeg_guard_audit
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_pqeg_guard variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _trailH _queueH _orderH _tieH _candidateH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_pqeg_agreement_intro
    (originalFormulaTruth extractedRunTruth publicSoundness : Prop) :
    ay_pqeg_equisat originalFormulaTruth extractedRunTruth ->
    publicSoundness ->
    ay_pqeg_agreement originalFormulaTruth extractedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_pqeg_conj_intro
      (ay_pqeg_equisat originalFormulaTruth extractedRunTruth)
      publicSoundness eqsat sound

theorem ay_pqeg_accepted_extract_intro
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlOnly ->
    ay_pqeg_accepted_extract guardEvidence agreementEvidence searchControlOnly :=
  fun guardH agreementH searchH =>
    ay_pqeg_conj_intro guardEvidence
      (ay_pqeg_conj agreementEvidence searchControlOnly) guardH
      (ay_pqeg_conj_intro agreementEvidence searchControlOnly agreementH searchH)

theorem ay_pqeg_accepted_guard
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqeg_accepted_extract guardEvidence agreementEvidence searchControlOnly ->
    guardEvidence :=
  fun accepted =>
    ay_pqeg_conj_left guardEvidence
      (ay_pqeg_conj agreementEvidence searchControlOnly) accepted

theorem ay_pqeg_accepted_agreement
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqeg_accepted_extract guardEvidence agreementEvidence searchControlOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_pqeg_conj_left agreementEvidence searchControlOnly
      (ay_pqeg_conj_right guardEvidence
        (ay_pqeg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_pqeg_accepted_search_control
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_pqeg_accepted_extract guardEvidence agreementEvidence searchControlOnly ->
    searchControlOnly :=
  fun accepted =>
    ay_pqeg_conj_right agreementEvidence searchControlOnly
      (ay_pqeg_conj_right guardEvidence
        (ay_pqeg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_pqeg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pqeg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pqeg_conj_intro acceptedEvidence (ay_pqeg_conj outcome formulaTruth)
      acceptedH (ay_pqeg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pqeg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqeg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pqeg_conj_left acceptedEvidence (ay_pqeg_conj outcome formulaTruth)
      report

theorem ay_pqeg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqeg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pqeg_conj_left outcome formulaTruth
      (ay_pqeg_conj_right acceptedEvidence
        (ay_pqeg_conj outcome formulaTruth) report)

theorem ay_pqeg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqeg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pqeg_conj_right outcome formulaTruth
      (ay_pqeg_conj_right acceptedEvidence
        (ay_pqeg_conj outcome formulaTruth) report)

theorem ay_pqeg_preserves_formula_truth
    (originalFormulaTruth extractedRunTruth : Prop) :
    ay_pqeg_equisat originalFormulaTruth extractedRunTruth ->
    originalFormulaTruth ->
    extractedRunTruth :=
  fun eqsat truth =>
    ay_pqeg_equisat_forward originalFormulaTruth extractedRunTruth eqsat truth

theorem ay_pqeg_reflects_formula_truth
    (originalFormulaTruth extractedRunTruth : Prop) :
    ay_pqeg_equisat originalFormulaTruth extractedRunTruth ->
    extractedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_pqeg_equisat_backward originalFormulaTruth extractedRunTruth eqsat truth

theorem ay_pqeg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlOnly publicSoundness : Prop) :
    ay_pqeg_accepted_extract guardEvidence agreementEvidence searchControlOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_pqeg_accepted_agreement guardEvidence agreementEvidence
        searchControlOnly accepted)

theorem ay_pqeg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim diagnostic fallbackOrRecompute :=
  ay_pqeg_conj_intro diagnostic fallbackOrRecompute

theorem ay_pqeg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_pqeg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_pqeg_conj_right diagnostic fallbackOrRecompute

theorem ay_pqeg_queue_mismatch_no_claim
    (queueMismatch fallbackOrRecompute : Prop) :
    queueMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim queueMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro queueMismatch fallbackOrRecompute

theorem ay_pqeg_order_mismatch_no_claim
    (orderMismatch fallbackOrRecompute : Prop) :
    orderMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim orderMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro orderMismatch fallbackOrRecompute

theorem ay_pqeg_tie_mismatch_no_claim
    (tieMismatch fallbackOrRecompute : Prop) :
    tieMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim tieMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro tieMismatch fallbackOrRecompute

theorem ay_pqeg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_pqeg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim replayMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_pqeg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim domainMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_pqeg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim trailMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_pqeg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim buildMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_pqeg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_pqeg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_pqeg_no_claim auditMismatch fallbackOrRecompute :=
  ay_pqeg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_pqeg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_pqeg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_pqeg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_pqeg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_pqeg_public_report
      (ay_pqeg_accepted_extract guardEvidence agreementEvidence
        searchControlOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pqeg_accepted_guard guardEvidence agreementEvidence searchControlOnly
      (ay_pqeg_public_report_accepted
        (ay_pqeg_accepted_extract guardEvidence agreementEvidence
          searchControlOnly)
        outcome formulaTruth report)

theorem ay_pqeg_publication_requires_validator
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_pqeg_public_report
      (ay_pqeg_accepted_extract
        (ay_pqeg_guard variableDomainDigest assignmentTrailDigest
          priorityQueueDigest extractOrderWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pqeg_guard_validator variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_pqeg_publication_requires_guard
        (ay_pqeg_guard variableDomainDigest assignmentTrailDigest
          priorityQueueDigest extractOrderWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_pqeg_publication_requires_audit
    (variableDomainDigest assignmentTrailDigest priorityQueueDigest
      extractOrderWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_pqeg_public_report
      (ay_pqeg_accepted_extract
        (ay_pqeg_guard variableDomainDigest assignmentTrailDigest
          priorityQueueDigest extractOrderWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pqeg_guard_audit variableDomainDigest assignmentTrailDigest
      priorityQueueDigest extractOrderWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_pqeg_publication_requires_guard
        (ay_pqeg_guard variableDomainDigest assignmentTrailDigest
          priorityQueueDigest extractOrderWitness tiebreakManifest
          candidateLegalityWitness propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_pqeg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pqeg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pqeg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pqeg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pqeg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pqeg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
