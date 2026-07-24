-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching priority-queue update guard for sequential main-track CDCL.
-- Queue updates are heuristic data-structure maintenance only when activity,
-- queue before/after, ordering, tie-break, candidate, replay, fallback, build,
-- validator, and audit evidence agree.

def ay_pqug_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pqug_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pqug_conj (before -> after) (after -> before)

def ay_pqug_guard
    (variableDomainDigest : Prop)
    (activityUpdateLedger : Prop)
    (priorityQueueDigestBefore : Prop)
    (priorityQueueDigestAfter : Prop)
    (orderingInvariantWitness : Prop)
    (tiebreakManifest : Prop)
    (candidateLegalityWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityUpdateLedger ->
      priorityQueueDigestBefore ->
      priorityQueueDigestAfter ->
      orderingInvariantWitness ->
      tiebreakManifest ->
      candidateLegalityWitness ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pqug_agreement
    (originalFormulaTruth updatedRunTruth publicSoundness : Prop) : Prop :=
  ay_pqug_conj
    (ay_pqug_equisat originalFormulaTruth updatedRunTruth)
    publicSoundness

def ay_pqug_accepted_update
    (guardEvidence agreementEvidence maintenanceOnly : Prop) : Prop :=
  ay_pqug_conj guardEvidence
    (ay_pqug_conj agreementEvidence maintenanceOnly)

def ay_pqug_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pqug_conj acceptedEvidence
    (ay_pqug_conj outcome formulaTruth)

def ay_pqug_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_pqug_conj diagnostic fallbackOrRecompute

theorem ay_pqug_conj_intro (left right : Prop) :
    left -> right -> ay_pqug_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pqug_conj_left (left right : Prop) :
    ay_pqug_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pqug_conj_right (left right : Prop) :
    ay_pqug_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pqug_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pqug_equisat before after :=
  fun forward backward =>
    ay_pqug_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pqug_equisat_forward (before after : Prop) :
    ay_pqug_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pqug_conj_left (before -> after) (after -> before) eqsat

theorem ay_pqug_equisat_backward (before after : Prop) :
    ay_pqug_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pqug_conj_right (before -> after) (after -> before) eqsat

theorem ay_pqug_guard_intro
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityUpdateLedger ->
    priorityQueueDigestBefore ->
    priorityQueueDigestAfter ->
    orderingInvariantWitness ->
    tiebreakManifest ->
    candidateLegalityWitness ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript :=
  fun domainH activityH beforeH afterH orderH tieH candidateH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH activityH beforeH afterH orderH tieH candidateH replayH
      fallbackH buildH validatorH auditH

theorem ay_pqug_guard_domain
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_pqug_guard_activity
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    activityUpdateLedger :=
  fun guard =>
    guard activityUpdateLedger
      (fun _domainH activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => activityH)

theorem ay_pqug_guard_queue_before
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    priorityQueueDigestBefore :=
  fun guard =>
    guard priorityQueueDigestBefore
      (fun _domainH _activityH beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => beforeH)

theorem ay_pqug_guard_queue_after
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    priorityQueueDigestAfter :=
  fun guard =>
    guard priorityQueueDigestAfter
      (fun _domainH _activityH _beforeH afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => afterH)

theorem ay_pqug_guard_ordering
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    orderingInvariantWitness :=
  fun guard =>
    guard orderingInvariantWitness
      (fun _domainH _activityH _beforeH _afterH orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => orderH)

theorem ay_pqug_guard_tiebreak
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _activityH _beforeH _afterH _orderH tieH _candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_pqug_guard_candidate
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    candidateLegalityWitness :=
  fun guard =>
    guard candidateLegalityWitness
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH candidateH
          _replayH _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_pqug_guard_replay
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_pqug_guard_fallback
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_pqug_guard_build
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_pqug_guard_validator
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_pqug_guard_audit
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqug_guard variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter
      orderingInvariantWitness tiebreakManifest candidateLegalityWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _beforeH _afterH _orderH _tieH _candidateH
          _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_pqug_agreement_intro
    (originalFormulaTruth updatedRunTruth publicSoundness : Prop) :
    ay_pqug_equisat originalFormulaTruth updatedRunTruth ->
    publicSoundness ->
    ay_pqug_agreement originalFormulaTruth updatedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_pqug_conj_intro
      (ay_pqug_equisat originalFormulaTruth updatedRunTruth)
      publicSoundness eqsat sound

theorem ay_pqug_accepted_update_intro
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    maintenanceOnly ->
    ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly :=
  fun guardH agreementH maintenanceH =>
    ay_pqug_conj_intro guardEvidence
      (ay_pqug_conj agreementEvidence maintenanceOnly) guardH
      (ay_pqug_conj_intro agreementEvidence maintenanceOnly agreementH
        maintenanceH)

theorem ay_pqug_accepted_guard
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly ->
    guardEvidence :=
  fun accepted =>
    ay_pqug_conj_left guardEvidence
      (ay_pqug_conj agreementEvidence maintenanceOnly) accepted

theorem ay_pqug_accepted_agreement
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_pqug_conj_left agreementEvidence maintenanceOnly
      (ay_pqug_conj_right guardEvidence
        (ay_pqug_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqug_accepted_maintenance_only
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly ->
    maintenanceOnly :=
  fun accepted =>
    ay_pqug_conj_right agreementEvidence maintenanceOnly
      (ay_pqug_conj_right guardEvidence
        (ay_pqug_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqug_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pqug_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pqug_conj_intro acceptedEvidence (ay_pqug_conj outcome formulaTruth)
      acceptedH (ay_pqug_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pqug_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqug_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pqug_conj_left acceptedEvidence (ay_pqug_conj outcome formulaTruth)
      report

theorem ay_pqug_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqug_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pqug_conj_left outcome formulaTruth
      (ay_pqug_conj_right acceptedEvidence
        (ay_pqug_conj outcome formulaTruth) report)

theorem ay_pqug_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqug_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pqug_conj_right outcome formulaTruth
      (ay_pqug_conj_right acceptedEvidence
        (ay_pqug_conj outcome formulaTruth) report)

theorem ay_pqug_preserves_formula_truth
    (originalFormulaTruth updatedRunTruth : Prop) :
    ay_pqug_equisat originalFormulaTruth updatedRunTruth ->
    originalFormulaTruth ->
    updatedRunTruth :=
  fun eqsat truth =>
    ay_pqug_equisat_forward originalFormulaTruth updatedRunTruth eqsat truth

theorem ay_pqug_reflects_formula_truth
    (originalFormulaTruth updatedRunTruth : Prop) :
    ay_pqug_equisat originalFormulaTruth updatedRunTruth ->
    updatedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_pqug_equisat_backward originalFormulaTruth updatedRunTruth eqsat truth

theorem ay_pqug_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence maintenanceOnly publicSoundness : Prop) :
    ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_pqug_accepted_agreement guardEvidence agreementEvidence
        maintenanceOnly accepted)

theorem ay_pqug_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_pqug_no_claim diagnostic fallbackOrRecompute :=
  ay_pqug_conj_intro diagnostic fallbackOrRecompute

theorem ay_pqug_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_pqug_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_pqug_conj_right diagnostic fallbackOrRecompute

theorem ay_pqug_activity_mismatch_no_claim
    (activityMismatch fallbackOrRecompute : Prop) :
    activityMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim activityMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro activityMismatch fallbackOrRecompute

theorem ay_pqug_queue_before_mismatch_no_claim
    (queueBeforeMismatch fallbackOrRecompute : Prop) :
    queueBeforeMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim queueBeforeMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro queueBeforeMismatch fallbackOrRecompute

theorem ay_pqug_queue_after_mismatch_no_claim
    (queueAfterMismatch fallbackOrRecompute : Prop) :
    queueAfterMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim queueAfterMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro queueAfterMismatch fallbackOrRecompute

theorem ay_pqug_order_mismatch_no_claim
    (orderMismatch fallbackOrRecompute : Prop) :
    orderMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim orderMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro orderMismatch fallbackOrRecompute

theorem ay_pqug_tie_mismatch_no_claim
    (tieMismatch fallbackOrRecompute : Prop) :
    tieMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim tieMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro tieMismatch fallbackOrRecompute

theorem ay_pqug_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim candidateMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_pqug_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim replayMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_pqug_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim buildMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_pqug_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim validatorMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_pqug_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_pqug_no_claim auditMismatch fallbackOrRecompute :=
  ay_pqug_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_pqug_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_pqug_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_pqug_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_pqug_publication_requires_guard
    (guardEvidence agreementEvidence maintenanceOnly outcome formulaTruth :
      Prop) :
    ay_pqug_public_report
      (ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pqug_accepted_guard guardEvidence agreementEvidence maintenanceOnly
      (ay_pqug_public_report_accepted
        (ay_pqug_accepted_update guardEvidence agreementEvidence maintenanceOnly)
        outcome formulaTruth report)

theorem ay_pqug_publication_requires_validator
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqug_public_report
      (ay_pqug_accepted_update
        (ay_pqug_guard variableDomainDigest activityUpdateLedger
          priorityQueueDigestBefore priorityQueueDigestAfter
          orderingInvariantWitness tiebreakManifest candidateLegalityWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pqug_guard_validator variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter orderingInvariantWitness
      tiebreakManifest candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqug_publication_requires_guard
        (ay_pqug_guard variableDomainDigest activityUpdateLedger
          priorityQueueDigestBefore priorityQueueDigestAfter
          orderingInvariantWitness tiebreakManifest candidateLegalityWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqug_publication_requires_audit
    (variableDomainDigest activityUpdateLedger priorityQueueDigestBefore
      priorityQueueDigestAfter orderingInvariantWitness tiebreakManifest
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqug_public_report
      (ay_pqug_accepted_update
        (ay_pqug_guard variableDomainDigest activityUpdateLedger
          priorityQueueDigestBefore priorityQueueDigestAfter
          orderingInvariantWitness tiebreakManifest candidateLegalityWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pqug_guard_audit variableDomainDigest activityUpdateLedger
      priorityQueueDigestBefore priorityQueueDigestAfter orderingInvariantWitness
      tiebreakManifest candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqug_publication_requires_guard
        (ay_pqug_guard variableDomainDigest activityUpdateLedger
          priorityQueueDigestBefore priorityQueueDigestAfter
          orderingInvariantWitness tiebreakManifest candidateLegalityWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqug_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pqug_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pqug_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pqug_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pqug_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pqug_public_report_intro acceptedEvidence unsatOutcome formulaTruth
