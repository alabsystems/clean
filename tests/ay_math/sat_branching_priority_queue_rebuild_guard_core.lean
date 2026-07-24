-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching priority-queue rebuild guard for sequential main-track CDCL.
-- Queue rebuild is heuristic data-structure maintenance only when activity,
-- queue before/after, rebuild, ordering, candidate, replay, fallback, build,
-- validator, and audit evidence agree.

def ay_pqrg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pqrg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pqrg_conj (before -> after) (after -> before)

def ay_pqrg_guard
    (variableDomainDigest : Prop)
    (activityVectorDigest : Prop)
    (queueDigestBeforeRebuild : Prop)
    (rebuiltQueueDigest : Prop)
    (rebuildWitness : Prop)
    (orderingInvariantWitness : Prop)
    (candidateLegalityWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorDigest ->
      queueDigestBeforeRebuild ->
      rebuiltQueueDigest ->
      rebuildWitness ->
      orderingInvariantWitness ->
      candidateLegalityWitness ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pqrg_agreement
    (originalFormulaTruth rebuiltRunTruth publicSoundness : Prop) : Prop :=
  ay_pqrg_conj
    (ay_pqrg_equisat originalFormulaTruth rebuiltRunTruth)
    publicSoundness

def ay_pqrg_accepted_rebuild
    (guardEvidence agreementEvidence maintenanceOnly : Prop) : Prop :=
  ay_pqrg_conj guardEvidence
    (ay_pqrg_conj agreementEvidence maintenanceOnly)

def ay_pqrg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pqrg_conj acceptedEvidence
    (ay_pqrg_conj outcome formulaTruth)

def ay_pqrg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_pqrg_conj diagnostic fallbackOrRecompute

theorem ay_pqrg_conj_intro (left right : Prop) :
    left -> right -> ay_pqrg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pqrg_conj_left (left right : Prop) :
    ay_pqrg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pqrg_conj_right (left right : Prop) :
    ay_pqrg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pqrg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pqrg_equisat before after :=
  fun forward backward =>
    ay_pqrg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pqrg_equisat_forward (before after : Prop) :
    ay_pqrg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pqrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pqrg_equisat_backward (before after : Prop) :
    ay_pqrg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pqrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pqrg_guard_intro
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityVectorDigest ->
    queueDigestBeforeRebuild ->
    rebuiltQueueDigest ->
    rebuildWitness ->
    orderingInvariantWitness ->
    candidateLegalityWitness ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH activityH beforeH rebuiltH rebuildH orderH candidateH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH activityH beforeH rebuiltH rebuildH orderH candidateH replayH
      fallbackH buildH validatorH auditH

theorem ay_pqrg_guard_domain
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        domainH)

theorem ay_pqrg_guard_activity
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    activityVectorDigest :=
  fun guard =>
    guard activityVectorDigest
      (fun _domainH activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        activityH)

theorem ay_pqrg_guard_queue_before
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    queueDigestBeforeRebuild :=
  fun guard =>
    guard queueDigestBeforeRebuild
      (fun _domainH _activityH beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        beforeH)

theorem ay_pqrg_guard_rebuilt_queue
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    rebuiltQueueDigest :=
  fun guard =>
    guard rebuiltQueueDigest
      (fun _domainH _activityH _beforeH rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        rebuiltH)

theorem ay_pqrg_guard_rebuild
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    rebuildWitness :=
  fun guard =>
    guard rebuildWitness
      (fun _domainH _activityH _beforeH _rebuiltH rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        rebuildH)

theorem ay_pqrg_guard_ordering
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    orderingInvariantWitness :=
  fun guard =>
    guard orderingInvariantWitness
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH orderH
          _candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        orderH)

theorem ay_pqrg_guard_candidate
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    candidateLegalityWitness :=
  fun guard =>
    guard candidateLegalityWitness
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          candidateH _replayH _fallbackH _buildH _validatorH _auditH =>
        candidateH)

theorem ay_pqrg_guard_replay
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH replayH _fallbackH _buildH _validatorH _auditH =>
        replayH)

theorem ay_pqrg_guard_fallback
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH fallbackH _buildH _validatorH _auditH =>
        fallbackH)

theorem ay_pqrg_guard_build
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH buildH _validatorH _auditH =>
        buildH)

theorem ay_pqrg_guard_validator
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH validatorH _auditH =>
        validatorH)

theorem ay_pqrg_guard_audit
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqrg_guard variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _beforeH _rebuiltH _rebuildH _orderH
          _candidateH _replayH _fallbackH _buildH _validatorH auditH =>
        auditH)

theorem ay_pqrg_agreement_intro
    (originalFormulaTruth rebuiltRunTruth publicSoundness : Prop) :
    ay_pqrg_equisat originalFormulaTruth rebuiltRunTruth ->
    publicSoundness ->
    ay_pqrg_agreement originalFormulaTruth rebuiltRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_pqrg_conj_intro
      (ay_pqrg_equisat originalFormulaTruth rebuiltRunTruth)
      publicSoundness eqsat sound

theorem ay_pqrg_accepted_rebuild_intro
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    maintenanceOnly ->
    ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly :=
  fun guardH agreementH maintenanceH =>
    ay_pqrg_conj_intro guardEvidence
      (ay_pqrg_conj agreementEvidence maintenanceOnly) guardH
      (ay_pqrg_conj_intro agreementEvidence maintenanceOnly agreementH
        maintenanceH)

theorem ay_pqrg_accepted_guard
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly ->
    guardEvidence :=
  fun accepted =>
    ay_pqrg_conj_left guardEvidence
      (ay_pqrg_conj agreementEvidence maintenanceOnly) accepted

theorem ay_pqrg_accepted_agreement
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_pqrg_conj_left agreementEvidence maintenanceOnly
      (ay_pqrg_conj_right guardEvidence
        (ay_pqrg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqrg_accepted_maintenance_only
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly ->
    maintenanceOnly :=
  fun accepted =>
    ay_pqrg_conj_right agreementEvidence maintenanceOnly
      (ay_pqrg_conj_right guardEvidence
        (ay_pqrg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqrg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pqrg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pqrg_conj_intro acceptedEvidence (ay_pqrg_conj outcome formulaTruth)
      acceptedH (ay_pqrg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pqrg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqrg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pqrg_conj_left acceptedEvidence (ay_pqrg_conj outcome formulaTruth)
      report

theorem ay_pqrg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqrg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pqrg_conj_left outcome formulaTruth
      (ay_pqrg_conj_right acceptedEvidence
        (ay_pqrg_conj outcome formulaTruth) report)

theorem ay_pqrg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqrg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pqrg_conj_right outcome formulaTruth
      (ay_pqrg_conj_right acceptedEvidence
        (ay_pqrg_conj outcome formulaTruth) report)

theorem ay_pqrg_preserves_formula_truth
    (originalFormulaTruth rebuiltRunTruth : Prop) :
    ay_pqrg_equisat originalFormulaTruth rebuiltRunTruth ->
    originalFormulaTruth ->
    rebuiltRunTruth :=
  fun eqsat truth =>
    ay_pqrg_equisat_forward originalFormulaTruth rebuiltRunTruth eqsat truth

theorem ay_pqrg_reflects_formula_truth
    (originalFormulaTruth rebuiltRunTruth : Prop) :
    ay_pqrg_equisat originalFormulaTruth rebuiltRunTruth ->
    rebuiltRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_pqrg_equisat_backward originalFormulaTruth rebuiltRunTruth eqsat truth

theorem ay_pqrg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence maintenanceOnly publicSoundness : Prop) :
    ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_pqrg_accepted_agreement guardEvidence agreementEvidence
        maintenanceOnly accepted)

theorem ay_pqrg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim diagnostic fallbackOrRecompute :=
  ay_pqrg_conj_intro diagnostic fallbackOrRecompute

theorem ay_pqrg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_pqrg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_pqrg_conj_right diagnostic fallbackOrRecompute

theorem ay_pqrg_activity_mismatch_no_claim
    (activityMismatch fallbackOrRecompute : Prop) :
    activityMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim activityMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro activityMismatch fallbackOrRecompute

theorem ay_pqrg_queue_before_mismatch_no_claim
    (queueBeforeMismatch fallbackOrRecompute : Prop) :
    queueBeforeMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim queueBeforeMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro queueBeforeMismatch fallbackOrRecompute

theorem ay_pqrg_rebuilt_queue_mismatch_no_claim
    (rebuiltQueueMismatch fallbackOrRecompute : Prop) :
    rebuiltQueueMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim rebuiltQueueMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro rebuiltQueueMismatch fallbackOrRecompute

theorem ay_pqrg_rebuild_mismatch_no_claim
    (rebuildMismatch fallbackOrRecompute : Prop) :
    rebuildMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim rebuildMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro rebuildMismatch fallbackOrRecompute

theorem ay_pqrg_order_mismatch_no_claim
    (orderMismatch fallbackOrRecompute : Prop) :
    orderMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim orderMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro orderMismatch fallbackOrRecompute

theorem ay_pqrg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_pqrg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim replayMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_pqrg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim buildMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_pqrg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_pqrg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_pqrg_no_claim auditMismatch fallbackOrRecompute :=
  ay_pqrg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_pqrg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_pqrg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_pqrg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_pqrg_publication_requires_guard
    (guardEvidence agreementEvidence maintenanceOnly outcome formulaTruth :
      Prop) :
    ay_pqrg_public_report
      (ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pqrg_accepted_guard guardEvidence agreementEvidence maintenanceOnly
      (ay_pqrg_public_report_accepted
        (ay_pqrg_accepted_rebuild guardEvidence agreementEvidence maintenanceOnly)
        outcome formulaTruth report)

theorem ay_pqrg_publication_requires_validator
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqrg_public_report
      (ay_pqrg_accepted_rebuild
        (ay_pqrg_guard variableDomainDigest activityVectorDigest
          queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
          orderingInvariantWitness candidateLegalityWitness propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pqrg_guard_validator variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqrg_publication_requires_guard
        (ay_pqrg_guard variableDomainDigest activityVectorDigest
          queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
          orderingInvariantWitness candidateLegalityWitness propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqrg_publication_requires_audit
    (variableDomainDigest activityVectorDigest queueDigestBeforeRebuild
      rebuiltQueueDigest rebuildWitness orderingInvariantWitness
      candidateLegalityWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqrg_public_report
      (ay_pqrg_accepted_rebuild
        (ay_pqrg_guard variableDomainDigest activityVectorDigest
          queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
          orderingInvariantWitness candidateLegalityWitness propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pqrg_guard_audit variableDomainDigest activityVectorDigest
      queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
      orderingInvariantWitness candidateLegalityWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqrg_publication_requires_guard
        (ay_pqrg_guard variableDomainDigest activityVectorDigest
          queueDigestBeforeRebuild rebuiltQueueDigest rebuildWitness
          orderingInvariantWitness candidateLegalityWitness propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqrg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pqrg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pqrg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pqrg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pqrg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pqrg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
