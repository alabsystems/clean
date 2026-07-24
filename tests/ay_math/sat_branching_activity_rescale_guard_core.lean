-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Activity-rescale guard for ay branching heuristics.
-- Rescaling is heuristic numeric maintenance only; it must preserve intended
-- ordering evidence and must not be treated as SAT/UNSAT correctness evidence.

def ay_arg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_arg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_arg_conj (before -> after) (after -> before)

def ay_arg_guard
    (variableDomainDigest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (rescaleFactorManifest : Prop)
    (orderingPreservationWitness : Prop)
    (priorityQueueRebuildDigest : Prop)
    (tiebreakManifest : Prop)
    (conflictBumpLedgerContext : Prop)
    (propagationReplayTranscript : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorBeforeDigest ->
      activityVectorAfterDigest ->
      rescaleFactorManifest ->
      orderingPreservationWitness ->
      priorityQueueRebuildDigest ->
      tiebreakManifest ->
      conflictBumpLedgerContext ->
      propagationReplayTranscript ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_arg_agreement
    (originalFormulaTruth rescaledRunTruth publicSoundness : Prop) : Prop :=
  ay_arg_conj
    (ay_arg_equisat originalFormulaTruth rescaledRunTruth)
    publicSoundness

def ay_arg_accepted_rescale
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) : Prop :=
  ay_arg_conj guardEvidence
    (ay_arg_conj agreementEvidence numericMaintenanceOnly)

def ay_arg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_arg_conj acceptedEvidence
    (ay_arg_conj outcome formulaTruth)

def ay_arg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_arg_conj diagnostic fallbackOrRecompute

theorem ay_arg_conj_intro (left right : Prop) :
    left -> right -> ay_arg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_arg_conj_left (left right : Prop) :
    ay_arg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_arg_conj_right (left right : Prop) :
    ay_arg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_arg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_arg_equisat before after :=
  fun forward backward =>
    ay_arg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_arg_equisat_forward (before after : Prop) :
    ay_arg_equisat before after -> before -> after :=
  fun eqsat => ay_arg_conj_left (before -> after) (after -> before) eqsat

theorem ay_arg_equisat_backward (before after : Prop) :
    ay_arg_equisat before after -> after -> before :=
  fun eqsat => ay_arg_conj_right (before -> after) (after -> before) eqsat

theorem ay_arg_guard_intro
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityVectorBeforeDigest ->
    activityVectorAfterDigest ->
    rescaleFactorManifest ->
    orderingPreservationWitness ->
    priorityQueueRebuildDigest ->
    tiebreakManifest ->
    conflictBumpLedgerContext ->
    propagationReplayTranscript ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH beforeH afterH rescaleH orderH queueH tieH conflictH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH beforeH afterH rescaleH orderH queueH tieH conflictH replayH
      fallbackH buildH validatorH auditH

theorem ay_arg_guard_domain
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        domainH)

theorem ay_arg_guard_activity_before
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityVectorBeforeDigest :=
  fun guard =>
    guard activityVectorBeforeDigest
      (fun _domainH beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        beforeH)

theorem ay_arg_guard_activity_after
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityVectorAfterDigest :=
  fun guard =>
    guard activityVectorAfterDigest
      (fun _domainH _beforeH afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        afterH)

theorem ay_arg_guard_rescale
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    rescaleFactorManifest :=
  fun guard =>
    guard rescaleFactorManifest
      (fun _domainH _beforeH _afterH rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        rescaleH)

theorem ay_arg_guard_ordering
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    orderingPreservationWitness :=
  fun guard =>
    guard orderingPreservationWitness
      (fun _domainH _beforeH _afterH _rescaleH orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        orderH)

theorem ay_arg_guard_queue
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    priorityQueueRebuildDigest :=
  fun guard =>
    guard priorityQueueRebuildDigest
      (fun _domainH _beforeH _afterH _rescaleH _orderH queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        queueH)

theorem ay_arg_guard_tiebreak
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH tieH
          _conflictH _replayH _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_arg_guard_conflict
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    conflictBumpLedgerContext :=
  fun guard =>
    guard conflictBumpLedgerContext
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          conflictH _replayH _fallbackH _buildH _validatorH _auditH =>
        conflictH)

theorem ay_arg_guard_replay
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplayTranscript :=
  fun guard =>
    guard propagationReplayTranscript
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH replayH _fallbackH _buildH _validatorH _auditH =>
        replayH)

theorem ay_arg_guard_fallback
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH fallbackH _buildH _validatorH _auditH =>
        fallbackH)

theorem ay_arg_guard_build
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_arg_guard_validator
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH validatorH _auditH =>
        validatorH)

theorem ay_arg_guard_audit
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_arg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _beforeH _afterH _rescaleH _orderH _queueH _tieH
          _conflictH _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_arg_agreement_intro
    (originalFormulaTruth rescaledRunTruth publicSoundness : Prop) :
    ay_arg_equisat originalFormulaTruth rescaledRunTruth ->
    publicSoundness ->
    ay_arg_agreement originalFormulaTruth rescaledRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_arg_conj_intro
      (ay_arg_equisat originalFormulaTruth rescaledRunTruth)
      publicSoundness eqsat sound

theorem ay_arg_accepted_rescale_intro
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    numericMaintenanceOnly ->
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly :=
  fun guardH agreementH maintenanceH =>
    ay_arg_conj_intro guardEvidence
      (ay_arg_conj agreementEvidence numericMaintenanceOnly) guardH
      (ay_arg_conj_intro agreementEvidence numericMaintenanceOnly agreementH
        maintenanceH)

theorem ay_arg_accepted_guard
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) :
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly ->
    guardEvidence :=
  fun accepted =>
    ay_arg_conj_left guardEvidence
      (ay_arg_conj agreementEvidence numericMaintenanceOnly) accepted

theorem ay_arg_accepted_agreement
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) :
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_arg_conj_left agreementEvidence numericMaintenanceOnly
      (ay_arg_conj_right guardEvidence
        (ay_arg_conj agreementEvidence numericMaintenanceOnly) accepted)

theorem ay_arg_accepted_numeric_maintenance_only
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) :
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly ->
    numericMaintenanceOnly :=
  fun accepted =>
    ay_arg_conj_right agreementEvidence numericMaintenanceOnly
      (ay_arg_conj_right guardEvidence
        (ay_arg_conj agreementEvidence numericMaintenanceOnly) accepted)

theorem ay_arg_rescale_cannot_justify_publication
    (rescaleEvidence fallbackOrRecompute : Prop) :
    rescaleEvidence ->
    fallbackOrRecompute ->
    ay_arg_no_claim rescaleEvidence fallbackOrRecompute :=
  ay_arg_conj_intro rescaleEvidence fallbackOrRecompute

theorem ay_arg_preserves_branch_order_context
    (guardEvidence agreementEvidence numericMaintenanceOnly : Prop) :
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly ->
    numericMaintenanceOnly :=
  ay_arg_accepted_numeric_maintenance_only guardEvidence agreementEvidence
    numericMaintenanceOnly

theorem ay_arg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_arg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_arg_conj_intro acceptedEvidence (ay_arg_conj outcome formulaTruth)
      acceptedH (ay_arg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_arg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_arg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_arg_conj_left acceptedEvidence (ay_arg_conj outcome formulaTruth)
      report

theorem ay_arg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_arg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_arg_conj_left outcome formulaTruth
      (ay_arg_conj_right acceptedEvidence
        (ay_arg_conj outcome formulaTruth) report)

theorem ay_arg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_arg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_arg_conj_right outcome formulaTruth
      (ay_arg_conj_right acceptedEvidence
        (ay_arg_conj outcome formulaTruth) report)

theorem ay_arg_preserves_formula_truth
    (originalFormulaTruth rescaledRunTruth : Prop) :
    ay_arg_equisat originalFormulaTruth rescaledRunTruth ->
    originalFormulaTruth ->
    rescaledRunTruth :=
  fun eqsat truth =>
    ay_arg_equisat_forward originalFormulaTruth rescaledRunTruth eqsat truth

theorem ay_arg_reflects_formula_truth
    (originalFormulaTruth rescaledRunTruth : Prop) :
    ay_arg_equisat originalFormulaTruth rescaledRunTruth ->
    rescaledRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_arg_equisat_backward originalFormulaTruth rescaledRunTruth eqsat truth

theorem ay_arg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence numericMaintenanceOnly publicSoundness :
      Prop) :
    ay_arg_accepted_rescale guardEvidence agreementEvidence
      numericMaintenanceOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_arg_accepted_agreement guardEvidence agreementEvidence
        numericMaintenanceOnly accepted)

theorem ay_arg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_arg_no_claim diagnostic fallbackOrRecompute :=
  ay_arg_conj_intro diagnostic fallbackOrRecompute

theorem ay_arg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_arg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_arg_conj_right diagnostic fallbackOrRecompute

theorem ay_arg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim domainMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_arg_activity_mismatch_no_claim
    (activityMismatch fallbackOrRecompute : Prop) :
    activityMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim activityMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro activityMismatch fallbackOrRecompute

theorem ay_arg_rescale_mismatch_no_claim
    (rescaleMismatch fallbackOrRecompute : Prop) :
    rescaleMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim rescaleMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro rescaleMismatch fallbackOrRecompute

theorem ay_arg_order_mismatch_no_claim
    (orderMismatch fallbackOrRecompute : Prop) :
    orderMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim orderMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro orderMismatch fallbackOrRecompute

theorem ay_arg_queue_mismatch_no_claim
    (queueMismatch fallbackOrRecompute : Prop) :
    queueMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim queueMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro queueMismatch fallbackOrRecompute

theorem ay_arg_tiebreak_mismatch_no_claim
    (tieMismatch fallbackOrRecompute : Prop) :
    tieMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim tieMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro tieMismatch fallbackOrRecompute

theorem ay_arg_conflict_mismatch_no_claim
    (conflictMismatch fallbackOrRecompute : Prop) :
    conflictMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim conflictMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro conflictMismatch fallbackOrRecompute

theorem ay_arg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim replayMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_arg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim buildMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_arg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_arg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_arg_no_claim auditMismatch fallbackOrRecompute :=
  ay_arg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_arg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_arg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_arg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_arg_publication_requires_guard
    (guardEvidence agreementEvidence numericMaintenanceOnly outcome
      formulaTruth : Prop) :
    ay_arg_public_report
      (ay_arg_accepted_rescale guardEvidence agreementEvidence
        numericMaintenanceOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_arg_accepted_guard guardEvidence agreementEvidence numericMaintenanceOnly
      (ay_arg_public_report_accepted
        (ay_arg_accepted_rescale guardEvidence agreementEvidence
          numericMaintenanceOnly)
        outcome formulaTruth report)

theorem ay_arg_publication_requires_validator
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence numericMaintenanceOnly
      outcome formulaTruth : Prop) :
    ay_arg_public_report
      (ay_arg_accepted_rescale
        (ay_arg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest rescaleFactorManifest
          orderingPreservationWitness priorityQueueRebuildDigest
          tiebreakManifest conflictBumpLedgerContext propagationReplayTranscript
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence numericMaintenanceOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_arg_guard_validator variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_arg_publication_requires_guard
        (ay_arg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest rescaleFactorManifest
          orderingPreservationWitness priorityQueueRebuildDigest
          tiebreakManifest conflictBumpLedgerContext propagationReplayTranscript
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence numericMaintenanceOnly outcome formulaTruth report)

theorem ay_arg_publication_requires_audit
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence numericMaintenanceOnly
      outcome formulaTruth : Prop) :
    ay_arg_public_report
      (ay_arg_accepted_rescale
        (ay_arg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest rescaleFactorManifest
          orderingPreservationWitness priorityQueueRebuildDigest
          tiebreakManifest conflictBumpLedgerContext propagationReplayTranscript
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence numericMaintenanceOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_arg_guard_audit variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest rescaleFactorManifest orderingPreservationWitness
      priorityQueueRebuildDigest tiebreakManifest conflictBumpLedgerContext
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_arg_publication_requires_guard
        (ay_arg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest rescaleFactorManifest
          orderingPreservationWitness priorityQueueRebuildDigest
          tiebreakManifest conflictBumpLedgerContext propagationReplayTranscript
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence numericMaintenanceOnly outcome formulaTruth report)

theorem ay_arg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_arg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_arg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_arg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_arg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_arg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
