-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Activity decay/update guard for ay branching heuristics.
-- VSIDS-like bumps and decay are heuristic search-state maintenance only; they
-- must be reproducible and must not be treated as SAT/UNSAT correctness
-- evidence.

def ay_adg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_adg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_adg_conj (before -> after) (after -> before)

def ay_adg_guard
    (variableDomainDigest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (bumpLedger : Prop)
    (decayScheduleManifest : Prop)
    (conflictClauseDigest : Prop)
    (priorityQueueAgreement : Prop)
    (tiebreakManifest : Prop)
    (propagationReplayTranscript : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorBeforeDigest ->
      activityVectorAfterDigest ->
      bumpLedger ->
      decayScheduleManifest ->
      conflictClauseDigest ->
      priorityQueueAgreement ->
      tiebreakManifest ->
      propagationReplayTranscript ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_adg_agreement
    (originalFormulaTruth activityGuidedTruth publicSoundness : Prop) : Prop :=
  ay_adg_conj
    (ay_adg_equisat originalFormulaTruth activityGuidedTruth)
    publicSoundness

def ay_adg_accepted_activity
    (guardEvidence agreementEvidence maintenanceOnly : Prop) : Prop :=
  ay_adg_conj guardEvidence
    (ay_adg_conj agreementEvidence maintenanceOnly)

def ay_adg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_adg_conj acceptedEvidence
    (ay_adg_conj outcome formulaTruth)

def ay_adg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_adg_conj diagnostic fallbackOrRecompute

theorem ay_adg_conj_intro (left right : Prop) :
    left -> right -> ay_adg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_adg_conj_left (left right : Prop) :
    ay_adg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_adg_conj_right (left right : Prop) :
    ay_adg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_adg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_adg_equisat before after :=
  fun forward backward =>
    ay_adg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_adg_equisat_forward (before after : Prop) :
    ay_adg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_adg_conj_left (before -> after) (after -> before) eqsat

theorem ay_adg_equisat_backward (before after : Prop) :
    ay_adg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_adg_conj_right (before -> after) (after -> before) eqsat

theorem ay_adg_guard_intro
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    activityVectorBeforeDigest ->
    activityVectorAfterDigest ->
    bumpLedger ->
    decayScheduleManifest ->
    conflictClauseDigest ->
    priorityQueueAgreement ->
    tiebreakManifest ->
    propagationReplayTranscript ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH beforeH afterH bumpH decayH conflictH queueH tieH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH beforeH afterH bumpH decayH conflictH queueH tieH replayH
      fallbackH buildH validatorH auditH

theorem ay_adg_guard_domain
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_adg_guard_activity_before
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityVectorBeforeDigest :=
  fun guard =>
    guard activityVectorBeforeDigest
      (fun _domainH beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => beforeH)

theorem ay_adg_guard_activity_after
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityVectorAfterDigest :=
  fun guard =>
    guard activityVectorAfterDigest
      (fun _domainH _beforeH afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => afterH)

theorem ay_adg_guard_bump
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    bumpLedger :=
  fun guard =>
    guard bumpLedger
      (fun _domainH _beforeH _afterH bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => bumpH)

theorem ay_adg_guard_decay
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decayScheduleManifest :=
  fun guard =>
    guard decayScheduleManifest
      (fun _domainH _beforeH _afterH _bumpH decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => decayH)

theorem ay_adg_guard_conflict
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    conflictClauseDigest :=
  fun guard =>
    guard conflictClauseDigest
      (fun _domainH _beforeH _afterH _bumpH _decayH conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => conflictH)

theorem ay_adg_guard_queue
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    priorityQueueAgreement :=
  fun guard =>
    guard priorityQueueAgreement
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH queueH
          _tieH _replayH _fallbackH _buildH _validatorH _auditH => queueH)

theorem ay_adg_guard_tiebreak
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          tieH _replayH _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_adg_guard_replay
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplayTranscript :=
  fun guard =>
    guard propagationReplayTranscript
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_adg_guard_fallback
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_adg_guard_build
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_adg_guard_validator
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_adg_guard_audit
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adg_guard variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _beforeH _afterH _bumpH _decayH _conflictH _queueH
          _tieH _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_adg_agreement_intro
    (originalFormulaTruth activityGuidedTruth publicSoundness : Prop) :
    ay_adg_equisat originalFormulaTruth activityGuidedTruth ->
    publicSoundness ->
    ay_adg_agreement originalFormulaTruth activityGuidedTruth publicSoundness :=
  fun eqsat sound =>
    ay_adg_conj_intro
      (ay_adg_equisat originalFormulaTruth activityGuidedTruth)
      publicSoundness eqsat sound

theorem ay_adg_accepted_activity_intro
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    maintenanceOnly ->
    ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly :=
  fun guardH agreementH maintenanceH =>
    ay_adg_conj_intro guardEvidence
      (ay_adg_conj agreementEvidence maintenanceOnly) guardH
      (ay_adg_conj_intro agreementEvidence maintenanceOnly agreementH
        maintenanceH)

theorem ay_adg_accepted_guard
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly ->
    guardEvidence :=
  fun accepted =>
    ay_adg_conj_left guardEvidence
      (ay_adg_conj agreementEvidence maintenanceOnly) accepted

theorem ay_adg_accepted_agreement
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_adg_conj_left agreementEvidence maintenanceOnly
      (ay_adg_conj_right guardEvidence
        (ay_adg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_adg_accepted_maintenance_only
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly ->
    maintenanceOnly :=
  fun accepted =>
    ay_adg_conj_right agreementEvidence maintenanceOnly
      (ay_adg_conj_right guardEvidence
        (ay_adg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_adg_activity_cannot_justify_publication
    (activityEvidence fallbackOrRecompute : Prop) :
    activityEvidence ->
    fallbackOrRecompute ->
    ay_adg_no_claim activityEvidence fallbackOrRecompute :=
  ay_adg_conj_intro activityEvidence fallbackOrRecompute

theorem ay_adg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_adg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_adg_conj_intro acceptedEvidence (ay_adg_conj outcome formulaTruth)
      acceptedH (ay_adg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_adg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_adg_conj_left acceptedEvidence (ay_adg_conj outcome formulaTruth)
      report

theorem ay_adg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_adg_conj_left outcome formulaTruth
      (ay_adg_conj_right acceptedEvidence
        (ay_adg_conj outcome formulaTruth) report)

theorem ay_adg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_adg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_adg_conj_right outcome formulaTruth
      (ay_adg_conj_right acceptedEvidence
        (ay_adg_conj outcome formulaTruth) report)

theorem ay_adg_preserves_formula_truth
    (originalFormulaTruth activityGuidedTruth : Prop) :
    ay_adg_equisat originalFormulaTruth activityGuidedTruth ->
    originalFormulaTruth ->
    activityGuidedTruth :=
  fun eqsat truth =>
    ay_adg_equisat_forward originalFormulaTruth activityGuidedTruth eqsat truth

theorem ay_adg_reflects_formula_truth
    (originalFormulaTruth activityGuidedTruth : Prop) :
    ay_adg_equisat originalFormulaTruth activityGuidedTruth ->
    activityGuidedTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_adg_equisat_backward originalFormulaTruth activityGuidedTruth eqsat truth

theorem ay_adg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence maintenanceOnly publicSoundness : Prop) :
    ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_adg_accepted_agreement guardEvidence agreementEvidence
        maintenanceOnly accepted)

theorem ay_adg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_adg_no_claim diagnostic fallbackOrRecompute :=
  ay_adg_conj_intro diagnostic fallbackOrRecompute

theorem ay_adg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_adg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_adg_conj_right diagnostic fallbackOrRecompute

theorem ay_adg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim domainMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_adg_activity_mismatch_no_claim
    (activityMismatch fallbackOrRecompute : Prop) :
    activityMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim activityMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro activityMismatch fallbackOrRecompute

theorem ay_adg_bump_mismatch_no_claim
    (bumpMismatch fallbackOrRecompute : Prop) :
    bumpMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim bumpMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro bumpMismatch fallbackOrRecompute

theorem ay_adg_decay_mismatch_no_claim
    (decayMismatch fallbackOrRecompute : Prop) :
    decayMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim decayMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro decayMismatch fallbackOrRecompute

theorem ay_adg_conflict_mismatch_no_claim
    (conflictMismatch fallbackOrRecompute : Prop) :
    conflictMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim conflictMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro conflictMismatch fallbackOrRecompute

theorem ay_adg_queue_mismatch_no_claim
    (queueMismatch fallbackOrRecompute : Prop) :
    queueMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim queueMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro queueMismatch fallbackOrRecompute

theorem ay_adg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackOrRecompute : Prop) :
    tiebreakMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim tiebreakMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro tiebreakMismatch fallbackOrRecompute

theorem ay_adg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim replayMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_adg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim buildMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_adg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_adg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_adg_no_claim auditMismatch fallbackOrRecompute :=
  ay_adg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_adg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_adg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_adg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_adg_publication_requires_guard
    (guardEvidence agreementEvidence maintenanceOnly outcome formulaTruth :
      Prop) :
    ay_adg_public_report
      (ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_adg_accepted_guard guardEvidence agreementEvidence maintenanceOnly
      (ay_adg_public_report_accepted
        (ay_adg_accepted_activity guardEvidence agreementEvidence maintenanceOnly)
        outcome formulaTruth report)

theorem ay_adg_publication_requires_validator
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence maintenanceOnly outcome formulaTruth : Prop) :
    ay_adg_public_report
      (ay_adg_accepted_activity
        (ay_adg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest bumpLedger decayScheduleManifest
          conflictClauseDigest priorityQueueAgreement tiebreakManifest
          propagationReplayTranscript fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_adg_guard_validator variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_adg_publication_requires_guard
        (ay_adg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest bumpLedger decayScheduleManifest
          conflictClauseDigest priorityQueueAgreement tiebreakManifest
          propagationReplayTranscript fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_adg_publication_requires_audit
    (variableDomainDigest activityVectorBeforeDigest activityVectorAfterDigest
      bumpLedger decayScheduleManifest conflictClauseDigest
      priorityQueueAgreement tiebreakManifest propagationReplayTranscript
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence maintenanceOnly outcome formulaTruth : Prop) :
    ay_adg_public_report
      (ay_adg_accepted_activity
        (ay_adg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest bumpLedger decayScheduleManifest
          conflictClauseDigest priorityQueueAgreement tiebreakManifest
          propagationReplayTranscript fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_adg_guard_audit variableDomainDigest activityVectorBeforeDigest
      activityVectorAfterDigest bumpLedger decayScheduleManifest
      conflictClauseDigest priorityQueueAgreement tiebreakManifest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_adg_publication_requires_guard
        (ay_adg_guard variableDomainDigest activityVectorBeforeDigest
          activityVectorAfterDigest bumpLedger decayScheduleManifest
          conflictClauseDigest priorityQueueAgreement tiebreakManifest
          propagationReplayTranscript fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_adg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_adg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_adg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_adg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_adg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_adg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
