-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-saving guard for ay branching.
-- Cached polarities are heuristic decision-state only; they must not be
-- mistaken for SAT/UNSAT correctness evidence.

def ay_psg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_psg_conj (before -> after) (after -> before)

def ay_psg_guard
    (variableDomainDigest : Prop)
    (savedPhaseTableDigest : Prop)
    (assignmentTrailDigest : Prop)
    (conflictRestartBoundaryLedger : Prop)
    (phaseUpdateLedger : Prop)
    (decisionOrderDigest : Prop)
    (propagationReplayTranscript : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      savedPhaseTableDigest ->
      assignmentTrailDigest ->
      conflictRestartBoundaryLedger ->
      phaseUpdateLedger ->
      decisionOrderDigest ->
      propagationReplayTranscript ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_psg_agreement
    (originalFormulaTruth phaseGuidedTruth publicSoundness : Prop) : Prop :=
  ay_psg_conj
    (ay_psg_equisat originalFormulaTruth phaseGuidedTruth)
    publicSoundness

def ay_psg_accepted_phase
    (guardEvidence agreementEvidence heuristicOnly : Prop) : Prop :=
  ay_psg_conj guardEvidence
    (ay_psg_conj agreementEvidence heuristicOnly)

def ay_psg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_psg_conj acceptedEvidence
    (ay_psg_conj outcome formulaTruth)

def ay_psg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_psg_conj diagnostic fallbackOrRecompute

theorem ay_psg_conj_intro (left right : Prop) :
    left -> right -> ay_psg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_psg_conj_left (left right : Prop) :
    ay_psg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_psg_conj_right (left right : Prop) :
    ay_psg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_psg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_psg_equisat before after :=
  fun forward backward =>
    ay_psg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_psg_equisat_forward (before after : Prop) :
    ay_psg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_psg_conj_left (before -> after) (after -> before) eqsat

theorem ay_psg_equisat_backward (before after : Prop) :
    ay_psg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_psg_conj_right (before -> after) (after -> before) eqsat

theorem ay_psg_guard_intro
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    savedPhaseTableDigest ->
    assignmentTrailDigest ->
    conflictRestartBoundaryLedger ->
    phaseUpdateLedger ->
    decisionOrderDigest ->
    propagationReplayTranscript ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_psg_guard variableDomainDigest savedPhaseTableDigest
      assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
      decisionOrderDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH phaseH trailH restartH updateH decisionH replayH fallbackH
      buildH validatorH auditH result make =>
    make domainH phaseH trailH restartH updateH decisionH replayH fallbackH
      buildH validatorH auditH

theorem ay_psg_guard_domain
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _phaseH _trailH _restartH _updateH _decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_psg_guard_phase
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    savedPhaseTableDigest :=
  fun guard =>
    guard savedPhaseTableDigest
      (fun _domainH phaseH _trailH _restartH _updateH _decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => phaseH)

theorem ay_psg_guard_trail
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    assignmentTrailDigest :=
  fun guard =>
    guard assignmentTrailDigest
      (fun _domainH _phaseH trailH _restartH _updateH _decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => trailH)

theorem ay_psg_guard_restart_boundary
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    conflictRestartBoundaryLedger :=
  fun guard =>
    guard conflictRestartBoundaryLedger
      (fun _domainH _phaseH _trailH restartH _updateH _decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => restartH)

theorem ay_psg_guard_update
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    phaseUpdateLedger :=
  fun guard =>
    guard phaseUpdateLedger
      (fun _domainH _phaseH _trailH _restartH updateH _decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => updateH)

theorem ay_psg_guard_decision
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderDigest :=
  fun guard =>
    guard decisionOrderDigest
      (fun _domainH _phaseH _trailH _restartH _updateH decisionH _replayH
          _fallbackH _buildH _validatorH _auditH => decisionH)

theorem ay_psg_guard_replay
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplayTranscript :=
  fun guard =>
    guard propagationReplayTranscript
      (fun _domainH _phaseH _trailH _restartH _updateH _decisionH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_psg_guard_fallback
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _phaseH _trailH _restartH _updateH _decisionH _replayH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_psg_guard_build
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _phaseH _trailH _restartH _updateH _decisionH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_psg_guard_validator
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _phaseH _trailH _restartH _updateH _decisionH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_psg_guard_audit
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_psg_guard variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _phaseH _trailH _restartH _updateH _decisionH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_psg_agreement_intro
    (originalFormulaTruth phaseGuidedTruth publicSoundness : Prop) :
    ay_psg_equisat originalFormulaTruth phaseGuidedTruth ->
    publicSoundness ->
    ay_psg_agreement originalFormulaTruth phaseGuidedTruth publicSoundness :=
  fun eqsat sound =>
    ay_psg_conj_intro
      (ay_psg_equisat originalFormulaTruth phaseGuidedTruth)
      publicSoundness eqsat sound

theorem ay_psg_accepted_phase_intro
    (guardEvidence agreementEvidence heuristicOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    heuristicOnly ->
    ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly :=
  fun guardH agreementH heuristicH =>
    ay_psg_conj_intro guardEvidence
      (ay_psg_conj agreementEvidence heuristicOnly) guardH
      (ay_psg_conj_intro agreementEvidence heuristicOnly agreementH heuristicH)

theorem ay_psg_accepted_guard
    (guardEvidence agreementEvidence heuristicOnly : Prop) :
    ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly ->
    guardEvidence :=
  fun accepted =>
    ay_psg_conj_left guardEvidence
      (ay_psg_conj agreementEvidence heuristicOnly) accepted

theorem ay_psg_accepted_agreement
    (guardEvidence agreementEvidence heuristicOnly : Prop) :
    ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_psg_conj_left agreementEvidence heuristicOnly
      (ay_psg_conj_right guardEvidence
        (ay_psg_conj agreementEvidence heuristicOnly) accepted)

theorem ay_psg_accepted_heuristic_only
    (guardEvidence agreementEvidence heuristicOnly : Prop) :
    ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly ->
    heuristicOnly :=
  fun accepted =>
    ay_psg_conj_right agreementEvidence heuristicOnly
      (ay_psg_conj_right guardEvidence
        (ay_psg_conj agreementEvidence heuristicOnly) accepted)

theorem ay_psg_phase_cannot_justify_publication
    (phaseEvidence fallbackOrRecompute : Prop) :
    phaseEvidence ->
    fallbackOrRecompute ->
    ay_psg_no_claim phaseEvidence fallbackOrRecompute :=
  ay_psg_conj_intro phaseEvidence fallbackOrRecompute

theorem ay_psg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_psg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_psg_conj_intro acceptedEvidence (ay_psg_conj outcome formulaTruth)
      acceptedH (ay_psg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_psg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_psg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_psg_conj_left acceptedEvidence (ay_psg_conj outcome formulaTruth)
      report

theorem ay_psg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_psg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_psg_conj_left outcome formulaTruth
      (ay_psg_conj_right acceptedEvidence
        (ay_psg_conj outcome formulaTruth) report)

theorem ay_psg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_psg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_psg_conj_right outcome formulaTruth
      (ay_psg_conj_right acceptedEvidence
        (ay_psg_conj outcome formulaTruth) report)

theorem ay_psg_preserves_formula_truth
    (originalFormulaTruth phaseGuidedTruth : Prop) :
    ay_psg_equisat originalFormulaTruth phaseGuidedTruth ->
    originalFormulaTruth ->
    phaseGuidedTruth :=
  fun eqsat truth =>
    ay_psg_equisat_forward originalFormulaTruth phaseGuidedTruth eqsat truth

theorem ay_psg_reflects_formula_truth
    (originalFormulaTruth phaseGuidedTruth : Prop) :
    ay_psg_equisat originalFormulaTruth phaseGuidedTruth ->
    phaseGuidedTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_psg_equisat_backward originalFormulaTruth phaseGuidedTruth eqsat truth

theorem ay_psg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence heuristicOnly publicSoundness : Prop) :
    ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_psg_accepted_agreement guardEvidence agreementEvidence heuristicOnly
        accepted)

theorem ay_psg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_psg_no_claim diagnostic fallbackOrRecompute :=
  ay_psg_conj_intro diagnostic fallbackOrRecompute

theorem ay_psg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_psg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_psg_conj_right diagnostic fallbackOrRecompute

theorem ay_psg_phase_mismatch_no_claim
    (phaseMismatch fallbackOrRecompute : Prop) :
    phaseMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim phaseMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro phaseMismatch fallbackOrRecompute

theorem ay_psg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim trailMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_psg_restart_mismatch_no_claim
    (restartMismatch fallbackOrRecompute : Prop) :
    restartMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim restartMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro restartMismatch fallbackOrRecompute

theorem ay_psg_update_mismatch_no_claim
    (updateMismatch fallbackOrRecompute : Prop) :
    updateMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim updateMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro updateMismatch fallbackOrRecompute

theorem ay_psg_decision_mismatch_no_claim
    (decisionMismatch fallbackOrRecompute : Prop) :
    decisionMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim decisionMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro decisionMismatch fallbackOrRecompute

theorem ay_psg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim replayMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_psg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim buildMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_psg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_psg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_psg_no_claim auditMismatch fallbackOrRecompute :=
  ay_psg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_psg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_psg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_psg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_psg_publication_requires_guard
    (guardEvidence agreementEvidence heuristicOnly outcome formulaTruth : Prop) :
    ay_psg_public_report
      (ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_psg_accepted_guard guardEvidence agreementEvidence heuristicOnly
      (ay_psg_public_report_accepted
        (ay_psg_accepted_phase guardEvidence agreementEvidence heuristicOnly)
        outcome formulaTruth report)

theorem ay_psg_publication_requires_validator
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence heuristicOnly outcome
      formulaTruth : Prop) :
    ay_psg_public_report
      (ay_psg_accepted_phase
        (ay_psg_guard variableDomainDigest savedPhaseTableDigest
          assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
          decisionOrderDigest propagationReplayTranscript fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence heuristicOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_psg_guard_validator variableDomainDigest savedPhaseTableDigest
      assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
      decisionOrderDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_psg_publication_requires_guard
        (ay_psg_guard variableDomainDigest savedPhaseTableDigest
          assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
          decisionOrderDigest propagationReplayTranscript fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence heuristicOnly outcome formulaTruth report)

theorem ay_psg_publication_requires_audit
    (variableDomainDigest savedPhaseTableDigest assignmentTrailDigest
      conflictRestartBoundaryLedger phaseUpdateLedger decisionOrderDigest
      propagationReplayTranscript fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence heuristicOnly outcome
      formulaTruth : Prop) :
    ay_psg_public_report
      (ay_psg_accepted_phase
        (ay_psg_guard variableDomainDigest savedPhaseTableDigest
          assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
          decisionOrderDigest propagationReplayTranscript fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence heuristicOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_psg_guard_audit variableDomainDigest savedPhaseTableDigest
      assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
      decisionOrderDigest propagationReplayTranscript fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_psg_publication_requires_guard
        (ay_psg_guard variableDomainDigest savedPhaseTableDigest
          assignmentTrailDigest conflictRestartBoundaryLedger phaseUpdateLedger
          decisionOrderDigest propagationReplayTranscript fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence heuristicOnly outcome formulaTruth report)

theorem ay_psg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_psg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_psg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_psg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_psg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_psg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
