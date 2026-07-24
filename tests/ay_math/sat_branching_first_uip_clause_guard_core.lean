-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- First-UIP learned-clause guard for sequential main-track CDCL conflict analysis.
-- First-UIP construction is search-state transition evidence only; learned
-- clauses must remain tied to exact graph, UIP, resolution, replay, validator,
-- archive, and audit evidence.

def ay_fuipg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_fuipg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_fuipg_conj (before -> after) (after -> before)

def ay_fuipg_guard
    (conflictClauseDigest : Prop)
    (implicationGraphDigest : Prop)
    (decisionLevelMapDigest : Prop)
    (uipWitness : Prop)
    (resolutionChainDigest : Prop)
    (learnedClauseDigest : Prop)
    (assertingLiteralWitness : Prop)
    (backjumpLevelWitness : Prop)
    (trailTruncationLedger : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictClauseDigest ->
      implicationGraphDigest ->
      decisionLevelMapDigest ->
      uipWitness ->
      resolutionChainDigest ->
      learnedClauseDigest ->
      assertingLiteralWitness ->
      backjumpLevelWitness ->
      trailTruncationLedger ->
      propagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      result) ->
    result

def ay_fuipg_agreement
    (originalFormulaTruth firstUipRunTruth publicSoundness : Prop) : Prop :=
  ay_fuipg_conj
    (ay_fuipg_equisat originalFormulaTruth firstUipRunTruth)
    publicSoundness

def ay_fuipg_accepted_first_uip
    (guardEvidence agreementEvidence transitionOnly : Prop) : Prop :=
  ay_fuipg_conj guardEvidence
    (ay_fuipg_conj agreementEvidence transitionOnly)

def ay_fuipg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_fuipg_conj acceptedEvidence
    (ay_fuipg_conj outcome formulaTruth)

def ay_fuipg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_fuipg_conj diagnostic fallbackOrRecompute

theorem ay_fuipg_conj_intro (left right : Prop) :
    left -> right -> ay_fuipg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_fuipg_conj_left (left right : Prop) :
    ay_fuipg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_fuipg_conj_right (left right : Prop) :
    ay_fuipg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_fuipg_equisat_intro (before after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_fuipg_equisat before after :=
  fun forward backward =>
    ay_fuipg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_fuipg_equisat_forward (before after : Prop) :
    ay_fuipg_equisat before after -> before -> after :=
  fun eqsat => ay_fuipg_conj_left (before -> after) (after -> before) eqsat

theorem ay_fuipg_equisat_backward (before after : Prop) :
    ay_fuipg_equisat before after -> after -> before :=
  fun eqsat => ay_fuipg_conj_right (before -> after) (after -> before) eqsat

theorem ay_fuipg_guard_intro
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    conflictClauseDigest ->
    implicationGraphDigest ->
    decisionLevelMapDigest ->
    uipWitness ->
    resolutionChainDigest ->
    learnedClauseDigest ->
    assertingLiteralWitness ->
    backjumpLevelWitness ->
    trailTruncationLedger ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript :=
  fun conflictH graphH levelH uipH resolutionH learnedH assertingH backjumpH
      trailH replayH buildH validatorH archiveH fallbackH auditH result make =>
    make conflictH graphH levelH uipH resolutionH learnedH assertingH
      backjumpH trailH replayH buildH validatorH archiveH fallbackH auditH

theorem ay_fuipg_guard_conflict
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    conflictClauseDigest :=
  fun guard =>
    guard conflictClauseDigest
      (fun conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => conflictH)

theorem ay_fuipg_guard_graph
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    implicationGraphDigest :=
  fun guard =>
    guard implicationGraphDigest
      (fun _conflictH graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => graphH)

theorem ay_fuipg_guard_level
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    decisionLevelMapDigest :=
  fun guard =>
    guard decisionLevelMapDigest
      (fun _conflictH _graphH levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => levelH)

theorem ay_fuipg_guard_uip
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    uipWitness :=
  fun guard =>
    guard uipWitness
      (fun _conflictH _graphH _levelH uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => uipH)

theorem ay_fuipg_guard_resolution
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    resolutionChainDigest :=
  fun guard =>
    guard resolutionChainDigest
      (fun _conflictH _graphH _levelH _uipH resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => resolutionH)

theorem ay_fuipg_guard_learned
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    learnedClauseDigest :=
  fun guard =>
    guard learnedClauseDigest
      (fun _conflictH _graphH _levelH _uipH _resolutionH learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => learnedH)

theorem ay_fuipg_guard_asserting
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    assertingLiteralWitness :=
  fun guard =>
    guard assertingLiteralWitness
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => assertingH)

theorem ay_fuipg_guard_backjump
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    backjumpLevelWitness :=
  fun guard =>
    guard backjumpLevelWitness
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => backjumpH)

theorem ay_fuipg_guard_trail
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    trailTruncationLedger :=
  fun guard =>
    guard trailTruncationLedger
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH trailH _replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => trailH)

theorem ay_fuipg_guard_replay
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    propagationReplayTranscript :=
  fun guard =>
    guard propagationReplayTranscript
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH replayH _buildH _validatorH
          _archiveH _fallbackH _auditH => replayH)

theorem ay_fuipg_guard_build
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH buildH _validatorH
          _archiveH _fallbackH _auditH => buildH)

theorem ay_fuipg_guard_validator
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH validatorH
          _archiveH _fallbackH _auditH => validatorH)

theorem ay_fuipg_guard_archive
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    archiveManifest :=
  fun guard =>
    guard archiveManifest
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          archiveH _fallbackH _auditH => archiveH)

theorem ay_fuipg_guard_fallback
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH fallbackH _auditH => fallbackH)

theorem ay_fuipg_guard_audit
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_fuipg_guard conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _conflictH _graphH _levelH _uipH _resolutionH _learnedH
          _assertingH _backjumpH _trailH _replayH _buildH _validatorH
          _archiveH _fallbackH auditH => auditH)

theorem ay_fuipg_agreement_intro
    (originalFormulaTruth firstUipRunTruth publicSoundness : Prop) :
    ay_fuipg_equisat originalFormulaTruth firstUipRunTruth ->
    publicSoundness ->
    ay_fuipg_agreement originalFormulaTruth firstUipRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_fuipg_conj_intro
      (ay_fuipg_equisat originalFormulaTruth firstUipRunTruth)
      publicSoundness eqsat sound

theorem ay_fuipg_accepted_first_uip_intro
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    transitionOnly ->
    ay_fuipg_accepted_first_uip guardEvidence agreementEvidence transitionOnly :=
  fun guardH agreementH transitionH =>
    ay_fuipg_conj_intro guardEvidence
      (ay_fuipg_conj agreementEvidence transitionOnly) guardH
      (ay_fuipg_conj_intro agreementEvidence transitionOnly agreementH
        transitionH)

theorem ay_fuipg_accepted_guard
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_fuipg_accepted_first_uip guardEvidence agreementEvidence transitionOnly ->
    guardEvidence :=
  fun accepted =>
    ay_fuipg_conj_left guardEvidence
      (ay_fuipg_conj agreementEvidence transitionOnly) accepted

theorem ay_fuipg_accepted_agreement
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_fuipg_accepted_first_uip guardEvidence agreementEvidence transitionOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_fuipg_conj_left agreementEvidence transitionOnly
      (ay_fuipg_conj_right guardEvidence
        (ay_fuipg_conj agreementEvidence transitionOnly) accepted)

theorem ay_fuipg_accepted_transition_only
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_fuipg_accepted_first_uip guardEvidence agreementEvidence transitionOnly ->
    transitionOnly :=
  fun accepted =>
    ay_fuipg_conj_right agreementEvidence transitionOnly
      (ay_fuipg_conj_right guardEvidence
        (ay_fuipg_conj agreementEvidence transitionOnly) accepted)

theorem ay_fuipg_first_uip_cannot_justify_publication
    (firstUipEvidence fallbackOrRecompute : Prop) :
    firstUipEvidence ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim firstUipEvidence fallbackOrRecompute :=
  ay_fuipg_conj_intro firstUipEvidence fallbackOrRecompute

theorem ay_fuipg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_fuipg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_fuipg_conj_intro acceptedEvidence (ay_fuipg_conj outcome formulaTruth)
      acceptedH (ay_fuipg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_fuipg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_fuipg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_fuipg_conj_left acceptedEvidence
      (ay_fuipg_conj outcome formulaTruth) report

theorem ay_fuipg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_fuipg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_fuipg_conj_left outcome formulaTruth
      (ay_fuipg_conj_right acceptedEvidence
        (ay_fuipg_conj outcome formulaTruth) report)

theorem ay_fuipg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_fuipg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_fuipg_conj_right outcome formulaTruth
      (ay_fuipg_conj_right acceptedEvidence
        (ay_fuipg_conj outcome formulaTruth) report)

theorem ay_fuipg_preserves_formula_truth
    (originalFormulaTruth firstUipRunTruth : Prop) :
    ay_fuipg_equisat originalFormulaTruth firstUipRunTruth ->
    originalFormulaTruth ->
    firstUipRunTruth :=
  fun eqsat truth =>
    ay_fuipg_equisat_forward originalFormulaTruth firstUipRunTruth eqsat truth

theorem ay_fuipg_reflects_formula_truth
    (originalFormulaTruth firstUipRunTruth : Prop) :
    ay_fuipg_equisat originalFormulaTruth firstUipRunTruth ->
    firstUipRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_fuipg_equisat_backward originalFormulaTruth firstUipRunTruth eqsat truth

theorem ay_fuipg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence transitionOnly publicSoundness : Prop) :
    ay_fuipg_accepted_first_uip guardEvidence agreementEvidence transitionOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_fuipg_accepted_agreement guardEvidence agreementEvidence
        transitionOnly accepted)

theorem ay_fuipg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim diagnostic fallbackOrRecompute :=
  ay_fuipg_conj_intro diagnostic fallbackOrRecompute

theorem ay_fuipg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_fuipg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_fuipg_conj_right diagnostic fallbackOrRecompute

theorem ay_fuipg_conflict_mismatch_no_claim
    (conflictMismatch fallbackOrRecompute : Prop) :
    conflictMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim conflictMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro conflictMismatch fallbackOrRecompute

theorem ay_fuipg_graph_mismatch_no_claim
    (graphMismatch fallbackOrRecompute : Prop) :
    graphMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim graphMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro graphMismatch fallbackOrRecompute

theorem ay_fuipg_level_mismatch_no_claim
    (levelMismatch fallbackOrRecompute : Prop) :
    levelMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim levelMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro levelMismatch fallbackOrRecompute

theorem ay_fuipg_uip_mismatch_no_claim
    (uipMismatch fallbackOrRecompute : Prop) :
    uipMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim uipMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro uipMismatch fallbackOrRecompute

theorem ay_fuipg_resolution_mismatch_no_claim
    (resolutionMismatch fallbackOrRecompute : Prop) :
    resolutionMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim resolutionMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro resolutionMismatch fallbackOrRecompute

theorem ay_fuipg_learned_mismatch_no_claim
    (learnedMismatch fallbackOrRecompute : Prop) :
    learnedMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim learnedMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro learnedMismatch fallbackOrRecompute

theorem ay_fuipg_asserting_mismatch_no_claim
    (assertingMismatch fallbackOrRecompute : Prop) :
    assertingMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim assertingMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro assertingMismatch fallbackOrRecompute

theorem ay_fuipg_backjump_mismatch_no_claim
    (backjumpMismatch fallbackOrRecompute : Prop) :
    backjumpMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim backjumpMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro backjumpMismatch fallbackOrRecompute

theorem ay_fuipg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim trailMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_fuipg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim replayMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_fuipg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim buildMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_fuipg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_fuipg_archive_mismatch_no_claim
    (archiveMismatch fallbackOrRecompute : Prop) :
    archiveMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim archiveMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro archiveMismatch fallbackOrRecompute

theorem ay_fuipg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_fuipg_no_claim auditMismatch fallbackOrRecompute :=
  ay_fuipg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_fuipg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_fuipg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_fuipg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_fuipg_publication_requires_guard
    (guardEvidence agreementEvidence transitionOnly outcome formulaTruth :
      Prop) :
    ay_fuipg_public_report
      (ay_fuipg_accepted_first_uip guardEvidence agreementEvidence
        transitionOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_fuipg_accepted_guard guardEvidence agreementEvidence transitionOnly
      (ay_fuipg_public_report_accepted
        (ay_fuipg_accepted_first_uip guardEvidence agreementEvidence
          transitionOnly)
        outcome formulaTruth report)

theorem ay_fuipg_publication_requires_validator
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript agreementEvidence
      transitionOnly outcome formulaTruth : Prop) :
    ay_fuipg_public_report
      (ay_fuipg_accepted_first_uip
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_fuipg_guard_validator conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_fuipg_publication_requires_guard
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_fuipg_publication_requires_archive
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript agreementEvidence
      transitionOnly outcome formulaTruth : Prop) :
    ay_fuipg_public_report
      (ay_fuipg_accepted_first_uip
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    archiveManifest :=
  fun report =>
    ay_fuipg_guard_archive conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_fuipg_publication_requires_guard
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_fuipg_publication_requires_audit
    (conflictClauseDigest implicationGraphDigest decisionLevelMapDigest
      uipWitness resolutionChainDigest learnedClauseDigest
      assertingLiteralWitness backjumpLevelWitness trailTruncationLedger
      propagationReplayTranscript solverBuildEvidence validatorGate
      archiveManifest fallbackBaseline auditTranscript agreementEvidence
      transitionOnly outcome formulaTruth : Prop) :
    ay_fuipg_public_report
      (ay_fuipg_accepted_first_uip
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_fuipg_guard_audit conflictClauseDigest implicationGraphDigest
      decisionLevelMapDigest uipWitness resolutionChainDigest
      learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
      trailTruncationLedger propagationReplayTranscript solverBuildEvidence
      validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_fuipg_publication_requires_guard
        (ay_fuipg_guard conflictClauseDigest implicationGraphDigest
          decisionLevelMapDigest uipWitness resolutionChainDigest
          learnedClauseDigest assertingLiteralWitness backjumpLevelWitness
          trailTruncationLedger propagationReplayTranscript solverBuildEvidence
          validatorGate archiveManifest fallbackBaseline auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_fuipg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_fuipg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_fuipg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_fuipg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_fuipg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_fuipg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
