-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Backjump-level guard for sequential main-track CDCL conflict analysis.
-- Non-chronological backjumping is search-state transition evidence only; it
-- must remain tied to exact conflict-analysis replay evidence and cannot by
-- itself justify public SAT/UNSAT publication.

def ay_bjg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bjg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bjg_conj (before -> after) (after -> before)

def ay_bjg_guard
    (conflictClauseDigest : Prop)
    (implicationGraphAntecedentDigest : Prop)
    (decisionLevelMapDigest : Prop)
    (assertingClauseWitness : Prop)
    (computedBackjumpLevelWitness : Prop)
    (trailTruncationLedger : Prop)
    (propagationReplayAfterBackjump : Prop)
    (learnedClauseDigest : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (fallbackBaseline : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictClauseDigest ->
      implicationGraphAntecedentDigest ->
      decisionLevelMapDigest ->
      assertingClauseWitness ->
      computedBackjumpLevelWitness ->
      trailTruncationLedger ->
      propagationReplayAfterBackjump ->
      learnedClauseDigest ->
      solverBuildEvidence ->
      validatorGate ->
      fallbackBaseline ->
      archiveManifest ->
      auditTranscript ->
      result) ->
    result

def ay_bjg_agreement
    (originalFormulaTruth backjumpRunTruth publicSoundness : Prop) : Prop :=
  ay_bjg_conj
    (ay_bjg_equisat originalFormulaTruth backjumpRunTruth)
    publicSoundness

def ay_bjg_accepted_backjump
    (guardEvidence agreementEvidence transitionOnly : Prop) : Prop :=
  ay_bjg_conj guardEvidence
    (ay_bjg_conj agreementEvidence transitionOnly)

def ay_bjg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_bjg_conj acceptedEvidence
    (ay_bjg_conj outcome formulaTruth)

def ay_bjg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_bjg_conj diagnostic fallbackOrRecompute

theorem ay_bjg_conj_intro (left right : Prop) :
    left -> right -> ay_bjg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bjg_conj_left (left right : Prop) :
    ay_bjg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bjg_conj_right (left right : Prop) :
    ay_bjg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bjg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_bjg_equisat before after :=
  fun forward backward =>
    ay_bjg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bjg_equisat_forward (before after : Prop) :
    ay_bjg_equisat before after -> before -> after :=
  fun eqsat => ay_bjg_conj_left (before -> after) (after -> before) eqsat

theorem ay_bjg_equisat_backward (before after : Prop) :
    ay_bjg_equisat before after -> after -> before :=
  fun eqsat => ay_bjg_conj_right (before -> after) (after -> before) eqsat

theorem ay_bjg_guard_intro
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    conflictClauseDigest ->
    implicationGraphAntecedentDigest ->
    decisionLevelMapDigest ->
    assertingClauseWitness ->
    computedBackjumpLevelWitness ->
    trailTruncationLedger ->
    propagationReplayAfterBackjump ->
    learnedClauseDigest ->
    solverBuildEvidence ->
    validatorGate ->
    fallbackBaseline ->
    archiveManifest ->
    auditTranscript ->
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript :=
  fun conflictH graphH levelH assertingH backjumpH trailH replayH learnedH
      buildH validatorH fallbackH archiveH auditH result make =>
    make conflictH graphH levelH assertingH backjumpH trailH replayH learnedH
      buildH validatorH fallbackH archiveH auditH

theorem ay_bjg_guard_conflict
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    conflictClauseDigest :=
  fun guard =>
    guard conflictClauseDigest
      (fun conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        conflictH)

theorem ay_bjg_guard_graph
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    implicationGraphAntecedentDigest :=
  fun guard =>
    guard implicationGraphAntecedentDigest
      (fun _conflictH graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        graphH)

theorem ay_bjg_guard_level_map
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    decisionLevelMapDigest :=
  fun guard =>
    guard decisionLevelMapDigest
      (fun _conflictH _graphH levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        levelH)

theorem ay_bjg_guard_asserting
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    assertingClauseWitness :=
  fun guard =>
    guard assertingClauseWitness
      (fun _conflictH _graphH _levelH assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        assertingH)

theorem ay_bjg_guard_backjump
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    computedBackjumpLevelWitness :=
  fun guard =>
    guard computedBackjumpLevelWitness
      (fun _conflictH _graphH _levelH _assertingH backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        backjumpH)

theorem ay_bjg_guard_trail
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    trailTruncationLedger :=
  fun guard =>
    guard trailTruncationLedger
      (fun _conflictH _graphH _levelH _assertingH _backjumpH trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        trailH)

theorem ay_bjg_guard_replay
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    propagationReplayAfterBackjump :=
  fun guard =>
    guard propagationReplayAfterBackjump
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        replayH)

theorem ay_bjg_guard_learned
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    learnedClauseDigest :=
  fun guard =>
    guard learnedClauseDigest
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          learnedH _buildH _validatorH _fallbackH _archiveH _auditH =>
        learnedH)

theorem ay_bjg_guard_build
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH buildH _validatorH _fallbackH _archiveH _auditH =>
        buildH)

theorem ay_bjg_guard_validator
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH validatorH _fallbackH _archiveH _auditH =>
        validatorH)

theorem ay_bjg_guard_fallback
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH fallbackH _archiveH _auditH =>
        fallbackH)

theorem ay_bjg_guard_archive
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    archiveManifest :=
  fun guard =>
    guard archiveManifest
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH archiveH _auditH =>
        archiveH)

theorem ay_bjg_guard_audit
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness
      computedBackjumpLevelWitness trailTruncationLedger
      propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
      validatorGate fallbackBaseline archiveManifest auditTranscript : Prop) :
    ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _conflictH _graphH _levelH _assertingH _backjumpH _trailH _replayH
          _learnedH _buildH _validatorH _fallbackH _archiveH auditH =>
        auditH)

theorem ay_bjg_agreement_intro
    (originalFormulaTruth backjumpRunTruth publicSoundness : Prop) :
    ay_bjg_equisat originalFormulaTruth backjumpRunTruth ->
    publicSoundness ->
    ay_bjg_agreement originalFormulaTruth backjumpRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_bjg_conj_intro
      (ay_bjg_equisat originalFormulaTruth backjumpRunTruth)
      publicSoundness eqsat sound

theorem ay_bjg_accepted_backjump_intro
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    transitionOnly ->
    ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly :=
  fun guardH agreementH transitionH =>
    ay_bjg_conj_intro guardEvidence
      (ay_bjg_conj agreementEvidence transitionOnly) guardH
      (ay_bjg_conj_intro agreementEvidence transitionOnly agreementH
        transitionH)

theorem ay_bjg_accepted_guard
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly ->
    guardEvidence :=
  fun accepted =>
    ay_bjg_conj_left guardEvidence
      (ay_bjg_conj agreementEvidence transitionOnly) accepted

theorem ay_bjg_accepted_agreement
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_bjg_conj_left agreementEvidence transitionOnly
      (ay_bjg_conj_right guardEvidence
        (ay_bjg_conj agreementEvidence transitionOnly) accepted)

theorem ay_bjg_accepted_transition_only
    (guardEvidence agreementEvidence transitionOnly : Prop) :
    ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly ->
    transitionOnly :=
  fun accepted =>
    ay_bjg_conj_right agreementEvidence transitionOnly
      (ay_bjg_conj_right guardEvidence
        (ay_bjg_conj agreementEvidence transitionOnly) accepted)

theorem ay_bjg_backjump_cannot_justify_publication
    (backjumpEvidence fallbackOrRecompute : Prop) :
    backjumpEvidence ->
    fallbackOrRecompute ->
    ay_bjg_no_claim backjumpEvidence fallbackOrRecompute :=
  ay_bjg_conj_intro backjumpEvidence fallbackOrRecompute

theorem ay_bjg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bjg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bjg_conj_intro acceptedEvidence (ay_bjg_conj outcome formulaTruth)
      acceptedH (ay_bjg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bjg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_bjg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_bjg_conj_left acceptedEvidence (ay_bjg_conj outcome formulaTruth)
      report

theorem ay_bjg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_bjg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_bjg_conj_left outcome formulaTruth
      (ay_bjg_conj_right acceptedEvidence
        (ay_bjg_conj outcome formulaTruth) report)

theorem ay_bjg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_bjg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_bjg_conj_right outcome formulaTruth
      (ay_bjg_conj_right acceptedEvidence
        (ay_bjg_conj outcome formulaTruth) report)

theorem ay_bjg_preserves_formula_truth
    (originalFormulaTruth backjumpRunTruth : Prop) :
    ay_bjg_equisat originalFormulaTruth backjumpRunTruth ->
    originalFormulaTruth ->
    backjumpRunTruth :=
  fun eqsat truth =>
    ay_bjg_equisat_forward originalFormulaTruth backjumpRunTruth eqsat truth

theorem ay_bjg_reflects_formula_truth
    (originalFormulaTruth backjumpRunTruth : Prop) :
    ay_bjg_equisat originalFormulaTruth backjumpRunTruth ->
    backjumpRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_bjg_equisat_backward originalFormulaTruth backjumpRunTruth eqsat truth

theorem ay_bjg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence transitionOnly publicSoundness : Prop) :
    ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_bjg_accepted_agreement guardEvidence agreementEvidence transitionOnly
        accepted)

theorem ay_bjg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_bjg_no_claim diagnostic fallbackOrRecompute :=
  ay_bjg_conj_intro diagnostic fallbackOrRecompute

theorem ay_bjg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_bjg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_bjg_conj_right diagnostic fallbackOrRecompute

theorem ay_bjg_conflict_mismatch_no_claim
    (conflictMismatch fallbackOrRecompute : Prop) :
    conflictMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim conflictMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro conflictMismatch fallbackOrRecompute

theorem ay_bjg_graph_mismatch_no_claim
    (graphMismatch fallbackOrRecompute : Prop) :
    graphMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim graphMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro graphMismatch fallbackOrRecompute

theorem ay_bjg_level_mismatch_no_claim
    (levelMismatch fallbackOrRecompute : Prop) :
    levelMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim levelMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro levelMismatch fallbackOrRecompute

theorem ay_bjg_asserting_mismatch_no_claim
    (assertingMismatch fallbackOrRecompute : Prop) :
    assertingMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim assertingMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro assertingMismatch fallbackOrRecompute

theorem ay_bjg_backjump_mismatch_no_claim
    (backjumpMismatch fallbackOrRecompute : Prop) :
    backjumpMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim backjumpMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro backjumpMismatch fallbackOrRecompute

theorem ay_bjg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim trailMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_bjg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim replayMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_bjg_learned_mismatch_no_claim
    (learnedMismatch fallbackOrRecompute : Prop) :
    learnedMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim learnedMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro learnedMismatch fallbackOrRecompute

theorem ay_bjg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim buildMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_bjg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_bjg_archive_mismatch_no_claim
    (archiveMismatch fallbackOrRecompute : Prop) :
    archiveMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim archiveMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro archiveMismatch fallbackOrRecompute

theorem ay_bjg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_bjg_no_claim auditMismatch fallbackOrRecompute :=
  ay_bjg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_bjg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_bjg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_bjg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_bjg_publication_requires_guard
    (guardEvidence agreementEvidence transitionOnly outcome formulaTruth : Prop) :
    ay_bjg_public_report
      (ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_bjg_accepted_guard guardEvidence agreementEvidence transitionOnly
      (ay_bjg_public_report_accepted
        (ay_bjg_accepted_backjump guardEvidence agreementEvidence transitionOnly)
        outcome formulaTruth report)

theorem ay_bjg_publication_requires_validator
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript agreementEvidence transitionOnly outcome formulaTruth :
      Prop) :
    ay_bjg_public_report
      (ay_bjg_accepted_backjump
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_bjg_guard_validator conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript
      (ay_bjg_publication_requires_guard
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_bjg_publication_requires_archive
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript agreementEvidence transitionOnly outcome formulaTruth :
      Prop) :
    ay_bjg_public_report
      (ay_bjg_accepted_backjump
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    archiveManifest :=
  fun report =>
    ay_bjg_guard_archive conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript
      (ay_bjg_publication_requires_guard
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_bjg_publication_requires_audit
    (conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript agreementEvidence transitionOnly outcome formulaTruth :
      Prop) :
    ay_bjg_public_report
      (ay_bjg_accepted_backjump
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_bjg_guard_audit conflictClauseDigest implicationGraphAntecedentDigest
      decisionLevelMapDigest assertingClauseWitness computedBackjumpLevelWitness
      trailTruncationLedger propagationReplayAfterBackjump learnedClauseDigest
      solverBuildEvidence validatorGate fallbackBaseline archiveManifest
      auditTranscript
      (ay_bjg_publication_requires_guard
        (ay_bjg_guard conflictClauseDigest implicationGraphAntecedentDigest
          decisionLevelMapDigest assertingClauseWitness
          computedBackjumpLevelWitness trailTruncationLedger
          propagationReplayAfterBackjump learnedClauseDigest solverBuildEvidence
          validatorGate fallbackBaseline archiveManifest auditTranscript)
        agreementEvidence transitionOnly outcome formulaTruth report)

theorem ay_bjg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_bjg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_bjg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_bjg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_bjg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_bjg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
