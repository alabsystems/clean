-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Learned-clause assertion-level guard for sequential main-track CDCL.
-- Assertion/backjump computation is search-control and learned-clause evidence
-- only when graph, learned clause, levels, reason, replay, fallback, build,
-- validator, and audit evidence agree.

def ay_lalg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lalg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_lalg_conj (before -> after) (after -> before)

def ay_lalg_guard
    (variableDomainDigest : Prop)
    (implicationGraphDigest : Prop)
    (learnedClauseDigest : Prop)
    (assertionLevelWitness : Prop)
    (backjumpLevelWitness : Prop)
    (decisionStackDigest : Prop)
    (reasonClauseLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      implicationGraphDigest ->
      learnedClauseDigest ->
      assertionLevelWitness ->
      backjumpLevelWitness ->
      decisionStackDigest ->
      reasonClauseLedger ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_lalg_agreement
    (originalFormulaTruth learnedRunTruth publicSoundness : Prop) : Prop :=
  ay_lalg_conj
    (ay_lalg_equisat originalFormulaTruth learnedRunTruth)
    publicSoundness

def ay_lalg_accepted_assertion_level
    (guardEvidence agreementEvidence learningSearchControl : Prop) : Prop :=
  ay_lalg_conj guardEvidence
    (ay_lalg_conj agreementEvidence learningSearchControl)

def ay_lalg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_lalg_conj acceptedEvidence
    (ay_lalg_conj outcome formulaTruth)

def ay_lalg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_lalg_conj diagnostic fallbackOrRecompute

theorem ay_lalg_conj_intro (left right : Prop) :
    left -> right -> ay_lalg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_lalg_conj_left (left right : Prop) :
    ay_lalg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_lalg_conj_right (left right : Prop) :
    ay_lalg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_lalg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_lalg_equisat before after :=
  fun forward backward =>
    ay_lalg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_lalg_equisat_forward (before after : Prop) :
    ay_lalg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_lalg_conj_left (before -> after) (after -> before) eqsat

theorem ay_lalg_equisat_backward (before after : Prop) :
    ay_lalg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_lalg_conj_right (before -> after) (after -> before) eqsat

theorem ay_lalg_guard_intro
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    implicationGraphDigest ->
    learnedClauseDigest ->
    assertionLevelWitness ->
    backjumpLevelWitness ->
    decisionStackDigest ->
    reasonClauseLedger ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH graphH learnedH assertionH backjumpH stackH reasonH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH graphH learnedH assertionH backjumpH stackH reasonH replayH
      fallbackH buildH validatorH auditH

theorem ay_lalg_guard_domain
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_lalg_guard_graph
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    implicationGraphDigest :=
  fun guard =>
    guard implicationGraphDigest
      (fun _domainH graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => graphH)

theorem ay_lalg_guard_learned_clause
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    learnedClauseDigest :=
  fun guard =>
    guard learnedClauseDigest
      (fun _domainH _graphH learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => learnedH)

theorem ay_lalg_guard_assertion_level
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    assertionLevelWitness :=
  fun guard =>
    guard assertionLevelWitness
      (fun _domainH _graphH _learnedH assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => assertionH)

theorem ay_lalg_guard_backjump_level
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    backjumpLevelWitness :=
  fun guard =>
    guard backjumpLevelWitness
      (fun _domainH _graphH _learnedH _assertionH backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => backjumpH)

theorem ay_lalg_guard_stack
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _domainH _graphH _learnedH _assertionH _backjumpH stackH _reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => stackH)

theorem ay_lalg_guard_reason
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH reasonH
          _replayH _fallbackH _buildH _validatorH _auditH => reasonH)

theorem ay_lalg_guard_replay
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_lalg_guard_fallback
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_lalg_guard_build
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_lalg_guard_validator
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_lalg_guard_audit
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_lalg_guard variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _graphH _learnedH _assertionH _backjumpH _stackH _reasonH
          _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_lalg_agreement_intro
    (originalFormulaTruth learnedRunTruth publicSoundness : Prop) :
    ay_lalg_equisat originalFormulaTruth learnedRunTruth ->
    publicSoundness ->
    ay_lalg_agreement originalFormulaTruth learnedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_lalg_conj_intro
      (ay_lalg_equisat originalFormulaTruth learnedRunTruth)
      publicSoundness eqsat sound

theorem ay_lalg_accepted_assertion_level_intro
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    guardEvidence ->
    agreementEvidence ->
    learningSearchControl ->
    ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
      learningSearchControl :=
  fun guardH agreementH learningH =>
    ay_lalg_conj_intro guardEvidence
      (ay_lalg_conj agreementEvidence learningSearchControl) guardH
      (ay_lalg_conj_intro agreementEvidence learningSearchControl agreementH
        learningH)

theorem ay_lalg_accepted_guard
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
      learningSearchControl ->
    guardEvidence :=
  fun accepted =>
    ay_lalg_conj_left guardEvidence
      (ay_lalg_conj agreementEvidence learningSearchControl) accepted

theorem ay_lalg_accepted_agreement
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
      learningSearchControl ->
    agreementEvidence :=
  fun accepted =>
    ay_lalg_conj_left agreementEvidence learningSearchControl
      (ay_lalg_conj_right guardEvidence
        (ay_lalg_conj agreementEvidence learningSearchControl) accepted)

theorem ay_lalg_accepted_learning_search_control
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
      learningSearchControl ->
    learningSearchControl :=
  fun accepted =>
    ay_lalg_conj_right agreementEvidence learningSearchControl
      (ay_lalg_conj_right guardEvidence
        (ay_lalg_conj agreementEvidence learningSearchControl) accepted)

theorem ay_lalg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_lalg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_lalg_conj_intro acceptedEvidence (ay_lalg_conj outcome formulaTruth)
      acceptedH (ay_lalg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_lalg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lalg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_lalg_conj_left acceptedEvidence (ay_lalg_conj outcome formulaTruth)
      report

theorem ay_lalg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lalg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_lalg_conj_left outcome formulaTruth
      (ay_lalg_conj_right acceptedEvidence
        (ay_lalg_conj outcome formulaTruth) report)

theorem ay_lalg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lalg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_lalg_conj_right outcome formulaTruth
      (ay_lalg_conj_right acceptedEvidence
        (ay_lalg_conj outcome formulaTruth) report)

theorem ay_lalg_preserves_formula_truth
    (originalFormulaTruth learnedRunTruth : Prop) :
    ay_lalg_equisat originalFormulaTruth learnedRunTruth ->
    originalFormulaTruth ->
    learnedRunTruth :=
  fun eqsat truth =>
    ay_lalg_equisat_forward originalFormulaTruth learnedRunTruth eqsat truth

theorem ay_lalg_reflects_formula_truth
    (originalFormulaTruth learnedRunTruth : Prop) :
    ay_lalg_equisat originalFormulaTruth learnedRunTruth ->
    learnedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_lalg_equisat_backward originalFormulaTruth learnedRunTruth eqsat truth

theorem ay_lalg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence learningSearchControl publicSoundness :
      Prop) :
    ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
      learningSearchControl ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_lalg_accepted_agreement guardEvidence agreementEvidence
        learningSearchControl accepted)

theorem ay_lalg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_lalg_no_claim diagnostic fallbackOrRecompute :=
  ay_lalg_conj_intro diagnostic fallbackOrRecompute

theorem ay_lalg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_lalg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_lalg_conj_right diagnostic fallbackOrRecompute

theorem ay_lalg_graph_mismatch_no_claim
    (graphMismatch fallbackOrRecompute : Prop) :
    graphMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim graphMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro graphMismatch fallbackOrRecompute

theorem ay_lalg_learned_mismatch_no_claim
    (learnedMismatch fallbackOrRecompute : Prop) :
    learnedMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim learnedMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro learnedMismatch fallbackOrRecompute

theorem ay_lalg_assertion_mismatch_no_claim
    (assertionMismatch fallbackOrRecompute : Prop) :
    assertionMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim assertionMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro assertionMismatch fallbackOrRecompute

theorem ay_lalg_backjump_mismatch_no_claim
    (backjumpMismatch fallbackOrRecompute : Prop) :
    backjumpMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim backjumpMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro backjumpMismatch fallbackOrRecompute

theorem ay_lalg_reason_mismatch_no_claim
    (reasonMismatch fallbackOrRecompute : Prop) :
    reasonMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim reasonMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro reasonMismatch fallbackOrRecompute

theorem ay_lalg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim replayMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_lalg_stack_mismatch_no_claim
    (stackMismatch fallbackOrRecompute : Prop) :
    stackMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim stackMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro stackMismatch fallbackOrRecompute

theorem ay_lalg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim buildMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_lalg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_lalg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_lalg_no_claim auditMismatch fallbackOrRecompute :=
  ay_lalg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_lalg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_lalg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_lalg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_lalg_publication_requires_guard
    (guardEvidence agreementEvidence learningSearchControl outcome formulaTruth :
      Prop) :
    ay_lalg_public_report
      (ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
        learningSearchControl)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_lalg_accepted_guard guardEvidence agreementEvidence learningSearchControl
      (ay_lalg_public_report_accepted
        (ay_lalg_accepted_assertion_level guardEvidence agreementEvidence
          learningSearchControl)
        outcome formulaTruth report)

theorem ay_lalg_publication_requires_validator
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence learningSearchControl
      outcome formulaTruth : Prop) :
    ay_lalg_public_report
      (ay_lalg_accepted_assertion_level
        (ay_lalg_guard variableDomainDigest implicationGraphDigest
          learnedClauseDigest assertionLevelWitness backjumpLevelWitness
          decisionStackDigest reasonClauseLedger propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_lalg_guard_validator variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_lalg_publication_requires_guard
        (ay_lalg_guard variableDomainDigest implicationGraphDigest
          learnedClauseDigest assertionLevelWitness backjumpLevelWitness
          decisionStackDigest reasonClauseLedger propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl outcome formulaTruth report)

theorem ay_lalg_publication_requires_audit
    (variableDomainDigest implicationGraphDigest learnedClauseDigest
      assertionLevelWitness backjumpLevelWitness decisionStackDigest
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence learningSearchControl
      outcome formulaTruth : Prop) :
    ay_lalg_public_report
      (ay_lalg_accepted_assertion_level
        (ay_lalg_guard variableDomainDigest implicationGraphDigest
          learnedClauseDigest assertionLevelWitness backjumpLevelWitness
          decisionStackDigest reasonClauseLedger propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_lalg_guard_audit variableDomainDigest implicationGraphDigest
      learnedClauseDigest assertionLevelWitness backjumpLevelWitness
      decisionStackDigest reasonClauseLedger propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_lalg_publication_requires_guard
        (ay_lalg_guard variableDomainDigest implicationGraphDigest
          learnedClauseDigest assertionLevelWitness backjumpLevelWitness
          decisionStackDigest reasonClauseLedger propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl outcome formulaTruth report)

theorem ay_lalg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_lalg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_lalg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_lalg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_lalg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_lalg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
