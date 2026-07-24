-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Conflict-analysis cut guard for sequential main-track CDCL learning.
-- Conflict analysis is learning/search-control evidence only when graph,
-- conflict clause, cut, reason, replay, fallback, build, validator, and audit
-- evidence agree.

def ay_cacg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cacg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cacg_conj (before -> after) (after -> before)

def ay_cacg_guard
    (variableDomainDigest : Prop)
    (implicationGraphDigest : Prop)
    (conflictClauseDigest : Prop)
    (decisionStackDigest : Prop)
    (cutFirstUipWitness : Prop)
    (reasonClauseLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      implicationGraphDigest ->
      conflictClauseDigest ->
      decisionStackDigest ->
      cutFirstUipWitness ->
      reasonClauseLedger ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cacg_agreement
    (originalFormulaTruth learnedRunTruth publicSoundness : Prop) : Prop :=
  ay_cacg_conj
    (ay_cacg_equisat originalFormulaTruth learnedRunTruth)
    publicSoundness

def ay_cacg_accepted_conflict_analysis
    (guardEvidence agreementEvidence learningSearchControl : Prop) : Prop :=
  ay_cacg_conj guardEvidence
    (ay_cacg_conj agreementEvidence learningSearchControl)

def ay_cacg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_cacg_conj acceptedEvidence
    (ay_cacg_conj outcome formulaTruth)

def ay_cacg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_cacg_conj diagnostic fallbackOrRecompute

theorem ay_cacg_conj_intro (left right : Prop) :
    left -> right -> ay_cacg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cacg_conj_left (left right : Prop) :
    ay_cacg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cacg_conj_right (left right : Prop) :
    ay_cacg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cacg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_cacg_equisat before after :=
  fun forward backward =>
    ay_cacg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cacg_equisat_forward (before after : Prop) :
    ay_cacg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cacg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cacg_equisat_backward (before after : Prop) :
    ay_cacg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cacg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cacg_guard_intro
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    implicationGraphDigest ->
    conflictClauseDigest ->
    decisionStackDigest ->
    cutFirstUipWitness ->
    reasonClauseLedger ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH graphH conflictH stackH cutH reasonH replayH fallbackH buildH
      validatorH auditH result make =>
    make domainH graphH conflictH stackH cutH reasonH replayH fallbackH buildH
      validatorH auditH

theorem ay_cacg_guard_domain
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _graphH _conflictH _stackH _cutH _reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_cacg_guard_graph
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    implicationGraphDigest :=
  fun guard =>
    guard implicationGraphDigest
      (fun _domainH graphH _conflictH _stackH _cutH _reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => graphH)

theorem ay_cacg_guard_conflict
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    conflictClauseDigest :=
  fun guard =>
    guard conflictClauseDigest
      (fun _domainH _graphH conflictH _stackH _cutH _reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => conflictH)

theorem ay_cacg_guard_stack
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _domainH _graphH _conflictH stackH _cutH _reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => stackH)

theorem ay_cacg_guard_cut
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    cutFirstUipWitness :=
  fun guard =>
    guard cutFirstUipWitness
      (fun _domainH _graphH _conflictH _stackH cutH _reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => cutH)

theorem ay_cacg_guard_reason
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _graphH _conflictH _stackH _cutH reasonH _replayH
          _fallbackH _buildH _validatorH _auditH => reasonH)

theorem ay_cacg_guard_replay
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _graphH _conflictH _stackH _cutH _reasonH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_cacg_guard_fallback
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _graphH _conflictH _stackH _cutH _reasonH _replayH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_cacg_guard_build
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _graphH _conflictH _stackH _cutH _reasonH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_cacg_guard_validator
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _graphH _conflictH _stackH _cutH _reasonH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_cacg_guard_audit
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_cacg_guard variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _graphH _conflictH _stackH _cutH _reasonH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_cacg_agreement_intro
    (originalFormulaTruth learnedRunTruth publicSoundness : Prop) :
    ay_cacg_equisat originalFormulaTruth learnedRunTruth ->
    publicSoundness ->
    ay_cacg_agreement originalFormulaTruth learnedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_cacg_conj_intro
      (ay_cacg_equisat originalFormulaTruth learnedRunTruth)
      publicSoundness eqsat sound

theorem ay_cacg_accepted_conflict_analysis_intro
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    guardEvidence ->
    agreementEvidence ->
    learningSearchControl ->
    ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
      learningSearchControl :=
  fun guardH agreementH learningH =>
    ay_cacg_conj_intro guardEvidence
      (ay_cacg_conj agreementEvidence learningSearchControl) guardH
      (ay_cacg_conj_intro agreementEvidence learningSearchControl agreementH
        learningH)

theorem ay_cacg_accepted_guard
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
      learningSearchControl ->
    guardEvidence :=
  fun accepted =>
    ay_cacg_conj_left guardEvidence
      (ay_cacg_conj agreementEvidence learningSearchControl) accepted

theorem ay_cacg_accepted_agreement
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
      learningSearchControl ->
    agreementEvidence :=
  fun accepted =>
    ay_cacg_conj_left agreementEvidence learningSearchControl
      (ay_cacg_conj_right guardEvidence
        (ay_cacg_conj agreementEvidence learningSearchControl) accepted)

theorem ay_cacg_accepted_learning_search_control
    (guardEvidence agreementEvidence learningSearchControl : Prop) :
    ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
      learningSearchControl ->
    learningSearchControl :=
  fun accepted =>
    ay_cacg_conj_right agreementEvidence learningSearchControl
      (ay_cacg_conj_right guardEvidence
        (ay_cacg_conj agreementEvidence learningSearchControl) accepted)

theorem ay_cacg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cacg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cacg_conj_intro acceptedEvidence (ay_cacg_conj outcome formulaTruth)
      acceptedH (ay_cacg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cacg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cacg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_cacg_conj_left acceptedEvidence (ay_cacg_conj outcome formulaTruth)
      report

theorem ay_cacg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cacg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_cacg_conj_left outcome formulaTruth
      (ay_cacg_conj_right acceptedEvidence
        (ay_cacg_conj outcome formulaTruth) report)

theorem ay_cacg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cacg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_cacg_conj_right outcome formulaTruth
      (ay_cacg_conj_right acceptedEvidence
        (ay_cacg_conj outcome formulaTruth) report)

theorem ay_cacg_preserves_formula_truth
    (originalFormulaTruth learnedRunTruth : Prop) :
    ay_cacg_equisat originalFormulaTruth learnedRunTruth ->
    originalFormulaTruth ->
    learnedRunTruth :=
  fun eqsat truth =>
    ay_cacg_equisat_forward originalFormulaTruth learnedRunTruth eqsat truth

theorem ay_cacg_reflects_formula_truth
    (originalFormulaTruth learnedRunTruth : Prop) :
    ay_cacg_equisat originalFormulaTruth learnedRunTruth ->
    learnedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_cacg_equisat_backward originalFormulaTruth learnedRunTruth eqsat truth

theorem ay_cacg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence learningSearchControl publicSoundness :
      Prop) :
    ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
      learningSearchControl ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_cacg_accepted_agreement guardEvidence agreementEvidence
        learningSearchControl accepted)

theorem ay_cacg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_cacg_no_claim diagnostic fallbackOrRecompute :=
  ay_cacg_conj_intro diagnostic fallbackOrRecompute

theorem ay_cacg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_cacg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_cacg_conj_right diagnostic fallbackOrRecompute

theorem ay_cacg_graph_mismatch_no_claim
    (graphMismatch fallbackOrRecompute : Prop) :
    graphMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim graphMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro graphMismatch fallbackOrRecompute

theorem ay_cacg_conflict_mismatch_no_claim
    (conflictMismatch fallbackOrRecompute : Prop) :
    conflictMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim conflictMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro conflictMismatch fallbackOrRecompute

theorem ay_cacg_cut_mismatch_no_claim
    (cutMismatch fallbackOrRecompute : Prop) :
    cutMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim cutMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro cutMismatch fallbackOrRecompute

theorem ay_cacg_reason_mismatch_no_claim
    (reasonMismatch fallbackOrRecompute : Prop) :
    reasonMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim reasonMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro reasonMismatch fallbackOrRecompute

theorem ay_cacg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim replayMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_cacg_stack_mismatch_no_claim
    (stackMismatch fallbackOrRecompute : Prop) :
    stackMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim stackMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro stackMismatch fallbackOrRecompute

theorem ay_cacg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim buildMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_cacg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_cacg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_cacg_no_claim auditMismatch fallbackOrRecompute :=
  ay_cacg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_cacg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_cacg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_cacg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_cacg_publication_requires_guard
    (guardEvidence agreementEvidence learningSearchControl outcome formulaTruth :
      Prop) :
    ay_cacg_public_report
      (ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
        learningSearchControl)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_cacg_accepted_guard guardEvidence agreementEvidence learningSearchControl
      (ay_cacg_public_report_accepted
        (ay_cacg_accepted_conflict_analysis guardEvidence agreementEvidence
          learningSearchControl)
        outcome formulaTruth report)

theorem ay_cacg_publication_requires_validator
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence learningSearchControl outcome formulaTruth : Prop) :
    ay_cacg_public_report
      (ay_cacg_accepted_conflict_analysis
        (ay_cacg_guard variableDomainDigest implicationGraphDigest
          conflictClauseDigest decisionStackDigest cutFirstUipWitness
          reasonClauseLedger propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_cacg_guard_validator variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_cacg_publication_requires_guard
        (ay_cacg_guard variableDomainDigest implicationGraphDigest
          conflictClauseDigest decisionStackDigest cutFirstUipWitness
          reasonClauseLedger propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl outcome formulaTruth report)

theorem ay_cacg_publication_requires_audit
    (variableDomainDigest implicationGraphDigest conflictClauseDigest
      decisionStackDigest cutFirstUipWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence learningSearchControl outcome formulaTruth : Prop) :
    ay_cacg_public_report
      (ay_cacg_accepted_conflict_analysis
        (ay_cacg_guard variableDomainDigest implicationGraphDigest
          conflictClauseDigest decisionStackDigest cutFirstUipWitness
          reasonClauseLedger propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_cacg_guard_audit variableDomainDigest implicationGraphDigest
      conflictClauseDigest decisionStackDigest cutFirstUipWitness
      reasonClauseLedger propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_cacg_publication_requires_guard
        (ay_cacg_guard variableDomainDigest implicationGraphDigest
          conflictClauseDigest decisionStackDigest cutFirstUipWitness
          reasonClauseLedger propagationReplay fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence learningSearchControl outcome formulaTruth report)

theorem ay_cacg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_cacg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_cacg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_cacg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_cacg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_cacg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
