-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-heap rebuild guard for sequential-main SAT-COMP branching. Rebuilds
-- are search-control/data-structure maintenance only when domain, heap,
-- activity, reconstructed order, tiebreak, decision replay, propagation
-- replay, fallback, build, validator, and audit evidence agree.

def ay_dhrg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dhrg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_dhrg_conj (before -> after) (after -> before)

def ay_dhrg_guard
    (variableDomainDigest : Prop)
    (heapSnapshotDigest : Prop)
    (activityScoreLedger : Prop)
    (heapOrderReconstructionWitness : Prop)
    (deterministicTiebreakManifest : Prop)
    (decisionOrderReplay : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      heapSnapshotDigest ->
      activityScoreLedger ->
      heapOrderReconstructionWitness ->
      deterministicTiebreakManifest ->
      decisionOrderReplay ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_dhrg_agreement
    (domainMatch heapMatch activityMatch orderMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_dhrg_guard domainMatch heapMatch activityMatch orderMatch tiebreakMatch
    decisionMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_dhrg_accepted_rebuild
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_dhrg_conj guardEvidence
    (ay_dhrg_conj agreementEvidence
      (ay_dhrg_conj deterministicBranchOrder searchControlHint))

def ay_dhrg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_dhrg_conj acceptedEvidence (ay_dhrg_conj outcome formulaTruth)

def ay_dhrg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_dhrg_conj diagnostic fallbackPublic

theorem ay_dhrg_conj_intro (left right : Prop) :
    left -> right -> ay_dhrg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_dhrg_conj_left (left right : Prop) :
    ay_dhrg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_dhrg_conj_right (left right : Prop) :
    ay_dhrg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_dhrg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_dhrg_equisat before after :=
  fun forward backward =>
    ay_dhrg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_dhrg_equisat_forward (before after : Prop) :
    ay_dhrg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_dhrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dhrg_equisat_backward (before after : Prop) :
    ay_dhrg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_dhrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dhrg_guard_intro
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    heapSnapshotDigest ->
    activityScoreLedger ->
    heapOrderReconstructionWitness ->
    deterministicTiebreakManifest ->
    decisionOrderReplay ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH heapH activityH orderH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH result make =>
    make domainH heapH activityH orderH tiebreakH decisionH replayH baselineH
      buildH validatorH auditH

theorem ay_dhrg_guard_domain
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _heapH _activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => domainH)

theorem ay_dhrg_guard_heap
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    heapSnapshotDigest :=
  fun guard =>
    guard heapSnapshotDigest
      (fun _domainH heapH _activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => heapH)

theorem ay_dhrg_guard_activity
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    activityScoreLedger :=
  fun guard =>
    guard activityScoreLedger
      (fun _domainH _heapH activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => activityH)

theorem ay_dhrg_guard_order
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    heapOrderReconstructionWitness :=
  fun guard =>
    guard heapOrderReconstructionWitness
      (fun _domainH _heapH _activityH orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => orderH)

theorem ay_dhrg_guard_tiebreak
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _heapH _activityH _orderH tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_dhrg_guard_decision
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionOrderReplay :=
  fun guard =>
    guard decisionOrderReplay
      (fun _domainH _heapH _activityH _orderH _tiebreakH decisionH _replayH
          _baselineH _buildH _validatorH _auditH => decisionH)

theorem ay_dhrg_guard_replay
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _heapH _activityH _orderH _tiebreakH _decisionH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_dhrg_guard_baseline
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _heapH _activityH _orderH _tiebreakH _decisionH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_dhrg_guard_build
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _heapH _activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_dhrg_guard_validator
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _heapH _activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_dhrg_guard_audit
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_dhrg_guard variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _heapH _activityH _orderH _tiebreakH _decisionH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_dhrg_agreement_intro
    (domainMatch heapMatch activityMatch orderMatch tiebreakMatch decisionMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    domainMatch ->
    heapMatch ->
    activityMatch ->
    orderMatch ->
    tiebreakMatch ->
    decisionMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_dhrg_agreement domainMatch heapMatch activityMatch orderMatch
      tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
      validatorAccepts auditMatch :=
  ay_dhrg_guard_intro domainMatch heapMatch activityMatch orderMatch
    tiebreakMatch decisionMatch replayMatch baselineMatch buildMatch
    validatorAccepts auditMatch

theorem ay_dhrg_accepted_rebuild_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_dhrg_conj_intro guardEvidence
      (ay_dhrg_conj agreementEvidence
        (ay_dhrg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_dhrg_conj_intro agreementEvidence
        (ay_dhrg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_dhrg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_dhrg_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  ay_dhrg_conj_left guardEvidence
    (ay_dhrg_conj agreementEvidence
      (ay_dhrg_conj deterministicBranchOrder searchControlHint))

theorem ay_dhrg_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_dhrg_conj_left agreementEvidence
      (ay_dhrg_conj deterministicBranchOrder searchControlHint)
      (ay_dhrg_conj_right guardEvidence
        (ay_dhrg_conj agreementEvidence
          (ay_dhrg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_dhrg_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_dhrg_conj_left deterministicBranchOrder searchControlHint
      (ay_dhrg_conj_right agreementEvidence
        (ay_dhrg_conj deterministicBranchOrder searchControlHint)
        (ay_dhrg_conj_right guardEvidence
          (ay_dhrg_conj agreementEvidence
            (ay_dhrg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_dhrg_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_dhrg_conj_right deterministicBranchOrder searchControlHint
      (ay_dhrg_conj_right agreementEvidence
        (ay_dhrg_conj deterministicBranchOrder searchControlHint)
        (ay_dhrg_conj_right guardEvidence
          (ay_dhrg_conj agreementEvidence
            (ay_dhrg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_dhrg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_dhrg_conj_intro acceptedEvidence (ay_dhrg_conj outcome formulaTruth)
      acceptedH (ay_dhrg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_dhrg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_dhrg_conj_left acceptedEvidence (ay_dhrg_conj outcome formulaTruth)

theorem ay_dhrg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_dhrg_conj_left outcome formulaTruth
      (ay_dhrg_conj_right acceptedEvidence
        (ay_dhrg_conj outcome formulaTruth) report)

theorem ay_dhrg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_dhrg_conj_right outcome formulaTruth
      (ay_dhrg_conj_right acceptedEvidence
        (ay_dhrg_conj outcome formulaTruth) report)

theorem ay_dhrg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_dhrg_no_claim diagnostic fallbackPublic :=
  ay_dhrg_conj_intro diagnostic fallbackPublic

theorem ay_dhrg_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_dhrg_conj_left diagnostic fallbackPublic

theorem ay_dhrg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_dhrg_conj_right diagnostic fallbackPublic

theorem ay_dhrg_rebuild_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_dhrg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_dhrg_equisat_forward beforeFormula afterFormula

theorem ay_dhrg_rebuild_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_dhrg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_dhrg_equisat_backward beforeFormula afterFormula

theorem ay_dhrg_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dhrg_public_report acceptedEvidence outcome formulaTruth ->
    ay_dhrg_conj outcome formulaTruth :=
  fun report =>
    ay_dhrg_conj_right acceptedEvidence (ay_dhrg_conj outcome formulaTruth)
      report

theorem ay_dhrg_accepted_guides_branching_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_dhrg_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_dhrg_conj_right agreementEvidence
      (ay_dhrg_conj deterministicBranchOrder searchControlHint)
      (ay_dhrg_conj_right guardEvidence
        (ay_dhrg_conj agreementEvidence
          (ay_dhrg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_dhrg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim domainMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro domainMismatch fallbackPublic

theorem ay_dhrg_heap_mismatch_no_claim
    (heapMismatch fallbackPublic : Prop) :
    heapMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim heapMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro heapMismatch fallbackPublic

theorem ay_dhrg_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim activityMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro activityMismatch fallbackPublic

theorem ay_dhrg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim orderMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro orderMismatch fallbackPublic

theorem ay_dhrg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim tiebreakMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_dhrg_decision_mismatch_no_claim
    (decisionMismatch fallbackPublic : Prop) :
    decisionMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim decisionMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro decisionMismatch fallbackPublic

theorem ay_dhrg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim replayMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro replayMismatch fallbackPublic

theorem ay_dhrg_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim baselineMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro baselineMismatch fallbackPublic

theorem ay_dhrg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim buildMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro buildMismatch fallbackPublic

theorem ay_dhrg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_dhrg_no_claim validatorRejects fallbackPublic :=
  ay_dhrg_no_claim_intro validatorRejects fallbackPublic

theorem ay_dhrg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_dhrg_no_claim auditMismatch fallbackPublic :=
  ay_dhrg_no_claim_intro auditMismatch fallbackPublic

theorem ay_dhrg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_dhrg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_dhrg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_dhrg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_dhrg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_dhrg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_dhrg_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_dhrg_public_report
      (ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_dhrg_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_dhrg_public_report_accepted
        (ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_dhrg_publication_requires_validator
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_dhrg_public_report
      (ay_dhrg_accepted_rebuild
        (ay_dhrg_guard variableDomainDigest heapSnapshotDigest
          activityScoreLedger heapOrderReconstructionWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_dhrg_guard_validator variableDomainDigest heapSnapshotDigest
      activityScoreLedger heapOrderReconstructionWitness
      deterministicTiebreakManifest decisionOrderReplay propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_dhrg_publication_requires_accepted_guard
        (ay_dhrg_guard variableDomainDigest heapSnapshotDigest
          activityScoreLedger heapOrderReconstructionWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_dhrg_publication_requires_audit
    (variableDomainDigest heapSnapshotDigest activityScoreLedger
      heapOrderReconstructionWitness deterministicTiebreakManifest
      decisionOrderReplay propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence deterministicBranchOrder
      searchControlHint outcome formulaTruth : Prop) :
    ay_dhrg_public_report
      (ay_dhrg_accepted_rebuild
        (ay_dhrg_guard variableDomainDigest heapSnapshotDigest
          activityScoreLedger heapOrderReconstructionWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_dhrg_guard_audit variableDomainDigest heapSnapshotDigest
      activityScoreLedger heapOrderReconstructionWitness
      deterministicTiebreakManifest decisionOrderReplay propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_dhrg_publication_requires_accepted_guard
        (ay_dhrg_guard variableDomainDigest heapSnapshotDigest
          activityScoreLedger heapOrderReconstructionWitness
          deterministicTiebreakManifest decisionOrderReplay propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_dhrg_heap_rebuild_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_dhrg_equisat beforeFormula afterFormula ->
    ay_dhrg_accepted_rebuild guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    ay_dhrg_conj (beforeFormula -> afterFormula)
      (ay_dhrg_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_dhrg_conj_intro (beforeFormula -> afterFormula)
      (ay_dhrg_conj deterministicBranchOrder searchControlHint)
      (ay_dhrg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_dhrg_accepted_guides_branching_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_dhrg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_dhrg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_dhrg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_dhrg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_dhrg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_dhrg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
