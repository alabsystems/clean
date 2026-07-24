-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-activity heap guard for sequential main-track CDCL branching.
-- The heap is search-control only when domain, activity, heap/order,
-- candidate, tie-break, replay, fallback, build, validator, and audit evidence
-- agree.

def ay_vahg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vahg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_vahg_conj (before -> after) (after -> before)

def ay_vahg_guard
    (variableDomainDigest : Prop)
    (activityVectorDigest : Prop)
    (heapOrderWitness : Prop)
    (decisionCandidateLedger : Prop)
    (deterministicTiebreakManifest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorDigest ->
      heapOrderWitness ->
      decisionCandidateLedger ->
      deterministicTiebreakManifest ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_vahg_agreement
    (domainMatch activityMatch heapMatch candidateMatch tiebreakMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_vahg_guard domainMatch activityMatch heapMatch candidateMatch
    tiebreakMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_vahg_accepted_heap
    (guardEvidence agreementEvidence searchControlHint : Prop) : Prop :=
  ay_vahg_conj guardEvidence
    (ay_vahg_conj agreementEvidence searchControlHint)

def ay_vahg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_vahg_conj acceptedEvidence (ay_vahg_conj outcome formulaTruth)

def ay_vahg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_vahg_conj diagnostic fallbackPublic

theorem ay_vahg_conj_intro (left right : Prop) :
    left -> right -> ay_vahg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_vahg_conj_left (left right : Prop) :
    ay_vahg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_vahg_conj_right (left right : Prop) :
    ay_vahg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_vahg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_vahg_equisat before after :=
  fun forward backward =>
    ay_vahg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_vahg_equisat_forward (before after : Prop) :
    ay_vahg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_vahg_conj_left (before -> after) (after -> before) eqsat

theorem ay_vahg_equisat_backward (before after : Prop) :
    ay_vahg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_vahg_conj_right (before -> after) (after -> before) eqsat

theorem ay_vahg_guard_intro
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    activityVectorDigest ->
    heapOrderWitness ->
    decisionCandidateLedger ->
    deterministicTiebreakManifest ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH activityH heapH candidateH tiebreakH replayH fallbackH buildH
      validatorH auditH result make =>
    make domainH activityH heapH candidateH tiebreakH replayH fallbackH buildH
      validatorH auditH

theorem ay_vahg_guard_domain
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _heapH _candidateH _tiebreakH _replayH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_vahg_guard_activity
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    activityVectorDigest :=
  fun guard =>
    guard activityVectorDigest
      (fun _domainH activityH _heapH _candidateH _tiebreakH _replayH
          _fallbackH _buildH _validatorH _auditH => activityH)

theorem ay_vahg_guard_heap
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    heapOrderWitness :=
  fun guard =>
    guard heapOrderWitness
      (fun _domainH _activityH heapH _candidateH _tiebreakH _replayH
          _fallbackH _buildH _validatorH _auditH => heapH)

theorem ay_vahg_guard_candidate
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionCandidateLedger :=
  fun guard =>
    guard decisionCandidateLedger
      (fun _domainH _activityH _heapH candidateH _tiebreakH _replayH
          _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_vahg_guard_tiebreak
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _activityH _heapH _candidateH tiebreakH _replayH
          _fallbackH _buildH _validatorH _auditH => tiebreakH)

theorem ay_vahg_guard_replay
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _activityH _heapH _candidateH _tiebreakH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_vahg_guard_fallback
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _heapH _candidateH _tiebreakH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_vahg_guard_build
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _heapH _candidateH _tiebreakH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_vahg_guard_validator
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _heapH _candidateH _tiebreakH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_vahg_guard_audit
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_vahg_guard variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _heapH _candidateH _tiebreakH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_vahg_agreement_intro
    (domainMatch activityMatch heapMatch candidateMatch tiebreakMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    activityMatch ->
    heapMatch ->
    candidateMatch ->
    tiebreakMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_vahg_agreement domainMatch activityMatch heapMatch candidateMatch
      tiebreakMatch replayMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_vahg_guard_intro domainMatch activityMatch heapMatch candidateMatch
    tiebreakMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_vahg_accepted_heap_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint :=
  fun guardH agreementH hintH =>
    ay_vahg_conj_intro guardEvidence
      (ay_vahg_conj agreementEvidence searchControlHint)
      guardH
      (ay_vahg_conj_intro agreementEvidence searchControlHint agreementH hintH)

theorem ay_vahg_accepted_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint ->
    guardEvidence :=
  ay_vahg_conj_left guardEvidence
    (ay_vahg_conj agreementEvidence searchControlHint)

theorem ay_vahg_accepted_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_vahg_conj_left agreementEvidence searchControlHint
      (ay_vahg_conj_right guardEvidence
        (ay_vahg_conj agreementEvidence searchControlHint) accepted)

theorem ay_vahg_accepted_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_vahg_conj_right agreementEvidence searchControlHint
      (ay_vahg_conj_right guardEvidence
        (ay_vahg_conj agreementEvidence searchControlHint) accepted)

theorem ay_vahg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_vahg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_vahg_conj_intro acceptedEvidence (ay_vahg_conj outcome formulaTruth)
      acceptedH (ay_vahg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_vahg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vahg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_vahg_conj_left acceptedEvidence (ay_vahg_conj outcome formulaTruth)

theorem ay_vahg_public_report_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vahg_public_report acceptedEvidence outcome formulaTruth ->
    ay_vahg_conj outcome formulaTruth :=
  fun report =>
    ay_vahg_conj_right acceptedEvidence (ay_vahg_conj outcome formulaTruth)
      report

theorem ay_vahg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_vahg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_vahg_conj_right outcome formulaTruth
      (ay_vahg_public_report_soundness acceptedEvidence outcome formulaTruth
        report)

theorem ay_vahg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_vahg_no_claim diagnostic fallbackPublic :=
  ay_vahg_conj_intro diagnostic fallbackPublic

theorem ay_vahg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_vahg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_vahg_conj_right diagnostic fallbackPublic

theorem ay_vahg_heap_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_vahg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_vahg_equisat_forward beforeFormula afterFormula

theorem ay_vahg_heap_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_vahg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_vahg_equisat_backward beforeFormula afterFormula

theorem ay_vahg_accepted_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      searchControlHint : Prop) :
    ay_vahg_equisat beforeFormula afterFormula ->
    ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint ->
    ay_vahg_conj (beforeFormula -> afterFormula) searchControlHint :=
  fun eqsat accepted =>
    ay_vahg_conj_intro (beforeFormula -> afterFormula) searchControlHint
      (ay_vahg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_vahg_accepted_search_control guardEvidence agreementEvidence
        searchControlHint accepted)

theorem ay_vahg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_vahg_no_claim domainMismatch fallbackPublic :=
  ay_vahg_no_claim_intro domainMismatch fallbackPublic

theorem ay_vahg_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch -> fallbackPublic ->
    ay_vahg_no_claim activityMismatch fallbackPublic :=
  ay_vahg_no_claim_intro activityMismatch fallbackPublic

theorem ay_vahg_heap_mismatch_no_claim
    (heapMismatch fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_vahg_no_claim heapMismatch fallbackPublic :=
  ay_vahg_no_claim_intro heapMismatch fallbackPublic

theorem ay_vahg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch -> fallbackPublic ->
    ay_vahg_no_claim orderMismatch fallbackPublic :=
  ay_vahg_no_claim_intro orderMismatch fallbackPublic

theorem ay_vahg_candidate_mismatch_no_claim
    (candidateMismatch fallbackPublic : Prop) :
    candidateMismatch -> fallbackPublic ->
    ay_vahg_no_claim candidateMismatch fallbackPublic :=
  ay_vahg_no_claim_intro candidateMismatch fallbackPublic

theorem ay_vahg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_vahg_no_claim tiebreakMismatch fallbackPublic :=
  ay_vahg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_vahg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_vahg_no_claim replayMismatch fallbackPublic :=
  ay_vahg_no_claim_intro replayMismatch fallbackPublic

theorem ay_vahg_fallback_mismatch_no_claim
    (fallbackMismatch fallbackPublic : Prop) :
    fallbackMismatch -> fallbackPublic ->
    ay_vahg_no_claim fallbackMismatch fallbackPublic :=
  ay_vahg_no_claim_intro fallbackMismatch fallbackPublic

theorem ay_vahg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_vahg_no_claim buildMismatch fallbackPublic :=
  ay_vahg_no_claim_intro buildMismatch fallbackPublic

theorem ay_vahg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects -> fallbackPublic ->
    ay_vahg_no_claim validatorRejects fallbackPublic :=
  ay_vahg_no_claim_intro validatorRejects fallbackPublic

theorem ay_vahg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_vahg_no_claim auditMismatch fallbackPublic :=
  ay_vahg_no_claim_intro auditMismatch fallbackPublic

theorem ay_vahg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_vahg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_vahg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_vahg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_vahg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_vahg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_vahg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth :
      Prop) :
    ay_vahg_public_report
      (ay_vahg_accepted_heap guardEvidence agreementEvidence searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_vahg_accepted_guard guardEvidence agreementEvidence searchControlHint
      (ay_vahg_public_report_accepted
        (ay_vahg_accepted_heap guardEvidence agreementEvidence
          searchControlHint)
        outcome formulaTruth report)

theorem ay_vahg_publication_requires_validator
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_vahg_public_report
      (ay_vahg_accepted_heap
        (ay_vahg_guard variableDomainDigest activityVectorDigest
          heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_vahg_guard_validator variableDomainDigest activityVectorDigest
      heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_vahg_publication_requires_guard
        (ay_vahg_guard variableDomainDigest activityVectorDigest
          heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_vahg_publication_requires_audit
    (variableDomainDigest activityVectorDigest heapOrderWitness
      decisionCandidateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_vahg_public_report
      (ay_vahg_accepted_heap
        (ay_vahg_guard variableDomainDigest activityVectorDigest
          heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_vahg_guard_audit variableDomainDigest activityVectorDigest
      heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_vahg_publication_requires_guard
        (ay_vahg_guard variableDomainDigest activityVectorDigest
          heapOrderWitness decisionCandidateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_vahg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence -> satOutcome -> formulaTruth ->
    ay_vahg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_vahg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_vahg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence -> unsatOutcome -> formulaTruth ->
    ay_vahg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_vahg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
