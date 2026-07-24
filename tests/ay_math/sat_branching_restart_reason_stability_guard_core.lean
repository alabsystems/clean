-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart/reason stability guard for sequential-main SAT-COMP search control.
-- Restart and reason-clause metadata are search-control only when domain,
-- restart epoch, reason ledger, stack digest, replay, tiebreak, fallback,
-- build, validator, and audit evidence agree.

def ay_rrsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rrsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rrsg_conj (before -> after) (after -> before)

def ay_rrsg_guard
    (variableDomainDigest : Prop)
    (restartEpochDigest : Prop)
    (reasonClauseLedger : Prop)
    (decisionStackDigest : Prop)
    (propagationReplay : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      restartEpochDigest ->
      reasonClauseLedger ->
      decisionStackDigest ->
      propagationReplay ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rrsg_agreement
    (domainMatch restartMatch reasonMatch stackMatch replayMatch tiebreakMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) : Prop :=
  ay_rrsg_guard domainMatch restartMatch reasonMatch stackMatch replayMatch
    tiebreakMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_rrsg_accepted_stability
    (guardEvidence agreementEvidence searchControlHint : Prop) : Prop :=
  ay_rrsg_conj guardEvidence
    (ay_rrsg_conj agreementEvidence searchControlHint)

def ay_rrsg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_rrsg_conj acceptedEvidence (ay_rrsg_conj outcome formulaTruth)

def ay_rrsg_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_rrsg_conj diagnostic fallbackPublic

theorem ay_rrsg_conj_intro (left right : Prop) :
    left -> right -> ay_rrsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rrsg_conj_left (left right : Prop) :
    ay_rrsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rrsg_conj_right (left right : Prop) :
    ay_rrsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rrsg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_rrsg_equisat before after :=
  fun forward backward =>
    ay_rrsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rrsg_equisat_forward (before after : Prop) :
    ay_rrsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rrsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_rrsg_equisat_backward (before after : Prop) :
    ay_rrsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rrsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_rrsg_guard_intro
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    restartEpochDigest ->
    reasonClauseLedger ->
    decisionStackDigest ->
    propagationReplay ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH restartH reasonH stackH replayH tiebreakH fallbackH buildH
      validatorH auditH result make =>
    make domainH restartH reasonH stackH replayH tiebreakH fallbackH buildH
      validatorH auditH

theorem ay_rrsg_guard_domain
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _restartH _reasonH _stackH _replayH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_rrsg_guard_restart
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    restartEpochDigest :=
  fun guard =>
    guard restartEpochDigest
      (fun _domainH restartH _reasonH _stackH _replayH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => restartH)

theorem ay_rrsg_guard_reason
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _restartH reasonH _stackH _replayH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => reasonH)

theorem ay_rrsg_guard_stack
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _domainH _restartH _reasonH stackH _replayH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => stackH)

theorem ay_rrsg_guard_replay
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _restartH _reasonH _stackH replayH _tiebreakH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_rrsg_guard_tiebreak
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _restartH _reasonH _stackH _replayH tiebreakH _fallbackH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_rrsg_guard_fallback
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _restartH _reasonH _stackH _replayH _tiebreakH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_rrsg_guard_build
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _restartH _reasonH _stackH _replayH _tiebreakH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_rrsg_guard_validator
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _restartH _reasonH _stackH _replayH _tiebreakH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_rrsg_guard_audit
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_rrsg_guard variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _restartH _reasonH _stackH _replayH _tiebreakH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_rrsg_agreement_intro
    (domainMatch restartMatch reasonMatch stackMatch replayMatch tiebreakMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    domainMatch ->
    restartMatch ->
    reasonMatch ->
    stackMatch ->
    replayMatch ->
    tiebreakMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rrsg_agreement domainMatch restartMatch reasonMatch stackMatch
      replayMatch tiebreakMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_rrsg_guard_intro domainMatch restartMatch reasonMatch stackMatch
    replayMatch tiebreakMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_rrsg_accepted_stability_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_rrsg_accepted_stability guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_rrsg_conj_intro guardEvidence
      (ay_rrsg_conj agreementEvidence searchControlHint)
      guardH
      (ay_rrsg_conj_intro agreementEvidence searchControlHint agreementH hintH)

theorem ay_rrsg_accepted_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rrsg_accepted_stability guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  ay_rrsg_conj_left guardEvidence
    (ay_rrsg_conj agreementEvidence searchControlHint)

theorem ay_rrsg_accepted_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rrsg_accepted_stability guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_rrsg_conj_left agreementEvidence searchControlHint
      (ay_rrsg_conj_right guardEvidence
        (ay_rrsg_conj agreementEvidence searchControlHint) accepted)

theorem ay_rrsg_accepted_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rrsg_accepted_stability guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_rrsg_conj_right agreementEvidence searchControlHint
      (ay_rrsg_conj_right guardEvidence
        (ay_rrsg_conj agreementEvidence searchControlHint) accepted)

theorem ay_rrsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rrsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rrsg_conj_intro acceptedEvidence (ay_rrsg_conj outcome formulaTruth)
      acceptedH (ay_rrsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rrsg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rrsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_rrsg_conj_left acceptedEvidence (ay_rrsg_conj outcome formulaTruth)

theorem ay_rrsg_public_report_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rrsg_public_report acceptedEvidence outcome formulaTruth ->
    ay_rrsg_conj outcome formulaTruth :=
  fun report =>
    ay_rrsg_conj_right acceptedEvidence (ay_rrsg_conj outcome formulaTruth)
      report

theorem ay_rrsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rrsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rrsg_conj_right outcome formulaTruth
      (ay_rrsg_public_report_soundness acceptedEvidence outcome formulaTruth
        report)

theorem ay_rrsg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_rrsg_no_claim diagnostic fallbackPublic :=
  ay_rrsg_conj_intro diagnostic fallbackPublic

theorem ay_rrsg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_rrsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_rrsg_conj_right diagnostic fallbackPublic

theorem ay_rrsg_stability_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rrsg_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_rrsg_equisat_forward beforeFormula afterFormula

theorem ay_rrsg_stability_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_rrsg_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_rrsg_equisat_backward beforeFormula afterFormula

theorem ay_rrsg_accepted_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      searchControlHint : Prop) :
    ay_rrsg_equisat beforeFormula afterFormula ->
    ay_rrsg_accepted_stability guardEvidence agreementEvidence
      searchControlHint ->
    ay_rrsg_conj (beforeFormula -> afterFormula) searchControlHint :=
  fun eqsat accepted =>
    ay_rrsg_conj_intro (beforeFormula -> afterFormula) searchControlHint
      (ay_rrsg_equisat_forward beforeFormula afterFormula eqsat)
      (ay_rrsg_accepted_search_control guardEvidence agreementEvidence
        searchControlHint accepted)

theorem ay_rrsg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_rrsg_no_claim domainMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro domainMismatch fallbackPublic

theorem ay_rrsg_restart_mismatch_no_claim
    (restartMismatch fallbackPublic : Prop) :
    restartMismatch -> fallbackPublic ->
    ay_rrsg_no_claim restartMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro restartMismatch fallbackPublic

theorem ay_rrsg_reason_mismatch_no_claim
    (reasonMismatch fallbackPublic : Prop) :
    reasonMismatch -> fallbackPublic ->
    ay_rrsg_no_claim reasonMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro reasonMismatch fallbackPublic

theorem ay_rrsg_stack_mismatch_no_claim
    (stackMismatch fallbackPublic : Prop) :
    stackMismatch -> fallbackPublic ->
    ay_rrsg_no_claim stackMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro stackMismatch fallbackPublic

theorem ay_rrsg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_rrsg_no_claim replayMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_rrsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_rrsg_no_claim tiebreakMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_rrsg_fallback_mismatch_no_claim
    (fallbackMismatch fallbackPublic : Prop) :
    fallbackMismatch -> fallbackPublic ->
    ay_rrsg_no_claim fallbackMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro fallbackMismatch fallbackPublic

theorem ay_rrsg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_rrsg_no_claim buildMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_rrsg_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects -> fallbackPublic ->
    ay_rrsg_no_claim validatorRejects fallbackPublic :=
  ay_rrsg_no_claim_intro validatorRejects fallbackPublic

theorem ay_rrsg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_rrsg_no_claim auditMismatch fallbackPublic :=
  ay_rrsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_rrsg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_rrsg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_rrsg_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_rrsg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_rrsg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_rrsg_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_rrsg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth :
      Prop) :
    ay_rrsg_public_report
      (ay_rrsg_accepted_stability guardEvidence agreementEvidence
        searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_rrsg_accepted_guard guardEvidence agreementEvidence searchControlHint
      (ay_rrsg_public_report_accepted
        (ay_rrsg_accepted_stability guardEvidence agreementEvidence
          searchControlHint)
        outcome formulaTruth report)

theorem ay_rrsg_publication_requires_validator
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_rrsg_public_report
      (ay_rrsg_accepted_stability
        (ay_rrsg_guard variableDomainDigest restartEpochDigest
          reasonClauseLedger decisionStackDigest propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_rrsg_guard_validator variableDomainDigest restartEpochDigest
      reasonClauseLedger decisionStackDigest propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_rrsg_publication_requires_guard
        (ay_rrsg_guard variableDomainDigest restartEpochDigest
          reasonClauseLedger decisionStackDigest propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_rrsg_publication_requires_audit
    (variableDomainDigest restartEpochDigest reasonClauseLedger
      decisionStackDigest propagationReplay deterministicTiebreakManifest
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlHint outcome formulaTruth : Prop) :
    ay_rrsg_public_report
      (ay_rrsg_accepted_stability
        (ay_rrsg_guard variableDomainDigest restartEpochDigest
          reasonClauseLedger decisionStackDigest propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_rrsg_guard_audit variableDomainDigest restartEpochDigest
      reasonClauseLedger decisionStackDigest propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_rrsg_publication_requires_guard
        (ay_rrsg_guard variableDomainDigest restartEpochDigest
          reasonClauseLedger decisionStackDigest propagationReplay
          deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
          validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_rrsg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence -> satOutcome -> formulaTruth ->
    ay_rrsg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_rrsg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_rrsg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence -> unsatOutcome -> formulaTruth ->
    ay_rrsg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_rrsg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
