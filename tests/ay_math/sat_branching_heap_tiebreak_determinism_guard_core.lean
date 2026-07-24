-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching heap tiebreak determinism guard skeleton for sequential-main
-- SAT-COMP branching. Heap pops are search-control only when heap digest,
-- equal-score tiebreaks, variable id ordering, live domain, fallback, build,
-- validator, and audit evidence agree with the public result.

def ay_htdg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_htdg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_htdg_conj (before -> after) (after -> before)

def ay_htdg_guard
    (heapDigest : Prop)
    (tiebreakManifest : Prop)
    (variableIdOrderingWitness : Prop)
    (liveVariableDomainManifest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (heapDigest ->
      tiebreakManifest ->
      variableIdOrderingWitness ->
      liveVariableDomainManifest ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_htdg_agreement
    (heapMatch : Prop)
    (tiebreakMatch : Prop)
    (orderMatch : Prop)
    (domainMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_htdg_guard heapMatch tiebreakMatch orderMatch domainMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_htdg_accepted_pop
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_htdg_conj guardEvidence
    (ay_htdg_conj agreementEvidence
      (ay_htdg_conj deterministicBranchOrder searchControlHint))

def ay_htdg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_htdg_conj acceptedEvidence (ay_htdg_conj outcome formulaTruth)

def ay_htdg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_htdg_conj diagnostic fallbackPublic

theorem ay_htdg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_htdg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_htdg_conj_left (left : Prop) (right : Prop) :
    ay_htdg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_htdg_conj_right (left : Prop) (right : Prop) :
    ay_htdg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_htdg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_htdg_equisat before after :=
  fun forward backward =>
    ay_htdg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_htdg_equisat_forward (before : Prop) (after : Prop) :
    ay_htdg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_htdg_conj_left (before -> after) (after -> before) eqsat

theorem ay_htdg_equisat_backward (before : Prop) (after : Prop) :
    ay_htdg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_htdg_conj_right (before -> after) (after -> before) eqsat

theorem ay_htdg_guard_intro
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    heapDigest ->
    tiebreakManifest ->
    variableIdOrderingWitness ->
    liveVariableDomainManifest ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun heapH tiebreakH orderH domainH fallbackH buildH validatorH auditH
      result make =>
    make heapH tiebreakH orderH domainH fallbackH buildH validatorH auditH

theorem ay_htdg_guard_heap
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    heapDigest :=
  fun guard =>
    guard heapDigest
      (fun heapH _tiebreakH _orderH _domainH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_htdg_guard_tiebreak
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _heapH tiebreakH _orderH _domainH _fallbackH _buildH
          _validatorH _auditH => tiebreakH)

theorem ay_htdg_guard_order
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    variableIdOrderingWitness :=
  fun guard =>
    guard variableIdOrderingWitness
      (fun _heapH _tiebreakH orderH _domainH _fallbackH _buildH
          _validatorH _auditH => orderH)

theorem ay_htdg_guard_domain
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    liveVariableDomainManifest :=
  fun guard =>
    guard liveVariableDomainManifest
      (fun _heapH _tiebreakH _orderH domainH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_htdg_guard_fallback
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _heapH _tiebreakH _orderH _domainH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_htdg_guard_build
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _heapH _tiebreakH _orderH _domainH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_htdg_guard_validator
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _heapH _tiebreakH _orderH _domainH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_htdg_guard_audit
    (heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_htdg_guard heapDigest tiebreakManifest variableIdOrderingWitness
      liveVariableDomainManifest fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _heapH _tiebreakH _orderH _domainH _fallbackH _buildH _validatorH
          auditH => auditH)

theorem ay_htdg_agreement_intro
    (heapMatch tiebreakMatch orderMatch domainMatch fallbackMatch buildMatch
      validatorAccepts auditMatch : Prop) :
    heapMatch ->
    tiebreakMatch ->
    orderMatch ->
    domainMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_htdg_agreement heapMatch tiebreakMatch orderMatch domainMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_htdg_guard_intro heapMatch tiebreakMatch orderMatch domainMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_htdg_accepted_pop_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_htdg_conj_intro guardEvidence
      (ay_htdg_conj agreementEvidence
        (ay_htdg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_htdg_conj_intro agreementEvidence
        (ay_htdg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_htdg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_htdg_accepted_pop_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_htdg_conj_left guardEvidence
      (ay_htdg_conj agreementEvidence
        (ay_htdg_conj deterministicBranchOrder searchControlHint))
      accepted

theorem ay_htdg_accepted_pop_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_htdg_conj_left agreementEvidence
      (ay_htdg_conj deterministicBranchOrder searchControlHint)
      (ay_htdg_conj_right guardEvidence
        (ay_htdg_conj agreementEvidence
          (ay_htdg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_htdg_accepted_pop_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_htdg_conj_left deterministicBranchOrder searchControlHint
      (ay_htdg_conj_right agreementEvidence
        (ay_htdg_conj deterministicBranchOrder searchControlHint)
        (ay_htdg_conj_right guardEvidence
          (ay_htdg_conj agreementEvidence
            (ay_htdg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_htdg_accepted_pop_hint
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_htdg_conj_right deterministicBranchOrder searchControlHint
      (ay_htdg_conj_right agreementEvidence
        (ay_htdg_conj deterministicBranchOrder searchControlHint)
        (ay_htdg_conj_right guardEvidence
          (ay_htdg_conj agreementEvidence
            (ay_htdg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_htdg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_htdg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_htdg_conj_intro acceptedEvidence
      (ay_htdg_conj outcome formulaTruth)
      acceptedH (ay_htdg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_htdg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_htdg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_htdg_conj_left acceptedEvidence (ay_htdg_conj outcome formulaTruth)
      report

theorem ay_htdg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_htdg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_htdg_conj_right outcome formulaTruth
      (ay_htdg_conj_right acceptedEvidence
        (ay_htdg_conj outcome formulaTruth) report)

theorem ay_htdg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_htdg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_htdg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_htdg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_htdg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_htdg_conj_right diagnostic fallbackPublic noClaim

theorem ay_htdg_heap_mismatch_no_claim
    (heapMismatch fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_htdg_no_claim heapMismatch fallbackPublic :=
  ay_htdg_no_claim_intro heapMismatch fallbackPublic

theorem ay_htdg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_htdg_no_claim tiebreakMismatch fallbackPublic :=
  ay_htdg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_htdg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch -> fallbackPublic ->
    ay_htdg_no_claim orderMismatch fallbackPublic :=
  ay_htdg_no_claim_intro orderMismatch fallbackPublic

theorem ay_htdg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_htdg_no_claim domainMismatch fallbackPublic :=
  ay_htdg_no_claim_intro domainMismatch fallbackPublic

theorem ay_htdg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_htdg_no_claim buildMismatch fallbackPublic :=
  ay_htdg_no_claim_intro buildMismatch fallbackPublic

theorem ay_htdg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_htdg_no_claim validatorRejection fallbackPublic :=
  ay_htdg_no_claim_intro validatorRejection fallbackPublic

theorem ay_htdg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_htdg_no_claim auditMismatch fallbackPublic :=
  ay_htdg_no_claim_intro auditMismatch fallbackPublic

theorem ay_htdg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_htdg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_htdg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_htdg_failed_tiebreak_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_htdg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_htdg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_htdg_accepted_pop_is_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  ay_htdg_accepted_pop_hint guardEvidence agreementEvidence
    deterministicBranchOrder searchControlHint

theorem ay_htdg_accepted_pop_preserves_branch_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  ay_htdg_accepted_pop_order guardEvidence agreementEvidence
    deterministicBranchOrder searchControlHint

theorem ay_htdg_accepted_pop_preserves_public_soundness
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    (guardEvidence -> agreementEvidence -> deterministicBranchOrder ->
      outcome -> formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_htdg_accepted_pop_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      (ay_htdg_accepted_pop_agreement guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      (ay_htdg_accepted_pop_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      outcomeH
      truthH

theorem ay_htdg_accepted_pop_guides_sat
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      satOutcome satTruth : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_htdg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_htdg_public_report_intro guardEvidence satOutcome satTruth
      (ay_htdg_accepted_pop_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      satH
      truthH

theorem ay_htdg_accepted_pop_guides_unsat
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_htdg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_htdg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_htdg_accepted_pop_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      unsatH
      truthH

theorem ay_htdg_heap_tiebreak_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_htdg_accepted_pop guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    (searchControlHint -> deterministicBranchOrder -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> deterministicBranchOrder -> formulaAfter ->
      formulaBefore) ->
    ay_htdg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_htdg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_htdg_accepted_pop_hint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted)
        (ay_htdg_accepted_pop_order guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted))
      (backward
        (ay_htdg_accepted_pop_hint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted)
        (ay_htdg_accepted_pop_order guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted))
