-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching score NaN/infinity/saturation guard skeleton for sequential-main
-- SAT-COMP branching. Score updates are search-control only when numeric
-- domain, finite witnesses, saturation policy, variable domain, tiebreak,
-- fallback, build, validator, and audit evidence agree with the public result.

def ay_snsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_snsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_snsg_conj (before -> after) (after -> before)

def ay_snsg_guard
    (scoreDomainManifest : Prop)
    (finiteNumberWitness : Prop)
    (saturationPolicy : Prop)
    (variableDomainManifest : Prop)
    (tiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (scoreDomainManifest ->
      finiteNumberWitness ->
      saturationPolicy ->
      variableDomainManifest ->
      tiebreakManifest ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_snsg_agreement
    (scoreDomainMatch : Prop)
    (finiteNumbers : Prop)
    (saturationMatch : Prop)
    (variableDomainMatch : Prop)
    (tiebreakMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_snsg_guard scoreDomainMatch finiteNumbers saturationMatch
    variableDomainMatch tiebreakMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

def ay_snsg_accepted_update
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (deterministicBranchOrder : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_snsg_conj guardEvidence
    (ay_snsg_conj agreementEvidence
      (ay_snsg_conj deterministicBranchOrder searchControlHint))

def ay_snsg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_snsg_conj acceptedEvidence (ay_snsg_conj outcome formulaTruth)

def ay_snsg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_snsg_conj diagnostic fallbackPublic

theorem ay_snsg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_snsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_snsg_conj_left (left : Prop) (right : Prop) :
    ay_snsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_snsg_conj_right (left : Prop) (right : Prop) :
    ay_snsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_snsg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_snsg_equisat before after :=
  fun forward backward =>
    ay_snsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_snsg_equisat_forward (before : Prop) (after : Prop) :
    ay_snsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_snsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_snsg_equisat_backward (before : Prop) (after : Prop) :
    ay_snsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_snsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_snsg_guard_intro
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    scoreDomainManifest ->
    finiteNumberWitness ->
    saturationPolicy ->
    variableDomainManifest ->
    tiebreakManifest ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun scoreH finiteH saturationH domainH tiebreakH fallbackH buildH
      validatorH auditH result make =>
    make scoreH finiteH saturationH domainH tiebreakH fallbackH buildH
      validatorH auditH

theorem ay_snsg_guard_score_domain
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    scoreDomainManifest :=
  fun guard =>
    guard scoreDomainManifest
      (fun scoreH _finiteH _satH _domainH _tieH _fallbackH _buildH
          _validatorH _auditH => scoreH)

theorem ay_snsg_guard_finite
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    finiteNumberWitness :=
  fun guard =>
    guard finiteNumberWitness
      (fun _scoreH finiteH _satH _domainH _tieH _fallbackH _buildH
          _validatorH _auditH => finiteH)

theorem ay_snsg_guard_saturation
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    saturationPolicy :=
  fun guard =>
    guard saturationPolicy
      (fun _scoreH _finiteH saturationH _domainH _tieH _fallbackH _buildH
          _validatorH _auditH => saturationH)

theorem ay_snsg_guard_variable_domain
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _scoreH _finiteH _satH domainH _tieH _fallbackH _buildH
          _validatorH _auditH => domainH)

theorem ay_snsg_guard_tiebreak
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _scoreH _finiteH _satH _domainH tiebreakH _fallbackH _buildH
          _validatorH _auditH => tiebreakH)

theorem ay_snsg_guard_fallback
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _scoreH _finiteH _satH _domainH _tieH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_snsg_guard_build
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _scoreH _finiteH _satH _domainH _tieH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_snsg_guard_validator
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _scoreH _finiteH _satH _domainH _tieH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_snsg_guard_audit
    (scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_snsg_guard scoreDomainManifest finiteNumberWitness saturationPolicy
      variableDomainManifest tiebreakManifest fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _scoreH _finiteH _satH _domainH _tieH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_snsg_agreement_intro
    (scoreDomainMatch finiteNumbers saturationMatch variableDomainMatch
      tiebreakMatch fallbackMatch buildMatch validatorAccepts
      auditMatch : Prop) :
    scoreDomainMatch ->
    finiteNumbers ->
    saturationMatch ->
    variableDomainMatch ->
    tiebreakMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_snsg_agreement scoreDomainMatch finiteNumbers saturationMatch
      variableDomainMatch tiebreakMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  ay_snsg_guard_intro scoreDomainMatch finiteNumbers saturationMatch
    variableDomainMatch tiebreakMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_snsg_accepted_update_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_snsg_conj_intro guardEvidence
      (ay_snsg_conj agreementEvidence
        (ay_snsg_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_snsg_conj_intro agreementEvidence
        (ay_snsg_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_snsg_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_snsg_accepted_update_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_snsg_conj_left guardEvidence
      (ay_snsg_conj agreementEvidence
        (ay_snsg_conj deterministicBranchOrder searchControlHint))
      accepted

theorem ay_snsg_accepted_update_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_snsg_conj_left agreementEvidence
      (ay_snsg_conj deterministicBranchOrder searchControlHint)
      (ay_snsg_conj_right guardEvidence
        (ay_snsg_conj agreementEvidence
          (ay_snsg_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_snsg_accepted_update_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_snsg_conj_left deterministicBranchOrder searchControlHint
      (ay_snsg_conj_right agreementEvidence
        (ay_snsg_conj deterministicBranchOrder searchControlHint)
        (ay_snsg_conj_right guardEvidence
          (ay_snsg_conj agreementEvidence
            (ay_snsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_snsg_accepted_update_hint
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_snsg_conj_right deterministicBranchOrder searchControlHint
      (ay_snsg_conj_right agreementEvidence
        (ay_snsg_conj deterministicBranchOrder searchControlHint)
        (ay_snsg_conj_right guardEvidence
          (ay_snsg_conj agreementEvidence
            (ay_snsg_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_snsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_snsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_snsg_conj_intro acceptedEvidence
      (ay_snsg_conj outcome formulaTruth)
      acceptedH (ay_snsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_snsg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_snsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_snsg_conj_left acceptedEvidence (ay_snsg_conj outcome formulaTruth)
      report

theorem ay_snsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_snsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_snsg_conj_right outcome formulaTruth
      (ay_snsg_conj_right acceptedEvidence
        (ay_snsg_conj outcome formulaTruth) report)

theorem ay_snsg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_snsg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_snsg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_snsg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_snsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_snsg_conj_right diagnostic fallbackPublic noClaim

theorem ay_snsg_nan_mismatch_no_claim
    (nanMismatch fallbackPublic : Prop) :
    nanMismatch -> fallbackPublic ->
    ay_snsg_no_claim nanMismatch fallbackPublic :=
  ay_snsg_no_claim_intro nanMismatch fallbackPublic

theorem ay_snsg_infinity_mismatch_no_claim
    (infinityMismatch fallbackPublic : Prop) :
    infinityMismatch -> fallbackPublic ->
    ay_snsg_no_claim infinityMismatch fallbackPublic :=
  ay_snsg_no_claim_intro infinityMismatch fallbackPublic

theorem ay_snsg_saturation_mismatch_no_claim
    (saturationMismatch fallbackPublic : Prop) :
    saturationMismatch -> fallbackPublic ->
    ay_snsg_no_claim saturationMismatch fallbackPublic :=
  ay_snsg_no_claim_intro saturationMismatch fallbackPublic

theorem ay_snsg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_snsg_no_claim domainMismatch fallbackPublic :=
  ay_snsg_no_claim_intro domainMismatch fallbackPublic

theorem ay_snsg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_snsg_no_claim tiebreakMismatch fallbackPublic :=
  ay_snsg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_snsg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_snsg_no_claim buildMismatch fallbackPublic :=
  ay_snsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_snsg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_snsg_no_claim validatorRejection fallbackPublic :=
  ay_snsg_no_claim_intro validatorRejection fallbackPublic

theorem ay_snsg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_snsg_no_claim auditMismatch fallbackPublic :=
  ay_snsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_snsg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_snsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_snsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_snsg_failed_score_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_snsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_snsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_snsg_accepted_update_is_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    searchControlHint :=
  ay_snsg_accepted_update_hint guardEvidence agreementEvidence
    deterministicBranchOrder searchControlHint

theorem ay_snsg_accepted_update_preserves_branch_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    deterministicBranchOrder :=
  ay_snsg_accepted_update_order guardEvidence agreementEvidence
    deterministicBranchOrder searchControlHint

theorem ay_snsg_accepted_update_preserves_public_soundness
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    (guardEvidence -> agreementEvidence -> deterministicBranchOrder ->
      outcome -> formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_snsg_accepted_update_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      (ay_snsg_accepted_update_agreement guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      (ay_snsg_accepted_update_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      outcomeH
      truthH

theorem ay_snsg_accepted_update_guides_sat
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      satOutcome satTruth : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_snsg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_snsg_public_report_intro guardEvidence satOutcome satTruth
      (ay_snsg_accepted_update_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      satH
      truthH

theorem ay_snsg_accepted_update_guides_unsat
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_snsg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_snsg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_snsg_accepted_update_guard guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)
      unsatH
      truthH

theorem ay_snsg_score_update_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_snsg_accepted_update guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint ->
    (searchControlHint -> deterministicBranchOrder -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> deterministicBranchOrder -> formulaAfter ->
      formulaBefore) ->
    ay_snsg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_snsg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_snsg_accepted_update_hint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted)
        (ay_snsg_accepted_update_order guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted))
      (backward
        (ay_snsg_accepted_update_hint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted)
        (ay_snsg_accepted_update_order guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint accepted))
