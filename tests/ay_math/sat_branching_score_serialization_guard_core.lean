-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision score serialization/deserialization guard skeleton for
-- sequential-main SAT-COMP branching. Score reload is search-control only when
-- digest, encoding, domain, tiebreak, ordering, fallback, build, validator,
-- and audit evidence agree with the checked public result.

def ay_sszg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sszg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_sszg_conj (before -> after) (after -> before)

def ay_sszg_guard
    (scoreFileDigest : Prop)
    (encodingPolicy : Prop)
    (variableDomainManifest : Prop)
    (tiebreakManifest : Prop)
    (restoredOrderingWitness : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (scoreFileDigest ->
      encodingPolicy ->
      variableDomainManifest ->
      tiebreakManifest ->
      restoredOrderingWitness ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_sszg_agreement
    (digestMatch : Prop)
    (encodingMatch : Prop)
    (domainMatch : Prop)
    (tiebreakMatch : Prop)
    (orderRestored : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_sszg_guard digestMatch encodingMatch domainMatch tiebreakMatch
    orderRestored fallbackMatch buildMatch validatorAccepts auditMatch

def ay_sszg_accepted_reload
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchOrderRelation : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_sszg_conj guardEvidence
    (ay_sszg_conj agreementEvidence
      (ay_sszg_conj branchOrderRelation searchControlHint))

def ay_sszg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_sszg_conj acceptedEvidence (ay_sszg_conj outcome formulaTruth)

def ay_sszg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_sszg_conj diagnostic fallbackPublic

theorem ay_sszg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_sszg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_sszg_conj_left (left : Prop) (right : Prop) :
    ay_sszg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_sszg_conj_right (left : Prop) (right : Prop) :
    ay_sszg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_sszg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_sszg_equisat before after :=
  fun forward backward =>
    ay_sszg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_sszg_equisat_forward (before : Prop) (after : Prop) :
    ay_sszg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_sszg_conj_left (before -> after) (after -> before) eqsat

theorem ay_sszg_equisat_backward (before : Prop) (after : Prop) :
    ay_sszg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_sszg_conj_right (before -> after) (after -> before) eqsat

theorem ay_sszg_guard_intro
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    scoreFileDigest ->
    encodingPolicy ->
    variableDomainManifest ->
    tiebreakManifest ->
    restoredOrderingWitness ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun digestH encodingH domainH tiebreakH orderH fallbackH buildH validatorH
      auditH result make =>
    make digestH encodingH domainH tiebreakH orderH fallbackH buildH
      validatorH auditH

theorem ay_sszg_guard_digest
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    scoreFileDigest :=
  fun guard =>
    guard scoreFileDigest
      (fun digestH _encodingH _domainH _tiebreakH _orderH _fallbackH
          _buildH _validatorH _auditH => digestH)

theorem ay_sszg_guard_encoding
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    encodingPolicy :=
  fun guard =>
    guard encodingPolicy
      (fun _digestH encodingH _domainH _tiebreakH _orderH _fallbackH
          _buildH _validatorH _auditH => encodingH)

theorem ay_sszg_guard_domain
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    variableDomainManifest :=
  fun guard =>
    guard variableDomainManifest
      (fun _digestH _encodingH domainH _tiebreakH _orderH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_sszg_guard_tiebreak
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _digestH _encodingH _domainH tiebreakH _orderH _fallbackH
          _buildH _validatorH _auditH => tiebreakH)

theorem ay_sszg_guard_order
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    restoredOrderingWitness :=
  fun guard =>
    guard restoredOrderingWitness
      (fun _digestH _encodingH _domainH _tiebreakH orderH _fallbackH
          _buildH _validatorH _auditH => orderH)

theorem ay_sszg_guard_fallback
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _digestH _encodingH _domainH _tiebreakH _orderH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_sszg_guard_build
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _digestH _encodingH _domainH _tiebreakH _orderH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_sszg_guard_validator
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _digestH _encodingH _domainH _tiebreakH _orderH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_sszg_guard_audit
    (scoreFileDigest encodingPolicy variableDomainManifest tiebreakManifest
      restoredOrderingWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_sszg_guard scoreFileDigest encodingPolicy variableDomainManifest
      tiebreakManifest restoredOrderingWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _digestH _encodingH _domainH _tiebreakH _orderH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_sszg_agreement_intro
    (digestMatch encodingMatch domainMatch tiebreakMatch orderRestored
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    digestMatch ->
    encodingMatch ->
    domainMatch ->
    tiebreakMatch ->
    orderRestored ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_sszg_agreement digestMatch encodingMatch domainMatch tiebreakMatch
      orderRestored fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_sszg_guard_intro digestMatch encodingMatch domainMatch tiebreakMatch
    orderRestored fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_sszg_accepted_reload_intro
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchOrderRelation ->
    searchControlHint ->
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_sszg_conj_intro guardEvidence
      (ay_sszg_conj agreementEvidence
        (ay_sszg_conj branchOrderRelation searchControlHint))
      guardH
      (ay_sszg_conj_intro agreementEvidence
        (ay_sszg_conj branchOrderRelation searchControlHint)
        agreementH
        (ay_sszg_conj_intro branchOrderRelation searchControlHint orderH
          hintH))

theorem ay_sszg_accepted_reload_guard
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_sszg_conj_left guardEvidence
      (ay_sszg_conj agreementEvidence
        (ay_sszg_conj branchOrderRelation searchControlHint))
      accepted

theorem ay_sszg_accepted_reload_agreement
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_sszg_conj_left agreementEvidence
      (ay_sszg_conj branchOrderRelation searchControlHint)
      (ay_sszg_conj_right guardEvidence
        (ay_sszg_conj agreementEvidence
          (ay_sszg_conj branchOrderRelation searchControlHint))
        accepted)

theorem ay_sszg_accepted_reload_order
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  fun accepted =>
    ay_sszg_conj_left branchOrderRelation searchControlHint
      (ay_sszg_conj_right agreementEvidence
        (ay_sszg_conj branchOrderRelation searchControlHint)
        (ay_sszg_conj_right guardEvidence
          (ay_sszg_conj agreementEvidence
            (ay_sszg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_sszg_accepted_reload_hint
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_sszg_conj_right branchOrderRelation searchControlHint
      (ay_sszg_conj_right agreementEvidence
        (ay_sszg_conj branchOrderRelation searchControlHint)
        (ay_sszg_conj_right guardEvidence
          (ay_sszg_conj agreementEvidence
            (ay_sszg_conj branchOrderRelation searchControlHint))
          accepted))

theorem ay_sszg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_sszg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_sszg_conj_intro acceptedEvidence
      (ay_sszg_conj outcome formulaTruth)
      acceptedH (ay_sszg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_sszg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sszg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_sszg_conj_left acceptedEvidence (ay_sszg_conj outcome formulaTruth)
      report

theorem ay_sszg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_sszg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_sszg_conj_right outcome formulaTruth
      (ay_sszg_conj_right acceptedEvidence
        (ay_sszg_conj outcome formulaTruth) report)

theorem ay_sszg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_sszg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_sszg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_sszg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_sszg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_sszg_conj_right diagnostic fallbackPublic noClaim

theorem ay_sszg_digest_mismatch_no_claim
    (digestMismatch fallbackPublic : Prop) :
    digestMismatch -> fallbackPublic ->
    ay_sszg_no_claim digestMismatch fallbackPublic :=
  ay_sszg_no_claim_intro digestMismatch fallbackPublic

theorem ay_sszg_encoding_mismatch_no_claim
    (encodingMismatch fallbackPublic : Prop) :
    encodingMismatch -> fallbackPublic ->
    ay_sszg_no_claim encodingMismatch fallbackPublic :=
  ay_sszg_no_claim_intro encodingMismatch fallbackPublic

theorem ay_sszg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_sszg_no_claim domainMismatch fallbackPublic :=
  ay_sszg_no_claim_intro domainMismatch fallbackPublic

theorem ay_sszg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_sszg_no_claim tiebreakMismatch fallbackPublic :=
  ay_sszg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_sszg_order_mismatch_no_claim
    (orderMismatch fallbackPublic : Prop) :
    orderMismatch -> fallbackPublic ->
    ay_sszg_no_claim orderMismatch fallbackPublic :=
  ay_sszg_no_claim_intro orderMismatch fallbackPublic

theorem ay_sszg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_sszg_no_claim buildMismatch fallbackPublic :=
  ay_sszg_no_claim_intro buildMismatch fallbackPublic

theorem ay_sszg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_sszg_no_claim validatorRejection fallbackPublic :=
  ay_sszg_no_claim_intro validatorRejection fallbackPublic

theorem ay_sszg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_sszg_no_claim auditMismatch fallbackPublic :=
  ay_sszg_no_claim_intro auditMismatch fallbackPublic

theorem ay_sszg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_sszg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_sszg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_sszg_failed_score_serialization_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_sszg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_sszg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_sszg_accepted_reload_is_search_control
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    searchControlHint :=
  ay_sszg_accepted_reload_hint guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_sszg_accepted_reload_preserves_branch_order
    (guardEvidence agreementEvidence branchOrderRelation
      searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    branchOrderRelation :=
  ay_sszg_accepted_reload_order guardEvidence agreementEvidence
    branchOrderRelation searchControlHint

theorem ay_sszg_accepted_reload_preserves_public_soundness
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (guardEvidence -> agreementEvidence -> branchOrderRelation -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_sszg_accepted_reload_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_sszg_accepted_reload_agreement guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      (ay_sszg_accepted_reload_order guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      outcomeH
      truthH

theorem ay_sszg_accepted_reload_guides_sat
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      satOutcome satTruth : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_sszg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_sszg_public_report_intro guardEvidence satOutcome satTruth
      (ay_sszg_accepted_reload_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      satH
      truthH

theorem ay_sszg_accepted_reload_guides_unsat
    (guardEvidence agreementEvidence branchOrderRelation searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_sszg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_sszg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_sszg_accepted_reload_guard guardEvidence agreementEvidence
        branchOrderRelation searchControlHint accepted)
      unsatH
      truthH

theorem ay_sszg_score_reload_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      branchOrderRelation searchControlHint : Prop) :
    ay_sszg_accepted_reload guardEvidence agreementEvidence
      branchOrderRelation searchControlHint ->
    (searchControlHint -> branchOrderRelation -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> branchOrderRelation -> formulaAfter ->
      formulaBefore) ->
    ay_sszg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_sszg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_sszg_accepted_reload_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_sszg_accepted_reload_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
      (backward
        (ay_sszg_accepted_reload_hint guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted)
        (ay_sszg_accepted_reload_order guardEvidence agreementEvidence
          branchOrderRelation searchControlHint accepted))
