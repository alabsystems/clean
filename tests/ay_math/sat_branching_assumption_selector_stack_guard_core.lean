-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption selector stack guard skeleton for sequential-main SAT-COMP
-- incremental-style interfaces. Selector handling is search-control/interface
-- bookkeeping only when manifest, selector domain, stack, activation, replay,
-- fallback, build, validator, and audit evidence agree.

def ay_assg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_assg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_assg_conj (before -> after) (after -> before)

def ay_assg_guard
    (assumptionManifest : Prop)
    (selectorLiteralDomainProof : Prop)
    (decisionStackDigest : Prop)
    (activationLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (assumptionManifest ->
      selectorLiteralDomainProof ->
      decisionStackDigest ->
      activationLedger ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_assg_agreement
    (manifestMatch : Prop)
    (domainMatch : Prop)
    (stackMatch : Prop)
    (activationMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_assg_guard manifestMatch domainMatch stackMatch activationMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_assg_accepted_selector
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (interfaceBookkeeping : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_assg_conj guardEvidence
    (ay_assg_conj agreementEvidence
      (ay_assg_conj interfaceBookkeeping searchControlHint))

def ay_assg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_assg_conj acceptedEvidence (ay_assg_conj outcome formulaTruth)

def ay_assg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_assg_conj diagnostic fallbackPublic

theorem ay_assg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_assg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_assg_conj_left (left : Prop) (right : Prop) :
    ay_assg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_assg_conj_right (left : Prop) (right : Prop) :
    ay_assg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_assg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_assg_equisat before after :=
  fun forward backward =>
    ay_assg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_assg_equisat_forward (before : Prop) (after : Prop) :
    ay_assg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_assg_conj_left (before -> after) (after -> before) eqsat

theorem ay_assg_equisat_backward (before : Prop) (after : Prop) :
    ay_assg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_assg_conj_right (before -> after) (after -> before) eqsat

theorem ay_assg_guard_intro
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    assumptionManifest ->
    selectorLiteralDomainProof ->
    decisionStackDigest ->
    activationLedger ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript :=
  fun manifestH domainH stackH activationH replayH fallbackH buildH
      validatorH auditH result make =>
    make manifestH domainH stackH activationH replayH fallbackH buildH
      validatorH auditH

theorem ay_assg_guard_manifest
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    assumptionManifest :=
  fun guard =>
    guard assumptionManifest
      (fun manifestH _domainH _stackH _activationH _replayH _fallbackH
          _buildH _validatorH _auditH => manifestH)

theorem ay_assg_guard_domain
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    selectorLiteralDomainProof :=
  fun guard =>
    guard selectorLiteralDomainProof
      (fun _manifestH domainH _stackH _activationH _replayH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_assg_guard_stack
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _manifestH _domainH stackH _activationH _replayH _fallbackH
          _buildH _validatorH _auditH => stackH)

theorem ay_assg_guard_activation
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    activationLedger :=
  fun guard =>
    guard activationLedger
      (fun _manifestH _domainH _stackH activationH _replayH _fallbackH
          _buildH _validatorH _auditH => activationH)

theorem ay_assg_guard_replay
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _manifestH _domainH _stackH _activationH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_assg_guard_fallback
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _manifestH _domainH _stackH _activationH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_assg_guard_build
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _manifestH _domainH _stackH _activationH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_assg_guard_validator
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _manifestH _domainH _stackH _activationH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_assg_guard_audit
    (assumptionManifest selectorLiteralDomainProof decisionStackDigest
      activationLedger propagationReplay fallbackBaseline buildEvidence
      validatorGate auditTranscript : Prop) :
    ay_assg_guard assumptionManifest selectorLiteralDomainProof
      decisionStackDigest activationLedger propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _manifestH _domainH _stackH _activationH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_assg_agreement_intro
    (manifestMatch domainMatch stackMatch activationMatch replayMatch
      fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    manifestMatch ->
    domainMatch ->
    stackMatch ->
    activationMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_assg_agreement manifestMatch domainMatch stackMatch activationMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_assg_guard_intro manifestMatch domainMatch stackMatch activationMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_assg_accepted_selector_intro
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    interfaceBookkeeping ->
    searchControlHint ->
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint :=
  fun guardH agreementH bookkeepingH hintH =>
    ay_assg_conj_intro guardEvidence
      (ay_assg_conj agreementEvidence
        (ay_assg_conj interfaceBookkeeping searchControlHint))
      guardH
      (ay_assg_conj_intro agreementEvidence
        (ay_assg_conj interfaceBookkeeping searchControlHint)
        agreementH
        (ay_assg_conj_intro interfaceBookkeeping searchControlHint
          bookkeepingH hintH))

theorem ay_assg_accepted_selector_guard
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_assg_conj_left guardEvidence
      (ay_assg_conj agreementEvidence
        (ay_assg_conj interfaceBookkeeping searchControlHint))
      accepted

theorem ay_assg_accepted_selector_agreement
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_assg_conj_left agreementEvidence
      (ay_assg_conj interfaceBookkeeping searchControlHint)
      (ay_assg_conj_right guardEvidence
        (ay_assg_conj agreementEvidence
          (ay_assg_conj interfaceBookkeeping searchControlHint))
        accepted)

theorem ay_assg_accepted_selector_bookkeeping
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    interfaceBookkeeping :=
  fun accepted =>
    ay_assg_conj_left interfaceBookkeeping searchControlHint
      (ay_assg_conj_right agreementEvidence
        (ay_assg_conj interfaceBookkeeping searchControlHint)
        (ay_assg_conj_right guardEvidence
          (ay_assg_conj agreementEvidence
            (ay_assg_conj interfaceBookkeeping searchControlHint))
          accepted))

theorem ay_assg_accepted_selector_hint
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_assg_conj_right interfaceBookkeeping searchControlHint
      (ay_assg_conj_right agreementEvidence
        (ay_assg_conj interfaceBookkeeping searchControlHint)
        (ay_assg_conj_right guardEvidence
          (ay_assg_conj agreementEvidence
            (ay_assg_conj interfaceBookkeeping searchControlHint))
          accepted))

theorem ay_assg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_assg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_assg_conj_intro acceptedEvidence
      (ay_assg_conj outcome formulaTruth)
      acceptedH (ay_assg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_assg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_assg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_assg_conj_left acceptedEvidence (ay_assg_conj outcome formulaTruth)
      report

theorem ay_assg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_assg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_assg_conj_right outcome formulaTruth
      (ay_assg_conj_right acceptedEvidence
        (ay_assg_conj outcome formulaTruth) report)

theorem ay_assg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_assg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_assg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_assg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_assg_conj_right diagnostic fallbackPublic noClaim

theorem ay_assg_manifest_mismatch_no_claim
    (manifestMismatch fallbackPublic : Prop) :
    manifestMismatch -> fallbackPublic ->
    ay_assg_no_claim manifestMismatch fallbackPublic :=
  ay_assg_no_claim_intro manifestMismatch fallbackPublic

theorem ay_assg_domain_mismatch_no_claim
    (domainMismatch fallbackPublic : Prop) :
    domainMismatch -> fallbackPublic ->
    ay_assg_no_claim domainMismatch fallbackPublic :=
  ay_assg_no_claim_intro domainMismatch fallbackPublic

theorem ay_assg_stack_mismatch_no_claim
    (stackMismatch fallbackPublic : Prop) :
    stackMismatch -> fallbackPublic ->
    ay_assg_no_claim stackMismatch fallbackPublic :=
  ay_assg_no_claim_intro stackMismatch fallbackPublic

theorem ay_assg_activation_mismatch_no_claim
    (activationMismatch fallbackPublic : Prop) :
    activationMismatch -> fallbackPublic ->
    ay_assg_no_claim activationMismatch fallbackPublic :=
  ay_assg_no_claim_intro activationMismatch fallbackPublic

theorem ay_assg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_assg_no_claim replayMismatch fallbackPublic :=
  ay_assg_no_claim_intro replayMismatch fallbackPublic

theorem ay_assg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_assg_no_claim buildMismatch fallbackPublic :=
  ay_assg_no_claim_intro buildMismatch fallbackPublic

theorem ay_assg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_assg_no_claim validatorRejection fallbackPublic :=
  ay_assg_no_claim_intro validatorRejection fallbackPublic

theorem ay_assg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_assg_no_claim auditMismatch fallbackPublic :=
  ay_assg_no_claim_intro auditMismatch fallbackPublic

theorem ay_assg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_assg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_assg_failed_selector_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_assg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_assg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_assg_accepted_selector_is_interface_bookkeeping
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    interfaceBookkeeping :=
  ay_assg_accepted_selector_bookkeeping guardEvidence agreementEvidence
    interfaceBookkeeping searchControlHint

theorem ay_assg_accepted_selector_is_search_control
    (guardEvidence agreementEvidence interfaceBookkeeping
      searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    searchControlHint :=
  ay_assg_accepted_selector_hint guardEvidence agreementEvidence
    interfaceBookkeeping searchControlHint

theorem ay_assg_accepted_selector_preserves_public_soundness
    (guardEvidence agreementEvidence interfaceBookkeeping searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    (guardEvidence -> agreementEvidence -> interfaceBookkeeping -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_assg_accepted_selector_guard guardEvidence agreementEvidence
        interfaceBookkeeping searchControlHint accepted)
      (ay_assg_accepted_selector_agreement guardEvidence agreementEvidence
        interfaceBookkeeping searchControlHint accepted)
      (ay_assg_accepted_selector_bookkeeping guardEvidence agreementEvidence
        interfaceBookkeeping searchControlHint accepted)
      outcomeH
      truthH

theorem ay_assg_accepted_selector_guides_sat
    (guardEvidence agreementEvidence interfaceBookkeeping searchControlHint
      satOutcome satTruth : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_assg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_assg_public_report_intro guardEvidence satOutcome satTruth
      (ay_assg_accepted_selector_guard guardEvidence agreementEvidence
        interfaceBookkeeping searchControlHint accepted)
      satH
      truthH

theorem ay_assg_accepted_selector_guides_unsat
    (guardEvidence agreementEvidence interfaceBookkeeping searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_assg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_assg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_assg_accepted_selector_guard guardEvidence agreementEvidence
        interfaceBookkeeping searchControlHint accepted)
      unsatH
      truthH

theorem ay_assg_selector_handling_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint : Prop) :
    ay_assg_accepted_selector guardEvidence agreementEvidence
      interfaceBookkeeping searchControlHint ->
    (interfaceBookkeeping -> searchControlHint -> formulaBefore ->
      formulaAfter) ->
    (interfaceBookkeeping -> searchControlHint -> formulaAfter ->
      formulaBefore) ->
    ay_assg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_assg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_assg_accepted_selector_bookkeeping guardEvidence agreementEvidence
          interfaceBookkeeping searchControlHint accepted)
        (ay_assg_accepted_selector_hint guardEvidence agreementEvidence
          interfaceBookkeeping searchControlHint accepted))
      (backward
        (ay_assg_accepted_selector_bookkeeping guardEvidence agreementEvidence
          interfaceBookkeeping searchControlHint accepted)
        (ay_assg_accepted_selector_hint guardEvidence agreementEvidence
          interfaceBookkeeping searchControlHint accepted))
