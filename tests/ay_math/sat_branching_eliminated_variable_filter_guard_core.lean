-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Eliminated-variable branch-candidate filter guard skeleton for
-- sequential-main SAT-COMP branching. Filtering eliminated variables is
-- search-control/interface safety only when live/eliminated manifests, heap,
-- tiebreak, fallback, build, validator, and audit evidence agree.

def ay_evfg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_evfg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_evfg_conj (before -> after) (after -> before)

def ay_evfg_guard
    (liveVariableManifest : Prop)
    (eliminatedVariableLedger : Prop)
    (decisionHeapDigest : Prop)
    (tiebreakWitness : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (liveVariableManifest ->
      eliminatedVariableLedger ->
      decisionHeapDigest ->
      tiebreakWitness ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_evfg_agreement
    (liveMatch : Prop)
    (eliminatedMatch : Prop)
    (heapMatch : Prop)
    (tiebreakMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_evfg_guard liveMatch eliminatedMatch heapMatch tiebreakMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_evfg_accepted_filter
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (liveBranchOrder : Prop)
    (interfaceSafetyHint : Prop) : Prop :=
  ay_evfg_conj guardEvidence
    (ay_evfg_conj agreementEvidence
      (ay_evfg_conj liveBranchOrder interfaceSafetyHint))

def ay_evfg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_evfg_conj acceptedEvidence (ay_evfg_conj outcome formulaTruth)

def ay_evfg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_evfg_conj diagnostic fallbackPublic

theorem ay_evfg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_evfg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_evfg_conj_left (left : Prop) (right : Prop) :
    ay_evfg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_evfg_conj_right (left : Prop) (right : Prop) :
    ay_evfg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_evfg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_evfg_equisat before after :=
  fun forward backward =>
    ay_evfg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_evfg_equisat_forward (before : Prop) (after : Prop) :
    ay_evfg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_evfg_conj_left (before -> after) (after -> before) eqsat

theorem ay_evfg_equisat_backward (before : Prop) (after : Prop) :
    ay_evfg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_evfg_conj_right (before -> after) (after -> before) eqsat

theorem ay_evfg_guard_intro
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    liveVariableManifest ->
    eliminatedVariableLedger ->
    decisionHeapDigest ->
    tiebreakWitness ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun liveH eliminatedH heapH tiebreakH fallbackH buildH validatorH auditH
      result make =>
    make liveH eliminatedH heapH tiebreakH fallbackH buildH validatorH auditH

theorem ay_evfg_guard_live
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    liveVariableManifest :=
  fun guard =>
    guard liveVariableManifest
      (fun liveH _eliminatedH _heapH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => liveH)

theorem ay_evfg_guard_eliminated
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    eliminatedVariableLedger :=
  fun guard =>
    guard eliminatedVariableLedger
      (fun _liveH eliminatedH _heapH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => eliminatedH)

theorem ay_evfg_guard_heap
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    decisionHeapDigest :=
  fun guard =>
    guard decisionHeapDigest
      (fun _liveH _eliminatedH heapH _tiebreakH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_evfg_guard_tiebreak
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    tiebreakWitness :=
  fun guard =>
    guard tiebreakWitness
      (fun _liveH _eliminatedH _heapH tiebreakH _fallbackH _buildH
          _validatorH _auditH => tiebreakH)

theorem ay_evfg_guard_fallback
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _liveH _eliminatedH _heapH _tiebreakH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_evfg_guard_build
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _liveH _eliminatedH _heapH _tiebreakH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_evfg_guard_validator
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _liveH _eliminatedH _heapH _tiebreakH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_evfg_guard_audit
    (liveVariableManifest eliminatedVariableLedger decisionHeapDigest
      tiebreakWitness fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_evfg_guard liveVariableManifest eliminatedVariableLedger
      decisionHeapDigest tiebreakWitness fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _liveH _eliminatedH _heapH _tiebreakH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_evfg_agreement_intro
    (liveMatch eliminatedMatch heapMatch tiebreakMatch fallbackMatch
      buildMatch validatorAccepts auditMatch : Prop) :
    liveMatch ->
    eliminatedMatch ->
    heapMatch ->
    tiebreakMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_evfg_agreement liveMatch eliminatedMatch heapMatch tiebreakMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_evfg_guard_intro liveMatch eliminatedMatch heapMatch tiebreakMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_evfg_accepted_filter_intro
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    liveBranchOrder ->
    interfaceSafetyHint ->
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint :=
  fun guardH agreementH orderH hintH =>
    ay_evfg_conj_intro guardEvidence
      (ay_evfg_conj agreementEvidence
        (ay_evfg_conj liveBranchOrder interfaceSafetyHint))
      guardH
      (ay_evfg_conj_intro agreementEvidence
        (ay_evfg_conj liveBranchOrder interfaceSafetyHint)
        agreementH
        (ay_evfg_conj_intro liveBranchOrder interfaceSafetyHint orderH
          hintH))

theorem ay_evfg_accepted_filter_guard
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    guardEvidence :=
  fun accepted =>
    ay_evfg_conj_left guardEvidence
      (ay_evfg_conj agreementEvidence
        (ay_evfg_conj liveBranchOrder interfaceSafetyHint))
      accepted

theorem ay_evfg_accepted_filter_agreement
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    agreementEvidence :=
  fun accepted =>
    ay_evfg_conj_left agreementEvidence
      (ay_evfg_conj liveBranchOrder interfaceSafetyHint)
      (ay_evfg_conj_right guardEvidence
        (ay_evfg_conj agreementEvidence
          (ay_evfg_conj liveBranchOrder interfaceSafetyHint))
        accepted)

theorem ay_evfg_accepted_filter_order
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    liveBranchOrder :=
  fun accepted =>
    ay_evfg_conj_left liveBranchOrder interfaceSafetyHint
      (ay_evfg_conj_right agreementEvidence
        (ay_evfg_conj liveBranchOrder interfaceSafetyHint)
        (ay_evfg_conj_right guardEvidence
          (ay_evfg_conj agreementEvidence
            (ay_evfg_conj liveBranchOrder interfaceSafetyHint))
          accepted))

theorem ay_evfg_accepted_filter_hint
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    interfaceSafetyHint :=
  fun accepted =>
    ay_evfg_conj_right liveBranchOrder interfaceSafetyHint
      (ay_evfg_conj_right agreementEvidence
        (ay_evfg_conj liveBranchOrder interfaceSafetyHint)
        (ay_evfg_conj_right guardEvidence
          (ay_evfg_conj agreementEvidence
            (ay_evfg_conj liveBranchOrder interfaceSafetyHint))
          accepted))

theorem ay_evfg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_evfg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_evfg_conj_intro acceptedEvidence
      (ay_evfg_conj outcome formulaTruth)
      acceptedH (ay_evfg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_evfg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_evfg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_evfg_conj_left acceptedEvidence (ay_evfg_conj outcome formulaTruth)
      report

theorem ay_evfg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_evfg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_evfg_conj_right outcome formulaTruth
      (ay_evfg_conj_right acceptedEvidence
        (ay_evfg_conj outcome formulaTruth) report)

theorem ay_evfg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_evfg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_evfg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_evfg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_evfg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_evfg_conj_right diagnostic fallbackPublic noClaim

theorem ay_evfg_live_mismatch_no_claim
    (liveMismatch fallbackPublic : Prop) :
    liveMismatch -> fallbackPublic ->
    ay_evfg_no_claim liveMismatch fallbackPublic :=
  ay_evfg_no_claim_intro liveMismatch fallbackPublic

theorem ay_evfg_eliminated_mismatch_no_claim
    (eliminatedMismatch fallbackPublic : Prop) :
    eliminatedMismatch -> fallbackPublic ->
    ay_evfg_no_claim eliminatedMismatch fallbackPublic :=
  ay_evfg_no_claim_intro eliminatedMismatch fallbackPublic

theorem ay_evfg_heap_mismatch_no_claim
    (heapMismatch fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic ->
    ay_evfg_no_claim heapMismatch fallbackPublic :=
  ay_evfg_no_claim_intro heapMismatch fallbackPublic

theorem ay_evfg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch -> fallbackPublic ->
    ay_evfg_no_claim tiebreakMismatch fallbackPublic :=
  ay_evfg_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_evfg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_evfg_no_claim buildMismatch fallbackPublic :=
  ay_evfg_no_claim_intro buildMismatch fallbackPublic

theorem ay_evfg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_evfg_no_claim validatorRejection fallbackPublic :=
  ay_evfg_no_claim_intro validatorRejection fallbackPublic

theorem ay_evfg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_evfg_no_claim auditMismatch fallbackPublic :=
  ay_evfg_no_claim_intro auditMismatch fallbackPublic

theorem ay_evfg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_evfg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_evfg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_evfg_failed_filter_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_evfg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_evfg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_evfg_accepted_filter_is_interface_safety
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    interfaceSafetyHint :=
  ay_evfg_accepted_filter_hint guardEvidence agreementEvidence liveBranchOrder
    interfaceSafetyHint

theorem ay_evfg_accepted_filter_preserves_live_branch_order
    (guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    liveBranchOrder :=
  ay_evfg_accepted_filter_order guardEvidence agreementEvidence liveBranchOrder
    interfaceSafetyHint

theorem ay_evfg_accepted_filter_preserves_public_soundness
    (guardEvidence agreementEvidence liveBranchOrder interfaceSafetyHint
      outcome formulaTruth publicSound : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    (guardEvidence -> agreementEvidence -> liveBranchOrder -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_evfg_accepted_filter_guard guardEvidence agreementEvidence
        liveBranchOrder interfaceSafetyHint accepted)
      (ay_evfg_accepted_filter_agreement guardEvidence agreementEvidence
        liveBranchOrder interfaceSafetyHint accepted)
      (ay_evfg_accepted_filter_order guardEvidence agreementEvidence
        liveBranchOrder interfaceSafetyHint accepted)
      outcomeH
      truthH

theorem ay_evfg_accepted_filter_guides_sat
    (guardEvidence agreementEvidence liveBranchOrder interfaceSafetyHint
      satOutcome satTruth : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    satOutcome ->
    satTruth ->
    ay_evfg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_evfg_public_report_intro guardEvidence satOutcome satTruth
      (ay_evfg_accepted_filter_guard guardEvidence agreementEvidence
        liveBranchOrder interfaceSafetyHint accepted)
      satH
      truthH

theorem ay_evfg_accepted_filter_guides_unsat
    (guardEvidence agreementEvidence liveBranchOrder interfaceSafetyHint
      unsatOutcome unsatTruth : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence
      liveBranchOrder interfaceSafetyHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_evfg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_evfg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_evfg_accepted_filter_guard guardEvidence agreementEvidence
        liveBranchOrder interfaceSafetyHint accepted)
      unsatH
      truthH

theorem ay_evfg_filter_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint : Prop) :
    ay_evfg_accepted_filter guardEvidence agreementEvidence liveBranchOrder
      interfaceSafetyHint ->
    (interfaceSafetyHint -> liveBranchOrder -> formulaBefore ->
      formulaAfter) ->
    (interfaceSafetyHint -> liveBranchOrder -> formulaAfter ->
      formulaBefore) ->
    ay_evfg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_evfg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_evfg_accepted_filter_hint guardEvidence agreementEvidence
          liveBranchOrder interfaceSafetyHint accepted)
        (ay_evfg_accepted_filter_order guardEvidence agreementEvidence
          liveBranchOrder interfaceSafetyHint accepted))
      (backward
        (ay_evfg_accepted_filter_hint guardEvidence agreementEvidence
          liveBranchOrder interfaceSafetyHint accepted)
        (ay_evfg_accepted_filter_order guardEvidence agreementEvidence
          liveBranchOrder interfaceSafetyHint accepted))
