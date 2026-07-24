-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Luby/geometric restart sequence guard skeleton for sequential-main SAT-COMP.
-- Restart sequence use is search-control only when sequence, counter, overflow,
-- replay, fallback, build, validator, and audit evidence agree with the
-- checked public result.

def ay_lrsg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_lrsg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_lrsg_conj (before -> after) (after -> before)

def ay_lrsg_guard
    (sequenceManifest : Prop)
    (indexCounterEpochLedger : Prop)
    (overflowPolicy : Prop)
    (conflictWindowReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (sequenceManifest ->
      indexCounterEpochLedger ->
      overflowPolicy ->
      conflictWindowReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_lrsg_agreement
    (sequenceMatch : Prop)
    (indexCounterMatch : Prop)
    (overflowMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_lrsg_guard sequenceMatch indexCounterMatch overflowMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_lrsg_accepted_sequence
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_lrsg_conj guardEvidence
    (ay_lrsg_conj agreementEvidence searchControlHint)

def ay_lrsg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_lrsg_conj acceptedEvidence (ay_lrsg_conj outcome formulaTruth)

def ay_lrsg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_lrsg_conj diagnostic fallbackPublic

theorem ay_lrsg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_lrsg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_lrsg_conj_left (left : Prop) (right : Prop) :
    ay_lrsg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_lrsg_conj_right (left : Prop) (right : Prop) :
    ay_lrsg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_lrsg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_lrsg_equisat before after :=
  fun forward backward =>
    ay_lrsg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_lrsg_equisat_forward (before : Prop) (after : Prop) :
    ay_lrsg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_lrsg_conj_left (before -> after) (after -> before) eqsat

theorem ay_lrsg_equisat_backward (before : Prop) (after : Prop) :
    ay_lrsg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_lrsg_conj_right (before -> after) (after -> before) eqsat

theorem ay_lrsg_guard_intro
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    sequenceManifest ->
    indexCounterEpochLedger ->
    overflowPolicy ->
    conflictWindowReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun sequenceH counterH overflowH replayH fallbackH buildH validatorH auditH
      result make =>
    make sequenceH counterH overflowH replayH fallbackH buildH validatorH
      auditH

theorem ay_lrsg_guard_sequence
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    sequenceManifest :=
  fun guard =>
    guard sequenceManifest
      (fun sequenceH _counterH _overflowH _replayH _fallbackH _buildH
          _validatorH _auditH => sequenceH)

theorem ay_lrsg_guard_counter
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    indexCounterEpochLedger :=
  fun guard =>
    guard indexCounterEpochLedger
      (fun _sequenceH counterH _overflowH _replayH _fallbackH _buildH
          _validatorH _auditH => counterH)

theorem ay_lrsg_guard_overflow
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    overflowPolicy :=
  fun guard =>
    guard overflowPolicy
      (fun _sequenceH _counterH overflowH _replayH _fallbackH _buildH
          _validatorH _auditH => overflowH)

theorem ay_lrsg_guard_replay
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    conflictWindowReplay :=
  fun guard =>
    guard conflictWindowReplay
      (fun _sequenceH _counterH _overflowH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_lrsg_guard_fallback
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _sequenceH _counterH _overflowH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_lrsg_guard_build
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _sequenceH _counterH _overflowH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_lrsg_guard_validator
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _sequenceH _counterH _overflowH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_lrsg_guard_audit
    (sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript : Prop) :
    ay_lrsg_guard sequenceManifest indexCounterEpochLedger overflowPolicy
      conflictWindowReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _sequenceH _counterH _overflowH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_lrsg_agreement_intro
    (sequenceMatch indexCounterMatch overflowMatch replayMatch fallbackMatch
      buildMatch validatorAccepts auditMatch : Prop) :
    sequenceMatch ->
    indexCounterMatch ->
    overflowMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_lrsg_agreement sequenceMatch indexCounterMatch overflowMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_lrsg_guard_intro sequenceMatch indexCounterMatch overflowMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_lrsg_accepted_sequence_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_lrsg_conj_intro guardEvidence
      (ay_lrsg_conj agreementEvidence searchControlHint)
      guardH
      (ay_lrsg_conj_intro agreementEvidence searchControlHint agreementH
        hintH)

theorem ay_lrsg_accepted_sequence_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_lrsg_conj_left guardEvidence
      (ay_lrsg_conj agreementEvidence searchControlHint) accepted

theorem ay_lrsg_accepted_sequence_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_lrsg_conj_left agreementEvidence searchControlHint
      (ay_lrsg_conj_right guardEvidence
        (ay_lrsg_conj agreementEvidence searchControlHint) accepted)

theorem ay_lrsg_accepted_sequence_hint
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_lrsg_conj_right agreementEvidence searchControlHint
      (ay_lrsg_conj_right guardEvidence
        (ay_lrsg_conj agreementEvidence searchControlHint) accepted)

theorem ay_lrsg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_lrsg_conj_intro acceptedEvidence
      (ay_lrsg_conj outcome formulaTruth)
      acceptedH (ay_lrsg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_lrsg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_lrsg_conj_left acceptedEvidence (ay_lrsg_conj outcome formulaTruth)
      report

theorem ay_lrsg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_lrsg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_lrsg_conj_right outcome formulaTruth
      (ay_lrsg_conj_right acceptedEvidence
        (ay_lrsg_conj outcome formulaTruth) report)

theorem ay_lrsg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_lrsg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_lrsg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_lrsg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_lrsg_conj_right diagnostic fallbackPublic noClaim

theorem ay_lrsg_manifest_mismatch_no_claim
    (manifestMismatch fallbackPublic : Prop) :
    manifestMismatch -> fallbackPublic ->
    ay_lrsg_no_claim manifestMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro manifestMismatch fallbackPublic

theorem ay_lrsg_index_mismatch_no_claim
    (indexMismatch fallbackPublic : Prop) :
    indexMismatch -> fallbackPublic ->
    ay_lrsg_no_claim indexMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro indexMismatch fallbackPublic

theorem ay_lrsg_overflow_mismatch_no_claim
    (overflowMismatch fallbackPublic : Prop) :
    overflowMismatch -> fallbackPublic ->
    ay_lrsg_no_claim overflowMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro overflowMismatch fallbackPublic

theorem ay_lrsg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_lrsg_no_claim replayMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro replayMismatch fallbackPublic

theorem ay_lrsg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_lrsg_no_claim buildMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro buildMismatch fallbackPublic

theorem ay_lrsg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_lrsg_no_claim validatorRejection fallbackPublic :=
  ay_lrsg_no_claim_intro validatorRejection fallbackPublic

theorem ay_lrsg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_lrsg_no_claim auditMismatch fallbackPublic :=
  ay_lrsg_no_claim_intro auditMismatch fallbackPublic

theorem ay_lrsg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_lrsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_lrsg_failed_sequence_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_lrsg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_lrsg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_lrsg_accepted_sequence_is_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  ay_lrsg_accepted_sequence_hint guardEvidence agreementEvidence
    searchControlHint

theorem ay_lrsg_accepted_sequence_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth
      publicSound : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_lrsg_accepted_sequence_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      (ay_lrsg_accepted_sequence_agreement guardEvidence agreementEvidence
        searchControlHint accepted)
      outcomeH
      truthH

theorem ay_lrsg_accepted_sequence_guides_sat
    (guardEvidence agreementEvidence searchControlHint satOutcome
      satTruth : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_lrsg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_lrsg_public_report_intro guardEvidence satOutcome satTruth
      (ay_lrsg_accepted_sequence_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      satH
      truthH

theorem ay_lrsg_accepted_sequence_guides_unsat
    (guardEvidence agreementEvidence searchControlHint unsatOutcome
      unsatTruth : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_lrsg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_lrsg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_lrsg_accepted_sequence_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      unsatH
      truthH

theorem ay_lrsg_restart_sequence_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      searchControlHint : Prop) :
    ay_lrsg_accepted_sequence guardEvidence agreementEvidence
      searchControlHint ->
    (searchControlHint -> formulaBefore -> formulaAfter) ->
    (searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_lrsg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_lrsg_equisat_intro formulaBefore formulaAfter
      (forward (ay_lrsg_accepted_sequence_hint guardEvidence agreementEvidence
        searchControlHint accepted))
      (backward (ay_lrsg_accepted_sequence_hint guardEvidence agreementEvidence
        searchControlHint accepted))
