-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart-counter overflow guard skeleton for sequential-main SAT-COMP restart
-- policy. Overflow handling is a search-control policy only when counter,
-- policy, epoch, replay, fallback, build, validator, and audit evidence agree.

def ay_rcog_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rcog_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rcog_conj (before -> after) (after -> before)

def ay_rcog_guard
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (restartCounterManifest ->
      overflowPolicy ->
      epochLedger ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rcog_agreement
    (counterManifestMatch : Prop)
    (overflowPolicyMatch : Prop)
    (epochLedgerMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_rcog_guard counterManifestMatch overflowPolicyMatch epochLedgerMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_rcog_accepted_restart_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) : Prop :=
  ay_rcog_conj guardEvidence
    (ay_rcog_conj agreementEvidence searchControlPolicy)

def ay_rcog_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_rcog_conj acceptedEvidence (ay_rcog_conj outcome formulaTruth)

def ay_rcog_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_rcog_conj diagnostic fallbackPublic

theorem ay_rcog_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_rcog_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rcog_conj_left (left : Prop) (right : Prop) :
    ay_rcog_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rcog_conj_right (left : Prop) (right : Prop) :
    ay_rcog_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rcog_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_rcog_equisat before after :=
  fun forward backward =>
    ay_rcog_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rcog_equisat_forward (before : Prop) (after : Prop) :
    ay_rcog_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rcog_conj_left (before -> after) (after -> before) eqsat

theorem ay_rcog_equisat_backward (before : Prop) (after : Prop) :
    ay_rcog_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rcog_conj_right (before -> after) (after -> before) eqsat

theorem ay_rcog_guard_intro
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    restartCounterManifest ->
    overflowPolicy ->
    epochLedger ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun counterH policyH epochH replayH fallbackH buildH validatorH auditH
      result make =>
    make counterH policyH epochH replayH fallbackH buildH validatorH auditH

theorem ay_rcog_guard_counter_manifest
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    restartCounterManifest :=
  fun guard =>
    guard restartCounterManifest
      (fun counterH _policyH _epochH _replayH _fallbackH _buildH
          _validatorH _auditH => counterH)

theorem ay_rcog_guard_overflow_policy
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    overflowPolicy :=
  fun guard =>
    guard overflowPolicy
      (fun _counterH policyH _epochH _replayH _fallbackH _buildH
          _validatorH _auditH => policyH)

theorem ay_rcog_guard_epoch
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    epochLedger :=
  fun guard =>
    guard epochLedger
      (fun _counterH _policyH epochH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_rcog_guard_replay
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _counterH _policyH _epochH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_rcog_guard_fallback
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _counterH _policyH _epochH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_rcog_guard_build
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _counterH _policyH _epochH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_rcog_guard_validator
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _counterH _policyH _epochH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_rcog_guard_audit
    (restartCounterManifest : Prop)
    (overflowPolicy : Prop)
    (epochLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_rcog_guard restartCounterManifest overflowPolicy epochLedger
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _counterH _policyH _epochH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_rcog_agreement_intro
    (counterManifestMatch : Prop)
    (overflowPolicyMatch : Prop)
    (epochLedgerMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    counterManifestMatch ->
    overflowPolicyMatch ->
    epochLedgerMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_rcog_agreement counterManifestMatch overflowPolicyMatch
      epochLedgerMatch replayMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_rcog_guard_intro counterManifestMatch overflowPolicyMatch
    epochLedgerMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_rcog_accepted_restart_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlPolicy ->
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy :=
  fun guardH agreementH policyH =>
    ay_rcog_conj_intro guardEvidence
      (ay_rcog_conj agreementEvidence searchControlPolicy)
      guardH
      (ay_rcog_conj_intro agreementEvidence searchControlPolicy agreementH
        policyH)

theorem ay_rcog_accepted_restart_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    guardEvidence :=
  fun accepted =>
    ay_rcog_conj_left guardEvidence
      (ay_rcog_conj agreementEvidence searchControlPolicy) accepted

theorem ay_rcog_accepted_restart_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    agreementEvidence :=
  fun accepted =>
    ay_rcog_conj_left agreementEvidence searchControlPolicy
      (ay_rcog_conj_right guardEvidence
        (ay_rcog_conj agreementEvidence searchControlPolicy) accepted)

theorem ay_rcog_accepted_restart_hint_policy
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    searchControlPolicy :=
  fun accepted =>
    ay_rcog_conj_right agreementEvidence searchControlPolicy
      (ay_rcog_conj_right guardEvidence
        (ay_rcog_conj agreementEvidence searchControlPolicy) accepted)

theorem ay_rcog_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rcog_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rcog_conj_intro acceptedEvidence
      (ay_rcog_conj outcome formulaTruth)
      acceptedH (ay_rcog_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rcog_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rcog_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_rcog_conj_left acceptedEvidence (ay_rcog_conj outcome formulaTruth)
      report

theorem ay_rcog_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_rcog_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rcog_conj_right outcome formulaTruth
      (ay_rcog_conj_right acceptedEvidence
        (ay_rcog_conj outcome formulaTruth) report)

theorem ay_rcog_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_rcog_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_rcog_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_rcog_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_rcog_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_rcog_conj_right diagnostic fallbackPublic noClaim

theorem ay_rcog_counter_manifest_mismatch_no_claim
    (counterManifestMismatch : Prop)
    (fallbackPublic : Prop) :
    counterManifestMismatch -> fallbackPublic ->
    ay_rcog_no_claim counterManifestMismatch fallbackPublic :=
  ay_rcog_no_claim_intro counterManifestMismatch fallbackPublic

theorem ay_rcog_overflow_policy_mismatch_no_claim
    (overflowPolicyMismatch : Prop)
    (fallbackPublic : Prop) :
    overflowPolicyMismatch -> fallbackPublic ->
    ay_rcog_no_claim overflowPolicyMismatch fallbackPublic :=
  ay_rcog_no_claim_intro overflowPolicyMismatch fallbackPublic

theorem ay_rcog_epoch_mismatch_no_claim
    (epochMismatch : Prop)
    (fallbackPublic : Prop) :
    epochMismatch -> fallbackPublic ->
    ay_rcog_no_claim epochMismatch fallbackPublic :=
  ay_rcog_no_claim_intro epochMismatch fallbackPublic

theorem ay_rcog_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_rcog_no_claim replayMismatch fallbackPublic :=
  ay_rcog_no_claim_intro replayMismatch fallbackPublic

theorem ay_rcog_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_rcog_no_claim fallbackFailure fallbackPublic :=
  ay_rcog_no_claim_intro fallbackFailure fallbackPublic

theorem ay_rcog_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_rcog_no_claim buildMismatch fallbackPublic :=
  ay_rcog_no_claim_intro buildMismatch fallbackPublic

theorem ay_rcog_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_rcog_no_claim validatorRejection fallbackPublic :=
  ay_rcog_no_claim_intro validatorRejection fallbackPublic

theorem ay_rcog_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_rcog_no_claim auditMismatch fallbackPublic :=
  ay_rcog_no_claim_intro auditMismatch fallbackPublic

theorem ay_rcog_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_rcog_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_rcog_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_rcog_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_rcog_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_rcog_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_rcog_accepted_overflow_is_search_control_policy
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    searchControlPolicy :=
  ay_rcog_accepted_restart_hint_policy guardEvidence agreementEvidence
    searchControlPolicy

theorem ay_rcog_accepted_overflow_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_rcog_accepted_restart_hint_guard guardEvidence agreementEvidence
        searchControlPolicy accepted)
      (ay_rcog_accepted_restart_hint_agreement guardEvidence agreementEvidence
        searchControlPolicy accepted)
      outcomeH
      truthH

theorem ay_rcog_accepted_overflow_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    satOutcome ->
    satTruth ->
    ay_rcog_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_rcog_public_report_intro guardEvidence satOutcome satTruth
      (ay_rcog_accepted_restart_hint_guard guardEvidence agreementEvidence
        searchControlPolicy accepted)
      satH
      truthH

theorem ay_rcog_accepted_overflow_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    unsatOutcome ->
    unsatTruth ->
    ay_rcog_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_rcog_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_rcog_accepted_restart_hint_guard guardEvidence agreementEvidence
        searchControlPolicy accepted)
      unsatH
      truthH

theorem ay_rcog_overflow_handling_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlPolicy : Prop) :
    ay_rcog_accepted_restart_hint guardEvidence agreementEvidence
      searchControlPolicy ->
    (searchControlPolicy -> formulaBefore -> formulaAfter) ->
    (searchControlPolicy -> formulaAfter -> formulaBefore) ->
    ay_rcog_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_rcog_equisat_intro formulaBefore formulaAfter
      (forward (ay_rcog_accepted_restart_hint_policy guardEvidence
        agreementEvidence searchControlPolicy accepted))
      (backward (ay_rcog_accepted_restart_hint_policy guardEvidence
        agreementEvidence searchControlPolicy accepted))
