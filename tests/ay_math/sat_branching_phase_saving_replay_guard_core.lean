-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Phase-saving replay guard skeleton for sequential-main SAT-COMP branching.
-- Saved phases are performance hints only when all replay and publication
-- evidence agrees with the checked public SAT/UNSAT result.

def ay_psav_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psav_equisat (before : Prop) (after : Prop) : Prop :=
  ay_psav_conj (before -> after) (after -> before)

def ay_psav_guard
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (phaseLedger ->
      levelScopeDigest ->
      assignmentDigest ->
      propagationReplay ->
      restartLedger ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_psav_agreement
    (phaseMatch : Prop)
    (levelScopeMatch : Prop)
    (assignmentMatch : Prop)
    (replayMatch : Prop)
    (restartMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_psav_guard phaseMatch levelScopeMatch assignmentMatch replayMatch
    restartMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_psav_accepted_phase_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) : Prop :=
  ay_psav_conj guardEvidence (ay_psav_conj agreementEvidence branchingHint)

def ay_psav_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_psav_conj acceptedEvidence (ay_psav_conj outcome formulaTruth)

def ay_psav_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_psav_conj diagnostic fallbackPublic

theorem ay_psav_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_psav_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_psav_conj_left (left : Prop) (right : Prop) :
    ay_psav_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_psav_conj_right (left : Prop) (right : Prop) :
    ay_psav_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_psav_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_psav_equisat before after :=
  fun forward backward =>
    ay_psav_conj_intro (before -> after) (after -> before) forward backward

theorem ay_psav_equisat_forward (before : Prop) (after : Prop) :
    ay_psav_equisat before after -> before -> after :=
  fun eqsat =>
    ay_psav_conj_left (before -> after) (after -> before) eqsat

theorem ay_psav_equisat_backward (before : Prop) (after : Prop) :
    ay_psav_equisat before after -> after -> before :=
  fun eqsat =>
    ay_psav_conj_right (before -> after) (after -> before) eqsat

theorem ay_psav_guard_intro
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    phaseLedger ->
    levelScopeDigest ->
    assignmentDigest ->
    propagationReplay ->
    restartLedger ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript :=
  fun phaseH levelH assignmentH replayH restartH fallbackH buildH
      validatorH auditH result make =>
    make phaseH levelH assignmentH replayH restartH fallbackH buildH
      validatorH auditH

theorem ay_psav_guard_phase
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    phaseLedger :=
  fun guard =>
    guard phaseLedger
      (fun phaseH _levelH _assignmentH _replayH _restartH _fallbackH
          _buildH _validatorH _auditH => phaseH)

theorem ay_psav_guard_level_scope
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _phaseH levelH _assignmentH _replayH _restartH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_psav_guard_assignment
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    assignmentDigest :=
  fun guard =>
    guard assignmentDigest
      (fun _phaseH _levelH assignmentH _replayH _restartH _fallbackH
          _buildH _validatorH _auditH => assignmentH)

theorem ay_psav_guard_replay
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _phaseH _levelH _assignmentH replayH _restartH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_psav_guard_restart
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    restartLedger :=
  fun guard =>
    guard restartLedger
      (fun _phaseH _levelH _assignmentH _replayH restartH _fallbackH
          _buildH _validatorH _auditH => restartH)

theorem ay_psav_guard_fallback
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _phaseH _levelH _assignmentH _replayH _restartH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_psav_guard_build
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _phaseH _levelH _assignmentH _replayH _restartH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_psav_guard_validator
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _phaseH _levelH _assignmentH _replayH _restartH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_psav_guard_audit
    (phaseLedger : Prop)
    (levelScopeDigest : Prop)
    (assignmentDigest : Prop)
    (propagationReplay : Prop)
    (restartLedger : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_psav_guard phaseLedger levelScopeDigest assignmentDigest
      propagationReplay restartLedger fallbackBaseline buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _phaseH _levelH _assignmentH _replayH _restartH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_psav_agreement_intro
    (phaseMatch : Prop)
    (levelScopeMatch : Prop)
    (assignmentMatch : Prop)
    (replayMatch : Prop)
    (restartMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    phaseMatch ->
    levelScopeMatch ->
    assignmentMatch ->
    replayMatch ->
    restartMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_psav_agreement phaseMatch levelScopeMatch assignmentMatch replayMatch
      restartMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_psav_guard_intro phaseMatch levelScopeMatch assignmentMatch replayMatch
    restartMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_psav_accepted_phase_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    branchingHint ->
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint :=
  fun guardH agreementH hintH =>
    ay_psav_conj_intro guardEvidence
      (ay_psav_conj agreementEvidence branchingHint)
      guardH
      (ay_psav_conj_intro agreementEvidence branchingHint agreementH hintH)

theorem ay_psav_accepted_phase_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    guardEvidence :=
  fun accepted =>
    ay_psav_conj_left guardEvidence
      (ay_psav_conj agreementEvidence branchingHint) accepted

theorem ay_psav_accepted_phase_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    agreementEvidence :=
  fun accepted =>
    ay_psav_conj_left agreementEvidence branchingHint
      (ay_psav_conj_right guardEvidence
        (ay_psav_conj agreementEvidence branchingHint) accepted)

theorem ay_psav_accepted_phase_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    branchingHint :=
  fun accepted =>
    ay_psav_conj_right agreementEvidence branchingHint
      (ay_psav_conj_right guardEvidence
        (ay_psav_conj agreementEvidence branchingHint) accepted)

theorem ay_psav_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_psav_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_psav_conj_intro acceptedEvidence (ay_psav_conj outcome formulaTruth)
      acceptedH (ay_psav_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_psav_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_psav_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_psav_conj_left acceptedEvidence (ay_psav_conj outcome formulaTruth)
      report

theorem ay_psav_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_psav_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_psav_conj_right outcome formulaTruth
      (ay_psav_conj_right acceptedEvidence (ay_psav_conj outcome formulaTruth)
        report)

theorem ay_psav_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_psav_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_psav_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_psav_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_psav_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_psav_conj_right diagnostic fallbackPublic noClaim

theorem ay_psav_phase_mismatch_no_claim
    (phaseMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseMismatch -> fallbackPublic ->
    ay_psav_no_claim phaseMismatch fallbackPublic :=
  ay_psav_no_claim_intro phaseMismatch fallbackPublic

theorem ay_psav_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_psav_no_claim levelScopeMismatch fallbackPublic :=
  ay_psav_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_psav_assignment_mismatch_no_claim
    (assignmentMismatch : Prop)
    (fallbackPublic : Prop) :
    assignmentMismatch -> fallbackPublic ->
    ay_psav_no_claim assignmentMismatch fallbackPublic :=
  ay_psav_no_claim_intro assignmentMismatch fallbackPublic

theorem ay_psav_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_psav_no_claim replayMismatch fallbackPublic :=
  ay_psav_no_claim_intro replayMismatch fallbackPublic

theorem ay_psav_restart_mismatch_no_claim
    (restartMismatch : Prop)
    (fallbackPublic : Prop) :
    restartMismatch -> fallbackPublic ->
    ay_psav_no_claim restartMismatch fallbackPublic :=
  ay_psav_no_claim_intro restartMismatch fallbackPublic

theorem ay_psav_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_psav_no_claim fallbackFailure fallbackPublic :=
  ay_psav_no_claim_intro fallbackFailure fallbackPublic

theorem ay_psav_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_psav_no_claim buildMismatch fallbackPublic :=
  ay_psav_no_claim_intro buildMismatch fallbackPublic

theorem ay_psav_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_psav_no_claim validatorRejection fallbackPublic :=
  ay_psav_no_claim_intro validatorRejection fallbackPublic

theorem ay_psav_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_psav_no_claim auditMismatch fallbackPublic :=
  ay_psav_no_claim_intro auditMismatch fallbackPublic

theorem ay_psav_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_psav_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_psav_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_psav_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_psav_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_psav_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_psav_accepted_phase_is_branching_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    branchingHint :=
  ay_psav_accepted_phase_hint_hint guardEvidence agreementEvidence branchingHint

theorem ay_psav_accepted_phase_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_psav_accepted_phase_hint_guard guardEvidence agreementEvidence
        branchingHint accepted)
      (ay_psav_accepted_phase_hint_agreement guardEvidence agreementEvidence
        branchingHint accepted)
      outcomeH
      truthH

theorem ay_psav_accepted_phase_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    satOutcome ->
    satTruth ->
    ay_psav_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_psav_public_report_intro guardEvidence satOutcome satTruth
      (ay_psav_accepted_phase_hint_guard guardEvidence agreementEvidence
        branchingHint accepted)
      satH
      truthH

theorem ay_psav_accepted_phase_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_psav_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_psav_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_psav_accepted_phase_hint_guard guardEvidence agreementEvidence
        branchingHint accepted)
      unsatH
      truthH

theorem ay_psav_phase_saving_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (branchingHint : Prop) :
    ay_psav_accepted_phase_hint guardEvidence agreementEvidence branchingHint ->
    (branchingHint -> formulaBefore -> formulaAfter) ->
    (branchingHint -> formulaAfter -> formulaBefore) ->
    ay_psav_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_psav_equisat_intro formulaBefore formulaAfter
      (forward (ay_psav_accepted_phase_hint_hint guardEvidence
        agreementEvidence branchingHint accepted))
      (backward (ay_psav_accepted_phase_hint_hint guardEvidence
        agreementEvidence branchingHint accepted))
