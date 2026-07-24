-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Chronological-backtracking budget guard skeleton for sequential-main SAT-COMP
-- branching/backtracking. Chronological fallback budgets are search-control
-- hints only when replay and publication evidence agree with the checked path.

def ay_cbtg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cbtg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cbtg_conj (before -> after) (after -> before)

def ay_cbtg_guard
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (backtrackEpochLedger ->
      levelScopeDigest ->
      trailSuffixDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cbtg_agreement
    (backtrackEpochMatch : Prop)
    (levelScopeMatch : Prop)
    (trailSuffixMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_cbtg_guard backtrackEpochMatch levelScopeMatch trailSuffixMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_cbtg_accepted_budget_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_cbtg_conj guardEvidence
    (ay_cbtg_conj agreementEvidence searchControlHint)

def ay_cbtg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_cbtg_conj acceptedEvidence (ay_cbtg_conj outcome formulaTruth)

def ay_cbtg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_cbtg_conj diagnostic fallbackPublic

theorem ay_cbtg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_cbtg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cbtg_conj_left (left : Prop) (right : Prop) :
    ay_cbtg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cbtg_conj_right (left : Prop) (right : Prop) :
    ay_cbtg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cbtg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_cbtg_equisat before after :=
  fun forward backward =>
    ay_cbtg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cbtg_equisat_forward (before : Prop) (after : Prop) :
    ay_cbtg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cbtg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cbtg_equisat_backward (before : Prop) (after : Prop) :
    ay_cbtg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cbtg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cbtg_guard_intro
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    backtrackEpochLedger ->
    levelScopeDigest ->
    trailSuffixDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript :=
  fun epochH levelH trailH replayH fallbackH buildH validatorH auditH
      result make =>
    make epochH levelH trailH replayH fallbackH buildH validatorH auditH

theorem ay_cbtg_guard_backtrack_epoch
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    backtrackEpochLedger :=
  fun guard =>
    guard backtrackEpochLedger
      (fun epochH _levelH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_cbtg_guard_level_scope
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    levelScopeDigest :=
  fun guard =>
    guard levelScopeDigest
      (fun _epochH levelH _trailH _replayH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_cbtg_guard_trail_suffix
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    trailSuffixDigest :=
  fun guard =>
    guard trailSuffixDigest
      (fun _epochH _levelH trailH _replayH _fallbackH _buildH
          _validatorH _auditH => trailH)

theorem ay_cbtg_guard_replay
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _epochH _levelH _trailH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_cbtg_guard_fallback
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _levelH _trailH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_cbtg_guard_build
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _levelH _trailH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_cbtg_guard_validator
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _levelH _trailH _replayH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_cbtg_guard_audit
    (backtrackEpochLedger : Prop)
    (levelScopeDigest : Prop)
    (trailSuffixDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_cbtg_guard backtrackEpochLedger levelScopeDigest trailSuffixDigest
      propagationReplay fallbackBaseline buildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _epochH _levelH _trailH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_cbtg_agreement_intro
    (backtrackEpochMatch : Prop)
    (levelScopeMatch : Prop)
    (trailSuffixMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    backtrackEpochMatch ->
    levelScopeMatch ->
    trailSuffixMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_cbtg_agreement backtrackEpochMatch levelScopeMatch trailSuffixMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_cbtg_guard_intro backtrackEpochMatch levelScopeMatch trailSuffixMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_cbtg_accepted_budget_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint :=
  fun guardH agreementH hintH =>
    ay_cbtg_conj_intro guardEvidence
      (ay_cbtg_conj agreementEvidence searchControlHint)
      guardH
      (ay_cbtg_conj_intro agreementEvidence searchControlHint agreementH
        hintH)

theorem ay_cbtg_accepted_budget_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_cbtg_conj_left guardEvidence
      (ay_cbtg_conj agreementEvidence searchControlHint) accepted

theorem ay_cbtg_accepted_budget_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_cbtg_conj_left agreementEvidence searchControlHint
      (ay_cbtg_conj_right guardEvidence
        (ay_cbtg_conj agreementEvidence searchControlHint) accepted)

theorem ay_cbtg_accepted_budget_hint_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_cbtg_conj_right agreementEvidence searchControlHint
      (ay_cbtg_conj_right guardEvidence
        (ay_cbtg_conj agreementEvidence searchControlHint) accepted)

theorem ay_cbtg_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cbtg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cbtg_conj_intro acceptedEvidence
      (ay_cbtg_conj outcome formulaTruth)
      acceptedH (ay_cbtg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cbtg_public_report_requires_accepted
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_cbtg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_cbtg_conj_left acceptedEvidence (ay_cbtg_conj outcome formulaTruth)
      report

theorem ay_cbtg_public_report_truth
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_cbtg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_cbtg_conj_right outcome formulaTruth
      (ay_cbtg_conj_right acceptedEvidence
        (ay_cbtg_conj outcome formulaTruth) report)

theorem ay_cbtg_no_claim_intro (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_cbtg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_cbtg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_cbtg_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_cbtg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_cbtg_conj_right diagnostic fallbackPublic noClaim

theorem ay_cbtg_backtrack_epoch_mismatch_no_claim
    (backtrackEpochMismatch : Prop)
    (fallbackPublic : Prop) :
    backtrackEpochMismatch -> fallbackPublic ->
    ay_cbtg_no_claim backtrackEpochMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro backtrackEpochMismatch fallbackPublic

theorem ay_cbtg_level_scope_mismatch_no_claim
    (levelScopeMismatch : Prop)
    (fallbackPublic : Prop) :
    levelScopeMismatch -> fallbackPublic ->
    ay_cbtg_no_claim levelScopeMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro levelScopeMismatch fallbackPublic

theorem ay_cbtg_trail_suffix_mismatch_no_claim
    (trailSuffixMismatch : Prop)
    (fallbackPublic : Prop) :
    trailSuffixMismatch -> fallbackPublic ->
    ay_cbtg_no_claim trailSuffixMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro trailSuffixMismatch fallbackPublic

theorem ay_cbtg_replay_mismatch_no_claim
    (replayMismatch : Prop)
    (fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_cbtg_no_claim replayMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro replayMismatch fallbackPublic

theorem ay_cbtg_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure -> fallbackPublic ->
    ay_cbtg_no_claim fallbackFailure fallbackPublic :=
  ay_cbtg_no_claim_intro fallbackFailure fallbackPublic

theorem ay_cbtg_build_mismatch_no_claim
    (buildMismatch : Prop)
    (fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_cbtg_no_claim buildMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro buildMismatch fallbackPublic

theorem ay_cbtg_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_cbtg_no_claim validatorRejection fallbackPublic :=
  ay_cbtg_no_claim_intro validatorRejection fallbackPublic

theorem ay_cbtg_audit_mismatch_no_claim
    (auditMismatch : Prop)
    (fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_cbtg_no_claim auditMismatch fallbackPublic :=
  ay_cbtg_no_claim_intro auditMismatch fallbackPublic

theorem ay_cbtg_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicSound : Prop) :
    ay_cbtg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_cbtg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_cbtg_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (publicationBlocked : Prop) :
    ay_cbtg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_cbtg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_cbtg_accepted_budget_is_search_control_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    searchControlHint :=
  ay_cbtg_accepted_budget_hint_hint guardEvidence agreementEvidence
    searchControlHint

theorem ay_cbtg_accepted_budget_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (publicSound : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    (guardEvidence -> agreementEvidence -> outcome -> formulaTruth ->
      publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_cbtg_accepted_budget_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      (ay_cbtg_accepted_budget_hint_agreement guardEvidence agreementEvidence
        searchControlHint accepted)
      outcomeH
      truthH

theorem ay_cbtg_accepted_budget_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (satOutcome : Prop)
    (satTruth : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_cbtg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_cbtg_public_report_intro guardEvidence satOutcome satTruth
      (ay_cbtg_accepted_budget_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      satH
      truthH

theorem ay_cbtg_accepted_budget_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop)
    (unsatOutcome : Prop)
    (unsatTruth : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_cbtg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_cbtg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_cbtg_accepted_budget_hint_guard guardEvidence agreementEvidence
        searchControlHint accepted)
      unsatH
      truthH

theorem ay_cbtg_chronological_budget_does_not_change_satisfiability
    (formulaBefore : Prop)
    (formulaAfter : Prop)
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (searchControlHint : Prop) :
    ay_cbtg_accepted_budget_hint guardEvidence agreementEvidence
      searchControlHint ->
    (searchControlHint -> formulaBefore -> formulaAfter) ->
    (searchControlHint -> formulaAfter -> formulaBefore) ->
    ay_cbtg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_cbtg_equisat_intro formulaBefore formulaAfter
      (forward (ay_cbtg_accepted_budget_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))
      (backward (ay_cbtg_accepted_budget_hint_hint guardEvidence
        agreementEvidence searchControlHint accepted))
