-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Non-chronological backjump guard skeleton for sequential-main SAT-COMP CDCL.
-- Backjumping is search-control only when conflict levels, asserting-clause
-- replay, decision-stack digests, rollback, propagation replay, fallback,
-- build, validator, and audit evidence agree with the public result.

def ay_ncbg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ncbg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_ncbg_conj (before -> after) (after -> before)

def ay_ncbg_guard
    (conflictLevelLedger : Prop)
    (assertingLevelWitness : Prop)
    (decisionStackBeforeDigest : Prop)
    (decisionStackAfterDigest : Prop)
    (assignmentRollbackProof : Prop)
    (propagationReplay : Prop)
    (fallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictLevelLedger ->
      assertingLevelWitness ->
      decisionStackBeforeDigest ->
      decisionStackAfterDigest ->
      assignmentRollbackProof ->
      propagationReplay ->
      fallbackPolicy ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_ncbg_agreement
    (levelMatch : Prop)
    (assertingReplay : Prop)
    (stackBeforeMatch : Prop)
    (stackAfterMatch : Prop)
    (rollbackMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_ncbg_guard levelMatch assertingReplay stackBeforeMatch stackAfterMatch
    rollbackMatch replayMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

def ay_ncbg_accepted_backjump
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (assertingClauseObligation : Prop)
    (searchControlHint : Prop) : Prop :=
  ay_ncbg_conj guardEvidence
    (ay_ncbg_conj agreementEvidence
      (ay_ncbg_conj assertingClauseObligation searchControlHint))

def ay_ncbg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_ncbg_conj acceptedEvidence (ay_ncbg_conj outcome formulaTruth)

def ay_ncbg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_ncbg_conj diagnostic fallbackPublic

theorem ay_ncbg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_ncbg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_ncbg_conj_left (left : Prop) (right : Prop) :
    ay_ncbg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_ncbg_conj_right (left : Prop) (right : Prop) :
    ay_ncbg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_ncbg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_ncbg_equisat before after :=
  fun forward backward =>
    ay_ncbg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_ncbg_equisat_forward (before : Prop) (after : Prop) :
    ay_ncbg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_ncbg_conj_left (before -> after) (after -> before) eqsat

theorem ay_ncbg_equisat_backward (before : Prop) (after : Prop) :
    ay_ncbg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_ncbg_conj_right (before -> after) (after -> before) eqsat

theorem ay_ncbg_guard_intro
    (conflictLevelLedger : Prop)
    (assertingLevelWitness : Prop)
    (decisionStackBeforeDigest : Prop)
    (decisionStackAfterDigest : Prop)
    (assignmentRollbackProof : Prop)
    (propagationReplay : Prop)
    (fallbackPolicy : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    conflictLevelLedger ->
    assertingLevelWitness ->
    decisionStackBeforeDigest ->
    decisionStackAfterDigest ->
    assignmentRollbackProof ->
    propagationReplay ->
    fallbackPolicy ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript :=
  fun levelH assertingH beforeH afterH rollbackH replayH fallbackH buildH
      validatorH auditH result make =>
    make levelH assertingH beforeH afterH rollbackH replayH fallbackH buildH
      validatorH auditH

theorem ay_ncbg_guard_level
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    conflictLevelLedger :=
  fun guard =>
    guard conflictLevelLedger
      (fun levelH _assertingH _beforeH _afterH _rollbackH _replayH
          _fallbackH _buildH _validatorH _auditH => levelH)

theorem ay_ncbg_guard_asserting
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    assertingLevelWitness :=
  fun guard =>
    guard assertingLevelWitness
      (fun _levelH assertingH _beforeH _afterH _rollbackH _replayH
          _fallbackH _buildH _validatorH _auditH => assertingH)

theorem ay_ncbg_guard_stack_before
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    decisionStackBeforeDigest :=
  fun guard =>
    guard decisionStackBeforeDigest
      (fun _levelH _assertingH beforeH _afterH _rollbackH _replayH
          _fallbackH _buildH _validatorH _auditH => beforeH)

theorem ay_ncbg_guard_stack_after
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    decisionStackAfterDigest :=
  fun guard =>
    guard decisionStackAfterDigest
      (fun _levelH _assertingH _beforeH afterH _rollbackH _replayH
          _fallbackH _buildH _validatorH _auditH => afterH)

theorem ay_ncbg_guard_rollback
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    assignmentRollbackProof :=
  fun guard =>
    guard assignmentRollbackProof
      (fun _levelH _assertingH _beforeH _afterH rollbackH _replayH
          _fallbackH _buildH _validatorH _auditH => rollbackH)

theorem ay_ncbg_guard_replay
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _levelH _assertingH _beforeH _afterH _rollbackH replayH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_ncbg_guard_fallback
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    fallbackPolicy :=
  fun guard =>
    guard fallbackPolicy
      (fun _levelH _assertingH _beforeH _afterH _rollbackH _replayH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_ncbg_guard_build
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _levelH _assertingH _beforeH _afterH _rollbackH _replayH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_ncbg_guard_validator
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _levelH _assertingH _beforeH _afterH _rollbackH _replayH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_ncbg_guard_audit
    (conflictLevelLedger assertingLevelWitness decisionStackBeforeDigest
      decisionStackAfterDigest assignmentRollbackProof propagationReplay
      fallbackPolicy buildEvidence validatorGate auditTranscript : Prop) :
    ay_ncbg_guard conflictLevelLedger assertingLevelWitness
      decisionStackBeforeDigest decisionStackAfterDigest
      assignmentRollbackProof propagationReplay fallbackPolicy buildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _levelH _assertingH _beforeH _afterH _rollbackH _replayH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_ncbg_agreement_intro
    (levelMatch assertingReplay stackBeforeMatch stackAfterMatch rollbackMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch : Prop) :
    levelMatch ->
    assertingReplay ->
    stackBeforeMatch ->
    stackAfterMatch ->
    rollbackMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_ncbg_agreement levelMatch assertingReplay stackBeforeMatch
      stackAfterMatch rollbackMatch replayMatch fallbackMatch buildMatch
      validatorAccepts auditMatch :=
  ay_ncbg_guard_intro levelMatch assertingReplay stackBeforeMatch
    stackAfterMatch rollbackMatch replayMatch fallbackMatch buildMatch
    validatorAccepts auditMatch

theorem ay_ncbg_accepted_backjump_intro
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    assertingClauseObligation ->
    searchControlHint ->
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint :=
  fun guardH agreementH assertingH hintH =>
    ay_ncbg_conj_intro guardEvidence
      (ay_ncbg_conj agreementEvidence
        (ay_ncbg_conj assertingClauseObligation searchControlHint))
      guardH
      (ay_ncbg_conj_intro agreementEvidence
        (ay_ncbg_conj assertingClauseObligation searchControlHint)
        agreementH
        (ay_ncbg_conj_intro assertingClauseObligation searchControlHint
          assertingH hintH))

theorem ay_ncbg_accepted_backjump_guard
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_ncbg_conj_left guardEvidence
      (ay_ncbg_conj agreementEvidence
        (ay_ncbg_conj assertingClauseObligation searchControlHint))
      accepted

theorem ay_ncbg_accepted_backjump_agreement
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_ncbg_conj_left agreementEvidence
      (ay_ncbg_conj assertingClauseObligation searchControlHint)
      (ay_ncbg_conj_right guardEvidence
        (ay_ncbg_conj agreementEvidence
          (ay_ncbg_conj assertingClauseObligation searchControlHint))
        accepted)

theorem ay_ncbg_accepted_backjump_asserting_obligation
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    assertingClauseObligation :=
  fun accepted =>
    ay_ncbg_conj_left assertingClauseObligation searchControlHint
      (ay_ncbg_conj_right agreementEvidence
        (ay_ncbg_conj assertingClauseObligation searchControlHint)
        (ay_ncbg_conj_right guardEvidence
          (ay_ncbg_conj agreementEvidence
            (ay_ncbg_conj assertingClauseObligation searchControlHint))
          accepted))

theorem ay_ncbg_accepted_backjump_hint
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_ncbg_conj_right assertingClauseObligation searchControlHint
      (ay_ncbg_conj_right agreementEvidence
        (ay_ncbg_conj assertingClauseObligation searchControlHint)
        (ay_ncbg_conj_right guardEvidence
          (ay_ncbg_conj agreementEvidence
            (ay_ncbg_conj assertingClauseObligation searchControlHint))
          accepted))

theorem ay_ncbg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_ncbg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_ncbg_conj_intro acceptedEvidence
      (ay_ncbg_conj outcome formulaTruth)
      acceptedH (ay_ncbg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_ncbg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_ncbg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_ncbg_conj_left acceptedEvidence (ay_ncbg_conj outcome formulaTruth)
      report

theorem ay_ncbg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_ncbg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_ncbg_conj_right outcome formulaTruth
      (ay_ncbg_conj_right acceptedEvidence
        (ay_ncbg_conj outcome formulaTruth) report)

theorem ay_ncbg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_ncbg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_ncbg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_ncbg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_ncbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_ncbg_conj_right diagnostic fallbackPublic noClaim

theorem ay_ncbg_level_mismatch_no_claim
    (levelMismatch fallbackPublic : Prop) :
    levelMismatch -> fallbackPublic ->
    ay_ncbg_no_claim levelMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro levelMismatch fallbackPublic

theorem ay_ncbg_stack_mismatch_no_claim
    (stackMismatch fallbackPublic : Prop) :
    stackMismatch -> fallbackPublic ->
    ay_ncbg_no_claim stackMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro stackMismatch fallbackPublic

theorem ay_ncbg_rollback_mismatch_no_claim
    (rollbackMismatch fallbackPublic : Prop) :
    rollbackMismatch -> fallbackPublic ->
    ay_ncbg_no_claim rollbackMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro rollbackMismatch fallbackPublic

theorem ay_ncbg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_ncbg_no_claim replayMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro replayMismatch fallbackPublic

theorem ay_ncbg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_ncbg_no_claim buildMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro buildMismatch fallbackPublic

theorem ay_ncbg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_ncbg_no_claim validatorRejection fallbackPublic :=
  ay_ncbg_no_claim_intro validatorRejection fallbackPublic

theorem ay_ncbg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_ncbg_no_claim auditMismatch fallbackPublic :=
  ay_ncbg_no_claim_intro auditMismatch fallbackPublic

theorem ay_ncbg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_ncbg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_ncbg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_ncbg_failed_backjump_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_ncbg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_ncbg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_ncbg_accepted_backjump_is_search_control
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    searchControlHint :=
  ay_ncbg_accepted_backjump_hint guardEvidence agreementEvidence
    assertingClauseObligation searchControlHint

theorem ay_ncbg_accepted_backjump_preserves_asserting_obligation
    (guardEvidence agreementEvidence assertingClauseObligation
      searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    assertingClauseObligation :=
  ay_ncbg_accepted_backjump_asserting_obligation guardEvidence
    agreementEvidence assertingClauseObligation searchControlHint

theorem ay_ncbg_accepted_backjump_preserves_public_soundness
    (guardEvidence agreementEvidence assertingClauseObligation searchControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    (guardEvidence -> agreementEvidence -> assertingClauseObligation ->
      outcome -> formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_ncbg_accepted_backjump_guard guardEvidence agreementEvidence
        assertingClauseObligation searchControlHint accepted)
      (ay_ncbg_accepted_backjump_agreement guardEvidence agreementEvidence
        assertingClauseObligation searchControlHint accepted)
      (ay_ncbg_accepted_backjump_asserting_obligation guardEvidence
        agreementEvidence assertingClauseObligation searchControlHint accepted)
      outcomeH
      truthH

theorem ay_ncbg_accepted_backjump_guides_sat
    (guardEvidence agreementEvidence assertingClauseObligation searchControlHint
      satOutcome satTruth : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    satOutcome ->
    satTruth ->
    ay_ncbg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_ncbg_public_report_intro guardEvidence satOutcome satTruth
      (ay_ncbg_accepted_backjump_guard guardEvidence agreementEvidence
        assertingClauseObligation searchControlHint accepted)
      satH
      truthH

theorem ay_ncbg_accepted_backjump_guides_unsat
    (guardEvidence agreementEvidence assertingClauseObligation searchControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_ncbg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_ncbg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_ncbg_accepted_backjump_guard guardEvidence agreementEvidence
        assertingClauseObligation searchControlHint accepted)
      unsatH
      truthH

theorem ay_ncbg_backjump_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint : Prop) :
    ay_ncbg_accepted_backjump guardEvidence agreementEvidence
      assertingClauseObligation searchControlHint ->
    (searchControlHint -> assertingClauseObligation -> formulaBefore ->
      formulaAfter) ->
    (searchControlHint -> assertingClauseObligation -> formulaAfter ->
      formulaBefore) ->
    ay_ncbg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_ncbg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_ncbg_accepted_backjump_hint guardEvidence agreementEvidence
          assertingClauseObligation searchControlHint accepted)
        (ay_ncbg_accepted_backjump_asserting_obligation guardEvidence
          agreementEvidence assertingClauseObligation searchControlHint
          accepted))
      (backward
        (ay_ncbg_accepted_backjump_hint guardEvidence agreementEvidence
          assertingClauseObligation searchControlHint accepted)
        (ay_ncbg_accepted_backjump_asserting_obligation guardEvidence
          agreementEvidence assertingClauseObligation searchControlHint
          accepted))
