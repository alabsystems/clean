-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision/propagation trail compaction guard skeleton for sequential-main
-- SAT-COMP branching. Compaction is data-layout/search-control only when trail,
-- level, reason remap, assignment equivalence, replay, fallback, build,
-- validator, and audit evidence agree with the public result.

def ay_tcfg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_tcfg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_tcfg_conj (before -> after) (after -> before)

def ay_tcfg_guard
    (trailDigestBefore : Prop)
    (trailDigestAfter : Prop)
    (decisionLevelPartitionWitness : Prop)
    (reasonClausePointerRemap : Prop)
    (assignmentEquivalenceWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (trailDigestBefore ->
      trailDigestAfter ->
      decisionLevelPartitionWitness ->
      reasonClausePointerRemap ->
      assignmentEquivalenceWitness ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_tcfg_agreement
    (beforeDigestMatch : Prop)
    (afterDigestMatch : Prop)
    (levelPartitionMatch : Prop)
    (reasonRemapMatch : Prop)
    (assignmentEquivalence : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_tcfg_guard beforeDigestMatch afterDigestMatch levelPartitionMatch
    reasonRemapMatch assignmentEquivalence replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

def ay_tcfg_accepted_compaction
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (reasonReplayObligation : Prop)
    (layoutControlHint : Prop) : Prop :=
  ay_tcfg_conj guardEvidence
    (ay_tcfg_conj agreementEvidence
      (ay_tcfg_conj reasonReplayObligation layoutControlHint))

def ay_tcfg_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_tcfg_conj acceptedEvidence (ay_tcfg_conj outcome formulaTruth)

def ay_tcfg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_tcfg_conj diagnostic fallbackPublic

theorem ay_tcfg_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_tcfg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_tcfg_conj_left (left : Prop) (right : Prop) :
    ay_tcfg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_tcfg_conj_right (left : Prop) (right : Prop) :
    ay_tcfg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_tcfg_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_tcfg_equisat before after :=
  fun forward backward =>
    ay_tcfg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_tcfg_equisat_forward (before : Prop) (after : Prop) :
    ay_tcfg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_tcfg_conj_left (before -> after) (after -> before) eqsat

theorem ay_tcfg_equisat_backward (before : Prop) (after : Prop) :
    ay_tcfg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_tcfg_conj_right (before -> after) (after -> before) eqsat

theorem ay_tcfg_guard_intro
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    trailDigestBefore ->
    trailDigestAfter ->
    decisionLevelPartitionWitness ->
    reasonClausePointerRemap ->
    assignmentEquivalenceWitness ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript :=
  fun beforeH afterH levelH remapH equivH replayH fallbackH buildH
      validatorH auditH result make =>
    make beforeH afterH levelH remapH equivH replayH fallbackH buildH
      validatorH auditH

theorem ay_tcfg_guard_before_digest
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    trailDigestBefore :=
  fun guard =>
    guard trailDigestBefore
      (fun beforeH _afterH _levelH _remapH _equivH _replayH _fallbackH
          _buildH _validatorH _auditH => beforeH)

theorem ay_tcfg_guard_after_digest
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    trailDigestAfter :=
  fun guard =>
    guard trailDigestAfter
      (fun _beforeH afterH _levelH _remapH _equivH _replayH _fallbackH
          _buildH _validatorH _auditH => afterH)

theorem ay_tcfg_guard_level_partition
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    decisionLevelPartitionWitness :=
  fun guard =>
    guard decisionLevelPartitionWitness
      (fun _beforeH _afterH levelH _remapH _equivH _replayH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_tcfg_guard_reason_remap
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    reasonClausePointerRemap :=
  fun guard =>
    guard reasonClausePointerRemap
      (fun _beforeH _afterH _levelH remapH _equivH _replayH _fallbackH
          _buildH _validatorH _auditH => remapH)

theorem ay_tcfg_guard_assignment_equiv
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    assignmentEquivalenceWitness :=
  fun guard =>
    guard assignmentEquivalenceWitness
      (fun _beforeH _afterH _levelH _remapH equivH _replayH _fallbackH
          _buildH _validatorH _auditH => equivH)

theorem ay_tcfg_guard_replay
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _beforeH _afterH _levelH _remapH _equivH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_tcfg_guard_fallback
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _beforeH _afterH _levelH _remapH _equivH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_tcfg_guard_build
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _beforeH _afterH _levelH _remapH _equivH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_tcfg_guard_validator
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _beforeH _afterH _levelH _remapH _equivH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_tcfg_guard_audit
    (trailDigestBefore trailDigestAfter decisionLevelPartitionWitness
      reasonClausePointerRemap assignmentEquivalenceWitness propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript : Prop) :
    ay_tcfg_guard trailDigestBefore trailDigestAfter
      decisionLevelPartitionWitness reasonClausePointerRemap
      assignmentEquivalenceWitness propagationReplay fallbackBaseline
      buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _beforeH _afterH _levelH _remapH _equivH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_tcfg_agreement_intro
    (beforeDigestMatch afterDigestMatch levelPartitionMatch reasonRemapMatch
      assignmentEquivalence replayMatch fallbackMatch buildMatch
      validatorAccepts auditMatch : Prop) :
    beforeDigestMatch ->
    afterDigestMatch ->
    levelPartitionMatch ->
    reasonRemapMatch ->
    assignmentEquivalence ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_tcfg_agreement beforeDigestMatch afterDigestMatch levelPartitionMatch
      reasonRemapMatch assignmentEquivalence replayMatch fallbackMatch
      buildMatch validatorAccepts auditMatch :=
  ay_tcfg_guard_intro beforeDigestMatch afterDigestMatch levelPartitionMatch
    reasonRemapMatch assignmentEquivalence replayMatch fallbackMatch
    buildMatch validatorAccepts auditMatch

theorem ay_tcfg_accepted_compaction_intro
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    reasonReplayObligation ->
    layoutControlHint ->
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint :=
  fun guardH agreementH reasonH hintH =>
    ay_tcfg_conj_intro guardEvidence
      (ay_tcfg_conj agreementEvidence
        (ay_tcfg_conj reasonReplayObligation layoutControlHint))
      guardH
      (ay_tcfg_conj_intro agreementEvidence
        (ay_tcfg_conj reasonReplayObligation layoutControlHint)
        agreementH
        (ay_tcfg_conj_intro reasonReplayObligation layoutControlHint reasonH
          hintH))

theorem ay_tcfg_accepted_compaction_guard
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_tcfg_conj_left guardEvidence
      (ay_tcfg_conj agreementEvidence
        (ay_tcfg_conj reasonReplayObligation layoutControlHint))
      accepted

theorem ay_tcfg_accepted_compaction_agreement
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_tcfg_conj_left agreementEvidence
      (ay_tcfg_conj reasonReplayObligation layoutControlHint)
      (ay_tcfg_conj_right guardEvidence
        (ay_tcfg_conj agreementEvidence
          (ay_tcfg_conj reasonReplayObligation layoutControlHint))
        accepted)

theorem ay_tcfg_accepted_compaction_reason_obligation
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    reasonReplayObligation :=
  fun accepted =>
    ay_tcfg_conj_left reasonReplayObligation layoutControlHint
      (ay_tcfg_conj_right agreementEvidence
        (ay_tcfg_conj reasonReplayObligation layoutControlHint)
        (ay_tcfg_conj_right guardEvidence
          (ay_tcfg_conj agreementEvidence
            (ay_tcfg_conj reasonReplayObligation layoutControlHint))
          accepted))

theorem ay_tcfg_accepted_compaction_hint
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    layoutControlHint :=
  fun accepted =>
    ay_tcfg_conj_right reasonReplayObligation layoutControlHint
      (ay_tcfg_conj_right agreementEvidence
        (ay_tcfg_conj reasonReplayObligation layoutControlHint)
        (ay_tcfg_conj_right guardEvidence
          (ay_tcfg_conj agreementEvidence
            (ay_tcfg_conj reasonReplayObligation layoutControlHint))
          accepted))

theorem ay_tcfg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_tcfg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_tcfg_conj_intro acceptedEvidence
      (ay_tcfg_conj outcome formulaTruth)
      acceptedH (ay_tcfg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_tcfg_public_report_requires_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_tcfg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_tcfg_conj_left acceptedEvidence (ay_tcfg_conj outcome formulaTruth)
      report

theorem ay_tcfg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_tcfg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_tcfg_conj_right outcome formulaTruth
      (ay_tcfg_conj_right acceptedEvidence
        (ay_tcfg_conj outcome formulaTruth) report)

theorem ay_tcfg_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_tcfg_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_tcfg_conj_intro diagnostic fallbackPublic diagnosticH fallbackH

theorem ay_tcfg_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_tcfg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_tcfg_conj_right diagnostic fallbackPublic noClaim

theorem ay_tcfg_digest_mismatch_no_claim
    (digestMismatch fallbackPublic : Prop) :
    digestMismatch -> fallbackPublic ->
    ay_tcfg_no_claim digestMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro digestMismatch fallbackPublic

theorem ay_tcfg_level_mismatch_no_claim
    (levelMismatch fallbackPublic : Prop) :
    levelMismatch -> fallbackPublic ->
    ay_tcfg_no_claim levelMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro levelMismatch fallbackPublic

theorem ay_tcfg_remap_mismatch_no_claim
    (remapMismatch fallbackPublic : Prop) :
    remapMismatch -> fallbackPublic ->
    ay_tcfg_no_claim remapMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro remapMismatch fallbackPublic

theorem ay_tcfg_equivalence_mismatch_no_claim
    (equivalenceMismatch fallbackPublic : Prop) :
    equivalenceMismatch -> fallbackPublic ->
    ay_tcfg_no_claim equivalenceMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro equivalenceMismatch fallbackPublic

theorem ay_tcfg_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch -> fallbackPublic ->
    ay_tcfg_no_claim replayMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro replayMismatch fallbackPublic

theorem ay_tcfg_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch -> fallbackPublic ->
    ay_tcfg_no_claim buildMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro buildMismatch fallbackPublic

theorem ay_tcfg_validator_rejection_no_claim
    (validatorRejection fallbackPublic : Prop) :
    validatorRejection -> fallbackPublic ->
    ay_tcfg_no_claim validatorRejection fallbackPublic :=
  ay_tcfg_no_claim_intro validatorRejection fallbackPublic

theorem ay_tcfg_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch -> fallbackPublic ->
    ay_tcfg_no_claim auditMismatch fallbackPublic :=
  ay_tcfg_no_claim_intro auditMismatch fallbackPublic

theorem ay_tcfg_recompute_preserves_public_soundness
    (diagnostic fallbackPublic publicSound : Prop) :
    ay_tcfg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicSound) ->
    publicSound :=
  fun noClaim fallbackSound =>
    fallbackSound (ay_tcfg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_tcfg_failed_compaction_guard_cannot_bless_publication
    (diagnostic fallbackPublic publicationBlocked : Prop) :
    ay_tcfg_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> publicationBlocked) ->
    publicationBlocked :=
  fun noClaim blockedFromFallback =>
    blockedFromFallback (ay_tcfg_no_claim_preserves_fallback diagnostic
      fallbackPublic noClaim)

theorem ay_tcfg_accepted_compaction_is_layout_control
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    layoutControlHint :=
  ay_tcfg_accepted_compaction_hint guardEvidence agreementEvidence
    reasonReplayObligation layoutControlHint

theorem ay_tcfg_accepted_compaction_preserves_reason_replay
    (guardEvidence agreementEvidence reasonReplayObligation
      layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    reasonReplayObligation :=
  ay_tcfg_accepted_compaction_reason_obligation guardEvidence
    agreementEvidence reasonReplayObligation layoutControlHint

theorem ay_tcfg_accepted_compaction_preserves_public_soundness
    (guardEvidence agreementEvidence reasonReplayObligation layoutControlHint
      outcome formulaTruth publicSound : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    (guardEvidence -> agreementEvidence -> reasonReplayObligation -> outcome ->
      formulaTruth -> publicSound) ->
    outcome ->
    formulaTruth ->
    publicSound :=
  fun accepted soundFromEvidence outcomeH truthH =>
    soundFromEvidence
      (ay_tcfg_accepted_compaction_guard guardEvidence agreementEvidence
        reasonReplayObligation layoutControlHint accepted)
      (ay_tcfg_accepted_compaction_agreement guardEvidence agreementEvidence
        reasonReplayObligation layoutControlHint accepted)
      (ay_tcfg_accepted_compaction_reason_obligation guardEvidence
        agreementEvidence reasonReplayObligation layoutControlHint accepted)
      outcomeH
      truthH

theorem ay_tcfg_accepted_compaction_guides_sat
    (guardEvidence agreementEvidence reasonReplayObligation layoutControlHint
      satOutcome satTruth : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    satOutcome ->
    satTruth ->
    ay_tcfg_public_report guardEvidence satOutcome satTruth :=
  fun accepted satH truthH =>
    ay_tcfg_public_report_intro guardEvidence satOutcome satTruth
      (ay_tcfg_accepted_compaction_guard guardEvidence agreementEvidence
        reasonReplayObligation layoutControlHint accepted)
      satH
      truthH

theorem ay_tcfg_accepted_compaction_guides_unsat
    (guardEvidence agreementEvidence reasonReplayObligation layoutControlHint
      unsatOutcome unsatTruth : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    unsatOutcome ->
    unsatTruth ->
    ay_tcfg_public_report guardEvidence unsatOutcome unsatTruth :=
  fun accepted unsatH truthH =>
    ay_tcfg_public_report_intro guardEvidence unsatOutcome unsatTruth
      (ay_tcfg_accepted_compaction_guard guardEvidence agreementEvidence
        reasonReplayObligation layoutControlHint accepted)
      unsatH
      truthH

theorem ay_tcfg_compaction_preserves_formula_truth
    (formulaBefore formulaAfter guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint : Prop) :
    ay_tcfg_accepted_compaction guardEvidence agreementEvidence
      reasonReplayObligation layoutControlHint ->
    (layoutControlHint -> reasonReplayObligation -> formulaBefore ->
      formulaAfter) ->
    (layoutControlHint -> reasonReplayObligation -> formulaAfter ->
      formulaBefore) ->
    ay_tcfg_equisat formulaBefore formulaAfter :=
  fun accepted forward backward =>
    ay_tcfg_equisat_intro formulaBefore formulaAfter
      (forward
        (ay_tcfg_accepted_compaction_hint guardEvidence agreementEvidence
          reasonReplayObligation layoutControlHint accepted)
        (ay_tcfg_accepted_compaction_reason_obligation guardEvidence
          agreementEvidence reasonReplayObligation layoutControlHint accepted))
      (backward
        (ay_tcfg_accepted_compaction_hint guardEvidence agreementEvidence
          reasonReplayObligation layoutControlHint accepted)
        (ay_tcfg_accepted_compaction_reason_obligation guardEvidence
          agreementEvidence reasonReplayObligation layoutControlHint accepted))
