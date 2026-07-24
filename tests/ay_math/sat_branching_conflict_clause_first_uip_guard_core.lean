-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- First-UIP conflict clause guard skeleton for sequential-main SAT. A learned
-- clause can guide conflict analysis only when graph, cut, asserting literal,
-- clause digest, propagation replay, fallback, build, validator, and audit
-- evidence agree.

def ay_fuig_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_fuig_equisat (before : Prop) (after : Prop) : Prop :=
  ay_fuig_conj (before -> after) (after -> before)

def ay_fuig_guard
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (implicationGraphSnapshot ->
      cutWitnessLedger ->
      assertingLiteralManifest ->
      learntClauseDigest ->
      propagationReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_fuig_agreement
    (graphMatch : Prop)
    (cutMatch : Prop)
    (assertingMatch : Prop)
    (digestMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_fuig_guard graphMatch cutMatch assertingMatch digestMatch replayMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_fuig_accepted_clause
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) : Prop :=
  ay_fuig_conj guardEvidence
    (ay_fuig_conj agreementEvidence learnedConsequence)

def ay_fuig_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_fuig_conj acceptedEvidence (ay_fuig_conj outcome formulaTruth)

def ay_fuig_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_fuig_conj diagnostic fallbackPublic

theorem ay_fuig_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_fuig_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_fuig_conj_left (left : Prop) (right : Prop) :
    ay_fuig_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_fuig_conj_right (left : Prop) (right : Prop) :
    ay_fuig_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_fuig_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_fuig_equisat before after :=
  fun forward backward =>
    ay_fuig_conj_intro (before -> after) (after -> before) forward backward

theorem ay_fuig_equisat_forward (before : Prop) (after : Prop) :
    ay_fuig_equisat before after -> before -> after :=
  fun eqsat =>
    ay_fuig_conj_left (before -> after) (after -> before) eqsat

theorem ay_fuig_equisat_backward (before : Prop) (after : Prop) :
    ay_fuig_equisat before after -> after -> before :=
  fun eqsat =>
    ay_fuig_conj_right (before -> after) (after -> before) eqsat

theorem ay_fuig_guard_intro
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    implicationGraphSnapshot ->
    cutWitnessLedger ->
    assertingLiteralManifest ->
    learntClauseDigest ->
    propagationReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript :=
  fun graphH cutH assertingH digestH replayH fallbackH buildH validatorH
      auditH result build =>
    build graphH cutH assertingH digestH replayH fallbackH buildH validatorH
      auditH

theorem ay_fuig_guard_graph
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    implicationGraphSnapshot :=
  fun guard =>
    guard implicationGraphSnapshot
      (fun graphH _cutH _assertingH _digestH _replayH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_fuig_guard_cut
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    cutWitnessLedger :=
  fun guard =>
    guard cutWitnessLedger
      (fun _graphH cutH _assertingH _digestH _replayH _fallbackH _buildH
          _validatorH _auditH => cutH)

theorem ay_fuig_guard_asserting
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    assertingLiteralManifest :=
  fun guard =>
    guard assertingLiteralManifest
      (fun _graphH _cutH assertingH _digestH _replayH _fallbackH _buildH
          _validatorH _auditH => assertingH)

theorem ay_fuig_guard_digest
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    learntClauseDigest :=
  fun guard =>
    guard learntClauseDigest
      (fun _graphH _cutH _assertingH digestH _replayH _fallbackH _buildH
          _validatorH _auditH => digestH)

theorem ay_fuig_guard_replay
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _graphH _cutH _assertingH _digestH replayH _fallbackH _buildH
          _validatorH _auditH => replayH)

theorem ay_fuig_guard_fallback
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _graphH _cutH _assertingH _digestH _replayH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_fuig_guard_build
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _graphH _cutH _assertingH _digestH _replayH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_fuig_guard_validator
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _graphH _cutH _assertingH _digestH _replayH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_fuig_guard_audit
    (implicationGraphSnapshot : Prop)
    (cutWitnessLedger : Prop)
    (assertingLiteralManifest : Prop)
    (learntClauseDigest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) :
    ay_fuig_guard implicationGraphSnapshot cutWitnessLedger
      assertingLiteralManifest learntClauseDigest propagationReplay
      fallbackBaseline buildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _graphH _cutH _assertingH _digestH _replayH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_fuig_agreement_intro
    (graphMatch : Prop)
    (cutMatch : Prop)
    (assertingMatch : Prop)
    (digestMatch : Prop)
    (replayMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    graphMatch ->
    cutMatch ->
    assertingMatch ->
    digestMatch ->
    replayMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_fuig_agreement graphMatch cutMatch assertingMatch digestMatch
      replayMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_fuig_guard_intro graphMatch cutMatch assertingMatch digestMatch
    replayMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_fuig_accepted_clause_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) :
    guardEvidence ->
    agreementEvidence ->
    learnedConsequence ->
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence :=
  fun guardH agreementH learnedH =>
    ay_fuig_conj_intro guardEvidence
      (ay_fuig_conj agreementEvidence learnedConsequence)
      guardH
      (ay_fuig_conj_intro agreementEvidence learnedConsequence
        agreementH learnedH)

theorem ay_fuig_accepted_clause_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    guardEvidence :=
  fun accepted =>
    ay_fuig_conj_left guardEvidence
      (ay_fuig_conj agreementEvidence learnedConsequence)
      accepted

theorem ay_fuig_accepted_clause_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    agreementEvidence :=
  fun accepted =>
    ay_fuig_conj_left agreementEvidence learnedConsequence
      (ay_fuig_conj_right guardEvidence
        (ay_fuig_conj agreementEvidence learnedConsequence)
        accepted)

theorem ay_fuig_accepted_clause_learned_consequence
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    learnedConsequence :=
  fun accepted =>
    ay_fuig_conj_right agreementEvidence learnedConsequence
      (ay_fuig_conj_right guardEvidence
        (ay_fuig_conj agreementEvidence learnedConsequence)
        accepted)

theorem ay_fuig_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_fuig_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_fuig_conj_intro acceptedEvidence
      (ay_fuig_conj outcome formulaTruth)
      acceptedH
      (ay_fuig_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_fuig_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_fuig_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_fuig_conj_left acceptedEvidence
      (ay_fuig_conj outcome formulaTruth)
      public

theorem ay_fuig_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_fuig_no_claim diagnostic fallbackPublic :=
  ay_fuig_conj_intro diagnostic fallbackPublic

theorem ay_fuig_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_fuig_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_fuig_conj_right diagnostic fallbackPublic noClaim

theorem ay_fuig_graph_failure_no_claim
    (graphFailure : Prop)
    (fallbackPublic : Prop) :
    graphFailure -> fallbackPublic -> ay_fuig_no_claim graphFailure fallbackPublic :=
  ay_fuig_no_claim_intro graphFailure fallbackPublic

theorem ay_fuig_cut_failure_no_claim
    (cutFailure : Prop)
    (fallbackPublic : Prop) :
    cutFailure -> fallbackPublic -> ay_fuig_no_claim cutFailure fallbackPublic :=
  ay_fuig_no_claim_intro cutFailure fallbackPublic

theorem ay_fuig_asserting_failure_no_claim
    (assertingFailure : Prop)
    (fallbackPublic : Prop) :
    assertingFailure ->
    fallbackPublic ->
    ay_fuig_no_claim assertingFailure fallbackPublic :=
  ay_fuig_no_claim_intro assertingFailure fallbackPublic

theorem ay_fuig_digest_failure_no_claim
    (digestFailure : Prop)
    (fallbackPublic : Prop) :
    digestFailure ->
    fallbackPublic ->
    ay_fuig_no_claim digestFailure fallbackPublic :=
  ay_fuig_no_claim_intro digestFailure fallbackPublic

theorem ay_fuig_replay_failure_no_claim
    (replayFailure : Prop)
    (fallbackPublic : Prop) :
    replayFailure ->
    fallbackPublic ->
    ay_fuig_no_claim replayFailure fallbackPublic :=
  ay_fuig_no_claim_intro replayFailure fallbackPublic

theorem ay_fuig_fallback_failure_no_claim
    (fallbackFailure : Prop)
    (fallbackPublic : Prop) :
    fallbackFailure ->
    fallbackPublic ->
    ay_fuig_no_claim fallbackFailure fallbackPublic :=
  ay_fuig_no_claim_intro fallbackFailure fallbackPublic

theorem ay_fuig_build_failure_no_claim
    (buildFailure : Prop)
    (fallbackPublic : Prop) :
    buildFailure -> fallbackPublic -> ay_fuig_no_claim buildFailure fallbackPublic :=
  ay_fuig_no_claim_intro buildFailure fallbackPublic

theorem ay_fuig_validator_failure_no_claim
    (validatorFailure : Prop)
    (fallbackPublic : Prop) :
    validatorFailure ->
    fallbackPublic ->
    ay_fuig_no_claim validatorFailure fallbackPublic :=
  ay_fuig_no_claim_intro validatorFailure fallbackPublic

theorem ay_fuig_audit_failure_no_claim
    (auditFailure : Prop)
    (fallbackPublic : Prop) :
    auditFailure -> fallbackPublic -> ay_fuig_no_claim auditFailure fallbackPublic :=
  ay_fuig_no_claim_intro auditFailure fallbackPublic

theorem ay_fuig_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_fuig_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_fuig_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_fuig_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_fuig_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_fuig_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_fuig_accepted_clause_is_valid_learned_consequence
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    learnedConsequence :=
  ay_fuig_accepted_clause_learned_consequence guardEvidence agreementEvidence
    learnedConsequence

theorem ay_fuig_accepted_clause_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    ay_fuig_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_fuig_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_fuig_accepted_clause_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    satOutcome ->
    formulaTruth ->
    ay_fuig_public_report
      (ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_fuig_public_report_intro
      (ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_fuig_accepted_clause_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    unsatOutcome ->
    formulaTruth ->
    ay_fuig_public_report
      (ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence)
      unsatOutcome
      formulaTruth :=
  ay_fuig_accepted_clause_guides_sat guardEvidence agreementEvidence
    learnedConsequence unsatOutcome formulaTruth

theorem ay_fuig_learned_clause_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (learnedConsequence : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_fuig_accepted_clause guardEvidence agreementEvidence learnedConsequence ->
    ay_fuig_equisat beforeTruth afterTruth ->
    ay_fuig_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_fuig_equisat_intro afterTruth beforeTruth
      (ay_fuig_equisat_backward beforeTruth afterTruth eqsat)
      (ay_fuig_equisat_forward beforeTruth afterTruth eqsat)
