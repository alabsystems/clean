-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Conflict-clause minimization replay guard skeleton for sequential-main SAT.
-- Minimized conflict clauses are solver state only when first-UIP/minimization,
-- removed-literal, assertion-level, activity, fallback, build, validator, and
-- audit evidence agree.

def ay_bccm_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bccm_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bccm_conj (before -> after) (after -> before)

def ay_bccm_replay_guard
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (conflictMinimization ->
      removedLiterals ->
      assertionLevel ->
      activityReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bccm_guard_agreement
    (minimizationMatch : Prop)
    (removedLiteralMatch : Prop)
    (assertionMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bccm_replay_guard minimizationMatch removedLiteralMatch assertionMatch
    activityMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bccm_accepted_clause
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop) : Prop :=
  ay_bccm_conj guardEvidence (ay_bccm_conj agreementEvidence minimizedClause)

def ay_bccm_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bccm_conj acceptedEvidence (ay_bccm_conj outcome formulaTruth)

def ay_bccm_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bccm_conj diagnostic fallbackPublic

theorem ay_bccm_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bccm_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bccm_conj_left (left : Prop) (right : Prop) :
    ay_bccm_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bccm_conj_right (left : Prop) (right : Prop) :
    ay_bccm_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bccm_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bccm_equisat before after :=
  fun forward backward =>
    ay_bccm_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bccm_equisat_forward (before : Prop) (after : Prop) :
    ay_bccm_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bccm_conj_left (before -> after) (after -> before) eqsat

theorem ay_bccm_equisat_backward (before : Prop) (after : Prop) :
    ay_bccm_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bccm_conj_right (before -> after) (after -> before) eqsat

theorem ay_bccm_replay_guard_intro
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    conflictMinimization ->
    removedLiterals ->
    assertionLevel ->
    activityReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun minimizationH removedH assertionH activityH fallbackH buildH
      validatorH auditH result build =>
    build minimizationH removedH assertionH activityH fallbackH buildH
      validatorH auditH

theorem ay_bccm_replay_guard_minimization
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    conflictMinimization :=
  fun guard =>
    guard conflictMinimization
      (fun minimizationH _removedH _assertionH _activityH _fallbackH
          _buildH _validatorH _auditH => minimizationH)

theorem ay_bccm_replay_guard_removed_literals
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    removedLiterals :=
  fun guard =>
    guard removedLiterals
      (fun _minimizationH removedH _assertionH _activityH _fallbackH
          _buildH _validatorH _auditH => removedH)

theorem ay_bccm_replay_guard_assertion
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    assertionLevel :=
  fun guard =>
    guard assertionLevel
      (fun _minimizationH _removedH assertionH _activityH _fallbackH
          _buildH _validatorH _auditH => assertionH)

theorem ay_bccm_replay_guard_activity
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityReplay :=
  fun guard =>
    guard activityReplay
      (fun _minimizationH _removedH _assertionH activityH _fallbackH
          _buildH _validatorH _auditH => activityH)

theorem ay_bccm_replay_guard_fallback
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _minimizationH _removedH _assertionH _activityH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_bccm_replay_guard_build
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _minimizationH _removedH _assertionH _activityH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_bccm_replay_guard_validator
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _minimizationH _removedH _assertionH _activityH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_bccm_replay_guard_audit
    (conflictMinimization : Prop)
    (removedLiterals : Prop)
    (assertionLevel : Prop)
    (activityReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bccm_replay_guard conflictMinimization removedLiterals assertionLevel
      activityReplay fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _minimizationH _removedH _assertionH _activityH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_bccm_guard_agreement_intro
    (minimizationMatch : Prop)
    (removedLiteralMatch : Prop)
    (assertionMatch : Prop)
    (activityMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    minimizationMatch ->
    removedLiteralMatch ->
    assertionMatch ->
    activityMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bccm_guard_agreement minimizationMatch removedLiteralMatch
      assertionMatch activityMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  ay_bccm_replay_guard_intro minimizationMatch removedLiteralMatch
    assertionMatch activityMatch fallbackMatch buildMatch validatorAccepts
    auditMatch

theorem ay_bccm_accepted_clause_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop) :
    guardEvidence ->
    agreementEvidence ->
    minimizedClause ->
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause :=
  fun guardH agreementH clauseH =>
    ay_bccm_conj_intro guardEvidence
      (ay_bccm_conj agreementEvidence minimizedClause)
      guardH
      (ay_bccm_conj_intro agreementEvidence minimizedClause agreementH clauseH)

theorem ay_bccm_accepted_clause_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    guardEvidence :=
  fun accepted =>
    ay_bccm_conj_left guardEvidence
      (ay_bccm_conj agreementEvidence minimizedClause)
      accepted

theorem ay_bccm_accepted_clause_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    agreementEvidence :=
  fun accepted =>
    ay_bccm_conj_left agreementEvidence minimizedClause
      (ay_bccm_conj_right guardEvidence
        (ay_bccm_conj agreementEvidence minimizedClause)
        accepted)

theorem ay_bccm_accepted_clause_clause
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    minimizedClause :=
  fun accepted =>
    ay_bccm_conj_right agreementEvidence minimizedClause
      (ay_bccm_conj_right guardEvidence
        (ay_bccm_conj agreementEvidence minimizedClause)
        accepted)

theorem ay_bccm_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bccm_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bccm_conj_intro acceptedEvidence
      (ay_bccm_conj outcome formulaTruth)
      acceptedH
      (ay_bccm_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bccm_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bccm_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bccm_conj_left acceptedEvidence
      (ay_bccm_conj outcome formulaTruth)
      public

theorem ay_bccm_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bccm_no_claim diagnostic fallbackPublic :=
  ay_bccm_conj_intro diagnostic fallbackPublic

theorem ay_bccm_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bccm_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bccm_conj_right diagnostic fallbackPublic noClaim

theorem ay_bccm_minimization_drift_no_claim
    (minimizationDrift : Prop)
    (fallbackPublic : Prop) :
    minimizationDrift ->
    fallbackPublic ->
    ay_bccm_no_claim minimizationDrift fallbackPublic :=
  ay_bccm_no_claim_intro minimizationDrift fallbackPublic

theorem ay_bccm_removed_literal_mismatch_no_claim
    (removedLiteralMismatch : Prop)
    (fallbackPublic : Prop) :
    removedLiteralMismatch ->
    fallbackPublic ->
    ay_bccm_no_claim removedLiteralMismatch fallbackPublic :=
  ay_bccm_no_claim_intro removedLiteralMismatch fallbackPublic

theorem ay_bccm_assertion_mismatch_no_claim
    (assertionMismatch : Prop)
    (fallbackPublic : Prop) :
    assertionMismatch ->
    fallbackPublic ->
    ay_bccm_no_claim assertionMismatch fallbackPublic :=
  ay_bccm_no_claim_intro assertionMismatch fallbackPublic

theorem ay_bccm_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bccm_no_claim staleBuild fallbackPublic :=
  ay_bccm_no_claim_intro staleBuild fallbackPublic

theorem ay_bccm_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bccm_no_claim auditContradiction fallbackPublic :=
  ay_bccm_no_claim_intro auditContradiction fallbackPublic

theorem ay_bccm_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bccm_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bccm_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bccm_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bccm_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bccm_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bccm_accepted_clause_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    satOutcome ->
    formulaTruth ->
    ay_bccm_public_report
      (ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bccm_public_report_intro
      (ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bccm_accepted_clause_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    unsatOutcome ->
    formulaTruth ->
    ay_bccm_public_report
      (ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause)
      unsatOutcome
      formulaTruth :=
  ay_bccm_accepted_clause_guides_sat guardEvidence agreementEvidence
    minimizedClause unsatOutcome formulaTruth

theorem ay_bccm_accepted_clause_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    ay_bccm_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bccm_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bccm_minimized_clause_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (minimizedClause : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bccm_accepted_clause guardEvidence agreementEvidence minimizedClause ->
    ay_bccm_equisat beforeTruth afterTruth ->
    ay_bccm_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bccm_equisat_intro afterTruth beforeTruth
      (ay_bccm_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bccm_equisat_forward beforeTruth afterTruth eqsat)
