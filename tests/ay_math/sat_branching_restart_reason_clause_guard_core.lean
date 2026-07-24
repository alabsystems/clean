-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart reason-clause guard soundness skeleton for ay SAT solving.
-- Restart decisions may use reason-clause summaries only when reason ids,
-- implication graph slices, decision levels, conflict epochs, fallback
-- baselines, solver builds, validator gates, and audit evidence agree.

def ay_brrc_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brrc_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brrc_equisat (before : Prop) (after : Prop) :=
  ay_brrc_conj (before -> after) (after -> before)

def ay_brrc_reason_clause_guard
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (reasonClauseIds -> implicationGraphSlice -> decisionLevelSnapshot ->
      conflictEpoch -> fallbackBaseline -> solverBuildIdentity ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_brrc_guard_agreement
    (reasonClauseMatch : Prop) (graphSliceMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_brrc_reason_clause_guard reasonClauseMatch graphSliceMatch levelMatch
    epochMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brrc_accepted_hint
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :=
  ay_brrc_conj guard (ay_brrc_conj agreement restartHint)

def ay_brrc_outcome (model : Prop) (conflict : Prop) :=
  ay_brrc_disj model conflict

def ay_brrc_public_report (outcome : Prop) (formula : Prop) :=
  ay_brrc_conj outcome formula

def ay_brrc_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_brrc_conj hintCert public

def ay_brrc_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_brrc_conj fallbackPublic diagnostic

theorem ay_brrc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_brrc_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brrc_conj_left
    (left : Prop) (right : Prop) :
    ay_brrc_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brrc_conj_right
    (left : Prop) (right : Prop) :
    ay_brrc_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brrc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_brrc_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brrc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_brrc_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brrc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_brrc_equisat before after :=
  fun forward backward =>
    ay_brrc_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brrc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_brrc_equisat before after -> before -> after :=
  fun equisat =>
    ay_brrc_conj_left (before -> after) (after -> before) equisat

theorem ay_brrc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_brrc_equisat before after -> after -> before :=
  fun equisat =>
    ay_brrc_conj_right (before -> after) (after -> before) equisat

theorem ay_brrc_reason_clause_guard_intro
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    reasonClauseIds ->
    implicationGraphSlice ->
    decisionLevelSnapshot ->
    conflictEpoch ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence :=
  fun reasonH graphH levelH epochH fallbackH buildH validatorH auditH
      result build =>
    build reasonH graphH levelH epochH fallbackH buildH validatorH auditH

theorem ay_brrc_reason_clause_guard_reasons
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    reasonClauseIds :=
  fun guard =>
    guard reasonClauseIds
      (fun reasonH _graphH _levelH _epochH _fallbackH _buildH
          _validatorH _auditH => reasonH)

theorem ay_brrc_reason_clause_guard_graph
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _reasonH graphH _levelH _epochH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_brrc_reason_clause_guard_level
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _reasonH _graphH levelH _epochH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_brrc_reason_clause_guard_epoch
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    conflictEpoch :=
  fun guard =>
    guard conflictEpoch
      (fun _reasonH _graphH _levelH epochH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_brrc_reason_clause_guard_fallback
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _reasonH _graphH _levelH _epochH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brrc_reason_clause_guard_build
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    guard solverBuildIdentity
      (fun _reasonH _graphH _levelH _epochH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brrc_reason_clause_guard_validator
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _reasonH _graphH _levelH _epochH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brrc_reason_clause_guard_audit
    (reasonClauseIds : Prop) (implicationGraphSlice : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_brrc_reason_clause_guard reasonClauseIds implicationGraphSlice
      decisionLevelSnapshot conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _reasonH _graphH _levelH _epochH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brrc_guard_agreement_intro
    (reasonClauseMatch : Prop) (graphSliceMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    reasonClauseMatch ->
    graphSliceMatch ->
    levelMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brrc_guard_agreement reasonClauseMatch graphSliceMatch levelMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun reasonH graphH levelH epochH fallbackH buildH validatorH auditH =>
    ay_brrc_reason_clause_guard_intro reasonClauseMatch graphSliceMatch
      levelMatch epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      reasonH graphH levelH epochH fallbackH buildH validatorH auditH

theorem ay_brrc_guard_agreement_reasons
    (reasonClauseMatch : Prop) (graphSliceMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_brrc_guard_agreement reasonClauseMatch graphSliceMatch levelMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    reasonClauseMatch :=
  fun agreement =>
    ay_brrc_reason_clause_guard_reasons reasonClauseMatch graphSliceMatch
      levelMatch epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_brrc_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    guard ->
    agreement ->
    restartHint ->
    ay_brrc_accepted_hint guard agreement restartHint :=
  fun guardH agreementH hintH =>
    ay_brrc_conj_intro guard (ay_brrc_conj agreement restartHint)
      guardH
      (ay_brrc_conj_intro agreement restartHint agreementH hintH)

theorem ay_brrc_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_brrc_accepted_hint guard agreement restartHint -> guard :=
  fun accepted =>
    ay_brrc_conj_left guard (ay_brrc_conj agreement restartHint) accepted

theorem ay_brrc_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_brrc_accepted_hint guard agreement restartHint -> agreement :=
  fun accepted =>
    ay_brrc_conj_left agreement restartHint
      (ay_brrc_conj_right guard (ay_brrc_conj agreement restartHint)
        accepted)

theorem ay_brrc_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (restartHint : Prop) :
    ay_brrc_accepted_hint guard agreement restartHint -> restartHint :=
  fun accepted =>
    ay_brrc_conj_right agreement restartHint
      (ay_brrc_conj_right guard (ay_brrc_conj agreement restartHint)
        accepted)

theorem ay_brrc_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_brrc_public_report (ay_brrc_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brrc_conj_intro (ay_brrc_outcome model conflict) formula
      (ay_brrc_disj_left model conflict modelH)
      formulaH

theorem ay_brrc_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_brrc_public_report (ay_brrc_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brrc_conj_intro (ay_brrc_outcome model conflict) formula
      (ay_brrc_disj_right model conflict conflictH)
      formulaH

theorem ay_brrc_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_brrc_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_brrc_conj_intro hintCert public hintH publicH

theorem ay_brrc_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_brrc_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brrc_conj_right hintCert public accepted

theorem ay_brrc_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_brrc_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_brrc_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brrc_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brrc_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brrc_conj_left fallbackPublic diagnostic noClaim

theorem ay_brrc_stale_reason_clause_no_claim
    (staleReasonClause : Prop) (fallbackPublic : Prop) :
    staleReasonClause ->
    fallbackPublic ->
    ay_brrc_no_claim staleReasonClause fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro staleReasonClause fallbackPublic
      fallbackH diagnosticH

theorem ay_brrc_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_brrc_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_brrc_level_mismatch_no_claim
    (levelMismatch : Prop) (fallbackPublic : Prop) :
    levelMismatch ->
    fallbackPublic ->
    ay_brrc_no_claim levelMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro levelMismatch fallbackPublic fallbackH diagnosticH

theorem ay_brrc_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_brrc_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_brrc_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brrc_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_brrc_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_brrc_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_brrc_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_brrc_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_brrc_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brrc_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brrc_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_brrc_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brrc_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_brrc_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_brrc_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (restartHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brrc_accepted_hint guard agreement restartHint ->
    model ->
    formula ->
    ay_brrc_accepted_report
      (ay_brrc_accepted_hint guard agreement restartHint)
      (ay_brrc_public_report (ay_brrc_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_brrc_accepted_report_intro
      (ay_brrc_accepted_hint guard agreement restartHint)
      (ay_brrc_public_report (ay_brrc_outcome model conflict) formula)
      accepted
      (ay_brrc_public_sat_report model conflict formula modelH formulaH)

theorem ay_brrc_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (restartHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brrc_accepted_hint guard agreement restartHint ->
    conflict ->
    formula ->
    ay_brrc_accepted_report
      (ay_brrc_accepted_hint guard agreement restartHint)
      (ay_brrc_public_report (ay_brrc_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_brrc_accepted_report_intro
      (ay_brrc_accepted_hint guard agreement restartHint)
      (ay_brrc_public_report (ay_brrc_outcome model conflict) formula)
      accepted
      (ay_brrc_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_brrc_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_brrc_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_brrc_accepted_report_public hintCert public accepted

theorem ay_brrc_restart_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_brrc_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_brrc_equisat_forward beforeHint afterHint equisat beforeH
