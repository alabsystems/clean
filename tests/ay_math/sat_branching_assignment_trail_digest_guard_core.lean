-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded assignment-trail digest guard soundness skeleton for ay SAT solving.
-- Trail summaries may guide branching and restart decisions only when the
-- assignment digest, decision levels, implication graph slice, variable map,
-- fallback baseline, solver build, validator gate, and audit evidence agree.

def ay_batd_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_batd_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_batd_equisat (before : Prop) (after : Prop) :=
  ay_batd_conj (before -> after) (after -> before)

def ay_batd_trail_digest_guard
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (assignmentTrailDigest -> decisionLevelSnapshot ->
      implicationGraphSlice -> variableMap -> fallbackBaseline ->
      solverBuildIdentity -> validatorGate -> auditEvidence -> result) ->
    result

def ay_batd_guard_agreement
    (digestMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (variableMapMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_batd_trail_digest_guard digestMatch levelMatch graphSliceMatch
    variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_batd_accepted_hint
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop) :=
  ay_batd_conj guard (ay_batd_conj agreement trailDigestHint)

def ay_batd_outcome (model : Prop) (conflict : Prop) :=
  ay_batd_disj model conflict

def ay_batd_public_report (outcome : Prop) (formula : Prop) :=
  ay_batd_conj outcome formula

def ay_batd_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_batd_conj hintCert public

def ay_batd_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_batd_conj fallbackPublic diagnostic

theorem ay_batd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_batd_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_batd_conj_left
    (left : Prop) (right : Prop) :
    ay_batd_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_batd_conj_right
    (left : Prop) (right : Prop) :
    ay_batd_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_batd_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_batd_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_batd_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_batd_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_batd_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_batd_equisat before after :=
  fun forward backward =>
    ay_batd_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_batd_equisat_forward
    (before : Prop) (after : Prop) :
    ay_batd_equisat before after -> before -> after :=
  fun equisat =>
    ay_batd_conj_left (before -> after) (after -> before) equisat

theorem ay_batd_equisat_backward
    (before : Prop) (after : Prop) :
    ay_batd_equisat before after -> after -> before :=
  fun equisat =>
    ay_batd_conj_right (before -> after) (after -> before) equisat

theorem ay_batd_trail_digest_guard_intro
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    assignmentTrailDigest ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    variableMap ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence :=
  fun digestH levelH graphH mapH fallbackH buildH validatorH auditH
      result build =>
    build digestH levelH graphH mapH fallbackH buildH validatorH auditH

theorem ay_batd_trail_digest_guard_digest
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    assignmentTrailDigest :=
  fun guard =>
    guard assignmentTrailDigest
      (fun digestH _levelH _graphH _mapH _fallbackH _buildH
          _validatorH _auditH => digestH)

theorem ay_batd_trail_digest_guard_level
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _digestH levelH _graphH _mapH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_batd_trail_digest_guard_graph
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _digestH _levelH graphH _mapH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_batd_trail_digest_guard_variable_map
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    variableMap :=
  fun guard =>
    guard variableMap
      (fun _digestH _levelH _graphH mapH _fallbackH _buildH
          _validatorH _auditH => mapH)

theorem ay_batd_trail_digest_guard_fallback
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _digestH _levelH _graphH _mapH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_batd_trail_digest_guard_build
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    guard solverBuildIdentity
      (fun _digestH _levelH _graphH _mapH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_batd_trail_digest_guard_validator
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _digestH _levelH _graphH _mapH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_batd_trail_digest_guard_audit
    (assignmentTrailDigest : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (variableMap : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_batd_trail_digest_guard assignmentTrailDigest
      decisionLevelSnapshot implicationGraphSlice variableMap fallbackBaseline
      solverBuildIdentity validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _digestH _levelH _graphH _mapH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_batd_guard_agreement_intro
    (digestMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (variableMapMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    digestMatch ->
    levelMatch ->
    graphSliceMatch ->
    variableMapMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_batd_guard_agreement digestMatch levelMatch graphSliceMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun digestH levelH graphH mapH fallbackH buildH validatorH auditH =>
    ay_batd_trail_digest_guard_intro digestMatch levelMatch graphSliceMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch
      digestH levelH graphH mapH fallbackH buildH validatorH auditH

theorem ay_batd_guard_agreement_digest
    (digestMatch : Prop) (levelMatch : Prop)
    (graphSliceMatch : Prop) (variableMapMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_batd_guard_agreement digestMatch levelMatch graphSliceMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    digestMatch :=
  fun agreement =>
    ay_batd_trail_digest_guard_digest digestMatch levelMatch graphSliceMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_batd_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop) :
    guard ->
    agreement ->
    trailDigestHint ->
    ay_batd_accepted_hint guard agreement trailDigestHint :=
  fun guardH agreementH hintH =>
    ay_batd_conj_intro guard (ay_batd_conj agreement trailDigestHint)
      guardH
      (ay_batd_conj_intro agreement trailDigestHint agreementH hintH)

theorem ay_batd_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop) :
    ay_batd_accepted_hint guard agreement trailDigestHint -> guard :=
  fun accepted =>
    ay_batd_conj_left guard (ay_batd_conj agreement trailDigestHint)
      accepted

theorem ay_batd_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop) :
    ay_batd_accepted_hint guard agreement trailDigestHint -> agreement :=
  fun accepted =>
    ay_batd_conj_left agreement trailDigestHint
      (ay_batd_conj_right guard (ay_batd_conj agreement trailDigestHint)
        accepted)

theorem ay_batd_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop) :
    ay_batd_accepted_hint guard agreement trailDigestHint ->
    trailDigestHint :=
  fun accepted =>
    ay_batd_conj_right agreement trailDigestHint
      (ay_batd_conj_right guard (ay_batd_conj agreement trailDigestHint)
        accepted)

theorem ay_batd_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_batd_public_report (ay_batd_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_batd_conj_intro (ay_batd_outcome model conflict) formula
      (ay_batd_disj_left model conflict modelH)
      formulaH

theorem ay_batd_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_batd_public_report (ay_batd_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_batd_conj_intro (ay_batd_outcome model conflict) formula
      (ay_batd_disj_right model conflict conflictH)
      formulaH

theorem ay_batd_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_batd_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_batd_conj_intro hintCert public hintH publicH

theorem ay_batd_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_batd_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_batd_conj_right hintCert public accepted

theorem ay_batd_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_batd_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_batd_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_batd_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_batd_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_batd_conj_left fallbackPublic diagnostic noClaim

theorem ay_batd_digest_mismatch_no_claim
    (digestMismatch : Prop) (fallbackPublic : Prop) :
    digestMismatch ->
    fallbackPublic ->
    ay_batd_no_claim digestMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro digestMismatch fallbackPublic fallbackH diagnosticH

theorem ay_batd_level_drift_no_claim
    (levelDrift : Prop) (fallbackPublic : Prop) :
    levelDrift ->
    fallbackPublic ->
    ay_batd_no_claim levelDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro levelDrift fallbackPublic fallbackH diagnosticH

theorem ay_batd_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_batd_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_batd_variable_map_drift_no_claim
    (variableMapDrift : Prop) (fallbackPublic : Prop) :
    variableMapDrift ->
    fallbackPublic ->
    ay_batd_no_claim variableMapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro variableMapDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_batd_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_batd_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_batd_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_batd_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_batd_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_batd_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_batd_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_batd_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_batd_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_batd_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_batd_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_batd_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_batd_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_batd_accepted_hint guard agreement trailDigestHint ->
    model ->
    formula ->
    ay_batd_accepted_report
      (ay_batd_accepted_hint guard agreement trailDigestHint)
      (ay_batd_public_report (ay_batd_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_batd_accepted_report_intro
      (ay_batd_accepted_hint guard agreement trailDigestHint)
      (ay_batd_public_report (ay_batd_outcome model conflict) formula)
      accepted
      (ay_batd_public_sat_report model conflict formula modelH formulaH)

theorem ay_batd_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (trailDigestHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_batd_accepted_hint guard agreement trailDigestHint ->
    conflict ->
    formula ->
    ay_batd_accepted_report
      (ay_batd_accepted_hint guard agreement trailDigestHint)
      (ay_batd_public_report (ay_batd_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_batd_accepted_report_intro
      (ay_batd_accepted_hint guard agreement trailDigestHint)
      (ay_batd_public_report (ay_batd_outcome model conflict) formula)
      accepted
      (ay_batd_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_batd_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_batd_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_batd_accepted_report_public hintCert public accepted

theorem ay_batd_trail_digest_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_batd_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_batd_equisat_forward beforeHint afterHint equisat beforeH
