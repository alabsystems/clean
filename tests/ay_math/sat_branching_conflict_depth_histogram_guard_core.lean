-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded conflict-depth histogram guard soundness skeleton for ay SAT
-- solving. Conflict-depth and decision-level histograms may guide branching
-- or restart policy only when bucket data, decision levels, graph slices,
-- epochs, fallback baselines, solver builds, validator gates, and audit
-- evidence agree.

def ay_bcdh_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcdh_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bcdh_equisat (before : Prop) (after : Prop) :=
  ay_bcdh_conj (before -> after) (after -> before)

def ay_bcdh_histogram_guard
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (depthBuckets -> decisionLevelSnapshot -> implicationGraphSlice ->
      conflictEpoch -> fallbackBaseline -> solverBuildIdentity ->
      validatorGate -> auditEvidence -> result) ->
    result

def ay_bcdh_guard_agreement
    (bucketMatch : Prop) (levelSnapshotMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_bcdh_histogram_guard bucketMatch levelSnapshotMatch graphSliceMatch
    epochMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bcdh_accepted_hint
    (guard : Prop) (agreement : Prop) (histogramHint : Prop) :=
  ay_bcdh_conj guard (ay_bcdh_conj agreement histogramHint)

def ay_bcdh_outcome (model : Prop) (conflict : Prop) :=
  ay_bcdh_disj model conflict

def ay_bcdh_public_report (outcome : Prop) (formula : Prop) :=
  ay_bcdh_conj outcome formula

def ay_bcdh_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bcdh_conj hintCert public

def ay_bcdh_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bcdh_conj fallbackPublic diagnostic

theorem ay_bcdh_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bcdh_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcdh_conj_left
    (left : Prop) (right : Prop) :
    ay_bcdh_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcdh_conj_right
    (left : Prop) (right : Prop) :
    ay_bcdh_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcdh_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bcdh_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcdh_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bcdh_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcdh_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcdh_equisat before after :=
  fun forward backward =>
    ay_bcdh_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcdh_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bcdh_equisat before after -> before -> after :=
  fun equisat =>
    ay_bcdh_conj_left (before -> after) (after -> before) equisat

theorem ay_bcdh_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bcdh_equisat before after -> after -> before :=
  fun equisat =>
    ay_bcdh_conj_right (before -> after) (after -> before) equisat

theorem ay_bcdh_histogram_guard_intro
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    depthBuckets ->
    decisionLevelSnapshot ->
    implicationGraphSlice ->
    conflictEpoch ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence :=
  fun bucketH levelH graphH epochH fallbackH buildH validatorH auditH
      result build =>
    build bucketH levelH graphH epochH fallbackH buildH validatorH auditH

theorem ay_bcdh_histogram_guard_buckets
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    depthBuckets :=
  fun guard =>
    guard depthBuckets
      (fun bucketH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => bucketH)

theorem ay_bcdh_histogram_guard_level
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    decisionLevelSnapshot :=
  fun guard =>
    guard decisionLevelSnapshot
      (fun _bucketH levelH _graphH _epochH _fallbackH _buildH
          _validatorH _auditH => levelH)

theorem ay_bcdh_histogram_guard_graph
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    implicationGraphSlice :=
  fun guard =>
    guard implicationGraphSlice
      (fun _bucketH _levelH graphH _epochH _fallbackH _buildH
          _validatorH _auditH => graphH)

theorem ay_bcdh_histogram_guard_epoch
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    conflictEpoch :=
  fun guard =>
    guard conflictEpoch
      (fun _bucketH _levelH _graphH epochH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bcdh_histogram_guard_fallback
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _bucketH _levelH _graphH _epochH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bcdh_histogram_guard_build
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    guard solverBuildIdentity
      (fun _bucketH _levelH _graphH _epochH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bcdh_histogram_guard_validator
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _bucketH _levelH _graphH _epochH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bcdh_histogram_guard_audit
    (depthBuckets : Prop) (decisionLevelSnapshot : Prop)
    (implicationGraphSlice : Prop) (conflictEpoch : Prop)
    (fallbackBaseline : Prop) (solverBuildIdentity : Prop)
    (validatorGate : Prop) (auditEvidence : Prop) :
    ay_bcdh_histogram_guard depthBuckets decisionLevelSnapshot
      implicationGraphSlice conflictEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _bucketH _levelH _graphH _epochH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bcdh_guard_agreement_intro
    (bucketMatch : Prop) (levelSnapshotMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    bucketMatch ->
    levelSnapshotMatch ->
    graphSliceMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcdh_guard_agreement bucketMatch levelSnapshotMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun bucketH levelH graphH epochH fallbackH buildH validatorH auditH =>
    ay_bcdh_histogram_guard_intro bucketMatch levelSnapshotMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch bucketH levelH graphH epochH fallbackH buildH validatorH
      auditH

theorem ay_bcdh_guard_agreement_buckets
    (bucketMatch : Prop) (levelSnapshotMatch : Prop)
    (graphSliceMatch : Prop) (epochMatch : Prop)
    (fallbackMatch : Prop) (buildMatch : Prop)
    (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_bcdh_guard_agreement bucketMatch levelSnapshotMatch graphSliceMatch
      epochMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    bucketMatch :=
  fun agreement =>
    ay_bcdh_histogram_guard_buckets bucketMatch levelSnapshotMatch
      graphSliceMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch agreement

theorem ay_bcdh_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (histogramHint : Prop) :
    guard ->
    agreement ->
    histogramHint ->
    ay_bcdh_accepted_hint guard agreement histogramHint :=
  fun guardH agreementH hintH =>
    ay_bcdh_conj_intro guard (ay_bcdh_conj agreement histogramHint)
      guardH
      (ay_bcdh_conj_intro agreement histogramHint agreementH hintH)

theorem ay_bcdh_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (histogramHint : Prop) :
    ay_bcdh_accepted_hint guard agreement histogramHint -> guard :=
  fun accepted =>
    ay_bcdh_conj_left guard (ay_bcdh_conj agreement histogramHint)
      accepted

theorem ay_bcdh_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (histogramHint : Prop) :
    ay_bcdh_accepted_hint guard agreement histogramHint -> agreement :=
  fun accepted =>
    ay_bcdh_conj_left agreement histogramHint
      (ay_bcdh_conj_right guard (ay_bcdh_conj agreement histogramHint)
        accepted)

theorem ay_bcdh_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (histogramHint : Prop) :
    ay_bcdh_accepted_hint guard agreement histogramHint ->
    histogramHint :=
  fun accepted =>
    ay_bcdh_conj_right agreement histogramHint
      (ay_bcdh_conj_right guard (ay_bcdh_conj agreement histogramHint)
        accepted)

theorem ay_bcdh_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcdh_conj_intro (ay_bcdh_outcome model conflict) formula
      (ay_bcdh_disj_left model conflict modelH)
      formulaH

theorem ay_bcdh_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcdh_conj_intro (ay_bcdh_outcome model conflict) formula
      (ay_bcdh_disj_right model conflict conflictH)
      formulaH

theorem ay_bcdh_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bcdh_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bcdh_conj_intro hintCert public hintH publicH

theorem ay_bcdh_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bcdh_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcdh_conj_right hintCert public accepted

theorem ay_bcdh_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bcdh_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bcdh_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcdh_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcdh_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcdh_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcdh_bucket_drift_no_claim
    (bucketDrift : Prop) (fallbackPublic : Prop) :
    bucketDrift ->
    fallbackPublic ->
    ay_bcdh_no_claim bucketDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro bucketDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcdh_level_snapshot_mismatch_no_claim
    (levelSnapshotMismatch : Prop) (fallbackPublic : Prop) :
    levelSnapshotMismatch ->
    fallbackPublic ->
    ay_bcdh_no_claim levelSnapshotMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro levelSnapshotMismatch fallbackPublic
      fallbackH diagnosticH

theorem ay_bcdh_graph_slice_drift_no_claim
    (graphSliceDrift : Prop) (fallbackPublic : Prop) :
    graphSliceDrift ->
    fallbackPublic ->
    ay_bcdh_no_claim graphSliceDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro graphSliceDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcdh_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_bcdh_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcdh_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcdh_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bcdh_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bcdh_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcdh_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bcdh_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bcdh_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcdh_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcdh_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bcdh_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcdh_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bcdh_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bcdh_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (histogramHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcdh_accepted_hint guard agreement histogramHint ->
    model ->
    formula ->
    ay_bcdh_accepted_report
      (ay_bcdh_accepted_hint guard agreement histogramHint)
      (ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bcdh_accepted_report_intro
      (ay_bcdh_accepted_hint guard agreement histogramHint)
      (ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula)
      accepted
      (ay_bcdh_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcdh_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (histogramHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcdh_accepted_hint guard agreement histogramHint ->
    conflict ->
    formula ->
    ay_bcdh_accepted_report
      (ay_bcdh_accepted_hint guard agreement histogramHint)
      (ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bcdh_accepted_report_intro
      (ay_bcdh_accepted_hint guard agreement histogramHint)
      (ay_bcdh_public_report (ay_bcdh_outcome model conflict) formula)
      accepted
      (ay_bcdh_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bcdh_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bcdh_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcdh_accepted_report_public hintCert public accepted

theorem ay_bcdh_histogram_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bcdh_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bcdh_equisat_forward beforeHint afterHint equisat beforeH
