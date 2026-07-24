-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause bump/decay guard soundness skeleton for ay SAT solving.
-- Learned-clause bump and decay choices may guide branching only when bump
-- events, decay factors, clause identity maps, LBD/activity ledgers, restart
-- epochs, fallback baselines, solver builds, validator gates, and audit
-- evidence agree.

def ay_bcbd_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcbd_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bcbd_equisat (before : Prop) (after : Prop) :=
  ay_bcbd_conj (before -> after) (after -> before)

def ay_bcbd_bump_decay_guard
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (bumpEvents -> decayFactor -> clauseIdentityMap ->
      lbdActivityLedger -> restartEpoch -> fallbackBaseline ->
      solverBuildIdentity -> validatorGate -> auditEvidence -> result) ->
    result

def ay_bcbd_guard_agreement
    (bumpMatch : Prop) (decayMatch : Prop)
    (clauseMapMatch : Prop) (ledgerMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bcbd_bump_decay_guard bumpMatch decayMatch clauseMapMatch ledgerMatch
    epochMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bcbd_accepted_hint
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :=
  ay_bcbd_conj guard (ay_bcbd_conj agreement branchingHint)

def ay_bcbd_outcome (model : Prop) (conflict : Prop) :=
  ay_bcbd_disj model conflict

def ay_bcbd_public_report (outcome : Prop) (formula : Prop) :=
  ay_bcbd_conj outcome formula

def ay_bcbd_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bcbd_conj hintCert public

def ay_bcbd_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bcbd_conj fallbackPublic diagnostic

theorem ay_bcbd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bcbd_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcbd_conj_left
    (left : Prop) (right : Prop) :
    ay_bcbd_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcbd_conj_right
    (left : Prop) (right : Prop) :
    ay_bcbd_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcbd_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bcbd_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcbd_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bcbd_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcbd_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcbd_equisat before after :=
  fun forward backward =>
    ay_bcbd_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcbd_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bcbd_equisat before after -> before -> after :=
  fun equisat =>
    ay_bcbd_conj_left (before -> after) (after -> before) equisat

theorem ay_bcbd_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bcbd_equisat before after -> after -> before :=
  fun equisat =>
    ay_bcbd_conj_right (before -> after) (after -> before) equisat

theorem ay_bcbd_bump_decay_guard_intro
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    bumpEvents ->
    decayFactor ->
    clauseIdentityMap ->
    lbdActivityLedger ->
    restartEpoch ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence :=
  fun bumpH decayH mapH ledgerH epochH fallbackH buildH validatorH auditH
      result build =>
    build bumpH decayH mapH ledgerH epochH fallbackH buildH validatorH auditH

theorem ay_bcbd_bump_decay_guard_bumps
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    bumpEvents :=
  fun guard =>
    guard bumpEvents
      (fun bumpH _decayH _mapH _ledgerH _epochH _fallbackH _buildH
          _validatorH _auditH => bumpH)

theorem ay_bcbd_bump_decay_guard_decay
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    decayFactor :=
  fun guard =>
    guard decayFactor
      (fun _bumpH decayH _mapH _ledgerH _epochH _fallbackH _buildH
          _validatorH _auditH => decayH)

theorem ay_bcbd_bump_decay_guard_clause_map
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    clauseIdentityMap :=
  fun guard =>
    guard clauseIdentityMap
      (fun _bumpH _decayH mapH _ledgerH _epochH _fallbackH _buildH
          _validatorH _auditH => mapH)

theorem ay_bcbd_bump_decay_guard_ledger
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    lbdActivityLedger :=
  fun guard =>
    guard lbdActivityLedger
      (fun _bumpH _decayH _mapH ledgerH _epochH _fallbackH _buildH
          _validatorH _auditH => ledgerH)

theorem ay_bcbd_bump_decay_guard_epoch
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    restartEpoch :=
  fun guard =>
    guard restartEpoch
      (fun _bumpH _decayH _mapH _ledgerH epochH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bcbd_bump_decay_guard_fallback
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _bumpH _decayH _mapH _ledgerH _epochH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bcbd_bump_decay_guard_build
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    guard solverBuildIdentity
      (fun _bumpH _decayH _mapH _ledgerH _epochH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bcbd_bump_decay_guard_validator
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _bumpH _decayH _mapH _ledgerH _epochH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bcbd_bump_decay_guard_audit
    (bumpEvents : Prop) (decayFactor : Prop)
    (clauseIdentityMap : Prop) (lbdActivityLedger : Prop)
    (restartEpoch : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcbd_bump_decay_guard bumpEvents decayFactor clauseIdentityMap
      lbdActivityLedger restartEpoch fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _bumpH _decayH _mapH _ledgerH _epochH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bcbd_guard_agreement_intro
    (bumpMatch : Prop) (decayMatch : Prop)
    (clauseMapMatch : Prop) (ledgerMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    bumpMatch ->
    decayMatch ->
    clauseMapMatch ->
    ledgerMatch ->
    epochMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcbd_guard_agreement bumpMatch decayMatch clauseMapMatch
      ledgerMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch :=
  fun bumpH decayH mapH ledgerH epochH fallbackH buildH validatorH auditH =>
    ay_bcbd_bump_decay_guard_intro bumpMatch decayMatch clauseMapMatch
      ledgerMatch epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      bumpH decayH mapH ledgerH epochH fallbackH buildH validatorH auditH

theorem ay_bcbd_guard_agreement_bumps
    (bumpMatch : Prop) (decayMatch : Prop)
    (clauseMapMatch : Prop) (ledgerMatch : Prop)
    (epochMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bcbd_guard_agreement bumpMatch decayMatch clauseMapMatch
      ledgerMatch epochMatch fallbackMatch buildMatch validatorAccepts
      auditMatch ->
    bumpMatch :=
  fun agreement =>
    ay_bcbd_bump_decay_guard_bumps bumpMatch decayMatch clauseMapMatch
      ledgerMatch epochMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_bcbd_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    guard ->
    agreement ->
    branchingHint ->
    ay_bcbd_accepted_hint guard agreement branchingHint :=
  fun guardH agreementH hintH =>
    ay_bcbd_conj_intro guard (ay_bcbd_conj agreement branchingHint)
      guardH
      (ay_bcbd_conj_intro agreement branchingHint agreementH hintH)

theorem ay_bcbd_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bcbd_accepted_hint guard agreement branchingHint -> guard :=
  fun accepted =>
    ay_bcbd_conj_left guard (ay_bcbd_conj agreement branchingHint)
      accepted

theorem ay_bcbd_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bcbd_accepted_hint guard agreement branchingHint -> agreement :=
  fun accepted =>
    ay_bcbd_conj_left agreement branchingHint
      (ay_bcbd_conj_right guard (ay_bcbd_conj agreement branchingHint)
        accepted)

theorem ay_bcbd_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (branchingHint : Prop) :
    ay_bcbd_accepted_hint guard agreement branchingHint -> branchingHint :=
  fun accepted =>
    ay_bcbd_conj_right agreement branchingHint
      (ay_bcbd_conj_right guard (ay_bcbd_conj agreement branchingHint)
        accepted)

theorem ay_bcbd_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcbd_conj_intro (ay_bcbd_outcome model conflict) formula
      (ay_bcbd_disj_left model conflict modelH)
      formulaH

theorem ay_bcbd_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcbd_conj_intro (ay_bcbd_outcome model conflict) formula
      (ay_bcbd_disj_right model conflict conflictH)
      formulaH

theorem ay_bcbd_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bcbd_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bcbd_conj_intro hintCert public hintH publicH

theorem ay_bcbd_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bcbd_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcbd_conj_right hintCert public accepted

theorem ay_bcbd_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bcbd_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bcbd_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcbd_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcbd_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcbd_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcbd_missing_bump_event_no_claim
    (missingBumpEvent : Prop) (fallbackPublic : Prop) :
    missingBumpEvent ->
    fallbackPublic ->
    ay_bcbd_no_claim missingBumpEvent fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro missingBumpEvent fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbd_stale_clause_map_no_claim
    (staleClauseMap : Prop) (fallbackPublic : Prop) :
    staleClauseMap ->
    fallbackPublic ->
    ay_bcbd_no_claim staleClauseMap fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro staleClauseMap fallbackPublic fallbackH diagnosticH

theorem ay_bcbd_bad_decay_factor_no_claim
    (badDecayFactor : Prop) (fallbackPublic : Prop) :
    badDecayFactor ->
    fallbackPublic ->
    ay_bcbd_no_claim badDecayFactor fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro badDecayFactor fallbackPublic fallbackH diagnosticH

theorem ay_bcbd_activity_ledger_gap_no_claim
    (activityLedgerGap : Prop) (fallbackPublic : Prop) :
    activityLedgerGap ->
    fallbackPublic ->
    ay_bcbd_no_claim activityLedgerGap fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro activityLedgerGap fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbd_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_bcbd_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcbd_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcbd_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bcbd_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bcbd_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcbd_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bcbd_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbd_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcbd_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbd_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbd_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcbd_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bcbd_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bcbd_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcbd_accepted_hint guard agreement branchingHint ->
    model ->
    formula ->
    ay_bcbd_accepted_report
      (ay_bcbd_accepted_hint guard agreement branchingHint)
      (ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bcbd_accepted_report_intro
      (ay_bcbd_accepted_hint guard agreement branchingHint)
      (ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula)
      accepted
      (ay_bcbd_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcbd_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (branchingHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcbd_accepted_hint guard agreement branchingHint ->
    conflict ->
    formula ->
    ay_bcbd_accepted_report
      (ay_bcbd_accepted_hint guard agreement branchingHint)
      (ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bcbd_accepted_report_intro
      (ay_bcbd_accepted_hint guard agreement branchingHint)
      (ay_bcbd_public_report (ay_bcbd_outcome model conflict) formula)
      accepted
      (ay_bcbd_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bcbd_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bcbd_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcbd_accepted_report_public hintCert public accepted

theorem ay_bcbd_bump_decay_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bcbd_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bcbd_equisat_forward beforeHint afterHint equisat beforeH
