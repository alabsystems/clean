-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded binary-implication cache guard soundness skeleton for ay SAT
-- solving. Cached binary implications may guide propagation and branching
-- only when implication edges, watched literals, parent clauses, cache epoch,
-- variable map, fallback baseline, solver build, validator gate, and audit
-- evidence agree.

def ay_bbic_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bbic_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bbic_equisat (before : Prop) (after : Prop) :=
  ay_bbic_conj (before -> after) (after -> before)

def ay_bbic_cache_guard
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :=
  forall result : Prop,
    (implicationEdges -> watchedLiterals -> parentClauses ->
      cacheEpoch -> variableMap -> fallbackBaseline ->
      solverBuildIdentity -> validatorGate -> auditEvidence -> result) ->
    result

def ay_bbic_guard_agreement
    (edgeMatch : Prop) (watchMatch : Prop)
    (parentMatch : Prop) (epochMatch : Prop)
    (variableMapMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :=
  ay_bbic_cache_guard edgeMatch watchMatch parentMatch epochMatch
    variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bbic_accepted_hint
    (guard : Prop) (agreement : Prop) (cacheHint : Prop) :=
  ay_bbic_conj guard (ay_bbic_conj agreement cacheHint)

def ay_bbic_outcome (model : Prop) (conflict : Prop) :=
  ay_bbic_disj model conflict

def ay_bbic_public_report (outcome : Prop) (formula : Prop) :=
  ay_bbic_conj outcome formula

def ay_bbic_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bbic_conj hintCert public

def ay_bbic_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bbic_conj fallbackPublic diagnostic

theorem ay_bbic_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bbic_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bbic_conj_left
    (left : Prop) (right : Prop) :
    ay_bbic_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bbic_conj_right
    (left : Prop) (right : Prop) :
    ay_bbic_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bbic_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bbic_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bbic_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bbic_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bbic_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bbic_equisat before after :=
  fun forward backward =>
    ay_bbic_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bbic_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bbic_equisat before after -> before -> after :=
  fun equisat =>
    ay_bbic_conj_left (before -> after) (after -> before) equisat

theorem ay_bbic_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bbic_equisat before after -> after -> before :=
  fun equisat =>
    ay_bbic_conj_right (before -> after) (after -> before) equisat

theorem ay_bbic_cache_guard_intro
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    implicationEdges ->
    watchedLiterals ->
    parentClauses ->
    cacheEpoch ->
    variableMap ->
    fallbackBaseline ->
    solverBuildIdentity ->
    validatorGate ->
    auditEvidence ->
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence :=
  fun edgeH watchH parentH epochH mapH fallbackH buildH validatorH auditH
      result build =>
    build edgeH watchH parentH epochH mapH fallbackH buildH validatorH auditH

theorem ay_bbic_cache_guard_edges
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    implicationEdges :=
  fun guard =>
    guard implicationEdges
      (fun edgeH _watchH _parentH _epochH _mapH _fallbackH _buildH
          _validatorH _auditH => edgeH)

theorem ay_bbic_cache_guard_watches
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    watchedLiterals :=
  fun guard =>
    guard watchedLiterals
      (fun _edgeH watchH _parentH _epochH _mapH _fallbackH _buildH
          _validatorH _auditH => watchH)

theorem ay_bbic_cache_guard_parents
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    parentClauses :=
  fun guard =>
    guard parentClauses
      (fun _edgeH _watchH parentH _epochH _mapH _fallbackH _buildH
          _validatorH _auditH => parentH)

theorem ay_bbic_cache_guard_epoch
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    cacheEpoch :=
  fun guard =>
    guard cacheEpoch
      (fun _edgeH _watchH _parentH epochH _mapH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_bbic_cache_guard_variable_map
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    variableMap :=
  fun guard =>
    guard variableMap
      (fun _edgeH _watchH _parentH _epochH mapH _fallbackH _buildH
          _validatorH _auditH => mapH)

theorem ay_bbic_cache_guard_fallback
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _edgeH _watchH _parentH _epochH _mapH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bbic_cache_guard_build
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    solverBuildIdentity :=
  fun guard =>
    guard solverBuildIdentity
      (fun _edgeH _watchH _parentH _epochH _mapH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bbic_cache_guard_validator
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _edgeH _watchH _parentH _epochH _mapH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bbic_cache_guard_audit
    (implicationEdges : Prop) (watchedLiterals : Prop)
    (parentClauses : Prop) (cacheEpoch : Prop)
    (variableMap : Prop) (fallbackBaseline : Prop)
    (solverBuildIdentity : Prop) (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bbic_cache_guard implicationEdges watchedLiterals parentClauses
      cacheEpoch variableMap fallbackBaseline solverBuildIdentity
      validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _edgeH _watchH _parentH _epochH _mapH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bbic_guard_agreement_intro
    (edgeMatch : Prop) (watchMatch : Prop)
    (parentMatch : Prop) (epochMatch : Prop)
    (variableMapMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    edgeMatch ->
    watchMatch ->
    parentMatch ->
    epochMatch ->
    variableMapMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bbic_guard_agreement edgeMatch watchMatch parentMatch epochMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun edgeH watchH parentH epochH mapH fallbackH buildH validatorH auditH =>
    ay_bbic_cache_guard_intro edgeMatch watchMatch parentMatch epochMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch
      edgeH watchH parentH epochH mapH fallbackH buildH validatorH auditH

theorem ay_bbic_guard_agreement_edges
    (edgeMatch : Prop) (watchMatch : Prop)
    (parentMatch : Prop) (epochMatch : Prop)
    (variableMapMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_bbic_guard_agreement edgeMatch watchMatch parentMatch epochMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch ->
    edgeMatch :=
  fun agreement =>
    ay_bbic_cache_guard_edges edgeMatch watchMatch parentMatch epochMatch
      variableMapMatch fallbackMatch buildMatch validatorAccepts auditMatch
      agreement

theorem ay_bbic_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (cacheHint : Prop) :
    guard ->
    agreement ->
    cacheHint ->
    ay_bbic_accepted_hint guard agreement cacheHint :=
  fun guardH agreementH hintH =>
    ay_bbic_conj_intro guard (ay_bbic_conj agreement cacheHint)
      guardH
      (ay_bbic_conj_intro agreement cacheHint agreementH hintH)

theorem ay_bbic_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (cacheHint : Prop) :
    ay_bbic_accepted_hint guard agreement cacheHint -> guard :=
  fun accepted =>
    ay_bbic_conj_left guard (ay_bbic_conj agreement cacheHint) accepted

theorem ay_bbic_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (cacheHint : Prop) :
    ay_bbic_accepted_hint guard agreement cacheHint -> agreement :=
  fun accepted =>
    ay_bbic_conj_left agreement cacheHint
      (ay_bbic_conj_right guard (ay_bbic_conj agreement cacheHint)
        accepted)

theorem ay_bbic_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (cacheHint : Prop) :
    ay_bbic_accepted_hint guard agreement cacheHint -> cacheHint :=
  fun accepted =>
    ay_bbic_conj_right agreement cacheHint
      (ay_bbic_conj_right guard (ay_bbic_conj agreement cacheHint)
        accepted)

theorem ay_bbic_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bbic_public_report (ay_bbic_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bbic_conj_intro (ay_bbic_outcome model conflict) formula
      (ay_bbic_disj_left model conflict modelH)
      formulaH

theorem ay_bbic_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bbic_public_report (ay_bbic_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bbic_conj_intro (ay_bbic_outcome model conflict) formula
      (ay_bbic_disj_right model conflict conflictH)
      formulaH

theorem ay_bbic_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bbic_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bbic_conj_intro hintCert public hintH publicH

theorem ay_bbic_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bbic_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bbic_conj_right hintCert public accepted

theorem ay_bbic_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bbic_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bbic_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bbic_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bbic_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bbic_conj_left fallbackPublic diagnostic noClaim

theorem ay_bbic_stale_edge_no_claim
    (staleEdge : Prop) (fallbackPublic : Prop) :
    staleEdge ->
    fallbackPublic ->
    ay_bbic_no_claim staleEdge fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro staleEdge fallbackPublic fallbackH diagnosticH

theorem ay_bbic_missing_parent_clause_no_claim
    (missingParentClause : Prop) (fallbackPublic : Prop) :
    missingParentClause ->
    fallbackPublic ->
    ay_bbic_no_claim missingParentClause fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro missingParentClause fallbackPublic
      fallbackH diagnosticH

theorem ay_bbic_watch_drift_no_claim
    (watchDrift : Prop) (fallbackPublic : Prop) :
    watchDrift ->
    fallbackPublic ->
    ay_bbic_no_claim watchDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro watchDrift fallbackPublic fallbackH diagnosticH

theorem ay_bbic_cache_epoch_mismatch_no_claim
    (cacheEpochMismatch : Prop) (fallbackPublic : Prop) :
    cacheEpochMismatch ->
    fallbackPublic ->
    ay_bbic_no_claim cacheEpochMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro cacheEpochMismatch fallbackPublic
      fallbackH diagnosticH

theorem ay_bbic_variable_map_drift_no_claim
    (variableMapDrift : Prop) (fallbackPublic : Prop) :
    variableMapDrift ->
    fallbackPublic ->
    ay_bbic_no_claim variableMapDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro variableMapDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_bbic_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bbic_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bbic_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bbic_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bbic_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_bbic_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_bbic_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bbic_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbic_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bbic_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bbic_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bbic_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bbic_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (cacheHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bbic_accepted_hint guard agreement cacheHint ->
    model ->
    formula ->
    ay_bbic_accepted_report
      (ay_bbic_accepted_hint guard agreement cacheHint)
      (ay_bbic_public_report (ay_bbic_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bbic_accepted_report_intro
      (ay_bbic_accepted_hint guard agreement cacheHint)
      (ay_bbic_public_report (ay_bbic_outcome model conflict) formula)
      accepted
      (ay_bbic_public_sat_report model conflict formula modelH formulaH)

theorem ay_bbic_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (cacheHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bbic_accepted_hint guard agreement cacheHint ->
    conflict ->
    formula ->
    ay_bbic_accepted_report
      (ay_bbic_accepted_hint guard agreement cacheHint)
      (ay_bbic_public_report (ay_bbic_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bbic_accepted_report_intro
      (ay_bbic_accepted_hint guard agreement cacheHint)
      (ay_bbic_public_report (ay_bbic_outcome model conflict) formula)
      accepted
      (ay_bbic_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bbic_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bbic_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bbic_accepted_report_public hintCert public accepted

theorem ay_bbic_cache_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bbic_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bbic_equisat_forward beforeHint afterHint equisat beforeH
