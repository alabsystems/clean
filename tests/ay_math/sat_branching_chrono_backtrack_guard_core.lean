-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded chronological/non-chronological backtrack guard soundness skeleton
-- for ay SAT solving. Backtracking policy changes may guide search only when
-- implication graph, asserting clause, decision levels, conflict epoch, trail
-- replay, fallback baseline, solver build, and validator gate agree.

def ay_bcbg_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcbg_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bcbg_equisat (before : Prop) (after : Prop) :=
  ay_bcbg_conj (before -> after) (after -> before)

def ay_bcbg_backtrack_guard
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :=
  ay_bcbg_conj implicationGraph
    (ay_bcbg_conj assertingClause
      (ay_bcbg_conj decisionLevelSnapshot
        (ay_bcbg_conj conflictEpoch
          (ay_bcbg_conj trailReplay
            (ay_bcbg_conj fallbackBaseline
              (ay_bcbg_conj solverBuild validatorGate))))))

def ay_bcbg_guard_agreement
    (graphMatch : Prop) (assertingMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (trailMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) :=
  ay_bcbg_conj graphMatch
    (ay_bcbg_conj assertingMatch
      (ay_bcbg_conj levelMatch
        (ay_bcbg_conj epochMatch
          (ay_bcbg_conj trailMatch
            (ay_bcbg_conj fallbackMatch
              (ay_bcbg_conj buildMatch validatorAccepts))))))

def ay_bcbg_accepted_hint
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop) :=
  ay_bcbg_conj guard (ay_bcbg_conj agreement backtrackHint)

def ay_bcbg_outcome (model : Prop) (conflict : Prop) :=
  ay_bcbg_disj model conflict

def ay_bcbg_public_report (outcome : Prop) (formula : Prop) :=
  ay_bcbg_conj outcome formula

def ay_bcbg_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_bcbg_conj hintCert public

def ay_bcbg_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bcbg_conj fallbackPublic diagnostic

theorem ay_bcbg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bcbg_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcbg_conj_left
    (left : Prop) (right : Prop) :
    ay_bcbg_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcbg_conj_right
    (left : Prop) (right : Prop) :
    ay_bcbg_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcbg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bcbg_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcbg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bcbg_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcbg_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bcbg_equisat before after :=
  fun forward backward =>
    ay_bcbg_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcbg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bcbg_equisat before after -> before -> after :=
  fun equisat =>
    ay_bcbg_conj_left (before -> after) (after -> before) equisat

theorem ay_bcbg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bcbg_equisat before after -> after -> before :=
  fun equisat =>
    ay_bcbg_conj_right (before -> after) (after -> before) equisat

theorem ay_bcbg_backtrack_guard_intro
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    implicationGraph ->
    assertingClause ->
    decisionLevelSnapshot ->
    conflictEpoch ->
    trailReplay ->
    fallbackBaseline ->
    solverBuild ->
    validatorGate ->
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate :=
  fun graphH assertingH levelH epochH trailH fallbackH buildH validatorH =>
    ay_bcbg_conj_intro implicationGraph
      (ay_bcbg_conj assertingClause
        (ay_bcbg_conj decisionLevelSnapshot
          (ay_bcbg_conj conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate))))))
      graphH
      (ay_bcbg_conj_intro assertingClause
        (ay_bcbg_conj decisionLevelSnapshot
          (ay_bcbg_conj conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate)))))
        assertingH
        (ay_bcbg_conj_intro decisionLevelSnapshot
          (ay_bcbg_conj conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate))))
          levelH
          (ay_bcbg_conj_intro conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate)))
            epochH
            (ay_bcbg_conj_intro trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate))
              trailH
              (ay_bcbg_conj_intro fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate)
                fallbackH
                (ay_bcbg_conj_intro solverBuild validatorGate
                  buildH validatorH))))))

theorem ay_bcbg_backtrack_guard_graph
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    implicationGraph :=
  fun guard =>
    ay_bcbg_conj_left implicationGraph
      (ay_bcbg_conj assertingClause
        (ay_bcbg_conj decisionLevelSnapshot
          (ay_bcbg_conj conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate))))))
      guard

theorem ay_bcbg_backtrack_guard_tail
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    ay_bcbg_conj assertingClause
      (ay_bcbg_conj decisionLevelSnapshot
        (ay_bcbg_conj conflictEpoch
          (ay_bcbg_conj trailReplay
            (ay_bcbg_conj fallbackBaseline
              (ay_bcbg_conj solverBuild validatorGate))))) :=
  fun guard =>
    ay_bcbg_conj_right implicationGraph
      (ay_bcbg_conj assertingClause
        (ay_bcbg_conj decisionLevelSnapshot
          (ay_bcbg_conj conflictEpoch
            (ay_bcbg_conj trailReplay
              (ay_bcbg_conj fallbackBaseline
                (ay_bcbg_conj solverBuild validatorGate))))))
      guard

theorem ay_bcbg_backtrack_guard_asserting
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    assertingClause :=
  fun guard =>
    ay_bcbg_conj_left assertingClause
      (ay_bcbg_conj decisionLevelSnapshot
        (ay_bcbg_conj conflictEpoch
          (ay_bcbg_conj trailReplay
            (ay_bcbg_conj fallbackBaseline
              (ay_bcbg_conj solverBuild validatorGate)))))
      (ay_bcbg_backtrack_guard_tail implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_after_asserting
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    ay_bcbg_conj decisionLevelSnapshot
      (ay_bcbg_conj conflictEpoch
        (ay_bcbg_conj trailReplay
          (ay_bcbg_conj fallbackBaseline
            (ay_bcbg_conj solverBuild validatorGate)))) :=
  fun guard =>
    ay_bcbg_conj_right assertingClause
      (ay_bcbg_conj decisionLevelSnapshot
        (ay_bcbg_conj conflictEpoch
          (ay_bcbg_conj trailReplay
            (ay_bcbg_conj fallbackBaseline
              (ay_bcbg_conj solverBuild validatorGate)))))
      (ay_bcbg_backtrack_guard_tail implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_level
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    decisionLevelSnapshot :=
  fun guard =>
    ay_bcbg_conj_left decisionLevelSnapshot
      (ay_bcbg_conj conflictEpoch
        (ay_bcbg_conj trailReplay
          (ay_bcbg_conj fallbackBaseline
            (ay_bcbg_conj solverBuild validatorGate))))
      (ay_bcbg_backtrack_guard_after_asserting implicationGraph
        assertingClause decisionLevelSnapshot conflictEpoch trailReplay
        fallbackBaseline solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_after_level
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    ay_bcbg_conj conflictEpoch
      (ay_bcbg_conj trailReplay
        (ay_bcbg_conj fallbackBaseline
          (ay_bcbg_conj solverBuild validatorGate))) :=
  fun guard =>
    ay_bcbg_conj_right decisionLevelSnapshot
      (ay_bcbg_conj conflictEpoch
        (ay_bcbg_conj trailReplay
          (ay_bcbg_conj fallbackBaseline
            (ay_bcbg_conj solverBuild validatorGate))))
      (ay_bcbg_backtrack_guard_after_asserting implicationGraph
        assertingClause decisionLevelSnapshot conflictEpoch trailReplay
        fallbackBaseline solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_epoch
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    conflictEpoch :=
  fun guard =>
    ay_bcbg_conj_left conflictEpoch
      (ay_bcbg_conj trailReplay
        (ay_bcbg_conj fallbackBaseline
          (ay_bcbg_conj solverBuild validatorGate)))
      (ay_bcbg_backtrack_guard_after_level implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_after_epoch
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    ay_bcbg_conj trailReplay
      (ay_bcbg_conj fallbackBaseline
        (ay_bcbg_conj solverBuild validatorGate)) :=
  fun guard =>
    ay_bcbg_conj_right conflictEpoch
      (ay_bcbg_conj trailReplay
        (ay_bcbg_conj fallbackBaseline
          (ay_bcbg_conj solverBuild validatorGate)))
      (ay_bcbg_backtrack_guard_after_level implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_trail
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    trailReplay :=
  fun guard =>
    ay_bcbg_conj_left trailReplay
      (ay_bcbg_conj fallbackBaseline
        (ay_bcbg_conj solverBuild validatorGate))
      (ay_bcbg_backtrack_guard_after_epoch implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_after_trail
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    ay_bcbg_conj fallbackBaseline
      (ay_bcbg_conj solverBuild validatorGate) :=
  fun guard =>
    ay_bcbg_conj_right trailReplay
      (ay_bcbg_conj fallbackBaseline
        (ay_bcbg_conj solverBuild validatorGate))
      (ay_bcbg_backtrack_guard_after_epoch implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_fallback
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    fallbackBaseline :=
  fun guard =>
    ay_bcbg_conj_left fallbackBaseline
      (ay_bcbg_conj solverBuild validatorGate)
      (ay_bcbg_backtrack_guard_after_trail implicationGraph assertingClause
        decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
        solverBuild validatorGate guard)

theorem ay_bcbg_backtrack_guard_build
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    solverBuild :=
  fun guard =>
    ay_bcbg_conj_left solverBuild validatorGate
      (ay_bcbg_conj_right fallbackBaseline
        (ay_bcbg_conj solverBuild validatorGate)
        (ay_bcbg_backtrack_guard_after_trail implicationGraph assertingClause
          decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
          solverBuild validatorGate guard))

theorem ay_bcbg_backtrack_guard_validator
    (implicationGraph : Prop) (assertingClause : Prop)
    (decisionLevelSnapshot : Prop) (conflictEpoch : Prop)
    (trailReplay : Prop) (fallbackBaseline : Prop)
    (solverBuild : Prop) (validatorGate : Prop) :
    ay_bcbg_backtrack_guard implicationGraph assertingClause
      decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
      solverBuild validatorGate ->
    validatorGate :=
  fun guard =>
    ay_bcbg_conj_right solverBuild validatorGate
      (ay_bcbg_conj_right fallbackBaseline
        (ay_bcbg_conj solverBuild validatorGate)
        (ay_bcbg_backtrack_guard_after_trail implicationGraph assertingClause
          decisionLevelSnapshot conflictEpoch trailReplay fallbackBaseline
          solverBuild validatorGate guard))

theorem ay_bcbg_guard_agreement_intro
    (graphMatch : Prop) (assertingMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (trailMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) :
    graphMatch ->
    assertingMatch ->
    levelMatch ->
    epochMatch ->
    trailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    ay_bcbg_guard_agreement graphMatch assertingMatch levelMatch
      epochMatch trailMatch fallbackMatch buildMatch validatorAccepts :=
  fun graphH assertingH levelH epochH trailH fallbackH buildH validatorH =>
    ay_bcbg_backtrack_guard_intro graphMatch assertingMatch levelMatch
      epochMatch trailMatch fallbackMatch buildMatch validatorAccepts
      graphH assertingH levelH epochH trailH fallbackH buildH validatorH

theorem ay_bcbg_guard_agreement_graph
    (graphMatch : Prop) (assertingMatch : Prop)
    (levelMatch : Prop) (epochMatch : Prop)
    (trailMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) :
    ay_bcbg_guard_agreement graphMatch assertingMatch levelMatch
      epochMatch trailMatch fallbackMatch buildMatch validatorAccepts ->
    graphMatch :=
  fun agreement =>
    ay_bcbg_backtrack_guard_graph graphMatch assertingMatch levelMatch
      epochMatch trailMatch fallbackMatch buildMatch validatorAccepts agreement

theorem ay_bcbg_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop) :
    guard ->
    agreement ->
    backtrackHint ->
    ay_bcbg_accepted_hint guard agreement backtrackHint :=
  fun guardH agreementH hintH =>
    ay_bcbg_conj_intro guard (ay_bcbg_conj agreement backtrackHint)
      guardH
      (ay_bcbg_conj_intro agreement backtrackHint agreementH hintH)

theorem ay_bcbg_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop) :
    ay_bcbg_accepted_hint guard agreement backtrackHint -> guard :=
  fun accepted =>
    ay_bcbg_conj_left guard (ay_bcbg_conj agreement backtrackHint)
      accepted

theorem ay_bcbg_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop) :
    ay_bcbg_accepted_hint guard agreement backtrackHint -> agreement :=
  fun accepted =>
    ay_bcbg_conj_left agreement backtrackHint
      (ay_bcbg_conj_right guard (ay_bcbg_conj agreement backtrackHint)
        accepted)

theorem ay_bcbg_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop) :
    ay_bcbg_accepted_hint guard agreement backtrackHint -> backtrackHint :=
  fun accepted =>
    ay_bcbg_conj_right agreement backtrackHint
      (ay_bcbg_conj_right guard (ay_bcbg_conj agreement backtrackHint)
        accepted)

theorem ay_bcbg_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcbg_conj_intro (ay_bcbg_outcome model conflict) formula
      (ay_bcbg_disj_left model conflict modelH)
      formulaH

theorem ay_bcbg_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcbg_conj_intro (ay_bcbg_outcome model conflict) formula
      (ay_bcbg_disj_right model conflict conflictH)
      formulaH

theorem ay_bcbg_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_bcbg_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_bcbg_conj_intro hintCert public hintH publicH

theorem ay_bcbg_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_bcbg_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcbg_conj_right hintCert public accepted

theorem ay_bcbg_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_bcbg_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_bcbg_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcbg_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcbg_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcbg_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcbg_stale_implication_graph_no_claim
    (staleImplicationGraph : Prop) (fallbackPublic : Prop) :
    staleImplicationGraph ->
    fallbackPublic ->
    ay_bcbg_no_claim staleImplicationGraph fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro staleImplicationGraph fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbg_bad_asserting_clause_no_claim
    (badAssertingClause : Prop) (fallbackPublic : Prop) :
    badAssertingClause ->
    fallbackPublic ->
    ay_bcbg_no_claim badAssertingClause fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro badAssertingClause fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbg_trail_drift_no_claim
    (trailDrift : Prop) (fallbackPublic : Prop) :
    trailDrift ->
    fallbackPublic ->
    ay_bcbg_no_claim trailDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro trailDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcbg_level_mismatch_no_claim
    (levelMismatch : Prop) (fallbackPublic : Prop) :
    levelMismatch ->
    fallbackPublic ->
    ay_bcbg_no_claim levelMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro levelMismatch fallbackPublic fallbackH diagnosticH

theorem ay_bcbg_epoch_drift_no_claim
    (epochDrift : Prop) (fallbackPublic : Prop) :
    epochDrift ->
    fallbackPublic ->
    ay_bcbg_no_claim epochDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro epochDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcbg_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_bcbg_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_bcbg_build_drift_no_claim
    (buildDrift : Prop) (fallbackPublic : Prop) :
    buildDrift ->
    fallbackPublic ->
    ay_bcbg_no_claim buildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro buildDrift fallbackPublic fallbackH diagnosticH

theorem ay_bcbg_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcbg_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcbg_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_bcbg_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bcbg_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_bcbg_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_bcbg_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcbg_accepted_hint guard agreement backtrackHint ->
    model ->
    formula ->
    ay_bcbg_accepted_report
      (ay_bcbg_accepted_hint guard agreement backtrackHint)
      (ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_bcbg_accepted_report_intro
      (ay_bcbg_accepted_hint guard agreement backtrackHint)
      (ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula)
      accepted
      (ay_bcbg_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcbg_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (backtrackHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_bcbg_accepted_hint guard agreement backtrackHint ->
    conflict ->
    formula ->
    ay_bcbg_accepted_report
      (ay_bcbg_accepted_hint guard agreement backtrackHint)
      (ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_bcbg_accepted_report_intro
      (ay_bcbg_accepted_hint guard agreement backtrackHint)
      (ay_bcbg_public_report (ay_bcbg_outcome model conflict) formula)
      accepted
      (ay_bcbg_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_bcbg_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_bcbg_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_bcbg_accepted_report_public hintCert public accepted

theorem ay_bcbg_backtrack_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_bcbg_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_bcbg_equisat_forward beforeHint afterHint equisat beforeH
