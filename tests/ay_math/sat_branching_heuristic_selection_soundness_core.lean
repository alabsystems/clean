-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked branching heuristic selection soundness for sequential SAT-COMP ay.
-- Selecting a candidate heuristic from benchmark evidence changes only
-- guidance/schedule. Semantic SAT/UNSAT claims remain backed by accepted
-- replay and learned-clause guard agreement. Benchmark or trace mismatches are
-- diagnostic no-claim entries that preserve fallback public soundness.

def AyHeuristicConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHeuristicDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyHeuristicEquisat (before : Prop) (after : Prop) :=
  AyHeuristicConj (before -> after) (after -> before)

def AyHeuristicScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyHeuristicState (formula : Prop) (frame : Prop) :=
  AyHeuristicConj formula frame

def AyHeuristicSelection
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop) :=
  AyHeuristicConj baseline
    (AyHeuristicConj candidate benchmarkEvidence)

def AyHeuristicTrace
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :=
  AyHeuristicConj seed
    (AyHeuristicConj digest
      (AyHeuristicConj variableDecision polarityDecision))

def AyHeuristicGuardAgreement (guard : Prop) (frame : Prop) :=
  AyHeuristicConj guard frame

def AyHeuristicAcceptedRun
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyHeuristicConj selection
    (AyHeuristicConj trace
      (AyHeuristicConj guardAgreement
        (AyHeuristicConj learnedClause checker)))

def AyHeuristicOutcome (model : Prop) (conflict : Prop) :=
  AyHeuristicDisj model conflict

def AyHeuristicPublicReport (outcome : Prop) (frame : Prop) :=
  AyHeuristicConj outcome frame

def AyHeuristicAcceptedReport (guidance : Prop) (public : Prop) :=
  AyHeuristicConj guidance public

def AyHeuristicNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyHeuristicConj fallbackPublic diagnostic

theorem ay_heuristic_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHeuristicConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_heuristic_conj_left
    (left : Prop) (right : Prop) :
    AyHeuristicConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_heuristic_conj_right
    (left : Prop) (right : Prop) :
    AyHeuristicConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_heuristic_disj_left
    (left : Prop) (right : Prop) :
    left -> AyHeuristicDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_heuristic_disj_right
    (left : Prop) (right : Prop) :
    right -> AyHeuristicDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_heuristic_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyHeuristicEquisat before after :=
  fun forward backward =>
    ay_heuristic_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_heuristic_equisat_forward
    (before : Prop) (after : Prop) :
    AyHeuristicEquisat before after -> before -> after :=
  fun equisat =>
    ay_heuristic_conj_left (before -> after) (after -> before)
      equisat

theorem ay_heuristic_equisat_backward
    (before : Prop) (after : Prop) :
    AyHeuristicEquisat before after -> after -> before :=
  fun equisat =>
    ay_heuristic_conj_right (before -> after) (after -> before)
      equisat

theorem ay_heuristic_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyHeuristicScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_heuristic_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyHeuristicState formula base ->
    assumption ->
    AyHeuristicState formula (AyHeuristicScope base assumption) :=
  fun state assumptionH =>
    ay_heuristic_conj_intro formula (AyHeuristicScope base assumption)
      (ay_heuristic_conj_left formula base state)
      (ay_heuristic_scope_push base assumption
        (ay_heuristic_conj_right formula base state)
        assumptionH)

theorem ay_heuristic_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyHeuristicEquisat original preprocessed ->
    AyHeuristicState original frame ->
    AyHeuristicState preprocessed frame :=
  fun preprocess state =>
    ay_heuristic_conj_intro preprocessed frame
      (ay_heuristic_equisat_forward original preprocessed preprocess
        (ay_heuristic_conj_left original frame state))
      (ay_heuristic_conj_right original frame state)

theorem ay_heuristic_selection_intro
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop) :
    baseline ->
    candidate ->
    benchmarkEvidence ->
    AyHeuristicSelection baseline candidate benchmarkEvidence :=
  fun baselineH candidateH evidenceH =>
    ay_heuristic_conj_intro baseline
      (AyHeuristicConj candidate benchmarkEvidence)
      baselineH
      (ay_heuristic_conj_intro candidate benchmarkEvidence
        candidateH evidenceH)

theorem ay_heuristic_selection_baseline
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop) :
    AyHeuristicSelection baseline candidate benchmarkEvidence -> baseline :=
  fun selection =>
    ay_heuristic_conj_left baseline
      (AyHeuristicConj candidate benchmarkEvidence)
      selection

theorem ay_heuristic_selection_candidate
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop) :
    AyHeuristicSelection baseline candidate benchmarkEvidence -> candidate :=
  fun selection =>
    ay_heuristic_conj_left candidate benchmarkEvidence
      (ay_heuristic_conj_right baseline
        (AyHeuristicConj candidate benchmarkEvidence)
        selection)

theorem ay_heuristic_selection_evidence
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop) :
    AyHeuristicSelection baseline candidate benchmarkEvidence ->
    benchmarkEvidence :=
  fun selection =>
    ay_heuristic_conj_right candidate benchmarkEvidence
      (ay_heuristic_conj_right baseline
        (AyHeuristicConj candidate benchmarkEvidence)
        selection)

theorem ay_heuristic_trace_intro
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    seed ->
    digest ->
    variableDecision ->
    polarityDecision ->
    AyHeuristicTrace seed digest variableDecision polarityDecision :=
  fun seedH digestH variableH polarityH =>
    ay_heuristic_conj_intro seed
      (AyHeuristicConj digest
        (AyHeuristicConj variableDecision polarityDecision))
      seedH
      (ay_heuristic_conj_intro digest
        (AyHeuristicConj variableDecision polarityDecision)
        digestH
        (ay_heuristic_conj_intro variableDecision polarityDecision
          variableH polarityH))

theorem ay_heuristic_trace_seed
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyHeuristicTrace seed digest variableDecision polarityDecision -> seed :=
  fun trace =>
    ay_heuristic_conj_left seed
      (AyHeuristicConj digest
        (AyHeuristicConj variableDecision polarityDecision))
      trace

theorem ay_heuristic_trace_digest
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyHeuristicTrace seed digest variableDecision polarityDecision -> digest :=
  fun trace =>
    ay_heuristic_conj_left digest
      (AyHeuristicConj variableDecision polarityDecision)
      (ay_heuristic_conj_right seed
        (AyHeuristicConj digest
          (AyHeuristicConj variableDecision polarityDecision))
        trace)

theorem ay_heuristic_trace_variable
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyHeuristicTrace seed digest variableDecision polarityDecision ->
    variableDecision :=
  fun trace =>
    ay_heuristic_conj_left variableDecision polarityDecision
      (ay_heuristic_conj_right digest
        (AyHeuristicConj variableDecision polarityDecision)
        (ay_heuristic_conj_right seed
          (AyHeuristicConj digest
            (AyHeuristicConj variableDecision polarityDecision))
          trace))

theorem ay_heuristic_trace_polarity
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyHeuristicTrace seed digest variableDecision polarityDecision ->
    polarityDecision :=
  fun trace =>
    ay_heuristic_conj_right variableDecision polarityDecision
      (ay_heuristic_conj_right digest
        (AyHeuristicConj variableDecision polarityDecision)
        (ay_heuristic_conj_right seed
          (AyHeuristicConj digest
            (AyHeuristicConj variableDecision polarityDecision))
          trace))

theorem ay_heuristic_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyHeuristicGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_heuristic_conj_intro guard frame guardH frameH

theorem ay_heuristic_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyHeuristicGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_heuristic_conj_left guard frame agreement

theorem ay_heuristic_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyHeuristicGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_heuristic_conj_right guard frame agreement

theorem ay_heuristic_accepted_run_intro
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    selection ->
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker :=
  fun selectionH traceH guardH learnedH checkerH =>
    ay_heuristic_conj_intro selection
      (AyHeuristicConj trace
        (AyHeuristicConj guardAgreement
          (AyHeuristicConj learnedClause checker)))
      selectionH
      (ay_heuristic_conj_intro trace
        (AyHeuristicConj guardAgreement
          (AyHeuristicConj learnedClause checker))
        traceH
        (ay_heuristic_conj_intro guardAgreement
          (AyHeuristicConj learnedClause checker)
          guardH
          (ay_heuristic_conj_intro learnedClause checker
            learnedH checkerH)))

theorem ay_heuristic_accepted_run_selection
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker ->
    selection :=
  fun run =>
    ay_heuristic_conj_left selection
      (AyHeuristicConj trace
        (AyHeuristicConj guardAgreement
          (AyHeuristicConj learnedClause checker)))
      run

theorem ay_heuristic_accepted_run_trace
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker ->
    trace :=
  fun run =>
    ay_heuristic_conj_left trace
      (AyHeuristicConj guardAgreement
        (AyHeuristicConj learnedClause checker))
      (ay_heuristic_conj_right selection
        (AyHeuristicConj trace
          (AyHeuristicConj guardAgreement
            (AyHeuristicConj learnedClause checker)))
        run)

theorem ay_heuristic_accepted_run_guard
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_heuristic_conj_left guardAgreement
      (AyHeuristicConj learnedClause checker)
      (ay_heuristic_conj_right trace
        (AyHeuristicConj guardAgreement
          (AyHeuristicConj learnedClause checker))
        (ay_heuristic_conj_right selection
          (AyHeuristicConj trace
            (AyHeuristicConj guardAgreement
              (AyHeuristicConj learnedClause checker)))
          run))

theorem ay_heuristic_accepted_run_learned
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_heuristic_conj_left learnedClause checker
      (ay_heuristic_conj_right guardAgreement
        (AyHeuristicConj learnedClause checker)
        (ay_heuristic_conj_right trace
          (AyHeuristicConj guardAgreement
            (AyHeuristicConj learnedClause checker))
          (ay_heuristic_conj_right selection
            (AyHeuristicConj trace
              (AyHeuristicConj guardAgreement
                (AyHeuristicConj learnedClause checker)))
            run)))

theorem ay_heuristic_accepted_run_checker
    (selection : Prop) (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyHeuristicAcceptedRun selection trace guardAgreement
      learnedClause checker ->
    checker :=
  fun run =>
    ay_heuristic_conj_right learnedClause checker
      (ay_heuristic_conj_right guardAgreement
        (AyHeuristicConj learnedClause checker)
        (ay_heuristic_conj_right trace
          (AyHeuristicConj guardAgreement
            (AyHeuristicConj learnedClause checker))
          (ay_heuristic_conj_right selection
            (AyHeuristicConj trace
              (AyHeuristicConj guardAgreement
                (AyHeuristicConj learnedClause checker)))
            run)))

theorem ay_heuristic_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyHeuristicEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyHeuristicState original base ->
    AyHeuristicPublicReport
      (AyHeuristicOutcome model conflict)
      (AyHeuristicScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_heuristic_conj_intro
      (AyHeuristicOutcome model conflict)
      (AyHeuristicScope base assumption)
      (ay_heuristic_disj_left model conflict
        (sat
          (ay_heuristic_conj_left preprocessed
            (AyHeuristicScope base assumption)
            (ay_heuristic_preprocess_forward original preprocessed
              (AyHeuristicScope base assumption)
              preprocess
              (ay_heuristic_state_push original base assumption
                state assumptionH)))))
      (ay_heuristic_scope_push base assumption
        (ay_heuristic_conj_right original base state)
        assumptionH)

theorem ay_heuristic_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyHeuristicAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_heuristic_conj_intro guidance public guidanceH publicH

theorem ay_heuristic_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyHeuristicAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_heuristic_conj_left guidance public report

theorem ay_heuristic_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyHeuristicAcceptedReport guidance public -> public :=
  fun report =>
    ay_heuristic_conj_right guidance public report

theorem ay_heuristic_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyHeuristicNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_heuristic_conj_intro fallbackPublic diagnostic
      fallbackH diagnosticH

theorem ay_heuristic_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyHeuristicNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_heuristic_conj_left fallbackPublic diagnostic noClaim

theorem ay_heuristic_rejection_diagnostic
    (benchmarkMismatch : Prop) (traceMismatch : Prop)
    (fallbackPublic : Prop) :
    fallbackPublic ->
    benchmarkMismatch ->
    traceMismatch ->
    AyHeuristicNoClaimEntry
      (AyHeuristicConj benchmarkMismatch traceMismatch)
      fallbackPublic :=
  fun fallbackH benchmarkH traceH =>
    ay_heuristic_no_claim_intro
      (AyHeuristicConj benchmarkMismatch traceMismatch)
      fallbackPublic
      fallbackH
      (ay_heuristic_conj_intro benchmarkMismatch traceMismatch
        benchmarkH traceH)

theorem ay_heuristic_selection_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop)
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guardAgreement : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyHeuristicEquisat original preprocessed ->
    assumption ->
    AyHeuristicAcceptedRun
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicTrace seed digest variableDecision polarityDecision)
      guardAgreement
      learnedClause
      checker ->
    (preprocessed -> model) ->
    AyHeuristicState original base ->
    AyHeuristicAcceptedReport
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicPublicReport
        (AyHeuristicOutcome model conflict)
        (AyHeuristicScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_heuristic_accepted_report_intro
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicPublicReport
        (AyHeuristicOutcome model conflict)
        (AyHeuristicScope base assumption))
      (ay_heuristic_accepted_run_selection
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicTrace seed digest variableDecision polarityDecision)
        guardAgreement learnedClause checker run)
      (ay_heuristic_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_heuristic_selection_guides_unsat
    (base : Prop) (assumption : Prop)
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop)
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyHeuristicAcceptedRun
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicTrace seed digest variableDecision polarityDecision)
      (AyHeuristicGuardAgreement guard
        (AyHeuristicScope base assumption))
      learnedClause
      checker ->
    (learnedClause -> conflict) ->
    AyHeuristicAcceptedReport
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicPublicReport
        (AyHeuristicOutcome model conflict)
        (AyHeuristicScope base assumption)) :=
  fun run learnedToConflict =>
    ay_heuristic_accepted_report_intro
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicPublicReport
        (AyHeuristicOutcome model conflict)
        (AyHeuristicScope base assumption))
      (ay_heuristic_accepted_run_selection
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicTrace seed digest variableDecision polarityDecision)
        (AyHeuristicGuardAgreement guard
          (AyHeuristicScope base assumption))
        learnedClause checker run)
      (ay_heuristic_conj_intro
        (AyHeuristicOutcome model conflict)
        (AyHeuristicScope base assumption)
        (ay_heuristic_disj_right model conflict
          (learnedToConflict
            (ay_heuristic_accepted_run_learned
              (AyHeuristicSelection baseline candidate benchmarkEvidence)
              (AyHeuristicTrace seed digest variableDecision polarityDecision)
              (AyHeuristicGuardAgreement guard
                (AyHeuristicScope base assumption))
              learnedClause checker run)))
        (ay_heuristic_guard_agreement_frame guard
          (AyHeuristicScope base assumption)
          (ay_heuristic_accepted_run_guard
            (AyHeuristicSelection baseline candidate benchmarkEvidence)
            (AyHeuristicTrace seed digest variableDecision polarityDecision)
            (AyHeuristicGuardAgreement guard
              (AyHeuristicScope base assumption))
            learnedClause checker run)))

theorem ay_heuristic_selection_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (baseline : Prop) (candidate : Prop) (benchmarkEvidence : Prop)
    (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyHeuristicEquisat original preprocessed ->
    assumption ->
    AyHeuristicAcceptedRun
      (AyHeuristicSelection baseline candidate benchmarkEvidence)
      (AyHeuristicTrace seed digest variableDecision polarityDecision)
      (AyHeuristicGuardAgreement guard
        (AyHeuristicScope base assumption))
      learnedClause
      checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyHeuristicState original base ->
    AyHeuristicConj
      (AyHeuristicAcceptedReport
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicPublicReport
          (AyHeuristicOutcome model conflict)
          (AyHeuristicScope base assumption)))
      (AyHeuristicAcceptedReport
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicPublicReport
          (AyHeuristicOutcome model conflict)
          (AyHeuristicScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_heuristic_conj_intro
      (AyHeuristicAcceptedReport
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicPublicReport
          (AyHeuristicOutcome model conflict)
          (AyHeuristicScope base assumption)))
      (AyHeuristicAcceptedReport
        (AyHeuristicSelection baseline candidate benchmarkEvidence)
        (AyHeuristicPublicReport
          (AyHeuristicOutcome model conflict)
          (AyHeuristicScope base assumption)))
      (ay_heuristic_selection_guides_sat original preprocessed
        base assumption baseline candidate benchmarkEvidence seed digest
        variableDecision polarityDecision
        (AyHeuristicGuardAgreement guard
          (AyHeuristicScope base assumption))
        learnedClause checker model conflict preprocess assumptionH run
        sat state)
      (ay_heuristic_selection_guides_unsat base assumption baseline
        candidate benchmarkEvidence seed digest variableDecision
        polarityDecision guard learnedClause checker model conflict
        run learnedToConflict)

theorem ay_heuristic_rejection_preserves_fallback_soundness
    (benchmarkMismatch : Prop) (traceMismatch : Prop)
    (fallbackPublic : Prop) :
    AyHeuristicNoClaimEntry
      (AyHeuristicConj benchmarkMismatch traceMismatch)
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_heuristic_no_claim_preserves_fallback
      (AyHeuristicConj benchmarkMismatch traceMismatch)
      fallbackPublic
      noClaim
