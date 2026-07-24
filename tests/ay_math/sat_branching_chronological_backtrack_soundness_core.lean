-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked chronological/non-chronological backtracking soundness skeleton for
-- sequential CDCL. Decision levels, backtrack targets, learned clauses, and
-- replay traces guide search schedule and learned-state evolution only. Public
-- SAT/UNSAT reports remain checker/replay-backed; invalid targets and trace
-- mismatches produce no-claim diagnostics preserving fallback soundness.

def AyBacktrackConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBacktrackDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBacktrackEquisat (before : Prop) (after : Prop) :=
  AyBacktrackConj (before -> after) (after -> before)

def AyBacktrackScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyBacktrackState (formula : Prop) (frame : Prop) :=
  AyBacktrackConj formula frame

def AyBacktrackTrace
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :=
  AyBacktrackConj decisionLevel
    (AyBacktrackConj targetLevel
      (AyBacktrackConj learnedState
        (AyBacktrackConj digest branchDecision)))

def AyBacktrackGuardAgreement (guard : Prop) (frame : Prop) :=
  AyBacktrackConj guard frame

def AyBacktrackAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyBacktrackConj trace
    (AyBacktrackConj guardAgreement
      (AyBacktrackConj learnedClause checker))

def AyBacktrackOutcome (model : Prop) (conflict : Prop) :=
  AyBacktrackDisj model conflict

def AyBacktrackPublicReport (outcome : Prop) (frame : Prop) :=
  AyBacktrackConj outcome frame

def AyBacktrackAcceptedReport (guidance : Prop) (public : Prop) :=
  AyBacktrackConj guidance public

def AyBacktrackNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBacktrackConj fallbackPublic diagnostic

theorem ay_backtrack_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBacktrackConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_backtrack_conj_left
    (left : Prop) (right : Prop) :
    AyBacktrackConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_backtrack_conj_right
    (left : Prop) (right : Prop) :
    AyBacktrackConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_backtrack_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBacktrackDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_backtrack_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBacktrackDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_backtrack_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBacktrackEquisat before after :=
  fun forward backward =>
    ay_backtrack_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_backtrack_equisat_forward
    (before : Prop) (after : Prop) :
    AyBacktrackEquisat before after -> before -> after :=
  fun equisat =>
    ay_backtrack_conj_left (before -> after) (after -> before)
      equisat

theorem ay_backtrack_equisat_backward
    (before : Prop) (after : Prop) :
    AyBacktrackEquisat before after -> after -> before :=
  fun equisat =>
    ay_backtrack_conj_right (before -> after) (after -> before)
      equisat

theorem ay_backtrack_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyBacktrackScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_backtrack_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBacktrackState formula base ->
    assumption ->
    AyBacktrackState formula (AyBacktrackScope base assumption) :=
  fun state assumptionH =>
    ay_backtrack_conj_intro formula (AyBacktrackScope base assumption)
      (ay_backtrack_conj_left formula base state)
      (ay_backtrack_scope_push base assumption
        (ay_backtrack_conj_right formula base state)
        assumptionH)

theorem ay_backtrack_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyBacktrackEquisat original preprocessed ->
    AyBacktrackState original frame ->
    AyBacktrackState preprocessed frame :=
  fun preprocess state =>
    ay_backtrack_conj_intro preprocessed frame
      (ay_backtrack_equisat_forward original preprocessed preprocess
        (ay_backtrack_conj_left original frame state))
      (ay_backtrack_conj_right original frame state)

theorem ay_backtrack_trace_intro
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    decisionLevel ->
    targetLevel ->
    learnedState ->
    digest ->
    branchDecision ->
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision :=
  fun decisionH targetH learnedH digestH branchH =>
    ay_backtrack_conj_intro decisionLevel
      (AyBacktrackConj targetLevel
        (AyBacktrackConj learnedState
          (AyBacktrackConj digest branchDecision)))
      decisionH
      (ay_backtrack_conj_intro targetLevel
        (AyBacktrackConj learnedState
          (AyBacktrackConj digest branchDecision))
        targetH
        (ay_backtrack_conj_intro learnedState
          (AyBacktrackConj digest branchDecision)
          learnedH
          (ay_backtrack_conj_intro digest branchDecision digestH branchH)))

theorem ay_backtrack_trace_decision_level
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision ->
    decisionLevel :=
  fun trace =>
    ay_backtrack_conj_left decisionLevel
      (AyBacktrackConj targetLevel
        (AyBacktrackConj learnedState
          (AyBacktrackConj digest branchDecision)))
      trace

theorem ay_backtrack_trace_target_level
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision ->
    targetLevel :=
  fun trace =>
    ay_backtrack_conj_left targetLevel
      (AyBacktrackConj learnedState
        (AyBacktrackConj digest branchDecision))
      (ay_backtrack_conj_right decisionLevel
        (AyBacktrackConj targetLevel
          (AyBacktrackConj learnedState
            (AyBacktrackConj digest branchDecision)))
        trace)

theorem ay_backtrack_trace_learned_state
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision ->
    learnedState :=
  fun trace =>
    ay_backtrack_conj_left learnedState
      (AyBacktrackConj digest branchDecision)
      (ay_backtrack_conj_right targetLevel
        (AyBacktrackConj learnedState
          (AyBacktrackConj digest branchDecision))
        (ay_backtrack_conj_right decisionLevel
          (AyBacktrackConj targetLevel
            (AyBacktrackConj learnedState
              (AyBacktrackConj digest branchDecision)))
          trace))

theorem ay_backtrack_trace_digest
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision ->
    digest :=
  fun trace =>
    ay_backtrack_conj_left digest branchDecision
      (ay_backtrack_conj_right learnedState
        (AyBacktrackConj digest branchDecision)
        (ay_backtrack_conj_right targetLevel
          (AyBacktrackConj learnedState
            (AyBacktrackConj digest branchDecision))
          (ay_backtrack_conj_right decisionLevel
            (AyBacktrackConj targetLevel
              (AyBacktrackConj learnedState
                (AyBacktrackConj digest branchDecision)))
            trace)))

theorem ay_backtrack_trace_branch_decision
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyBacktrackTrace decisionLevel targetLevel learnedState
      digest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_backtrack_conj_right digest branchDecision
      (ay_backtrack_conj_right learnedState
        (AyBacktrackConj digest branchDecision)
        (ay_backtrack_conj_right targetLevel
          (AyBacktrackConj learnedState
            (AyBacktrackConj digest branchDecision))
          (ay_backtrack_conj_right decisionLevel
            (AyBacktrackConj targetLevel
              (AyBacktrackConj learnedState
                (AyBacktrackConj digest branchDecision)))
            trace)))

theorem ay_backtrack_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyBacktrackGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_backtrack_conj_intro guard frame guardH frameH

theorem ay_backtrack_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyBacktrackGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_backtrack_conj_left guard frame agreement

theorem ay_backtrack_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyBacktrackGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_backtrack_conj_right guard frame agreement

theorem ay_backtrack_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyBacktrackAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_backtrack_conj_intro trace
      (AyBacktrackConj guardAgreement
        (AyBacktrackConj learnedClause checker))
      traceH
      (ay_backtrack_conj_intro guardAgreement
        (AyBacktrackConj learnedClause checker)
        guardH
        (ay_backtrack_conj_intro learnedClause checker learnedH checkerH))

theorem ay_backtrack_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBacktrackAcceptedRun trace guardAgreement learnedClause checker ->
    trace :=
  fun run =>
    ay_backtrack_conj_left trace
      (AyBacktrackConj guardAgreement
        (AyBacktrackConj learnedClause checker))
      run

theorem ay_backtrack_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBacktrackAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_backtrack_conj_left guardAgreement
      (AyBacktrackConj learnedClause checker)
      (ay_backtrack_conj_right trace
        (AyBacktrackConj guardAgreement
          (AyBacktrackConj learnedClause checker))
        run)

theorem ay_backtrack_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBacktrackAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_backtrack_conj_left learnedClause checker
      (ay_backtrack_conj_right guardAgreement
        (AyBacktrackConj learnedClause checker)
        (ay_backtrack_conj_right trace
          (AyBacktrackConj guardAgreement
            (AyBacktrackConj learnedClause checker))
          run))

theorem ay_backtrack_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBacktrackAcceptedRun trace guardAgreement learnedClause checker ->
    checker :=
  fun run =>
    ay_backtrack_conj_right learnedClause checker
      (ay_backtrack_conj_right guardAgreement
        (AyBacktrackConj learnedClause checker)
        (ay_backtrack_conj_right trace
          (AyBacktrackConj guardAgreement
            (AyBacktrackConj learnedClause checker))
          run))

theorem ay_backtrack_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyBacktrackEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyBacktrackState original base ->
    AyBacktrackPublicReport
      (AyBacktrackOutcome model conflict)
      (AyBacktrackScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_backtrack_conj_intro
      (AyBacktrackOutcome model conflict)
      (AyBacktrackScope base assumption)
      (ay_backtrack_disj_left model conflict
        (sat
          (ay_backtrack_conj_left preprocessed
            (AyBacktrackScope base assumption)
            (ay_backtrack_preprocess_forward original preprocessed
              (AyBacktrackScope base assumption)
              preprocess
              (ay_backtrack_state_push original base assumption
                state assumptionH)))))
      (ay_backtrack_scope_push base assumption
        (ay_backtrack_conj_right original base state)
        assumptionH)

theorem ay_backtrack_public_unsat_report
    (base : Prop) (assumption : Prop)
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyBacktrackAcceptedRun
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackGuardAgreement guard (AyBacktrackScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBacktrackPublicReport
      (AyBacktrackOutcome model conflict)
      (AyBacktrackScope base assumption) :=
  fun run learnedToConflict =>
    ay_backtrack_conj_intro
      (AyBacktrackOutcome model conflict)
      (AyBacktrackScope base assumption)
      (ay_backtrack_disj_right model conflict
        (learnedToConflict
          (ay_backtrack_accepted_run_learned
            (AyBacktrackTrace decisionLevel targetLevel learnedState
              digest branchDecision)
            (AyBacktrackGuardAgreement guard
              (AyBacktrackScope base assumption))
            learnedClause checker run)))
      (ay_backtrack_guard_agreement_frame guard
        (AyBacktrackScope base assumption)
        (ay_backtrack_accepted_run_guard
          (AyBacktrackTrace decisionLevel targetLevel learnedState
            digest branchDecision)
          (AyBacktrackGuardAgreement guard
            (AyBacktrackScope base assumption))
          learnedClause checker run))

theorem ay_backtrack_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyBacktrackAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_backtrack_conj_intro guidance public guidanceH publicH

theorem ay_backtrack_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyBacktrackAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_backtrack_conj_left guidance public report

theorem ay_backtrack_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyBacktrackAcceptedReport guidance public -> public :=
  fun report =>
    ay_backtrack_conj_right guidance public report

theorem ay_backtrack_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyBacktrackNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_backtrack_conj_intro fallbackPublic diagnostic
      fallbackH diagnosticH

theorem ay_backtrack_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBacktrackNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_backtrack_conj_left fallbackPublic diagnostic noClaim

theorem ay_backtrack_invalid_target_diagnostic
    (invalidTarget : Prop) (traceMismatch : Prop)
    (fallbackPublic : Prop) :
    fallbackPublic ->
    invalidTarget ->
    traceMismatch ->
    AyBacktrackNoClaimEntry
      (AyBacktrackConj invalidTarget traceMismatch)
      fallbackPublic :=
  fun fallbackH invalidH traceH =>
    ay_backtrack_no_claim_intro
      (AyBacktrackConj invalidTarget traceMismatch)
      fallbackPublic
      fallbackH
      (ay_backtrack_conj_intro invalidTarget traceMismatch
        invalidH traceH)

theorem ay_backtrack_policy_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyBacktrackEquisat original preprocessed ->
    assumption ->
    AyBacktrackAcceptedRun
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackGuardAgreement guard (AyBacktrackScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    AyBacktrackState original base ->
    AyBacktrackAcceptedReport
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackPublicReport
        (AyBacktrackOutcome model conflict)
        (AyBacktrackScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_backtrack_accepted_report_intro
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackPublicReport
        (AyBacktrackOutcome model conflict)
        (AyBacktrackScope base assumption))
      (ay_backtrack_accepted_run_trace
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackGuardAgreement guard
          (AyBacktrackScope base assumption))
        learnedClause checker run)
      (ay_backtrack_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_backtrack_policy_guides_unsat
    (base : Prop) (assumption : Prop)
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyBacktrackAcceptedRun
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackGuardAgreement guard (AyBacktrackScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBacktrackAcceptedReport
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackPublicReport
        (AyBacktrackOutcome model conflict)
        (AyBacktrackScope base assumption)) :=
  fun run learnedToConflict =>
    ay_backtrack_accepted_report_intro
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackPublicReport
        (AyBacktrackOutcome model conflict)
        (AyBacktrackScope base assumption))
      (ay_backtrack_accepted_run_trace
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackGuardAgreement guard
          (AyBacktrackScope base assumption))
        learnedClause checker run)
      (ay_backtrack_public_unsat_report base assumption decisionLevel
        targetLevel learnedState digest branchDecision guard learnedClause
        checker model conflict run learnedToConflict)

theorem ay_backtrack_policy_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyBacktrackEquisat original preprocessed ->
    assumption ->
    AyBacktrackAcceptedRun
      (AyBacktrackTrace decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyBacktrackGuardAgreement guard (AyBacktrackScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyBacktrackState original base ->
    AyBacktrackConj
      (AyBacktrackAcceptedReport
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackPublicReport
          (AyBacktrackOutcome model conflict)
          (AyBacktrackScope base assumption)))
      (AyBacktrackAcceptedReport
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackPublicReport
          (AyBacktrackOutcome model conflict)
          (AyBacktrackScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_backtrack_conj_intro
      (AyBacktrackAcceptedReport
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackPublicReport
          (AyBacktrackOutcome model conflict)
          (AyBacktrackScope base assumption)))
      (AyBacktrackAcceptedReport
        (AyBacktrackTrace decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyBacktrackPublicReport
          (AyBacktrackOutcome model conflict)
          (AyBacktrackScope base assumption)))
      (ay_backtrack_policy_guides_sat original preprocessed base assumption
        decisionLevel targetLevel learnedState digest branchDecision guard
        learnedClause checker model conflict preprocess assumptionH
        run sat state)
      (ay_backtrack_policy_guides_unsat base assumption decisionLevel
        targetLevel learnedState digest branchDecision guard learnedClause
        checker model conflict run learnedToConflict)

theorem ay_backtrack_invalid_target_preserves_fallback_soundness
    (invalidTarget : Prop) (traceMismatch : Prop)
    (fallbackPublic : Prop) :
    AyBacktrackNoClaimEntry
      (AyBacktrackConj invalidTarget traceMismatch)
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_backtrack_no_claim_preserves_fallback
      (AyBacktrackConj invalidTarget traceMismatch)
      fallbackPublic
      noClaim
