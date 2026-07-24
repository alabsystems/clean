-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked assumption-frame backtracking soundness skeleton for sequential
-- CDCL. Assumptions, restart/backtrack targets, learned-state guards, and
-- deterministic replay traces guide search scheduling only under a fixed
-- assumption frame. Public SAT/UNSAT reports remain checker/replay-backed;
-- invalid targets or frame mismatches produce diagnostic no-claim entries.

def AyFrameConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFrameDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFrameEquisat (before : Prop) (after : Prop) :=
  AyFrameConj (before -> after) (after -> before)

def AyAssumptionFrame (base : Prop) (assumption : Prop) :=
  AyFrameConj base assumption

def AyFrameState (formula : Prop) (frame : Prop) :=
  AyFrameConj formula frame

def AyFrameBacktrackTrace
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :=
  AyFrameConj assumptionFrame
    (AyFrameConj restartTarget
      (AyFrameConj decisionLevel
        (AyFrameConj backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision)))))

def AyFrameGuardAgreement (learnedGuard : Prop) (assumptionFrame : Prop) :=
  AyFrameConj learnedGuard assumptionFrame

def AyFrameAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyFrameConj trace
    (AyFrameConj guardAgreement
      (AyFrameConj learnedClause checker))

def AyFrameOutcome (model : Prop) (conflict : Prop) :=
  AyFrameDisj model conflict

def AyFramePublicReport (outcome : Prop) (assumptionFrame : Prop) :=
  AyFrameConj outcome assumptionFrame

def AyFrameAcceptedReport (guidance : Prop) (public : Prop) :=
  AyFrameConj guidance public

def AyFrameNoClaimDiagnostic (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyFrameConj fallbackPublic diagnostic

theorem ay_frame_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFrameConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_frame_conj_left
    (left : Prop) (right : Prop) :
    AyFrameConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_frame_conj_right
    (left : Prop) (right : Prop) :
    AyFrameConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_frame_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFrameDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_frame_disj_right
    (left : Prop) (right : Prop) :
    right -> AyFrameDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_frame_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFrameEquisat before after :=
  fun forward backward =>
    ay_frame_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_frame_equisat_forward
    (before : Prop) (after : Prop) :
    AyFrameEquisat before after -> before -> after :=
  fun equisat =>
    ay_frame_conj_left (before -> after) (after -> before) equisat

theorem ay_frame_equisat_backward
    (before : Prop) (after : Prop) :
    AyFrameEquisat before after -> after -> before :=
  fun equisat =>
    ay_frame_conj_right (before -> after) (after -> before) equisat

theorem ay_frame_assumption_intro
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyAssumptionFrame base assumption :=
  fun baseH assumptionH =>
    ay_frame_conj_intro base assumption baseH assumptionH

theorem ay_frame_assumption_base
    (base : Prop) (assumption : Prop) :
    AyAssumptionFrame base assumption -> base :=
  fun frame =>
    ay_frame_conj_left base assumption frame

theorem ay_frame_assumption_value
    (base : Prop) (assumption : Prop) :
    AyAssumptionFrame base assumption -> assumption :=
  fun frame =>
    ay_frame_conj_right base assumption frame

theorem ay_frame_state_under_assumption
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyFrameState formula base ->
    assumption ->
    AyFrameState formula (AyAssumptionFrame base assumption) :=
  fun state assumptionH =>
    ay_frame_conj_intro formula (AyAssumptionFrame base assumption)
      (ay_frame_conj_left formula base state)
      (ay_frame_assumption_intro base assumption
        (ay_frame_conj_right formula base state)
        assumptionH)

theorem ay_frame_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyFrameEquisat original preprocessed ->
    AyFrameState original frame ->
    AyFrameState preprocessed frame :=
  fun preprocess state =>
    ay_frame_conj_intro preprocessed frame
      (ay_frame_equisat_forward original preprocessed preprocess
        (ay_frame_conj_left original frame state))
      (ay_frame_conj_right original frame state)

theorem ay_frame_backtrack_trace_intro
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    assumptionFrame ->
    restartTarget ->
    decisionLevel ->
    backtrackTarget ->
    learnedState ->
    traceDigest ->
    branchDecision ->
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision :=
  fun frameH restartH decisionH targetH learnedH digestH branchH =>
    ay_frame_conj_intro assumptionFrame
      (AyFrameConj restartTarget
        (AyFrameConj decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision)))))
      frameH
      (ay_frame_conj_intro restartTarget
        (AyFrameConj decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision))))
        restartH
        (ay_frame_conj_intro decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision)))
          decisionH
          (ay_frame_conj_intro backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision))
            targetH
            (ay_frame_conj_intro learnedState
              (AyFrameConj traceDigest branchDecision)
              learnedH
              (ay_frame_conj_intro traceDigest branchDecision
                digestH branchH)))))

theorem ay_frame_trace_assumption_frame
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    assumptionFrame :=
  fun trace =>
    ay_frame_conj_left assumptionFrame
      (AyFrameConj restartTarget
        (AyFrameConj decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision)))))
      trace

theorem ay_frame_trace_tail
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    AyFrameConj restartTarget
      (AyFrameConj decisionLevel
        (AyFrameConj backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision)))) :=
  fun trace =>
    ay_frame_conj_right assumptionFrame
      (AyFrameConj restartTarget
        (AyFrameConj decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision)))))
      trace

theorem ay_frame_trace_restart_target
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    restartTarget :=
  fun trace =>
    ay_frame_conj_left restartTarget
      (AyFrameConj decisionLevel
        (AyFrameConj backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision))))
      (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
        backtrackTarget learnedState traceDigest branchDecision trace)

theorem ay_frame_trace_decision_level
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    decisionLevel :=
  fun trace =>
    ay_frame_conj_left decisionLevel
      (AyFrameConj backtrackTarget
        (AyFrameConj learnedState
          (AyFrameConj traceDigest branchDecision)))
      (ay_frame_conj_right restartTarget
        (AyFrameConj decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision))))
        (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision trace))

theorem ay_frame_trace_backtrack_target
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    backtrackTarget :=
  fun trace =>
    ay_frame_conj_left backtrackTarget
      (AyFrameConj learnedState
        (AyFrameConj traceDigest branchDecision))
      (ay_frame_conj_right decisionLevel
        (AyFrameConj backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision)))
        (ay_frame_conj_right restartTarget
          (AyFrameConj decisionLevel
            (AyFrameConj backtrackTarget
              (AyFrameConj learnedState
                (AyFrameConj traceDigest branchDecision))))
          (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
            backtrackTarget learnedState traceDigest branchDecision trace)))

theorem ay_frame_trace_learned_state
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    learnedState :=
  fun trace =>
    ay_frame_conj_left learnedState
      (AyFrameConj traceDigest branchDecision)
      (ay_frame_conj_right backtrackTarget
        (AyFrameConj learnedState
          (AyFrameConj traceDigest branchDecision))
        (ay_frame_conj_right decisionLevel
          (AyFrameConj backtrackTarget
            (AyFrameConj learnedState
              (AyFrameConj traceDigest branchDecision)))
          (ay_frame_conj_right restartTarget
            (AyFrameConj decisionLevel
              (AyFrameConj backtrackTarget
                (AyFrameConj learnedState
                  (AyFrameConj traceDigest branchDecision))))
            (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
              backtrackTarget learnedState traceDigest branchDecision trace))))

theorem ay_frame_trace_digest
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    traceDigest :=
  fun trace =>
    ay_frame_conj_left traceDigest branchDecision
      (ay_frame_conj_right learnedState
        (AyFrameConj traceDigest branchDecision)
        (ay_frame_conj_right backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision))
          (ay_frame_conj_right decisionLevel
            (AyFrameConj backtrackTarget
              (AyFrameConj learnedState
                (AyFrameConj traceDigest branchDecision)))
            (ay_frame_conj_right restartTarget
              (AyFrameConj decisionLevel
                (AyFrameConj backtrackTarget
                  (AyFrameConj learnedState
                    (AyFrameConj traceDigest branchDecision))))
              (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
                backtrackTarget learnedState traceDigest branchDecision
                trace)))))

theorem ay_frame_trace_branch_decision
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_frame_conj_right traceDigest branchDecision
      (ay_frame_conj_right learnedState
        (AyFrameConj traceDigest branchDecision)
        (ay_frame_conj_right backtrackTarget
          (AyFrameConj learnedState
            (AyFrameConj traceDigest branchDecision))
          (ay_frame_conj_right decisionLevel
            (AyFrameConj backtrackTarget
              (AyFrameConj learnedState
                (AyFrameConj traceDigest branchDecision)))
            (ay_frame_conj_right restartTarget
              (AyFrameConj decisionLevel
                (AyFrameConj backtrackTarget
                  (AyFrameConj learnedState
                    (AyFrameConj traceDigest branchDecision))))
              (ay_frame_trace_tail assumptionFrame restartTarget decisionLevel
                backtrackTarget learnedState traceDigest branchDecision
                trace)))))

theorem ay_frame_guard_agreement_intro
    (learnedGuard : Prop) (assumptionFrame : Prop) :
    learnedGuard ->
    assumptionFrame ->
    AyFrameGuardAgreement learnedGuard assumptionFrame :=
  fun guardH frameH =>
    ay_frame_conj_intro learnedGuard assumptionFrame guardH frameH

theorem ay_frame_guard_agreement_guard
    (learnedGuard : Prop) (assumptionFrame : Prop) :
    AyFrameGuardAgreement learnedGuard assumptionFrame -> learnedGuard :=
  fun agreement =>
    ay_frame_conj_left learnedGuard assumptionFrame agreement

theorem ay_frame_guard_agreement_frame
    (learnedGuard : Prop) (assumptionFrame : Prop) :
    AyFrameGuardAgreement learnedGuard assumptionFrame -> assumptionFrame :=
  fun agreement =>
    ay_frame_conj_right learnedGuard assumptionFrame agreement

theorem ay_frame_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyFrameAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_frame_conj_intro trace
      (AyFrameConj guardAgreement
        (AyFrameConj learnedClause checker))
      traceH
      (ay_frame_conj_intro guardAgreement
        (AyFrameConj learnedClause checker)
        guardH
        (ay_frame_conj_intro learnedClause checker learnedH checkerH))

theorem ay_frame_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyFrameAcceptedRun trace guardAgreement learnedClause checker -> trace :=
  fun accepted =>
    ay_frame_conj_left trace
      (AyFrameConj guardAgreement
        (AyFrameConj learnedClause checker))
      accepted

theorem ay_frame_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyFrameAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun accepted =>
    ay_frame_conj_left guardAgreement
      (AyFrameConj learnedClause checker)
      (ay_frame_conj_right trace
        (AyFrameConj guardAgreement
          (AyFrameConj learnedClause checker))
        accepted)

theorem ay_frame_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyFrameAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun accepted =>
    ay_frame_conj_left learnedClause checker
      (ay_frame_conj_right guardAgreement
        (AyFrameConj learnedClause checker)
        (ay_frame_conj_right trace
          (AyFrameConj guardAgreement
            (AyFrameConj learnedClause checker))
          accepted))

theorem ay_frame_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyFrameAcceptedRun trace guardAgreement learnedClause checker ->
    checker :=
  fun accepted =>
    ay_frame_conj_right learnedClause checker
      (ay_frame_conj_right guardAgreement
        (AyFrameConj learnedClause checker)
        (ay_frame_conj_right trace
          (AyFrameConj guardAgreement
            (AyFrameConj learnedClause checker))
          accepted))

theorem ay_frame_public_sat_report
    (model : Prop) (conflict : Prop) (assumptionFrame : Prop) :
    model ->
    assumptionFrame ->
    AyFramePublicReport (AyFrameOutcome model conflict) assumptionFrame :=
  fun modelH frameH =>
    ay_frame_conj_intro (AyFrameOutcome model conflict) assumptionFrame
      (ay_frame_disj_left model conflict modelH)
      frameH

theorem ay_frame_public_unsat_report
    (model : Prop) (conflict : Prop) (assumptionFrame : Prop) :
    conflict ->
    assumptionFrame ->
    AyFramePublicReport (AyFrameOutcome model conflict) assumptionFrame :=
  fun conflictH frameH =>
    ay_frame_conj_intro (AyFrameOutcome model conflict) assumptionFrame
      (ay_frame_disj_right model conflict conflictH)
      frameH

theorem ay_frame_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyFrameAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_frame_conj_intro guidance public guidanceH publicH

theorem ay_frame_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyFrameAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_frame_conj_left guidance public report

theorem ay_frame_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyFrameAcceptedReport guidance public -> public :=
  fun report =>
    ay_frame_conj_right guidance public report

theorem ay_frame_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyFrameNoClaimDiagnostic diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_frame_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_frame_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyFrameNoClaimDiagnostic diagnostic fallbackPublic -> fallbackPublic :=
  fun entry =>
    ay_frame_conj_left fallbackPublic diagnostic entry

theorem ay_frame_invalid_target_diagnostic
    (invalidTarget : Prop) (fallbackPublic : Prop) :
    invalidTarget ->
    fallbackPublic ->
    AyFrameNoClaimDiagnostic invalidTarget fallbackPublic :=
  fun invalidH fallbackH =>
    ay_frame_no_claim_intro invalidTarget fallbackPublic invalidH fallbackH

theorem ay_frame_assumption_mismatch_diagnostic
    (frameMismatch : Prop) (fallbackPublic : Prop) :
    frameMismatch ->
    fallbackPublic ->
    AyFrameNoClaimDiagnostic frameMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_frame_no_claim_intro frameMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_frame_policy_guides_sat
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop)
    (learnedGuard : Prop) (learnedClause : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    AyFrameGuardAgreement learnedGuard assumptionFrame ->
    learnedClause ->
    checker ->
    model ->
    AyFrameAcceptedReport
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame) :=
  fun trace agreement learnedH checkerH modelH =>
    ay_frame_accepted_report_intro
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame)
      (ay_frame_accepted_run_intro
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker
        trace agreement learnedH checkerH)
      (ay_frame_public_sat_report model conflict assumptionFrame modelH
        (ay_frame_trace_assumption_frame assumptionFrame restartTarget
          decisionLevel backtrackTarget learnedState traceDigest
          branchDecision trace))

theorem ay_frame_policy_guides_unsat
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop)
    (learnedGuard : Prop) (learnedClause : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
      backtrackTarget learnedState traceDigest branchDecision ->
    AyFrameGuardAgreement learnedGuard assumptionFrame ->
    learnedClause ->
    checker ->
    conflict ->
    AyFrameAcceptedReport
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame) :=
  fun trace agreement learnedH checkerH conflictH =>
    ay_frame_accepted_report_intro
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame)
      (ay_frame_accepted_run_intro
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker
        trace agreement learnedH checkerH)
      (ay_frame_public_unsat_report model conflict assumptionFrame
        conflictH
        (ay_frame_guard_agreement_frame learnedGuard assumptionFrame
          agreement))

theorem ay_frame_policy_full_soundness
    (assumptionFrame : Prop) (restartTarget : Prop)
    (decisionLevel : Prop) (backtrackTarget : Prop)
    (learnedState : Prop) (traceDigest : Prop) (branchDecision : Prop)
    (learnedGuard : Prop) (learnedClause : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyFrameAcceptedReport
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame) ->
    AyFramePublicReport (AyFrameOutcome model conflict)
      assumptionFrame :=
  fun report =>
    ay_frame_accepted_report_public
      (AyFrameAcceptedRun
        (AyFrameBacktrackTrace assumptionFrame restartTarget decisionLevel
          backtrackTarget learnedState traceDigest branchDecision)
        (AyFrameGuardAgreement learnedGuard assumptionFrame)
        learnedClause checker)
      (AyFramePublicReport (AyFrameOutcome model conflict)
        assumptionFrame)
      report

theorem ay_frame_mismatch_preserves_fallback_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyFrameNoClaimDiagnostic diagnostic fallbackPublic -> fallbackPublic :=
  fun entry =>
    ay_frame_no_claim_preserves_fallback diagnostic fallbackPublic entry
