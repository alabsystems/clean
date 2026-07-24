-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked joint restart/backtrack policy soundness skeleton for sequential
-- CDCL. Restart epochs, decision levels, backtrack targets, learned-state
-- guards, and replay traces guide search scheduling only. Public SAT/UNSAT
-- reports remain checker/replay-backed; invalid targets and restart mismatch
-- diagnostics make no new claim and preserve fallback soundness.

def AyJointConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyJointDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyJointEquisat (before : Prop) (after : Prop) :=
  AyJointConj (before -> after) (after -> before)

def AyJointScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyJointState (formula : Prop) (frame : Prop) :=
  AyJointConj formula frame

def AyJointTrace
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :=
  AyJointConj restartEpoch
    (AyJointConj decisionLevel
      (AyJointConj targetLevel
        (AyJointConj learnedState
          (AyJointConj digest branchDecision))))

def AyJointGuardAgreement (guard : Prop) (frame : Prop) :=
  AyJointConj guard frame

def AyJointAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyJointConj trace
    (AyJointConj guardAgreement
      (AyJointConj learnedClause checker))

def AyJointOutcome (model : Prop) (conflict : Prop) :=
  AyJointDisj model conflict

def AyJointPublicReport (outcome : Prop) (frame : Prop) :=
  AyJointConj outcome frame

def AyJointAcceptedReport (guidance : Prop) (public : Prop) :=
  AyJointConj guidance public

def AyJointNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyJointConj fallbackPublic diagnostic

theorem ay_joint_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyJointConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_joint_conj_left
    (left : Prop) (right : Prop) :
    AyJointConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_joint_conj_right
    (left : Prop) (right : Prop) :
    AyJointConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_joint_disj_left
    (left : Prop) (right : Prop) :
    left -> AyJointDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_joint_disj_right
    (left : Prop) (right : Prop) :
    right -> AyJointDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_joint_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyJointEquisat before after :=
  fun forward backward =>
    ay_joint_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_joint_equisat_forward
    (before : Prop) (after : Prop) :
    AyJointEquisat before after -> before -> after :=
  fun equisat =>
    ay_joint_conj_left (before -> after) (after -> before) equisat

theorem ay_joint_equisat_backward
    (before : Prop) (after : Prop) :
    AyJointEquisat before after -> after -> before :=
  fun equisat =>
    ay_joint_conj_right (before -> after) (after -> before) equisat

theorem ay_joint_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyJointScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_joint_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyJointState formula base ->
    assumption ->
    AyJointState formula (AyJointScope base assumption) :=
  fun state assumptionH =>
    ay_joint_conj_intro formula (AyJointScope base assumption)
      (ay_joint_conj_left formula base state)
      (ay_joint_scope_push base assumption
        (ay_joint_conj_right formula base state)
        assumptionH)

theorem ay_joint_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyJointEquisat original preprocessed ->
    AyJointState original frame ->
    AyJointState preprocessed frame :=
  fun preprocess state =>
    ay_joint_conj_intro preprocessed frame
      (ay_joint_equisat_forward original preprocessed preprocess
        (ay_joint_conj_left original frame state))
      (ay_joint_conj_right original frame state)

theorem ay_joint_trace_intro
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    restartEpoch ->
    decisionLevel ->
    targetLevel ->
    learnedState ->
    digest ->
    branchDecision ->
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision :=
  fun restartH decisionH targetH learnedH digestH branchH =>
    ay_joint_conj_intro restartEpoch
      (AyJointConj decisionLevel
        (AyJointConj targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision))))
      restartH
      (ay_joint_conj_intro decisionLevel
        (AyJointConj targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision)))
        decisionH
        (ay_joint_conj_intro targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision))
          targetH
          (ay_joint_conj_intro learnedState
            (AyJointConj digest branchDecision)
            learnedH
            (ay_joint_conj_intro digest branchDecision digestH branchH))))

theorem ay_joint_trace_restart_epoch
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    restartEpoch :=
  fun trace =>
    ay_joint_conj_left restartEpoch
      (AyJointConj decisionLevel
        (AyJointConj targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision))))
      trace

theorem ay_joint_trace_schedule_tail
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    AyJointConj decisionLevel
      (AyJointConj targetLevel
        (AyJointConj learnedState
          (AyJointConj digest branchDecision))) :=
  fun trace =>
    ay_joint_conj_right restartEpoch
      (AyJointConj decisionLevel
        (AyJointConj targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision))))
      trace

theorem ay_joint_trace_decision_level
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    decisionLevel :=
  fun trace =>
    ay_joint_conj_left decisionLevel
      (AyJointConj targetLevel
        (AyJointConj learnedState
          (AyJointConj digest branchDecision)))
      (ay_joint_trace_schedule_tail restartEpoch decisionLevel targetLevel
        learnedState digest branchDecision trace)

theorem ay_joint_trace_target_level
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    targetLevel :=
  fun trace =>
    ay_joint_conj_left targetLevel
      (AyJointConj learnedState (AyJointConj digest branchDecision))
      (ay_joint_conj_right decisionLevel
        (AyJointConj targetLevel
          (AyJointConj learnedState
            (AyJointConj digest branchDecision)))
        (ay_joint_trace_schedule_tail restartEpoch decisionLevel targetLevel
          learnedState digest branchDecision trace))

theorem ay_joint_trace_learned_state
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    learnedState :=
  fun trace =>
    ay_joint_conj_left learnedState (AyJointConj digest branchDecision)
      (ay_joint_conj_right targetLevel
        (AyJointConj learnedState (AyJointConj digest branchDecision))
        (ay_joint_conj_right decisionLevel
          (AyJointConj targetLevel
            (AyJointConj learnedState
              (AyJointConj digest branchDecision)))
          (ay_joint_trace_schedule_tail restartEpoch decisionLevel
            targetLevel learnedState digest branchDecision trace)))

theorem ay_joint_trace_digest
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    digest :=
  fun trace =>
    ay_joint_conj_left digest branchDecision
      (ay_joint_conj_right learnedState
        (AyJointConj digest branchDecision)
        (ay_joint_conj_right targetLevel
          (AyJointConj learnedState (AyJointConj digest branchDecision))
          (ay_joint_conj_right decisionLevel
            (AyJointConj targetLevel
              (AyJointConj learnedState
                (AyJointConj digest branchDecision)))
            (ay_joint_trace_schedule_tail restartEpoch decisionLevel
              targetLevel learnedState digest branchDecision trace))))

theorem ay_joint_trace_branch_decision
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop) :
    AyJointTrace restartEpoch decisionLevel targetLevel learnedState
      digest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_joint_conj_right digest branchDecision
      (ay_joint_conj_right learnedState
        (AyJointConj digest branchDecision)
        (ay_joint_conj_right targetLevel
          (AyJointConj learnedState (AyJointConj digest branchDecision))
          (ay_joint_conj_right decisionLevel
            (AyJointConj targetLevel
              (AyJointConj learnedState
                (AyJointConj digest branchDecision)))
            (ay_joint_trace_schedule_tail restartEpoch decisionLevel
              targetLevel learnedState digest branchDecision trace))))

theorem ay_joint_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyJointGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_joint_conj_intro guard frame guardH frameH

theorem ay_joint_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyJointGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_joint_conj_left guard frame agreement

theorem ay_joint_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyJointGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_joint_conj_right guard frame agreement

theorem ay_joint_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyJointAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_joint_conj_intro trace
      (AyJointConj guardAgreement
        (AyJointConj learnedClause checker))
      traceH
      (ay_joint_conj_intro guardAgreement
        (AyJointConj learnedClause checker)
        guardH
        (ay_joint_conj_intro learnedClause checker learnedH checkerH))

theorem ay_joint_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyJointAcceptedRun trace guardAgreement learnedClause checker -> trace :=
  fun run =>
    ay_joint_conj_left trace
      (AyJointConj guardAgreement
        (AyJointConj learnedClause checker))
      run

theorem ay_joint_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyJointAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_joint_conj_left guardAgreement
      (AyJointConj learnedClause checker)
      (ay_joint_conj_right trace
        (AyJointConj guardAgreement
          (AyJointConj learnedClause checker))
        run)

theorem ay_joint_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyJointAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_joint_conj_left learnedClause checker
      (ay_joint_conj_right guardAgreement
        (AyJointConj learnedClause checker)
        (ay_joint_conj_right trace
          (AyJointConj guardAgreement
            (AyJointConj learnedClause checker))
          run))

theorem ay_joint_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyJointAcceptedRun trace guardAgreement learnedClause checker -> checker :=
  fun run =>
    ay_joint_conj_right learnedClause checker
      (ay_joint_conj_right guardAgreement
        (AyJointConj learnedClause checker)
        (ay_joint_conj_right trace
          (AyJointConj guardAgreement
            (AyJointConj learnedClause checker))
          run))

theorem ay_joint_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyJointEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyJointState original base ->
    AyJointPublicReport
      (AyJointOutcome model conflict)
      (AyJointScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_joint_conj_intro
      (AyJointOutcome model conflict)
      (AyJointScope base assumption)
      (ay_joint_disj_left model conflict
        (sat
          (ay_joint_conj_left preprocessed
            (AyJointScope base assumption)
            (ay_joint_preprocess_forward original preprocessed
              (AyJointScope base assumption)
              preprocess
              (ay_joint_state_push original base assumption
                state assumptionH)))))
      (ay_joint_scope_push base assumption
        (ay_joint_conj_right original base state)
        assumptionH)

theorem ay_joint_public_unsat_report
    (base : Prop) (assumption : Prop)
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyJointAcceptedRun
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointGuardAgreement guard (AyJointScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyJointPublicReport
      (AyJointOutcome model conflict)
      (AyJointScope base assumption) :=
  fun run learnedToConflict =>
    ay_joint_conj_intro
      (AyJointOutcome model conflict)
      (AyJointScope base assumption)
      (ay_joint_disj_right model conflict
        (learnedToConflict
          (ay_joint_accepted_run_learned
            (AyJointTrace restartEpoch decisionLevel targetLevel
              learnedState digest branchDecision)
            (AyJointGuardAgreement guard (AyJointScope base assumption))
            learnedClause checker run)))
      (ay_joint_guard_agreement_frame guard
        (AyJointScope base assumption)
        (ay_joint_accepted_run_guard
          (AyJointTrace restartEpoch decisionLevel targetLevel
            learnedState digest branchDecision)
          (AyJointGuardAgreement guard (AyJointScope base assumption))
          learnedClause checker run))

theorem ay_joint_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyJointAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_joint_conj_intro guidance public guidanceH publicH

theorem ay_joint_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyJointAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_joint_conj_left guidance public report

theorem ay_joint_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyJointAcceptedReport guidance public -> public :=
  fun report =>
    ay_joint_conj_right guidance public report

theorem ay_joint_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyJointNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_joint_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_joint_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyJointNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_joint_conj_left fallbackPublic diagnostic noClaim

theorem ay_joint_mismatch_diagnostic
    (restartMismatch : Prop) (invalidTarget : Prop)
    (traceMismatch : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    restartMismatch ->
    invalidTarget ->
    traceMismatch ->
    AyJointNoClaimEntry
      (AyJointConj restartMismatch
        (AyJointConj invalidTarget traceMismatch))
      fallbackPublic :=
  fun fallbackH restartH invalidH traceH =>
    ay_joint_no_claim_intro
      (AyJointConj restartMismatch
        (AyJointConj invalidTarget traceMismatch))
      fallbackPublic
      fallbackH
      (ay_joint_conj_intro restartMismatch
        (AyJointConj invalidTarget traceMismatch)
        restartH
        (ay_joint_conj_intro invalidTarget traceMismatch
          invalidH traceH))

theorem ay_joint_policy_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyJointEquisat original preprocessed ->
    assumption ->
    AyJointAcceptedRun
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointGuardAgreement guard (AyJointScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    AyJointState original base ->
    AyJointAcceptedReport
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointPublicReport
        (AyJointOutcome model conflict)
        (AyJointScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_joint_accepted_report_intro
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointPublicReport
        (AyJointOutcome model conflict)
        (AyJointScope base assumption))
      (ay_joint_accepted_run_trace
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointGuardAgreement guard (AyJointScope base assumption))
        learnedClause checker run)
      (ay_joint_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_joint_policy_guides_unsat
    (base : Prop) (assumption : Prop)
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyJointAcceptedRun
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointGuardAgreement guard (AyJointScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyJointAcceptedReport
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointPublicReport
        (AyJointOutcome model conflict)
        (AyJointScope base assumption)) :=
  fun run learnedToConflict =>
    ay_joint_accepted_report_intro
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointPublicReport
        (AyJointOutcome model conflict)
        (AyJointScope base assumption))
      (ay_joint_accepted_run_trace
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointGuardAgreement guard (AyJointScope base assumption))
        learnedClause checker run)
      (ay_joint_public_unsat_report base assumption restartEpoch
        decisionLevel targetLevel learnedState digest branchDecision guard
        learnedClause checker model conflict run learnedToConflict)

theorem ay_joint_policy_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (restartEpoch : Prop) (decisionLevel : Prop) (targetLevel : Prop)
    (learnedState : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyJointEquisat original preprocessed ->
    assumption ->
    AyJointAcceptedRun
      (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
        digest branchDecision)
      (AyJointGuardAgreement guard (AyJointScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyJointState original base ->
    AyJointConj
      (AyJointAcceptedReport
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointPublicReport
          (AyJointOutcome model conflict)
          (AyJointScope base assumption)))
      (AyJointAcceptedReport
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointPublicReport
          (AyJointOutcome model conflict)
          (AyJointScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_joint_conj_intro
      (AyJointAcceptedReport
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointPublicReport
          (AyJointOutcome model conflict)
          (AyJointScope base assumption)))
      (AyJointAcceptedReport
        (AyJointTrace restartEpoch decisionLevel targetLevel learnedState
          digest branchDecision)
        (AyJointPublicReport
          (AyJointOutcome model conflict)
          (AyJointScope base assumption)))
      (ay_joint_policy_guides_sat original preprocessed base assumption
        restartEpoch decisionLevel targetLevel learnedState digest
        branchDecision guard learnedClause checker model conflict
        preprocess assumptionH run sat state)
      (ay_joint_policy_guides_unsat base assumption restartEpoch
        decisionLevel targetLevel learnedState digest branchDecision guard
        learnedClause checker model conflict run learnedToConflict)

theorem ay_joint_mismatch_preserves_fallback_soundness
    (restartMismatch : Prop) (invalidTarget : Prop)
    (traceMismatch : Prop) (fallbackPublic : Prop) :
    AyJointNoClaimEntry
      (AyJointConj restartMismatch
        (AyJointConj invalidTarget traceMismatch))
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_joint_no_claim_preserves_fallback
      (AyJointConj restartMismatch
        (AyJointConj invalidTarget traceMismatch))
      fallbackPublic
      noClaim
