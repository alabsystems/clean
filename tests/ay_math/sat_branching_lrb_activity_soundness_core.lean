-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked LRB/activity branching soundness skeleton for sequential SAT-COMP
-- solving. Learnt-rate/activity scores, bump/decay epochs, ranking, and branch
-- decisions guide search only. Public SAT/UNSAT reports remain
-- checker/replay-backed; score, epoch, digest, and guard mismatches are
-- no-claim diagnostics that preserve fallback public soundness.

def AyLrbConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLrbDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLrbEquisat (before : Prop) (after : Prop) :=
  AyLrbConj (before -> after) (after -> before)

def AyLrbScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyLrbState (formula : Prop) (frame : Prop) :=
  AyLrbConj formula frame

def AyLrbTrace
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :=
  AyLrbConj learntRate
    (AyLrbConj activity
      (AyLrbConj bumpEpoch
        (AyLrbConj decayEpoch
          (AyLrbConj ranking
            (AyLrbConj digest branchDecision)))))

def AyLrbGuardAgreement (guard : Prop) (frame : Prop) :=
  AyLrbConj guard frame

def AyLrbAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyLrbConj trace
    (AyLrbConj guardAgreement
      (AyLrbConj learnedClause checker))

def AyLrbOutcome (model : Prop) (conflict : Prop) :=
  AyLrbDisj model conflict

def AyLrbPublicReport (outcome : Prop) (frame : Prop) :=
  AyLrbConj outcome frame

def AyLrbAcceptedReport (guidance : Prop) (public : Prop) :=
  AyLrbConj guidance public

def AyLrbNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyLrbConj fallbackPublic diagnostic

theorem ay_lrb_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLrbConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_lrb_conj_left
    (left : Prop) (right : Prop) :
    AyLrbConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_lrb_conj_right
    (left : Prop) (right : Prop) :
    AyLrbConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_lrb_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLrbDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_lrb_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLrbDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_lrb_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyLrbEquisat before after :=
  fun forward backward =>
    ay_lrb_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_lrb_equisat_forward
    (before : Prop) (after : Prop) :
    AyLrbEquisat before after -> before -> after :=
  fun equisat =>
    ay_lrb_conj_left (before -> after) (after -> before) equisat

theorem ay_lrb_equisat_backward
    (before : Prop) (after : Prop) :
    AyLrbEquisat before after -> after -> before :=
  fun equisat =>
    ay_lrb_conj_right (before -> after) (after -> before) equisat

theorem ay_lrb_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyLrbScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_lrb_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyLrbState formula base ->
    assumption ->
    AyLrbState formula (AyLrbScope base assumption) :=
  fun state assumptionH =>
    ay_lrb_conj_intro formula (AyLrbScope base assumption)
      (ay_lrb_conj_left formula base state)
      (ay_lrb_scope_push base assumption
        (ay_lrb_conj_right formula base state)
        assumptionH)

theorem ay_lrb_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyLrbEquisat original preprocessed ->
    AyLrbState original frame ->
    AyLrbState preprocessed frame :=
  fun preprocess state =>
    ay_lrb_conj_intro preprocessed frame
      (ay_lrb_equisat_forward original preprocessed preprocess
        (ay_lrb_conj_left original frame state))
      (ay_lrb_conj_right original frame state)

theorem ay_lrb_trace_intro
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    learntRate ->
    activity ->
    bumpEpoch ->
    decayEpoch ->
    ranking ->
    digest ->
    branchDecision ->
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision :=
  fun learntH activityH bumpH decayH rankingH digestH branchH =>
    ay_lrb_conj_intro learntRate
      (AyLrbConj activity
        (AyLrbConj bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision)))))
      learntH
      (ay_lrb_conj_intro activity
        (AyLrbConj bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision))))
        activityH
        (ay_lrb_conj_intro bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision)))
          bumpH
          (ay_lrb_conj_intro decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision))
            decayH
            (ay_lrb_conj_intro ranking
              (AyLrbConj digest branchDecision)
              rankingH
              (ay_lrb_conj_intro digest branchDecision
                digestH branchH)))))

theorem ay_lrb_trace_learnt_rate
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    learntRate :=
  fun trace =>
    ay_lrb_conj_left learntRate
      (AyLrbConj activity
        (AyLrbConj bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision)))))
      trace

theorem ay_lrb_trace_activity
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    activity :=
  fun trace =>
    ay_lrb_conj_left activity
      (AyLrbConj bumpEpoch
        (AyLrbConj decayEpoch
          (AyLrbConj ranking
            (AyLrbConj digest branchDecision))))
      (ay_lrb_conj_right learntRate
        (AyLrbConj activity
          (AyLrbConj bumpEpoch
            (AyLrbConj decayEpoch
              (AyLrbConj ranking
                (AyLrbConj digest branchDecision)))))
        trace)

theorem ay_lrb_trace_bump_epoch
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    bumpEpoch :=
  fun trace =>
    ay_lrb_conj_left bumpEpoch
      (AyLrbConj decayEpoch
        (AyLrbConj ranking (AyLrbConj digest branchDecision)))
      (ay_lrb_conj_right activity
        (AyLrbConj bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking
              (AyLrbConj digest branchDecision))))
        (ay_lrb_conj_right learntRate
          (AyLrbConj activity
            (AyLrbConj bumpEpoch
              (AyLrbConj decayEpoch
                (AyLrbConj ranking
                  (AyLrbConj digest branchDecision)))))
          trace))

theorem ay_lrb_trace_decay_epoch
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    decayEpoch :=
  fun trace =>
    ay_lrb_conj_left decayEpoch
      (AyLrbConj ranking (AyLrbConj digest branchDecision))
      (ay_lrb_conj_right bumpEpoch
        (AyLrbConj decayEpoch
          (AyLrbConj ranking (AyLrbConj digest branchDecision)))
        (ay_lrb_conj_right activity
          (AyLrbConj bumpEpoch
            (AyLrbConj decayEpoch
              (AyLrbConj ranking
                (AyLrbConj digest branchDecision))))
          (ay_lrb_conj_right learntRate
            (AyLrbConj activity
              (AyLrbConj bumpEpoch
                (AyLrbConj decayEpoch
                  (AyLrbConj ranking
                    (AyLrbConj digest branchDecision)))))
            trace)))

theorem ay_lrb_trace_ranking
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    ranking :=
  fun trace =>
    ay_lrb_conj_left ranking (AyLrbConj digest branchDecision)
      (ay_lrb_conj_right decayEpoch
        (AyLrbConj ranking (AyLrbConj digest branchDecision))
        (ay_lrb_conj_right bumpEpoch
          (AyLrbConj decayEpoch
            (AyLrbConj ranking (AyLrbConj digest branchDecision)))
          (ay_lrb_conj_right activity
            (AyLrbConj bumpEpoch
              (AyLrbConj decayEpoch
                (AyLrbConj ranking
                  (AyLrbConj digest branchDecision))))
            (ay_lrb_conj_right learntRate
              (AyLrbConj activity
                (AyLrbConj bumpEpoch
                  (AyLrbConj decayEpoch
                    (AyLrbConj ranking
                      (AyLrbConj digest branchDecision)))))
              trace))))

theorem ay_lrb_trace_digest
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    digest :=
  fun trace =>
    ay_lrb_conj_left digest branchDecision
      (ay_lrb_conj_right ranking (AyLrbConj digest branchDecision)
        (ay_lrb_conj_right decayEpoch
          (AyLrbConj ranking (AyLrbConj digest branchDecision))
          (ay_lrb_conj_right bumpEpoch
            (AyLrbConj decayEpoch
              (AyLrbConj ranking (AyLrbConj digest branchDecision)))
            (ay_lrb_conj_right activity
              (AyLrbConj bumpEpoch
                (AyLrbConj decayEpoch
                  (AyLrbConj ranking
                    (AyLrbConj digest branchDecision))))
              (ay_lrb_conj_right learntRate
                (AyLrbConj activity
                  (AyLrbConj bumpEpoch
                    (AyLrbConj decayEpoch
                      (AyLrbConj ranking
                        (AyLrbConj digest branchDecision)))))
                trace)))))

theorem ay_lrb_trace_branch_decision
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop) :
    AyLrbTrace learntRate activity bumpEpoch decayEpoch
      ranking digest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_lrb_conj_right digest branchDecision
      (ay_lrb_conj_right ranking (AyLrbConj digest branchDecision)
        (ay_lrb_conj_right decayEpoch
          (AyLrbConj ranking (AyLrbConj digest branchDecision))
          (ay_lrb_conj_right bumpEpoch
            (AyLrbConj decayEpoch
              (AyLrbConj ranking (AyLrbConj digest branchDecision)))
            (ay_lrb_conj_right activity
              (AyLrbConj bumpEpoch
                (AyLrbConj decayEpoch
                  (AyLrbConj ranking
                    (AyLrbConj digest branchDecision))))
              (ay_lrb_conj_right learntRate
                (AyLrbConj activity
                  (AyLrbConj bumpEpoch
                    (AyLrbConj decayEpoch
                      (AyLrbConj ranking
                        (AyLrbConj digest branchDecision)))))
                trace)))))

theorem ay_lrb_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyLrbGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_lrb_conj_intro guard frame guardH frameH

theorem ay_lrb_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyLrbGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_lrb_conj_left guard frame agreement

theorem ay_lrb_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyLrbGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_lrb_conj_right guard frame agreement

theorem ay_lrb_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyLrbAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_lrb_conj_intro trace
      (AyLrbConj guardAgreement
        (AyLrbConj learnedClause checker))
      traceH
      (ay_lrb_conj_intro guardAgreement
        (AyLrbConj learnedClause checker)
        guardH
        (ay_lrb_conj_intro learnedClause checker learnedH checkerH))

theorem ay_lrb_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLrbAcceptedRun trace guardAgreement learnedClause checker ->
    trace :=
  fun run =>
    ay_lrb_conj_left trace
      (AyLrbConj guardAgreement
        (AyLrbConj learnedClause checker))
      run

theorem ay_lrb_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLrbAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_lrb_conj_left guardAgreement
      (AyLrbConj learnedClause checker)
      (ay_lrb_conj_right trace
        (AyLrbConj guardAgreement
          (AyLrbConj learnedClause checker))
        run)

theorem ay_lrb_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLrbAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_lrb_conj_left learnedClause checker
      (ay_lrb_conj_right guardAgreement
        (AyLrbConj learnedClause checker)
        (ay_lrb_conj_right trace
          (AyLrbConj guardAgreement
            (AyLrbConj learnedClause checker))
          run))

theorem ay_lrb_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLrbAcceptedRun trace guardAgreement learnedClause checker ->
    checker :=
  fun run =>
    ay_lrb_conj_right learnedClause checker
      (ay_lrb_conj_right guardAgreement
        (AyLrbConj learnedClause checker)
        (ay_lrb_conj_right trace
          (AyLrbConj guardAgreement
            (AyLrbConj learnedClause checker))
          run))

theorem ay_lrb_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyLrbEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyLrbState original base ->
    AyLrbPublicReport
      (AyLrbOutcome model conflict)
      (AyLrbScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_lrb_conj_intro
      (AyLrbOutcome model conflict)
      (AyLrbScope base assumption)
      (ay_lrb_disj_left model conflict
        (sat
          (ay_lrb_conj_left preprocessed
            (AyLrbScope base assumption)
            (ay_lrb_preprocess_forward original preprocessed
              (AyLrbScope base assumption)
              preprocess
              (ay_lrb_state_push original base assumption
                state assumptionH)))))
      (ay_lrb_scope_push base assumption
        (ay_lrb_conj_right original base state)
        assumptionH)

theorem ay_lrb_public_unsat_report
    (base : Prop) (assumption : Prop)
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyLrbAcceptedRun
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbGuardAgreement guard (AyLrbScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyLrbPublicReport
      (AyLrbOutcome model conflict)
      (AyLrbScope base assumption) :=
  fun run learnedToConflict =>
    ay_lrb_conj_intro
      (AyLrbOutcome model conflict)
      (AyLrbScope base assumption)
      (ay_lrb_disj_right model conflict
        (learnedToConflict
          (ay_lrb_accepted_run_learned
            (AyLrbTrace learntRate activity bumpEpoch decayEpoch
              ranking digest branchDecision)
            (AyLrbGuardAgreement guard (AyLrbScope base assumption))
            learnedClause checker run)))
      (ay_lrb_guard_agreement_frame guard
        (AyLrbScope base assumption)
        (ay_lrb_accepted_run_guard
          (AyLrbTrace learntRate activity bumpEpoch decayEpoch
            ranking digest branchDecision)
          (AyLrbGuardAgreement guard (AyLrbScope base assumption))
          learnedClause checker run))

theorem ay_lrb_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyLrbAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_lrb_conj_intro guidance public guidanceH publicH

theorem ay_lrb_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyLrbAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_lrb_conj_left guidance public report

theorem ay_lrb_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyLrbAcceptedReport guidance public -> public :=
  fun report =>
    ay_lrb_conj_right guidance public report

theorem ay_lrb_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyLrbNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_lrb_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_lrb_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyLrbNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_lrb_conj_left fallbackPublic diagnostic noClaim

theorem ay_lrb_mismatch_diagnostic
    (scoreMismatch : Prop) (epochMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    fallbackPublic ->
    scoreMismatch ->
    epochMismatch ->
    digestMismatch ->
    guardMismatch ->
    AyLrbNoClaimEntry
      (AyLrbConj
        (AyLrbConj scoreMismatch epochMismatch)
        (AyLrbConj digestMismatch guardMismatch))
      fallbackPublic :=
  fun fallbackH scoreH epochH digestH guardH =>
    ay_lrb_no_claim_intro
      (AyLrbConj
        (AyLrbConj scoreMismatch epochMismatch)
        (AyLrbConj digestMismatch guardMismatch))
      fallbackPublic
      fallbackH
      (ay_lrb_conj_intro
        (AyLrbConj scoreMismatch epochMismatch)
        (AyLrbConj digestMismatch guardMismatch)
        (ay_lrb_conj_intro scoreMismatch epochMismatch scoreH epochH)
        (ay_lrb_conj_intro digestMismatch guardMismatch digestH guardH))

theorem ay_lrb_activity_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyLrbEquisat original preprocessed ->
    assumption ->
    AyLrbAcceptedRun
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbGuardAgreement guard (AyLrbScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    AyLrbState original base ->
    AyLrbAcceptedReport
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbPublicReport
        (AyLrbOutcome model conflict)
        (AyLrbScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_lrb_accepted_report_intro
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbPublicReport
        (AyLrbOutcome model conflict)
        (AyLrbScope base assumption))
      (ay_lrb_accepted_run_trace
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbGuardAgreement guard (AyLrbScope base assumption))
        learnedClause checker run)
      (ay_lrb_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_lrb_activity_guides_unsat
    (base : Prop) (assumption : Prop)
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyLrbAcceptedRun
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbGuardAgreement guard (AyLrbScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyLrbAcceptedReport
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbPublicReport
        (AyLrbOutcome model conflict)
        (AyLrbScope base assumption)) :=
  fun run learnedToConflict =>
    ay_lrb_accepted_report_intro
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbPublicReport
        (AyLrbOutcome model conflict)
        (AyLrbScope base assumption))
      (ay_lrb_accepted_run_trace
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbGuardAgreement guard (AyLrbScope base assumption))
        learnedClause checker run)
      (ay_lrb_public_unsat_report base assumption learntRate activity
        bumpEpoch decayEpoch ranking digest branchDecision guard
        learnedClause checker model conflict run learnedToConflict)

theorem ay_lrb_activity_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (learntRate : Prop) (activity : Prop)
    (bumpEpoch : Prop) (decayEpoch : Prop)
    (ranking : Prop) (digest : Prop) (branchDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyLrbEquisat original preprocessed ->
    assumption ->
    AyLrbAcceptedRun
      (AyLrbTrace learntRate activity bumpEpoch decayEpoch
        ranking digest branchDecision)
      (AyLrbGuardAgreement guard (AyLrbScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyLrbState original base ->
    AyLrbConj
      (AyLrbAcceptedReport
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbPublicReport
          (AyLrbOutcome model conflict)
          (AyLrbScope base assumption)))
      (AyLrbAcceptedReport
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbPublicReport
          (AyLrbOutcome model conflict)
          (AyLrbScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_lrb_conj_intro
      (AyLrbAcceptedReport
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbPublicReport
          (AyLrbOutcome model conflict)
          (AyLrbScope base assumption)))
      (AyLrbAcceptedReport
        (AyLrbTrace learntRate activity bumpEpoch decayEpoch
          ranking digest branchDecision)
        (AyLrbPublicReport
          (AyLrbOutcome model conflict)
          (AyLrbScope base assumption)))
      (ay_lrb_activity_guides_sat original preprocessed base assumption
        learntRate activity bumpEpoch decayEpoch ranking digest
        branchDecision guard learnedClause checker model conflict
        preprocess assumptionH run sat state)
      (ay_lrb_activity_guides_unsat base assumption learntRate activity
        bumpEpoch decayEpoch ranking digest branchDecision guard
        learnedClause checker model conflict run learnedToConflict)

theorem ay_lrb_mismatch_preserves_fallback_soundness
    (scoreMismatch : Prop) (epochMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    AyLrbNoClaimEntry
      (AyLrbConj
        (AyLrbConj scoreMismatch epochMismatch)
        (AyLrbConj digestMismatch guardMismatch))
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_lrb_no_claim_preserves_fallback
      (AyLrbConj
        (AyLrbConj scoreMismatch epochMismatch)
        (AyLrbConj digestMismatch guardMismatch))
      fallbackPublic
      noClaim
