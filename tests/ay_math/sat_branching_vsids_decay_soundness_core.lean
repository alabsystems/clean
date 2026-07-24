-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked VSIDS/activity-decay soundness skeleton for sequential SAT-COMP
-- solving. Variable scores, decay/bump epochs, and selected branch decisions
-- guide ranking only. Public SAT/UNSAT reports remain checker/replay-backed;
-- score, epoch, digest, and guard mismatches are no-claim diagnostics that
-- preserve fallback public soundness.

def AyVsidsConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyVsidsDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVsidsEquisat (before : Prop) (after : Prop) :=
  AyVsidsConj (before -> after) (after -> before)

def AyVsidsScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyVsidsState (formula : Prop) (frame : Prop) :=
  AyVsidsConj formula frame

def AyVsidsTrace
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :=
  AyVsidsConj score
    (AyVsidsConj decayEpoch
      (AyVsidsConj bumpEpoch
        (AyVsidsConj digest branchDecision)))

def AyVsidsGuardAgreement (guard : Prop) (frame : Prop) :=
  AyVsidsConj guard frame

def AyVsidsAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyVsidsConj trace
    (AyVsidsConj guardAgreement
      (AyVsidsConj learnedClause checker))

def AyVsidsOutcome (model : Prop) (conflict : Prop) :=
  AyVsidsDisj model conflict

def AyVsidsPublicReport (outcome : Prop) (frame : Prop) :=
  AyVsidsConj outcome frame

def AyVsidsAcceptedReport (guidance : Prop) (public : Prop) :=
  AyVsidsConj guidance public

def AyVsidsNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyVsidsConj fallbackPublic diagnostic

theorem ay_vsids_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyVsidsConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_vsids_conj_left
    (left : Prop) (right : Prop) :
    AyVsidsConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_vsids_conj_right
    (left : Prop) (right : Prop) :
    AyVsidsConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_vsids_disj_left
    (left : Prop) (right : Prop) :
    left -> AyVsidsDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_vsids_disj_right
    (left : Prop) (right : Prop) :
    right -> AyVsidsDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_vsids_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyVsidsEquisat before after :=
  fun forward backward =>
    ay_vsids_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_vsids_equisat_forward
    (before : Prop) (after : Prop) :
    AyVsidsEquisat before after -> before -> after :=
  fun equisat =>
    ay_vsids_conj_left (before -> after) (after -> before) equisat

theorem ay_vsids_equisat_backward
    (before : Prop) (after : Prop) :
    AyVsidsEquisat before after -> after -> before :=
  fun equisat =>
    ay_vsids_conj_right (before -> after) (after -> before) equisat

theorem ay_vsids_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyVsidsScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_vsids_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyVsidsState formula base ->
    assumption ->
    AyVsidsState formula (AyVsidsScope base assumption) :=
  fun state assumptionH =>
    ay_vsids_conj_intro formula (AyVsidsScope base assumption)
      (ay_vsids_conj_left formula base state)
      (ay_vsids_scope_push base assumption
        (ay_vsids_conj_right formula base state)
        assumptionH)

theorem ay_vsids_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyVsidsEquisat original preprocessed ->
    AyVsidsState original frame ->
    AyVsidsState preprocessed frame :=
  fun preprocess state =>
    ay_vsids_conj_intro preprocessed frame
      (ay_vsids_equisat_forward original preprocessed preprocess
        (ay_vsids_conj_left original frame state))
      (ay_vsids_conj_right original frame state)

theorem ay_vsids_trace_intro
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    score ->
    decayEpoch ->
    bumpEpoch ->
    digest ->
    branchDecision ->
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision :=
  fun scoreH decayH bumpH digestH branchH =>
    ay_vsids_conj_intro score
      (AyVsidsConj decayEpoch
        (AyVsidsConj bumpEpoch
          (AyVsidsConj digest branchDecision)))
      scoreH
      (ay_vsids_conj_intro decayEpoch
        (AyVsidsConj bumpEpoch
          (AyVsidsConj digest branchDecision))
        decayH
        (ay_vsids_conj_intro bumpEpoch
          (AyVsidsConj digest branchDecision)
          bumpH
          (ay_vsids_conj_intro digest branchDecision digestH branchH)))

theorem ay_vsids_trace_score
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision ->
    score :=
  fun trace =>
    ay_vsids_conj_left score
      (AyVsidsConj decayEpoch
        (AyVsidsConj bumpEpoch
          (AyVsidsConj digest branchDecision)))
      trace

theorem ay_vsids_trace_decay_epoch
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision ->
    decayEpoch :=
  fun trace =>
    ay_vsids_conj_left decayEpoch
      (AyVsidsConj bumpEpoch (AyVsidsConj digest branchDecision))
      (ay_vsids_conj_right score
        (AyVsidsConj decayEpoch
          (AyVsidsConj bumpEpoch
            (AyVsidsConj digest branchDecision)))
        trace)

theorem ay_vsids_trace_bump_epoch
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision ->
    bumpEpoch :=
  fun trace =>
    ay_vsids_conj_left bumpEpoch
      (AyVsidsConj digest branchDecision)
      (ay_vsids_conj_right decayEpoch
        (AyVsidsConj bumpEpoch (AyVsidsConj digest branchDecision))
        (ay_vsids_conj_right score
          (AyVsidsConj decayEpoch
            (AyVsidsConj bumpEpoch
              (AyVsidsConj digest branchDecision)))
          trace))

theorem ay_vsids_trace_digest
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision ->
    digest :=
  fun trace =>
    ay_vsids_conj_left digest branchDecision
      (ay_vsids_conj_right bumpEpoch
        (AyVsidsConj digest branchDecision)
        (ay_vsids_conj_right decayEpoch
          (AyVsidsConj bumpEpoch (AyVsidsConj digest branchDecision))
          (ay_vsids_conj_right score
            (AyVsidsConj decayEpoch
              (AyVsidsConj bumpEpoch
                (AyVsidsConj digest branchDecision)))
            trace)))

theorem ay_vsids_trace_branch_decision
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) :
    AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_vsids_conj_right digest branchDecision
      (ay_vsids_conj_right bumpEpoch
        (AyVsidsConj digest branchDecision)
        (ay_vsids_conj_right decayEpoch
          (AyVsidsConj bumpEpoch (AyVsidsConj digest branchDecision))
          (ay_vsids_conj_right score
            (AyVsidsConj decayEpoch
              (AyVsidsConj bumpEpoch
                (AyVsidsConj digest branchDecision)))
            trace)))

theorem ay_vsids_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyVsidsGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_vsids_conj_intro guard frame guardH frameH

theorem ay_vsids_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyVsidsGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_vsids_conj_left guard frame agreement

theorem ay_vsids_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyVsidsGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_vsids_conj_right guard frame agreement

theorem ay_vsids_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyVsidsAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_vsids_conj_intro trace
      (AyVsidsConj guardAgreement
        (AyVsidsConj learnedClause checker))
      traceH
      (ay_vsids_conj_intro guardAgreement
        (AyVsidsConj learnedClause checker)
        guardH
        (ay_vsids_conj_intro learnedClause checker learnedH checkerH))

theorem ay_vsids_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyVsidsAcceptedRun trace guardAgreement learnedClause checker ->
    trace :=
  fun run =>
    ay_vsids_conj_left trace
      (AyVsidsConj guardAgreement
        (AyVsidsConj learnedClause checker))
      run

theorem ay_vsids_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyVsidsAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_vsids_conj_left guardAgreement
      (AyVsidsConj learnedClause checker)
      (ay_vsids_conj_right trace
        (AyVsidsConj guardAgreement
          (AyVsidsConj learnedClause checker))
        run)

theorem ay_vsids_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyVsidsAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_vsids_conj_left learnedClause checker
      (ay_vsids_conj_right guardAgreement
        (AyVsidsConj learnedClause checker)
        (ay_vsids_conj_right trace
          (AyVsidsConj guardAgreement
            (AyVsidsConj learnedClause checker))
          run))

theorem ay_vsids_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyVsidsAcceptedRun trace guardAgreement learnedClause checker ->
    checker :=
  fun run =>
    ay_vsids_conj_right learnedClause checker
      (ay_vsids_conj_right guardAgreement
        (AyVsidsConj learnedClause checker)
        (ay_vsids_conj_right trace
          (AyVsidsConj guardAgreement
            (AyVsidsConj learnedClause checker))
          run))

theorem ay_vsids_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyVsidsEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyVsidsState original base ->
    AyVsidsPublicReport
      (AyVsidsOutcome model conflict)
      (AyVsidsScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_vsids_conj_intro
      (AyVsidsOutcome model conflict)
      (AyVsidsScope base assumption)
      (ay_vsids_disj_left model conflict
        (sat
          (ay_vsids_conj_left preprocessed
            (AyVsidsScope base assumption)
            (ay_vsids_preprocess_forward original preprocessed
              (AyVsidsScope base assumption)
              preprocess
              (ay_vsids_state_push original base assumption
                state assumptionH)))))
      (ay_vsids_scope_push base assumption
        (ay_vsids_conj_right original base state)
        assumptionH)

theorem ay_vsids_public_unsat_report
    (base : Prop) (assumption : Prop)
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyVsidsAcceptedRun
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyVsidsPublicReport
      (AyVsidsOutcome model conflict)
      (AyVsidsScope base assumption) :=
  fun run learnedToConflict =>
    ay_vsids_conj_intro
      (AyVsidsOutcome model conflict)
      (AyVsidsScope base assumption)
      (ay_vsids_disj_right model conflict
        (learnedToConflict
          (ay_vsids_accepted_run_learned
            (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
            (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
            learnedClause checker run)))
      (ay_vsids_guard_agreement_frame guard
        (AyVsidsScope base assumption)
        (ay_vsids_accepted_run_guard
          (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
          (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
          learnedClause checker run))

theorem ay_vsids_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyVsidsAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_vsids_conj_intro guidance public guidanceH publicH

theorem ay_vsids_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyVsidsAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_vsids_conj_left guidance public report

theorem ay_vsids_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyVsidsAcceptedReport guidance public -> public :=
  fun report =>
    ay_vsids_conj_right guidance public report

theorem ay_vsids_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyVsidsNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_vsids_conj_intro fallbackPublic diagnostic
      fallbackH diagnosticH

theorem ay_vsids_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyVsidsNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_vsids_conj_left fallbackPublic diagnostic noClaim

theorem ay_vsids_mismatch_diagnostic
    (scoreMismatch : Prop) (epochMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    fallbackPublic ->
    scoreMismatch ->
    epochMismatch ->
    digestMismatch ->
    guardMismatch ->
    AyVsidsNoClaimEntry
      (AyVsidsConj
        (AyVsidsConj scoreMismatch epochMismatch)
        (AyVsidsConj digestMismatch guardMismatch))
      fallbackPublic :=
  fun fallbackH scoreH epochH digestH guardH =>
    ay_vsids_no_claim_intro
      (AyVsidsConj
        (AyVsidsConj scoreMismatch epochMismatch)
        (AyVsidsConj digestMismatch guardMismatch))
      fallbackPublic
      fallbackH
      (ay_vsids_conj_intro
        (AyVsidsConj scoreMismatch epochMismatch)
        (AyVsidsConj digestMismatch guardMismatch)
        (ay_vsids_conj_intro scoreMismatch epochMismatch
          scoreH epochH)
        (ay_vsids_conj_intro digestMismatch guardMismatch
          digestH guardH))

theorem ay_vsids_decay_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyVsidsEquisat original preprocessed ->
    assumption ->
    AyVsidsAcceptedRun
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    AyVsidsState original base ->
    AyVsidsAcceptedReport
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsPublicReport
        (AyVsidsOutcome model conflict)
        (AyVsidsScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_vsids_accepted_report_intro
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsPublicReport
        (AyVsidsOutcome model conflict)
        (AyVsidsScope base assumption))
      (ay_vsids_accepted_run_trace
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
        learnedClause checker run)
      (ay_vsids_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_vsids_decay_guides_unsat
    (base : Prop) (assumption : Prop)
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyVsidsAcceptedRun
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyVsidsAcceptedReport
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsPublicReport
        (AyVsidsOutcome model conflict)
        (AyVsidsScope base assumption)) :=
  fun run learnedToConflict =>
    ay_vsids_accepted_report_intro
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsPublicReport
        (AyVsidsOutcome model conflict)
        (AyVsidsScope base assumption))
      (ay_vsids_accepted_run_trace
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
        learnedClause checker run)
      (ay_vsids_public_unsat_report base assumption score decayEpoch
        bumpEpoch digest branchDecision guard learnedClause checker
        model conflict run learnedToConflict)

theorem ay_vsids_decay_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (score : Prop) (decayEpoch : Prop) (bumpEpoch : Prop)
    (digest : Prop) (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyVsidsEquisat original preprocessed ->
    assumption ->
    AyVsidsAcceptedRun
      (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
      (AyVsidsGuardAgreement guard (AyVsidsScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyVsidsState original base ->
    AyVsidsConj
      (AyVsidsAcceptedReport
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsPublicReport
          (AyVsidsOutcome model conflict)
          (AyVsidsScope base assumption)))
      (AyVsidsAcceptedReport
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsPublicReport
          (AyVsidsOutcome model conflict)
          (AyVsidsScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_vsids_conj_intro
      (AyVsidsAcceptedReport
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsPublicReport
          (AyVsidsOutcome model conflict)
          (AyVsidsScope base assumption)))
      (AyVsidsAcceptedReport
        (AyVsidsTrace score decayEpoch bumpEpoch digest branchDecision)
        (AyVsidsPublicReport
          (AyVsidsOutcome model conflict)
          (AyVsidsScope base assumption)))
      (ay_vsids_decay_guides_sat original preprocessed base assumption
        score decayEpoch bumpEpoch digest branchDecision guard
        learnedClause checker model conflict preprocess assumptionH
        run sat state)
      (ay_vsids_decay_guides_unsat base assumption score decayEpoch
        bumpEpoch digest branchDecision guard learnedClause checker
        model conflict run learnedToConflict)

theorem ay_vsids_mismatch_preserves_fallback_soundness
    (scoreMismatch : Prop) (epochMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    AyVsidsNoClaimEntry
      (AyVsidsConj
        (AyVsidsConj scoreMismatch epochMismatch)
        (AyVsidsConj digestMismatch guardMismatch))
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_vsids_no_claim_preserves_fallback
      (AyVsidsConj
        (AyVsidsConj scoreMismatch epochMismatch)
        (AyVsidsConj digestMismatch guardMismatch))
      fallbackPublic
      noClaim
