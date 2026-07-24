-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked phase-saving soundness skeleton for sequential SAT-COMP solving.
-- Saved phases and deterministic replay traces guide branching only. Public
-- SAT/UNSAT reports remain checker/replay-backed; seed, digest, phase, and
-- guard mismatches produce diagnostic no-claim entries that preserve fallback
-- public soundness.

def AyPhaseConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyPhaseDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPhaseEquisat (before : Prop) (after : Prop) :=
  AyPhaseConj (before -> after) (after -> before)

def AyPhaseScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyPhaseState (formula : Prop) (frame : Prop) :=
  AyPhaseConj formula frame

def AyPhaseTrace
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :=
  AyPhaseConj seed
    (AyPhaseConj digest
      (AyPhaseConj savedPhase branchDecision))

def AyPhaseGuardAgreement (guard : Prop) (frame : Prop) :=
  AyPhaseConj guard frame

def AyPhaseAcceptedRun
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyPhaseConj trace
    (AyPhaseConj guardAgreement
      (AyPhaseConj learnedClause checker))

def AyPhaseOutcome (model : Prop) (conflict : Prop) :=
  AyPhaseDisj model conflict

def AyPhasePublicReport (outcome : Prop) (frame : Prop) :=
  AyPhaseConj outcome frame

def AyPhaseAcceptedReport (guidance : Prop) (public : Prop) :=
  AyPhaseConj guidance public

def AyPhaseNoClaimEntry (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyPhaseConj fallbackPublic diagnostic

theorem ay_phase_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyPhaseConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_phase_conj_left
    (left : Prop) (right : Prop) :
    AyPhaseConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_phase_conj_right
    (left : Prop) (right : Prop) :
    AyPhaseConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_phase_disj_left
    (left : Prop) (right : Prop) :
    left -> AyPhaseDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_phase_disj_right
    (left : Prop) (right : Prop) :
    right -> AyPhaseDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_phase_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyPhaseEquisat before after :=
  fun forward backward =>
    ay_phase_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_phase_equisat_forward
    (before : Prop) (after : Prop) :
    AyPhaseEquisat before after -> before -> after :=
  fun equisat =>
    ay_phase_conj_left (before -> after) (after -> before) equisat

theorem ay_phase_equisat_backward
    (before : Prop) (after : Prop) :
    AyPhaseEquisat before after -> after -> before :=
  fun equisat =>
    ay_phase_conj_right (before -> after) (after -> before) equisat

theorem ay_phase_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyPhaseScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_phase_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyPhaseState formula base ->
    assumption ->
    AyPhaseState formula (AyPhaseScope base assumption) :=
  fun state assumptionH =>
    ay_phase_conj_intro formula (AyPhaseScope base assumption)
      (ay_phase_conj_left formula base state)
      (ay_phase_scope_push base assumption
        (ay_phase_conj_right formula base state)
        assumptionH)

theorem ay_phase_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyPhaseEquisat original preprocessed ->
    AyPhaseState original frame ->
    AyPhaseState preprocessed frame :=
  fun preprocess state =>
    ay_phase_conj_intro preprocessed frame
      (ay_phase_equisat_forward original preprocessed preprocess
        (ay_phase_conj_left original frame state))
      (ay_phase_conj_right original frame state)

theorem ay_phase_trace_intro
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :
    seed ->
    digest ->
    savedPhase ->
    branchDecision ->
    AyPhaseTrace seed digest savedPhase branchDecision :=
  fun seedH digestH phaseH branchH =>
    ay_phase_conj_intro seed
      (AyPhaseConj digest (AyPhaseConj savedPhase branchDecision))
      seedH
      (ay_phase_conj_intro digest
        (AyPhaseConj savedPhase branchDecision)
        digestH
        (ay_phase_conj_intro savedPhase branchDecision phaseH branchH))

theorem ay_phase_trace_seed
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :
    AyPhaseTrace seed digest savedPhase branchDecision -> seed :=
  fun trace =>
    ay_phase_conj_left seed
      (AyPhaseConj digest (AyPhaseConj savedPhase branchDecision))
      trace

theorem ay_phase_trace_digest
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :
    AyPhaseTrace seed digest savedPhase branchDecision -> digest :=
  fun trace =>
    ay_phase_conj_left digest
      (AyPhaseConj savedPhase branchDecision)
      (ay_phase_conj_right seed
        (AyPhaseConj digest (AyPhaseConj savedPhase branchDecision))
        trace)

theorem ay_phase_trace_saved_phase
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :
    AyPhaseTrace seed digest savedPhase branchDecision -> savedPhase :=
  fun trace =>
    ay_phase_conj_left savedPhase branchDecision
      (ay_phase_conj_right digest
        (AyPhaseConj savedPhase branchDecision)
        (ay_phase_conj_right seed
          (AyPhaseConj digest (AyPhaseConj savedPhase branchDecision))
          trace))

theorem ay_phase_trace_branch_decision
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) :
    AyPhaseTrace seed digest savedPhase branchDecision -> branchDecision :=
  fun trace =>
    ay_phase_conj_right savedPhase branchDecision
      (ay_phase_conj_right digest
        (AyPhaseConj savedPhase branchDecision)
        (ay_phase_conj_right seed
          (AyPhaseConj digest (AyPhaseConj savedPhase branchDecision))
          trace))

theorem ay_phase_guard_agreement_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyPhaseGuardAgreement guard frame :=
  fun guardH frameH =>
    ay_phase_conj_intro guard frame guardH frameH

theorem ay_phase_guard_agreement_guard
    (guard : Prop) (frame : Prop) :
    AyPhaseGuardAgreement guard frame -> guard :=
  fun agreement =>
    ay_phase_conj_left guard frame agreement

theorem ay_phase_guard_agreement_frame
    (guard : Prop) (frame : Prop) :
    AyPhaseGuardAgreement guard frame -> frame :=
  fun agreement =>
    ay_phase_conj_right guard frame agreement

theorem ay_phase_accepted_run_intro
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    trace ->
    guardAgreement ->
    learnedClause ->
    checker ->
    AyPhaseAcceptedRun trace guardAgreement learnedClause checker :=
  fun traceH guardH learnedH checkerH =>
    ay_phase_conj_intro trace
      (AyPhaseConj guardAgreement
        (AyPhaseConj learnedClause checker))
      traceH
      (ay_phase_conj_intro guardAgreement
        (AyPhaseConj learnedClause checker)
        guardH
        (ay_phase_conj_intro learnedClause checker learnedH checkerH))

theorem ay_phase_accepted_run_trace
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPhaseAcceptedRun trace guardAgreement learnedClause checker ->
    trace :=
  fun run =>
    ay_phase_conj_left trace
      (AyPhaseConj guardAgreement
        (AyPhaseConj learnedClause checker))
      run

theorem ay_phase_accepted_run_guard
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPhaseAcceptedRun trace guardAgreement learnedClause checker ->
    guardAgreement :=
  fun run =>
    ay_phase_conj_left guardAgreement
      (AyPhaseConj learnedClause checker)
      (ay_phase_conj_right trace
        (AyPhaseConj guardAgreement
          (AyPhaseConj learnedClause checker))
        run)

theorem ay_phase_accepted_run_learned
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPhaseAcceptedRun trace guardAgreement learnedClause checker ->
    learnedClause :=
  fun run =>
    ay_phase_conj_left learnedClause checker
      (ay_phase_conj_right guardAgreement
        (AyPhaseConj learnedClause checker)
        (ay_phase_conj_right trace
          (AyPhaseConj guardAgreement
            (AyPhaseConj learnedClause checker))
          run))

theorem ay_phase_accepted_run_checker
    (trace : Prop) (guardAgreement : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPhaseAcceptedRun trace guardAgreement learnedClause checker ->
    checker :=
  fun run =>
    ay_phase_conj_right learnedClause checker
      (ay_phase_conj_right guardAgreement
        (AyPhaseConj learnedClause checker)
        (ay_phase_conj_right trace
          (AyPhaseConj guardAgreement
            (AyPhaseConj learnedClause checker))
          run))

theorem ay_phase_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyPhaseEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyPhaseState original base ->
    AyPhasePublicReport
      (AyPhaseOutcome model conflict)
      (AyPhaseScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_phase_conj_intro
      (AyPhaseOutcome model conflict)
      (AyPhaseScope base assumption)
      (ay_phase_disj_left model conflict
        (sat
          (ay_phase_conj_left preprocessed
            (AyPhaseScope base assumption)
            (ay_phase_preprocess_forward original preprocessed
              (AyPhaseScope base assumption)
              preprocess
              (ay_phase_state_push original base assumption
                state assumptionH)))))
      (ay_phase_scope_push base assumption
        (ay_phase_conj_right original base state)
        assumptionH)

theorem ay_phase_public_unsat_report
    (base : Prop) (assumption : Prop)
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPhaseAcceptedRun
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyPhasePublicReport
      (AyPhaseOutcome model conflict)
      (AyPhaseScope base assumption) :=
  fun run learnedToConflict =>
    ay_phase_conj_intro
      (AyPhaseOutcome model conflict)
      (AyPhaseScope base assumption)
      (ay_phase_disj_right model conflict
        (learnedToConflict
          (ay_phase_accepted_run_learned
            (AyPhaseTrace seed digest savedPhase branchDecision)
            (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
            learnedClause checker run)))
      (ay_phase_guard_agreement_frame guard
        (AyPhaseScope base assumption)
        (ay_phase_accepted_run_guard
          (AyPhaseTrace seed digest savedPhase branchDecision)
          (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
          learnedClause checker run))

theorem ay_phase_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyPhaseAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_phase_conj_intro guidance public guidanceH publicH

theorem ay_phase_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyPhaseAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_phase_conj_left guidance public report

theorem ay_phase_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyPhaseAcceptedReport guidance public -> public :=
  fun report =>
    ay_phase_conj_right guidance public report

theorem ay_phase_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    AyPhaseNoClaimEntry diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_phase_conj_intro fallbackPublic diagnostic
      fallbackH diagnosticH

theorem ay_phase_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyPhaseNoClaimEntry diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_phase_conj_left fallbackPublic diagnostic noClaim

theorem ay_phase_mismatch_diagnostic
    (seedMismatch : Prop) (digestMismatch : Prop)
    (phaseMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    fallbackPublic ->
    seedMismatch ->
    digestMismatch ->
    phaseMismatch ->
    guardMismatch ->
    AyPhaseNoClaimEntry
      (AyPhaseConj
        (AyPhaseConj seedMismatch digestMismatch)
        (AyPhaseConj phaseMismatch guardMismatch))
      fallbackPublic :=
  fun fallbackH seedH digestH phaseH guardH =>
    ay_phase_no_claim_intro
      (AyPhaseConj
        (AyPhaseConj seedMismatch digestMismatch)
        (AyPhaseConj phaseMismatch guardMismatch))
      fallbackPublic
      fallbackH
      (ay_phase_conj_intro
        (AyPhaseConj seedMismatch digestMismatch)
        (AyPhaseConj phaseMismatch guardMismatch)
        (ay_phase_conj_intro seedMismatch digestMismatch seedH digestH)
        (ay_phase_conj_intro phaseMismatch guardMismatch phaseH guardH))

theorem ay_phase_saving_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPhaseEquisat original preprocessed ->
    assumption ->
    AyPhaseAcceptedRun
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    AyPhaseState original base ->
    AyPhaseAcceptedReport
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhasePublicReport
        (AyPhaseOutcome model conflict)
        (AyPhaseScope base assumption)) :=
  fun preprocess assumptionH run sat state =>
    ay_phase_accepted_report_intro
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhasePublicReport
        (AyPhaseOutcome model conflict)
        (AyPhaseScope base assumption))
      (ay_phase_accepted_run_trace
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
        learnedClause checker run)
      (ay_phase_public_sat_report original preprocessed base assumption
        model conflict preprocess assumptionH sat state)

theorem ay_phase_saving_guides_unsat
    (base : Prop) (assumption : Prop)
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPhaseAcceptedRun
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
      learnedClause checker ->
    (learnedClause -> conflict) ->
    AyPhaseAcceptedReport
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhasePublicReport
        (AyPhaseOutcome model conflict)
        (AyPhaseScope base assumption)) :=
  fun run learnedToConflict =>
    ay_phase_accepted_report_intro
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhasePublicReport
        (AyPhaseOutcome model conflict)
        (AyPhaseScope base assumption))
      (ay_phase_accepted_run_trace
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
        learnedClause checker run)
      (ay_phase_public_unsat_report base assumption seed digest savedPhase
        branchDecision guard learnedClause checker model conflict
        run learnedToConflict)

theorem ay_phase_saving_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (seed : Prop) (digest : Prop) (savedPhase : Prop)
    (branchDecision : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPhaseEquisat original preprocessed ->
    assumption ->
    AyPhaseAcceptedRun
      (AyPhaseTrace seed digest savedPhase branchDecision)
      (AyPhaseGuardAgreement guard (AyPhaseScope base assumption))
      learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyPhaseState original base ->
    AyPhaseConj
      (AyPhaseAcceptedReport
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhasePublicReport
          (AyPhaseOutcome model conflict)
          (AyPhaseScope base assumption)))
      (AyPhaseAcceptedReport
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhasePublicReport
          (AyPhaseOutcome model conflict)
          (AyPhaseScope base assumption))) :=
  fun preprocess assumptionH run sat learnedToConflict state =>
    ay_phase_conj_intro
      (AyPhaseAcceptedReport
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhasePublicReport
          (AyPhaseOutcome model conflict)
          (AyPhaseScope base assumption)))
      (AyPhaseAcceptedReport
        (AyPhaseTrace seed digest savedPhase branchDecision)
        (AyPhasePublicReport
          (AyPhaseOutcome model conflict)
          (AyPhaseScope base assumption)))
      (ay_phase_saving_guides_sat original preprocessed base assumption
        seed digest savedPhase branchDecision guard learnedClause checker
        model conflict preprocess assumptionH run sat state)
      (ay_phase_saving_guides_unsat base assumption seed digest savedPhase
        branchDecision guard learnedClause checker model conflict
        run learnedToConflict)

theorem ay_phase_mismatch_preserves_fallback_soundness
    (seedMismatch : Prop) (digestMismatch : Prop)
    (phaseMismatch : Prop) (guardMismatch : Prop)
    (fallbackPublic : Prop) :
    AyPhaseNoClaimEntry
      (AyPhaseConj
        (AyPhaseConj seedMismatch digestMismatch)
        (AyPhaseConj phaseMismatch guardMismatch))
      fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_phase_no_claim_preserves_fallback
      (AyPhaseConj
        (AyPhaseConj seedMismatch digestMismatch)
        (AyPhaseConj phaseMismatch guardMismatch))
      fallbackPublic
      noClaim
