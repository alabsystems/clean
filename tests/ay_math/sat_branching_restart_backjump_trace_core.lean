-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart/backjump trace replay soundness skeleton for ay SAT
-- solving. Replaying a trace containing restarts and non-chronological
-- backjumps is admissible only when each restart reset, learned clause,
-- backjump target, trail prefix, and checker replay agree. Trace gaps or
-- invalid targets fall back to no-claim/recompute.

def AyBRBTConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBRBTDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBRBTEquisat (before : Prop) (after : Prop) :=
  AyBRBTConj (before -> after) (after -> before)

def AyBRBTTraceStep
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :=
  AyBRBTConj restartReset
    (AyBRBTConj learnedClause
      (AyBRBTConj backjumpTarget
        (AyBRBTConj trailPrefix checkerReplay)))

def AyBRBTTraceReplay
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop) :=
  AyBRBTConj firstStep (AyBRBTConj secondStep traceDigest)

def AyBRBTAgreement
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :=
  AyBRBTConj restartMatch
    (AyBRBTConj learnedMatch
      (AyBRBTConj targetMatch
        (AyBRBTConj trailMatch checkerMatch)))

def AyBRBTAcceptedReplay
    (trace : Prop) (agreement : Prop) (completeReplay : Prop) :=
  AyBRBTConj trace (AyBRBTConj agreement completeReplay)

def AyBRBTOutcome (model : Prop) (conflict : Prop) :=
  AyBRBTDisj model conflict

def AyBRBTPublicReport (outcome : Prop) (formula : Prop) :=
  AyBRBTConj outcome formula

def AyBRBTAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBRBTConj evidence public

def AyBRBTNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBRBTConj fallbackPublic diagnostic

theorem ay_brbt_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBRBTConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brbt_conj_left
    (left : Prop) (right : Prop) :
    AyBRBTConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brbt_conj_right
    (left : Prop) (right : Prop) :
    AyBRBTConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brbt_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBRBTDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brbt_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBRBTDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brbt_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBRBTEquisat before after :=
  fun forward backward =>
    ay_brbt_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brbt_equisat_forward
    (before : Prop) (after : Prop) :
    AyBRBTEquisat before after -> before -> after :=
  fun equisat =>
    ay_brbt_conj_left (before -> after) (after -> before) equisat

theorem ay_brbt_equisat_backward
    (before : Prop) (after : Prop) :
    AyBRBTEquisat before after -> after -> before :=
  fun equisat =>
    ay_brbt_conj_right (before -> after) (after -> before) equisat

theorem ay_brbt_trace_step_intro
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    restartReset ->
    learnedClause ->
    backjumpTarget ->
    trailPrefix ->
    checkerReplay ->
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay :=
  fun restartH learnedH targetH trailH checkerH =>
    ay_brbt_conj_intro restartReset
      (AyBRBTConj learnedClause
        (AyBRBTConj backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay)))
      restartH
      (ay_brbt_conj_intro learnedClause
        (AyBRBTConj backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay))
        learnedH
        (ay_brbt_conj_intro backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay)
          targetH
          (ay_brbt_conj_intro trailPrefix checkerReplay
            trailH checkerH)))

theorem ay_brbt_trace_step_restart
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    restartReset :=
  fun step =>
    ay_brbt_conj_left restartReset
      (AyBRBTConj learnedClause
        (AyBRBTConj backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay)))
      step

theorem ay_brbt_trace_step_tail
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    AyBRBTConj learnedClause
      (AyBRBTConj backjumpTarget
        (AyBRBTConj trailPrefix checkerReplay)) :=
  fun step =>
    ay_brbt_conj_right restartReset
      (AyBRBTConj learnedClause
        (AyBRBTConj backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay)))
      step

theorem ay_brbt_trace_step_learned
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    learnedClause :=
  fun step =>
    ay_brbt_conj_left learnedClause
      (AyBRBTConj backjumpTarget
        (AyBRBTConj trailPrefix checkerReplay))
      (ay_brbt_trace_step_tail restartReset learnedClause
        backjumpTarget trailPrefix checkerReplay step)

theorem ay_brbt_trace_step_target
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    backjumpTarget :=
  fun step =>
    ay_brbt_conj_left backjumpTarget
      (AyBRBTConj trailPrefix checkerReplay)
      (ay_brbt_conj_right learnedClause
        (AyBRBTConj backjumpTarget
          (AyBRBTConj trailPrefix checkerReplay))
        (ay_brbt_trace_step_tail restartReset learnedClause
          backjumpTarget trailPrefix checkerReplay step))

theorem ay_brbt_trace_step_trail
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    trailPrefix :=
  fun step =>
    ay_brbt_conj_left trailPrefix checkerReplay
      (ay_brbt_conj_right backjumpTarget
        (AyBRBTConj trailPrefix checkerReplay)
        (ay_brbt_conj_right learnedClause
          (AyBRBTConj backjumpTarget
            (AyBRBTConj trailPrefix checkerReplay))
          (ay_brbt_trace_step_tail restartReset learnedClause
            backjumpTarget trailPrefix checkerReplay step)))

theorem ay_brbt_trace_step_checker
    (restartReset : Prop) (learnedClause : Prop)
    (backjumpTarget : Prop) (trailPrefix : Prop)
    (checkerReplay : Prop) :
    AyBRBTTraceStep restartReset learnedClause backjumpTarget
      trailPrefix checkerReplay ->
    checkerReplay :=
  fun step =>
    ay_brbt_conj_right trailPrefix checkerReplay
      (ay_brbt_conj_right backjumpTarget
        (AyBRBTConj trailPrefix checkerReplay)
        (ay_brbt_conj_right learnedClause
          (AyBRBTConj backjumpTarget
            (AyBRBTConj trailPrefix checkerReplay))
          (ay_brbt_trace_step_tail restartReset learnedClause
            backjumpTarget trailPrefix checkerReplay step)))

theorem ay_brbt_trace_replay_intro
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop) :
    firstStep ->
    secondStep ->
    traceDigest ->
    AyBRBTTraceReplay firstStep secondStep traceDigest :=
  fun firstH secondH digestH =>
    ay_brbt_conj_intro firstStep (AyBRBTConj secondStep traceDigest)
      firstH
      (ay_brbt_conj_intro secondStep traceDigest secondH digestH)

theorem ay_brbt_trace_replay_first
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop) :
    AyBRBTTraceReplay firstStep secondStep traceDigest -> firstStep :=
  fun trace =>
    ay_brbt_conj_left firstStep
      (AyBRBTConj secondStep traceDigest)
      trace

theorem ay_brbt_trace_replay_second
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop) :
    AyBRBTTraceReplay firstStep secondStep traceDigest -> secondStep :=
  fun trace =>
    ay_brbt_conj_left secondStep traceDigest
      (ay_brbt_conj_right firstStep
        (AyBRBTConj secondStep traceDigest)
        trace)

theorem ay_brbt_trace_replay_digest
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop) :
    AyBRBTTraceReplay firstStep secondStep traceDigest -> traceDigest :=
  fun trace =>
    ay_brbt_conj_right secondStep traceDigest
      (ay_brbt_conj_right firstStep
        (AyBRBTConj secondStep traceDigest)
        trace)

theorem ay_brbt_agreement_intro
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    restartMatch ->
    learnedMatch ->
    targetMatch ->
    trailMatch ->
    checkerMatch ->
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch :=
  fun restartH learnedH targetH trailH checkerH =>
    ay_brbt_conj_intro restartMatch
      (AyBRBTConj learnedMatch
        (AyBRBTConj targetMatch
          (AyBRBTConj trailMatch checkerMatch)))
      restartH
      (ay_brbt_conj_intro learnedMatch
        (AyBRBTConj targetMatch
          (AyBRBTConj trailMatch checkerMatch))
        learnedH
        (ay_brbt_conj_intro targetMatch
          (AyBRBTConj trailMatch checkerMatch)
          targetH
          (ay_brbt_conj_intro trailMatch checkerMatch
            trailH checkerH)))

theorem ay_brbt_agreement_restart
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    restartMatch :=
  fun agreement =>
    ay_brbt_conj_left restartMatch
      (AyBRBTConj learnedMatch
        (AyBRBTConj targetMatch
          (AyBRBTConj trailMatch checkerMatch)))
      agreement

theorem ay_brbt_agreement_tail
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    AyBRBTConj learnedMatch
      (AyBRBTConj targetMatch
        (AyBRBTConj trailMatch checkerMatch)) :=
  fun agreement =>
    ay_brbt_conj_right restartMatch
      (AyBRBTConj learnedMatch
        (AyBRBTConj targetMatch
          (AyBRBTConj trailMatch checkerMatch)))
      agreement

theorem ay_brbt_agreement_learned
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    learnedMatch :=
  fun agreement =>
    ay_brbt_conj_left learnedMatch
      (AyBRBTConj targetMatch
        (AyBRBTConj trailMatch checkerMatch))
      (ay_brbt_agreement_tail restartMatch learnedMatch targetMatch
        trailMatch checkerMatch agreement)

theorem ay_brbt_agreement_target
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    targetMatch :=
  fun agreement =>
    ay_brbt_conj_left targetMatch
      (AyBRBTConj trailMatch checkerMatch)
      (ay_brbt_conj_right learnedMatch
        (AyBRBTConj targetMatch
          (AyBRBTConj trailMatch checkerMatch))
        (ay_brbt_agreement_tail restartMatch learnedMatch targetMatch
          trailMatch checkerMatch agreement))

theorem ay_brbt_agreement_trail
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    trailMatch :=
  fun agreement =>
    ay_brbt_conj_left trailMatch checkerMatch
      (ay_brbt_conj_right targetMatch
        (AyBRBTConj trailMatch checkerMatch)
        (ay_brbt_conj_right learnedMatch
          (AyBRBTConj targetMatch
            (AyBRBTConj trailMatch checkerMatch))
          (ay_brbt_agreement_tail restartMatch learnedMatch targetMatch
            trailMatch checkerMatch agreement)))

theorem ay_brbt_agreement_checker
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) :
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_brbt_conj_right trailMatch checkerMatch
      (ay_brbt_conj_right targetMatch
        (AyBRBTConj trailMatch checkerMatch)
        (ay_brbt_conj_right learnedMatch
          (AyBRBTConj targetMatch
            (AyBRBTConj trailMatch checkerMatch))
          (ay_brbt_agreement_tail restartMatch learnedMatch targetMatch
            trailMatch checkerMatch agreement)))

theorem ay_brbt_accepted_replay_intro
    (trace : Prop) (agreement : Prop) (completeReplay : Prop) :
    trace ->
    agreement ->
    completeReplay ->
    AyBRBTAcceptedReplay trace agreement completeReplay :=
  fun traceH agreementH completeH =>
    ay_brbt_conj_intro trace (AyBRBTConj agreement completeReplay)
      traceH
      (ay_brbt_conj_intro agreement completeReplay
        agreementH completeH)

theorem ay_brbt_accepted_replay_trace
    (trace : Prop) (agreement : Prop) (completeReplay : Prop) :
    AyBRBTAcceptedReplay trace agreement completeReplay -> trace :=
  fun accepted =>
    ay_brbt_conj_left trace (AyBRBTConj agreement completeReplay)
      accepted

theorem ay_brbt_accepted_replay_agreement
    (trace : Prop) (agreement : Prop) (completeReplay : Prop) :
    AyBRBTAcceptedReplay trace agreement completeReplay -> agreement :=
  fun accepted =>
    ay_brbt_conj_left agreement completeReplay
      (ay_brbt_conj_right trace
        (AyBRBTConj agreement completeReplay)
        accepted)

theorem ay_brbt_accepted_replay_complete
    (trace : Prop) (agreement : Prop) (completeReplay : Prop) :
    AyBRBTAcceptedReplay trace agreement completeReplay ->
    completeReplay :=
  fun accepted =>
    ay_brbt_conj_right agreement completeReplay
      (ay_brbt_conj_right trace
        (AyBRBTConj agreement completeReplay)
        accepted)

theorem ay_brbt_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBRBTPublicReport (AyBRBTOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brbt_conj_intro (AyBRBTOutcome model conflict) formula
      (ay_brbt_disj_left model conflict modelH)
      formulaH

theorem ay_brbt_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBRBTPublicReport (AyBRBTOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brbt_conj_intro (AyBRBTOutcome model conflict) formula
      (ay_brbt_disj_right model conflict conflictH)
      formulaH

theorem ay_brbt_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBRBTAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_brbt_conj_intro evidence public evidenceH publicH

theorem ay_brbt_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBRBTAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_brbt_conj_left evidence public report

theorem ay_brbt_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBRBTAcceptedReport evidence public -> public :=
  fun report =>
    ay_brbt_conj_right evidence public report

theorem ay_brbt_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBRBTNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbt_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brbt_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRBTNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brbt_conj_left fallbackPublic diagnostic noClaim

theorem ay_brbt_trace_gap_no_claim
    (traceGap : Prop) (fallbackPublic : Prop) :
    traceGap ->
    fallbackPublic ->
    AyBRBTNoClaim traceGap fallbackPublic :=
  fun gapH fallbackH =>
    ay_brbt_no_claim_intro traceGap fallbackPublic gapH fallbackH

theorem ay_brbt_invalid_target_no_claim
    (invalidTarget : Prop) (fallbackPublic : Prop) :
    invalidTarget ->
    fallbackPublic ->
    AyBRBTNoClaim invalidTarget fallbackPublic :=
  fun invalidH fallbackH =>
    ay_brbt_no_claim_intro invalidTarget fallbackPublic
      invalidH fallbackH

theorem ay_brbt_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    AyBRBTNoClaim replayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_brbt_no_claim_intro replayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_brbt_invalid_target_cannot_justify_replay
    (invalidTarget : Prop) (fallbackPublic : Prop) :
    invalidTarget ->
    fallbackPublic ->
    AyBRBTNoClaim invalidTarget fallbackPublic :=
  fun invalidH fallbackH =>
    ay_brbt_invalid_target_no_claim invalidTarget fallbackPublic
      invalidH fallbackH

theorem ay_brbt_accepted_trace_guides_sat
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop)
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (completeReplay : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBRBTTraceReplay firstStep secondStep traceDigest ->
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    completeReplay ->
    model ->
    formula ->
    AyBRBTAcceptedReport
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula) :=
  fun trace agreement completeH modelH formulaH =>
    ay_brbt_accepted_report_intro
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula)
      (ay_brbt_accepted_replay_intro
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay
        trace agreement completeH)
      (ay_brbt_public_sat_report model conflict formula modelH formulaH)

theorem ay_brbt_accepted_trace_guides_unsat
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop)
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (completeReplay : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBRBTTraceReplay firstStep secondStep traceDigest ->
    AyBRBTAgreement restartMatch learnedMatch targetMatch
      trailMatch checkerMatch ->
    completeReplay ->
    conflict ->
    formula ->
    AyBRBTAcceptedReport
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula) :=
  fun trace agreement completeH conflictH formulaH =>
    ay_brbt_accepted_report_intro
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula)
      (ay_brbt_accepted_replay_intro
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay
        trace agreement completeH)
      (ay_brbt_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_brbt_accepted_trace_report_soundness
    (firstStep : Prop) (secondStep : Prop) (traceDigest : Prop)
    (restartMatch : Prop) (learnedMatch : Prop)
    (targetMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (completeReplay : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBRBTAcceptedReport
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula) ->
    AyBRBTPublicReport (AyBRBTOutcome model conflict) formula :=
  fun report =>
    ay_brbt_accepted_report_public
      (AyBRBTAcceptedReplay
        (AyBRBTTraceReplay firstStep secondStep traceDigest)
        (AyBRBTAgreement restartMatch learnedMatch targetMatch
          trailMatch checkerMatch)
        completeReplay)
      (AyBRBTPublicReport (AyBRBTOutcome model conflict) formula)
      report

theorem ay_brbt_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBRBTNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brbt_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
