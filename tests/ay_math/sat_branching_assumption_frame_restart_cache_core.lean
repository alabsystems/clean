-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked assumption-frame restart trace-cache soundness skeleton for
-- sequential CDCL. Cached restart/backtrack traces may guide replay only when
-- the assumption frame, restart epoch, trace digest, and learned-state guard
-- match. Mismatches produce diagnostic no-claim entries preserving fallback
-- public soundness.

def AyCacheConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCacheDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCacheEquisat (before : Prop) (after : Prop) :=
  AyCacheConj (before -> after) (after -> before)

def AyCacheAssumptionFrame (base : Prop) (assumption : Prop) :=
  AyCacheConj base assumption

def AyCacheState (formula : Prop) (frame : Prop) :=
  AyCacheConj formula frame

def AyCacheTrace
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :=
  AyCacheConj assumptionFrame
    (AyCacheConj restartEpoch
      (AyCacheConj backtrackTarget
        (AyCacheConj learnedState
          (AyCacheConj traceDigest branchDecision))))

def AyCachedRestartTrace
    (cachedFrame : Prop) (cachedEpoch : Prop) (cachedTrace : Prop) :=
  AyCacheConj cachedFrame (AyCacheConj cachedEpoch cachedTrace)

def AyCacheReplayAgreement
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :=
  AyCacheConj frameMatch
    (AyCacheConj epochMatch (AyCacheConj traceMatch guardMatch))

def AyCacheAcceptedRun
    (cache : Prop) (agreement : Prop)
    (replay : Prop) (checker : Prop) :=
  AyCacheConj cache
    (AyCacheConj agreement (AyCacheConj replay checker))

def AyCacheOutcome (model : Prop) (conflict : Prop) :=
  AyCacheDisj model conflict

def AyCachePublicReport (outcome : Prop) (assumptionFrame : Prop) :=
  AyCacheConj outcome assumptionFrame

def AyCacheAcceptedReport (guidance : Prop) (public : Prop) :=
  AyCacheConj guidance public

def AyCacheNoClaimDiagnostic (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyCacheConj fallbackPublic diagnostic

theorem ay_cache_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCacheConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_cache_conj_left
    (left : Prop) (right : Prop) :
    AyCacheConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_cache_conj_right
    (left : Prop) (right : Prop) :
    AyCacheConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_cache_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCacheDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_cache_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCacheDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_cache_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCacheEquisat before after :=
  fun forward backward =>
    ay_cache_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_cache_equisat_forward
    (before : Prop) (after : Prop) :
    AyCacheEquisat before after -> before -> after :=
  fun equisat =>
    ay_cache_conj_left (before -> after) (after -> before) equisat

theorem ay_cache_equisat_backward
    (before : Prop) (after : Prop) :
    AyCacheEquisat before after -> after -> before :=
  fun equisat =>
    ay_cache_conj_right (before -> after) (after -> before) equisat

theorem ay_cache_assumption_frame_intro
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyCacheAssumptionFrame base assumption :=
  fun baseH assumptionH =>
    ay_cache_conj_intro base assumption baseH assumptionH

theorem ay_cache_assumption_frame_base
    (base : Prop) (assumption : Prop) :
    AyCacheAssumptionFrame base assumption -> base :=
  fun frame =>
    ay_cache_conj_left base assumption frame

theorem ay_cache_assumption_frame_value
    (base : Prop) (assumption : Prop) :
    AyCacheAssumptionFrame base assumption -> assumption :=
  fun frame =>
    ay_cache_conj_right base assumption frame

theorem ay_cache_state_under_assumption
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyCacheState formula base ->
    assumption ->
    AyCacheState formula (AyCacheAssumptionFrame base assumption) :=
  fun state assumptionH =>
    ay_cache_conj_intro formula (AyCacheAssumptionFrame base assumption)
      (ay_cache_conj_left formula base state)
      (ay_cache_assumption_frame_intro base assumption
        (ay_cache_conj_right formula base state)
        assumptionH)

theorem ay_cache_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyCacheEquisat original preprocessed ->
    AyCacheState original frame ->
    AyCacheState preprocessed frame :=
  fun preprocess state =>
    ay_cache_conj_intro preprocessed frame
      (ay_cache_equisat_forward original preprocessed preprocess
        (ay_cache_conj_left original frame state))
      (ay_cache_conj_right original frame state)

theorem ay_cache_trace_intro
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    assumptionFrame ->
    restartEpoch ->
    backtrackTarget ->
    learnedState ->
    traceDigest ->
    branchDecision ->
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision :=
  fun frameH epochH targetH learnedH digestH branchH =>
    ay_cache_conj_intro assumptionFrame
      (AyCacheConj restartEpoch
        (AyCacheConj backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))))
      frameH
      (ay_cache_conj_intro restartEpoch
        (AyCacheConj backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision)))
        epochH
        (ay_cache_conj_intro backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))
          targetH
          (ay_cache_conj_intro learnedState
            (AyCacheConj traceDigest branchDecision)
            learnedH
            (ay_cache_conj_intro traceDigest branchDecision
              digestH branchH))))

theorem ay_cache_trace_frame
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    assumptionFrame :=
  fun trace =>
    ay_cache_conj_left assumptionFrame
      (AyCacheConj restartEpoch
        (AyCacheConj backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))))
      trace

theorem ay_cache_trace_tail
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    AyCacheConj restartEpoch
      (AyCacheConj backtrackTarget
        (AyCacheConj learnedState
          (AyCacheConj traceDigest branchDecision))) :=
  fun trace =>
    ay_cache_conj_right assumptionFrame
      (AyCacheConj restartEpoch
        (AyCacheConj backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))))
      trace

theorem ay_cache_trace_epoch
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    restartEpoch :=
  fun trace =>
    ay_cache_conj_left restartEpoch
      (AyCacheConj backtrackTarget
        (AyCacheConj learnedState
          (AyCacheConj traceDigest branchDecision)))
      (ay_cache_trace_tail assumptionFrame restartEpoch backtrackTarget
        learnedState traceDigest branchDecision trace)

theorem ay_cache_trace_backtrack_target
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    backtrackTarget :=
  fun trace =>
    ay_cache_conj_left backtrackTarget
      (AyCacheConj learnedState
        (AyCacheConj traceDigest branchDecision))
      (ay_cache_conj_right restartEpoch
        (AyCacheConj backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision)))
        (ay_cache_trace_tail assumptionFrame restartEpoch backtrackTarget
          learnedState traceDigest branchDecision trace))

theorem ay_cache_trace_learned_state
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    learnedState :=
  fun trace =>
    ay_cache_conj_left learnedState
      (AyCacheConj traceDigest branchDecision)
      (ay_cache_conj_right backtrackTarget
        (AyCacheConj learnedState
          (AyCacheConj traceDigest branchDecision))
        (ay_cache_conj_right restartEpoch
          (AyCacheConj backtrackTarget
            (AyCacheConj learnedState
              (AyCacheConj traceDigest branchDecision)))
          (ay_cache_trace_tail assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision trace)))

theorem ay_cache_trace_digest
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    traceDigest :=
  fun trace =>
    ay_cache_conj_left traceDigest branchDecision
      (ay_cache_conj_right learnedState
        (AyCacheConj traceDigest branchDecision)
        (ay_cache_conj_right backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))
          (ay_cache_conj_right restartEpoch
            (AyCacheConj backtrackTarget
              (AyCacheConj learnedState
                (AyCacheConj traceDigest branchDecision)))
            (ay_cache_trace_tail assumptionFrame restartEpoch
              backtrackTarget learnedState traceDigest branchDecision
              trace))))

theorem ay_cache_trace_branch_decision
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop) :
    AyCacheTrace assumptionFrame restartEpoch backtrackTarget
      learnedState traceDigest branchDecision ->
    branchDecision :=
  fun trace =>
    ay_cache_conj_right traceDigest branchDecision
      (ay_cache_conj_right learnedState
        (AyCacheConj traceDigest branchDecision)
        (ay_cache_conj_right backtrackTarget
          (AyCacheConj learnedState
            (AyCacheConj traceDigest branchDecision))
          (ay_cache_conj_right restartEpoch
            (AyCacheConj backtrackTarget
              (AyCacheConj learnedState
                (AyCacheConj traceDigest branchDecision)))
            (ay_cache_trace_tail assumptionFrame restartEpoch
              backtrackTarget learnedState traceDigest branchDecision
              trace))))

theorem ay_cache_restart_trace_intro
    (cachedFrame : Prop) (cachedEpoch : Prop) (cachedTrace : Prop) :
    cachedFrame ->
    cachedEpoch ->
    cachedTrace ->
    AyCachedRestartTrace cachedFrame cachedEpoch cachedTrace :=
  fun frameH epochH traceH =>
    ay_cache_conj_intro cachedFrame
      (AyCacheConj cachedEpoch cachedTrace)
      frameH
      (ay_cache_conj_intro cachedEpoch cachedTrace epochH traceH)

theorem ay_cache_restart_trace_frame
    (cachedFrame : Prop) (cachedEpoch : Prop) (cachedTrace : Prop) :
    AyCachedRestartTrace cachedFrame cachedEpoch cachedTrace ->
    cachedFrame :=
  fun cache =>
    ay_cache_conj_left cachedFrame
      (AyCacheConj cachedEpoch cachedTrace)
      cache

theorem ay_cache_restart_trace_epoch
    (cachedFrame : Prop) (cachedEpoch : Prop) (cachedTrace : Prop) :
    AyCachedRestartTrace cachedFrame cachedEpoch cachedTrace ->
    cachedEpoch :=
  fun cache =>
    ay_cache_conj_left cachedEpoch cachedTrace
      (ay_cache_conj_right cachedFrame
        (AyCacheConj cachedEpoch cachedTrace)
        cache)

theorem ay_cache_restart_trace_payload
    (cachedFrame : Prop) (cachedEpoch : Prop) (cachedTrace : Prop) :
    AyCachedRestartTrace cachedFrame cachedEpoch cachedTrace ->
    cachedTrace :=
  fun cache =>
    ay_cache_conj_right cachedEpoch cachedTrace
      (ay_cache_conj_right cachedFrame
        (AyCacheConj cachedEpoch cachedTrace)
        cache)

theorem ay_cache_replay_agreement_intro
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :
    frameMatch ->
    epochMatch ->
    traceMatch ->
    guardMatch ->
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch :=
  fun frameH epochH traceH guardH =>
    ay_cache_conj_intro frameMatch
      (AyCacheConj epochMatch (AyCacheConj traceMatch guardMatch))
      frameH
      (ay_cache_conj_intro epochMatch
        (AyCacheConj traceMatch guardMatch)
        epochH
        (ay_cache_conj_intro traceMatch guardMatch traceH guardH))

theorem ay_cache_replay_frame_match
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    frameMatch :=
  fun agreement =>
    ay_cache_conj_left frameMatch
      (AyCacheConj epochMatch (AyCacheConj traceMatch guardMatch))
      agreement

theorem ay_cache_replay_epoch_match
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    epochMatch :=
  fun agreement =>
    ay_cache_conj_left epochMatch (AyCacheConj traceMatch guardMatch)
      (ay_cache_conj_right frameMatch
        (AyCacheConj epochMatch (AyCacheConj traceMatch guardMatch))
        agreement)

theorem ay_cache_replay_trace_match
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    traceMatch :=
  fun agreement =>
    ay_cache_conj_left traceMatch guardMatch
      (ay_cache_conj_right epochMatch
        (AyCacheConj traceMatch guardMatch)
        (ay_cache_conj_right frameMatch
          (AyCacheConj epochMatch
            (AyCacheConj traceMatch guardMatch))
          agreement))

theorem ay_cache_replay_guard_match
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop) :
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    guardMatch :=
  fun agreement =>
    ay_cache_conj_right traceMatch guardMatch
      (ay_cache_conj_right epochMatch
        (AyCacheConj traceMatch guardMatch)
        (ay_cache_conj_right frameMatch
          (AyCacheConj epochMatch
            (AyCacheConj traceMatch guardMatch))
          agreement))

theorem ay_cache_accepted_run_intro
    (cache : Prop) (agreement : Prop) (replay : Prop) (checker : Prop) :
    cache ->
    agreement ->
    replay ->
    checker ->
    AyCacheAcceptedRun cache agreement replay checker :=
  fun cacheH agreementH replayH checkerH =>
    ay_cache_conj_intro cache
      (AyCacheConj agreement (AyCacheConj replay checker))
      cacheH
      (ay_cache_conj_intro agreement
        (AyCacheConj replay checker)
        agreementH
        (ay_cache_conj_intro replay checker replayH checkerH))

theorem ay_cache_accepted_run_cache
    (cache : Prop) (agreement : Prop) (replay : Prop) (checker : Prop) :
    AyCacheAcceptedRun cache agreement replay checker -> cache :=
  fun accepted =>
    ay_cache_conj_left cache
      (AyCacheConj agreement (AyCacheConj replay checker))
      accepted

theorem ay_cache_accepted_run_agreement
    (cache : Prop) (agreement : Prop) (replay : Prop) (checker : Prop) :
    AyCacheAcceptedRun cache agreement replay checker -> agreement :=
  fun accepted =>
    ay_cache_conj_left agreement (AyCacheConj replay checker)
      (ay_cache_conj_right cache
        (AyCacheConj agreement (AyCacheConj replay checker))
        accepted)

theorem ay_cache_accepted_run_replay
    (cache : Prop) (agreement : Prop) (replay : Prop) (checker : Prop) :
    AyCacheAcceptedRun cache agreement replay checker -> replay :=
  fun accepted =>
    ay_cache_conj_left replay checker
      (ay_cache_conj_right agreement
        (AyCacheConj replay checker)
        (ay_cache_conj_right cache
          (AyCacheConj agreement (AyCacheConj replay checker))
          accepted))

theorem ay_cache_accepted_run_checker
    (cache : Prop) (agreement : Prop) (replay : Prop) (checker : Prop) :
    AyCacheAcceptedRun cache agreement replay checker -> checker :=
  fun accepted =>
    ay_cache_conj_right replay checker
      (ay_cache_conj_right agreement
        (AyCacheConj replay checker)
        (ay_cache_conj_right cache
          (AyCacheConj agreement (AyCacheConj replay checker))
          accepted))

theorem ay_cache_public_sat_report
    (model : Prop) (conflict : Prop) (assumptionFrame : Prop) :
    model ->
    assumptionFrame ->
    AyCachePublicReport (AyCacheOutcome model conflict)
      assumptionFrame :=
  fun modelH frameH =>
    ay_cache_conj_intro (AyCacheOutcome model conflict) assumptionFrame
      (ay_cache_disj_left model conflict modelH)
      frameH

theorem ay_cache_public_unsat_report
    (model : Prop) (conflict : Prop) (assumptionFrame : Prop) :
    conflict ->
    assumptionFrame ->
    AyCachePublicReport (AyCacheOutcome model conflict)
      assumptionFrame :=
  fun conflictH frameH =>
    ay_cache_conj_intro (AyCacheOutcome model conflict) assumptionFrame
      (ay_cache_disj_right model conflict conflictH)
      frameH

theorem ay_cache_accepted_report_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyCacheAcceptedReport guidance public :=
  fun guidanceH publicH =>
    ay_cache_conj_intro guidance public guidanceH publicH

theorem ay_cache_accepted_report_guidance
    (guidance : Prop) (public : Prop) :
    AyCacheAcceptedReport guidance public -> guidance :=
  fun report =>
    ay_cache_conj_left guidance public report

theorem ay_cache_accepted_report_public
    (guidance : Prop) (public : Prop) :
    AyCacheAcceptedReport guidance public -> public :=
  fun report =>
    ay_cache_conj_right guidance public report

theorem ay_cache_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyCacheNoClaimDiagnostic diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_cache_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_cache_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyCacheNoClaimDiagnostic diagnostic fallbackPublic -> fallbackPublic :=
  fun entry =>
    ay_cache_conj_left fallbackPublic diagnostic entry

theorem ay_cache_frame_mismatch_diagnostic
    (frameMismatch : Prop) (fallbackPublic : Prop) :
    frameMismatch ->
    fallbackPublic ->
    AyCacheNoClaimDiagnostic frameMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_cache_no_claim_intro frameMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_cache_epoch_mismatch_diagnostic
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    AyCacheNoClaimDiagnostic epochMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_cache_no_claim_intro epochMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_cache_trace_mismatch_diagnostic
    (traceMismatch : Prop) (fallbackPublic : Prop) :
    traceMismatch ->
    fallbackPublic ->
    AyCacheNoClaimDiagnostic traceMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_cache_no_claim_intro traceMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_cache_matching_trace_guides_sat
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop)
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop)
    (replay : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyCachedRestartTrace assumptionFrame restartEpoch
      (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
        learnedState traceDigest branchDecision) ->
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    replay ->
    checker ->
    model ->
    AyCacheAcceptedReport
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame) :=
  fun cache agreement replayH checkerH modelH =>
    ay_cache_accepted_report_intro
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame)
      (ay_cache_accepted_run_intro
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker
        cache agreement replayH checkerH)
      (ay_cache_public_sat_report model conflict assumptionFrame modelH
        (ay_cache_restart_trace_frame assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision)
          cache))

theorem ay_cache_matching_trace_guides_unsat
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop)
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop)
    (replay : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyCachedRestartTrace assumptionFrame restartEpoch
      (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
        learnedState traceDigest branchDecision) ->
    AyCacheReplayAgreement frameMatch epochMatch traceMatch guardMatch ->
    replay ->
    checker ->
    conflict ->
    AyCacheAcceptedReport
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame) :=
  fun cache agreement replayH checkerH conflictH =>
    ay_cache_accepted_report_intro
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame)
      (ay_cache_accepted_run_intro
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker
        cache agreement replayH checkerH)
      (ay_cache_public_unsat_report model conflict assumptionFrame
        conflictH
        (ay_cache_restart_trace_frame assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision)
          cache))

theorem ay_cache_accepted_report_soundness
    (assumptionFrame : Prop) (restartEpoch : Prop)
    (backtrackTarget : Prop) (learnedState : Prop)
    (traceDigest : Prop) (branchDecision : Prop)
    (frameMatch : Prop) (epochMatch : Prop)
    (traceMatch : Prop) (guardMatch : Prop)
    (replay : Prop) (checker : Prop)
    (model : Prop) (conflict : Prop) :
    AyCacheAcceptedReport
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame) ->
    AyCachePublicReport (AyCacheOutcome model conflict)
      assumptionFrame :=
  fun report =>
    ay_cache_accepted_report_public
      (AyCacheAcceptedRun
        (AyCachedRestartTrace assumptionFrame restartEpoch
          (AyCacheTrace assumptionFrame restartEpoch backtrackTarget
            learnedState traceDigest branchDecision))
        (AyCacheReplayAgreement frameMatch epochMatch traceMatch
          guardMatch)
        replay checker)
      (AyCachePublicReport (AyCacheOutcome model conflict)
        assumptionFrame)
      report

theorem ay_cache_mismatch_preserves_fallback_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyCacheNoClaimDiagnostic diagnostic fallbackPublic -> fallbackPublic :=
  fun entry =>
    ay_cache_no_claim_preserves_fallback diagnostic fallbackPublic entry
