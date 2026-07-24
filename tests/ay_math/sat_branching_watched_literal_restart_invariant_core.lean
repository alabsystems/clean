-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded watched-literal restart invariant soundness skeleton for ay SAT
-- solving. Watch state and propagation queues remain admissible across
-- restarts only when watch certificates, clause-database epoch, trail-reset
-- evidence, and checker replay agree. Stale watch state is discarded or
-- recomputed and makes no public semantic claim.

def AyBWLRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBWLRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBWLREquisat (before : Prop) (after : Prop) :=
  AyBWLRConj (before -> after) (after -> before)

def AyBWLRWatchState
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :=
  AyBWLRConj watchCertificate
    (AyBWLRConj clauseEpoch
      (AyBWLRConj propagationQueue trailState))

def AyBWLRestartEvidence
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) :=
  AyBWLRConj trailReset (AyBWLRConj epochPreserved checkerReplay)

def AyBWLRReplayAgreement
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :=
  AyBWLRConj watchMatch
    (AyBWLRConj epochMatch
      (AyBWLRConj trailResetMatch checkerMatch))

def AyBWLRAcceptedRestart
    (watchState : Prop) (restartEvidence : Prop) (agreement : Prop) :=
  AyBWLRConj watchState (AyBWLRConj restartEvidence agreement)

def AyBWLRPropagatedClause
    (queueItem : Prop) (watchJustification : Prop) (checkerReplay : Prop) :=
  AyBWLRConj queueItem (AyBWLRConj watchJustification checkerReplay)

def AyBWLROutcome (model : Prop) (conflict : Prop) :=
  AyBWLRDisj model conflict

def AyBWLRPublicReport (outcome : Prop) (formula : Prop) :=
  AyBWLRConj outcome formula

def AyBWLRAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBWLRConj evidence public

def AyBWLRNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBWLRConj fallbackPublic diagnostic

theorem ay_bwlr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBWLRConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bwlr_conj_left
    (left : Prop) (right : Prop) :
    AyBWLRConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bwlr_conj_right
    (left : Prop) (right : Prop) :
    AyBWLRConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bwlr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBWLRDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bwlr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBWLRDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bwlr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBWLREquisat before after :=
  fun forward backward =>
    ay_bwlr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bwlr_equisat_forward
    (before : Prop) (after : Prop) :
    AyBWLREquisat before after -> before -> after :=
  fun equisat =>
    ay_bwlr_conj_left (before -> after) (after -> before) equisat

theorem ay_bwlr_equisat_backward
    (before : Prop) (after : Prop) :
    AyBWLREquisat before after -> after -> before :=
  fun equisat =>
    ay_bwlr_conj_right (before -> after) (after -> before) equisat

theorem ay_bwlr_watch_state_intro
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    watchCertificate ->
    clauseEpoch ->
    propagationQueue ->
    trailState ->
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState :=
  fun watchH epochH queueH trailH =>
    ay_bwlr_conj_intro watchCertificate
      (AyBWLRConj clauseEpoch
        (AyBWLRConj propagationQueue trailState))
      watchH
      (ay_bwlr_conj_intro clauseEpoch
        (AyBWLRConj propagationQueue trailState)
        epochH
        (ay_bwlr_conj_intro propagationQueue trailState
          queueH trailH))

theorem ay_bwlr_watch_state_certificate
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    watchCertificate :=
  fun state =>
    ay_bwlr_conj_left watchCertificate
      (AyBWLRConj clauseEpoch
        (AyBWLRConj propagationQueue trailState))
      state

theorem ay_bwlr_watch_state_tail
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    AyBWLRConj clauseEpoch
      (AyBWLRConj propagationQueue trailState) :=
  fun state =>
    ay_bwlr_conj_right watchCertificate
      (AyBWLRConj clauseEpoch
        (AyBWLRConj propagationQueue trailState))
      state

theorem ay_bwlr_watch_state_epoch
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    clauseEpoch :=
  fun state =>
    ay_bwlr_conj_left clauseEpoch
      (AyBWLRConj propagationQueue trailState)
      (ay_bwlr_watch_state_tail watchCertificate clauseEpoch
        propagationQueue trailState state)

theorem ay_bwlr_watch_state_queue
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    propagationQueue :=
  fun state =>
    ay_bwlr_conj_left propagationQueue trailState
      (ay_bwlr_conj_right clauseEpoch
        (AyBWLRConj propagationQueue trailState)
        (ay_bwlr_watch_state_tail watchCertificate clauseEpoch
          propagationQueue trailState state))

theorem ay_bwlr_watch_state_trail
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    trailState :=
  fun state =>
    ay_bwlr_conj_right propagationQueue trailState
      (ay_bwlr_conj_right clauseEpoch
        (AyBWLRConj propagationQueue trailState)
        (ay_bwlr_watch_state_tail watchCertificate clauseEpoch
          propagationQueue trailState state))

theorem ay_bwlr_restart_evidence_intro
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) :
    trailReset ->
    epochPreserved ->
    checkerReplay ->
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay :=
  fun trailH epochH checkerH =>
    ay_bwlr_conj_intro trailReset
      (AyBWLRConj epochPreserved checkerReplay)
      trailH
      (ay_bwlr_conj_intro epochPreserved checkerReplay epochH checkerH)

theorem ay_bwlr_restart_evidence_trail_reset
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) :
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay ->
    trailReset :=
  fun evidence =>
    ay_bwlr_conj_left trailReset
      (AyBWLRConj epochPreserved checkerReplay)
      evidence

theorem ay_bwlr_restart_evidence_epoch
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) :
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay ->
    epochPreserved :=
  fun evidence =>
    ay_bwlr_conj_left epochPreserved checkerReplay
      (ay_bwlr_conj_right trailReset
        (AyBWLRConj epochPreserved checkerReplay)
        evidence)

theorem ay_bwlr_restart_evidence_checker
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) :
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay ->
    checkerReplay :=
  fun evidence =>
    ay_bwlr_conj_right epochPreserved checkerReplay
      (ay_bwlr_conj_right trailReset
        (AyBWLRConj epochPreserved checkerReplay)
        evidence)

theorem ay_bwlr_replay_agreement_intro
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    watchMatch ->
    epochMatch ->
    trailResetMatch ->
    checkerMatch ->
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch :=
  fun watchH epochH trailH checkerH =>
    ay_bwlr_conj_intro watchMatch
      (AyBWLRConj epochMatch
        (AyBWLRConj trailResetMatch checkerMatch))
      watchH
      (ay_bwlr_conj_intro epochMatch
        (AyBWLRConj trailResetMatch checkerMatch)
        epochH
        (ay_bwlr_conj_intro trailResetMatch checkerMatch
          trailH checkerH))

theorem ay_bwlr_replay_agreement_watch
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    watchMatch :=
  fun agreement =>
    ay_bwlr_conj_left watchMatch
      (AyBWLRConj epochMatch
        (AyBWLRConj trailResetMatch checkerMatch))
      agreement

theorem ay_bwlr_replay_agreement_tail
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    AyBWLRConj epochMatch
      (AyBWLRConj trailResetMatch checkerMatch) :=
  fun agreement =>
    ay_bwlr_conj_right watchMatch
      (AyBWLRConj epochMatch
        (AyBWLRConj trailResetMatch checkerMatch))
      agreement

theorem ay_bwlr_replay_agreement_epoch
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    epochMatch :=
  fun agreement =>
    ay_bwlr_conj_left epochMatch
      (AyBWLRConj trailResetMatch checkerMatch)
      (ay_bwlr_replay_agreement_tail watchMatch epochMatch
        trailResetMatch checkerMatch agreement)

theorem ay_bwlr_replay_agreement_trail_reset
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    trailResetMatch :=
  fun agreement =>
    ay_bwlr_conj_left trailResetMatch checkerMatch
      (ay_bwlr_conj_right epochMatch
        (AyBWLRConj trailResetMatch checkerMatch)
        (ay_bwlr_replay_agreement_tail watchMatch epochMatch
          trailResetMatch checkerMatch agreement))

theorem ay_bwlr_replay_agreement_checker
    (watchMatch : Prop) (epochMatch : Prop)
    (trailResetMatch : Prop) (checkerMatch : Prop) :
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_bwlr_conj_right trailResetMatch checkerMatch
      (ay_bwlr_conj_right epochMatch
        (AyBWLRConj trailResetMatch checkerMatch)
        (ay_bwlr_replay_agreement_tail watchMatch epochMatch
          trailResetMatch checkerMatch agreement))

theorem ay_bwlr_accepted_restart_intro
    (watchState : Prop) (restartEvidence : Prop) (agreement : Prop) :
    watchState ->
    restartEvidence ->
    agreement ->
    AyBWLRAcceptedRestart watchState restartEvidence agreement :=
  fun stateH evidenceH agreementH =>
    ay_bwlr_conj_intro watchState
      (AyBWLRConj restartEvidence agreement)
      stateH
      (ay_bwlr_conj_intro restartEvidence agreement
        evidenceH agreementH)

theorem ay_bwlr_accepted_restart_state
    (watchState : Prop) (restartEvidence : Prop) (agreement : Prop) :
    AyBWLRAcceptedRestart watchState restartEvidence agreement ->
    watchState :=
  fun accepted =>
    ay_bwlr_conj_left watchState
      (AyBWLRConj restartEvidence agreement)
      accepted

theorem ay_bwlr_accepted_restart_evidence
    (watchState : Prop) (restartEvidence : Prop) (agreement : Prop) :
    AyBWLRAcceptedRestart watchState restartEvidence agreement ->
    restartEvidence :=
  fun accepted =>
    ay_bwlr_conj_left restartEvidence agreement
      (ay_bwlr_conj_right watchState
        (AyBWLRConj restartEvidence agreement)
        accepted)

theorem ay_bwlr_accepted_restart_agreement
    (watchState : Prop) (restartEvidence : Prop) (agreement : Prop) :
    AyBWLRAcceptedRestart watchState restartEvidence agreement ->
    agreement :=
  fun accepted =>
    ay_bwlr_conj_right restartEvidence agreement
      (ay_bwlr_conj_right watchState
        (AyBWLRConj restartEvidence agreement)
        accepted)

theorem ay_bwlr_propagated_clause_intro
    (queueItem : Prop) (watchJustification : Prop)
    (checkerReplay : Prop) :
    queueItem ->
    watchJustification ->
    checkerReplay ->
    AyBWLRPropagatedClause queueItem watchJustification checkerReplay :=
  fun queueH watchH checkerH =>
    ay_bwlr_conj_intro queueItem
      (AyBWLRConj watchJustification checkerReplay)
      queueH
      (ay_bwlr_conj_intro watchJustification checkerReplay
        watchH checkerH)

theorem ay_bwlr_propagated_clause_queue
    (queueItem : Prop) (watchJustification : Prop)
    (checkerReplay : Prop) :
    AyBWLRPropagatedClause queueItem watchJustification checkerReplay ->
    queueItem :=
  fun propagated =>
    ay_bwlr_conj_left queueItem
      (AyBWLRConj watchJustification checkerReplay)
      propagated

theorem ay_bwlr_propagated_clause_watch
    (queueItem : Prop) (watchJustification : Prop)
    (checkerReplay : Prop) :
    AyBWLRPropagatedClause queueItem watchJustification checkerReplay ->
    watchJustification :=
  fun propagated =>
    ay_bwlr_conj_left watchJustification checkerReplay
      (ay_bwlr_conj_right queueItem
        (AyBWLRConj watchJustification checkerReplay)
        propagated)

theorem ay_bwlr_propagated_clause_checker
    (queueItem : Prop) (watchJustification : Prop)
    (checkerReplay : Prop) :
    AyBWLRPropagatedClause queueItem watchJustification checkerReplay ->
    checkerReplay :=
  fun propagated =>
    ay_bwlr_conj_right watchJustification checkerReplay
      (ay_bwlr_conj_right queueItem
        (AyBWLRConj watchJustification checkerReplay)
        propagated)

theorem ay_bwlr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBWLRPublicReport (AyBWLROutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bwlr_conj_intro (AyBWLROutcome model conflict) formula
      (ay_bwlr_disj_left model conflict modelH)
      formulaH

theorem ay_bwlr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBWLRPublicReport (AyBWLROutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bwlr_conj_intro (AyBWLROutcome model conflict) formula
      (ay_bwlr_disj_right model conflict conflictH)
      formulaH

theorem ay_bwlr_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBWLRAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_bwlr_conj_intro evidence public evidenceH publicH

theorem ay_bwlr_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBWLRAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_bwlr_conj_left evidence public report

theorem ay_bwlr_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBWLRAcceptedReport evidence public -> public :=
  fun report =>
    ay_bwlr_conj_right evidence public report

theorem ay_bwlr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBWLRNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bwlr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bwlr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBWLRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bwlr_conj_left fallbackPublic diagnostic noClaim

theorem ay_bwlr_stale_watch_no_claim
    (staleWatch : Prop) (fallbackPublic : Prop) :
    staleWatch ->
    fallbackPublic ->
    AyBWLRNoClaim staleWatch fallbackPublic :=
  fun staleH fallbackH =>
    ay_bwlr_no_claim_intro staleWatch fallbackPublic staleH fallbackH

theorem ay_bwlr_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    AyBWLRNoClaim epochMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bwlr_no_claim_intro epochMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bwlr_trail_reset_mismatch_no_claim
    (trailMismatch : Prop) (fallbackPublic : Prop) :
    trailMismatch ->
    fallbackPublic ->
    AyBWLRNoClaim trailMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bwlr_no_claim_intro trailMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bwlr_checker_mismatch_no_claim
    (checkerMismatch : Prop) (fallbackPublic : Prop) :
    checkerMismatch ->
    fallbackPublic ->
    AyBWLRNoClaim checkerMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bwlr_no_claim_intro checkerMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bwlr_stale_watch_cannot_justify_propagation
    (staleWatch : Prop) (fallbackPublic : Prop) :
    staleWatch ->
    fallbackPublic ->
    AyBWLRNoClaim staleWatch fallbackPublic :=
  fun staleH fallbackH =>
    ay_bwlr_stale_watch_no_claim staleWatch fallbackPublic
      staleH fallbackH

theorem ay_bwlr_restart_guides_sat
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop)
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) (watchMatch : Prop)
    (epochMatch : Prop) (trailResetMatch : Prop)
    (checkerMatch : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay ->
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    model ->
    formula ->
    AyBWLRAcceptedReport
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula) :=
  fun state evidence agreement modelH formulaH =>
    ay_bwlr_accepted_report_intro
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula)
      (ay_bwlr_accepted_restart_intro
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch)
        state evidence agreement)
      (ay_bwlr_public_sat_report model conflict formula modelH formulaH)

theorem ay_bwlr_restart_guides_unsat
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop)
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) (watchMatch : Prop)
    (epochMatch : Prop) (trailResetMatch : Prop)
    (checkerMatch : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBWLRWatchState watchCertificate clauseEpoch
      propagationQueue trailState ->
    AyBWLRestartEvidence trailReset epochPreserved checkerReplay ->
    AyBWLRReplayAgreement watchMatch epochMatch
      trailResetMatch checkerMatch ->
    conflict ->
    formula ->
    AyBWLRAcceptedReport
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula) :=
  fun state evidence agreement conflictH formulaH =>
    ay_bwlr_accepted_report_intro
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula)
      (ay_bwlr_accepted_restart_intro
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch)
        state evidence agreement)
      (ay_bwlr_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bwlr_accepted_restart_report_soundness
    (watchCertificate : Prop) (clauseEpoch : Prop)
    (propagationQueue : Prop) (trailState : Prop)
    (trailReset : Prop) (epochPreserved : Prop)
    (checkerReplay : Prop) (watchMatch : Prop)
    (epochMatch : Prop) (trailResetMatch : Prop)
    (checkerMatch : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBWLRAcceptedReport
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula) ->
    AyBWLRPublicReport (AyBWLROutcome model conflict) formula :=
  fun report =>
    ay_bwlr_accepted_report_public
      (AyBWLRAcceptedRestart
        (AyBWLRWatchState watchCertificate clauseEpoch
          propagationQueue trailState)
        (AyBWLRestartEvidence trailReset epochPreserved checkerReplay)
        (AyBWLRReplayAgreement watchMatch epochMatch
          trailResetMatch checkerMatch))
      (AyBWLRPublicReport (AyBWLROutcome model conflict) formula)
      report

theorem ay_bwlr_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBWLRNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bwlr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
