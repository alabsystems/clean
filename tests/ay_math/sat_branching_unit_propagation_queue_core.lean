-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded unit-propagation queue certificate soundness skeleton for ay SAT
-- solving. Queued unit propagations after clause learning or restart are
-- admissible only when watch evidence, queue order, trail prefix, clause
-- database epoch, and checker replay agree. Stale or reordered queue state
-- falls back to no-claim/recompute and cannot justify public results.

def AyBUPQConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBUPQDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBUPQEquisat (before : Prop) (after : Prop) :=
  AyBUPQConj (before -> after) (after -> before)

def AyBUPQQueueCert
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :=
  AyBUPQConj unitPropagation
    (AyBUPQConj watchEvidence
      (AyBUPQConj queueOrder
        (AyBUPQConj trailPrefix
          (AyBUPQConj clauseEpoch checkerReplay))))

def AyBUPQAgreement
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :=
  AyBUPQConj watchMatch
    (AyBUPQConj orderMatch
      (AyBUPQConj trailMatch
        (AyBUPQConj epochMatch checkerMatch)))

def AyBUPQAcceptedPropagation
    (queueCert : Prop) (agreement : Prop) (learnedClause : Prop) :=
  AyBUPQConj queueCert (AyBUPQConj agreement learnedClause)

def AyBUPQOutcome (model : Prop) (conflict : Prop) :=
  AyBUPQDisj model conflict

def AyBUPQPublicReport (outcome : Prop) (formula : Prop) :=
  AyBUPQConj outcome formula

def AyBUPQAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBUPQConj evidence public

def AyBUPQNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBUPQConj fallbackPublic diagnostic

theorem ay_bupq_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBUPQConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bupq_conj_left
    (left : Prop) (right : Prop) :
    AyBUPQConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bupq_conj_right
    (left : Prop) (right : Prop) :
    AyBUPQConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bupq_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBUPQDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bupq_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBUPQDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bupq_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBUPQEquisat before after :=
  fun forward backward =>
    ay_bupq_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bupq_equisat_forward
    (before : Prop) (after : Prop) :
    AyBUPQEquisat before after -> before -> after :=
  fun equisat =>
    ay_bupq_conj_left (before -> after) (after -> before) equisat

theorem ay_bupq_equisat_backward
    (before : Prop) (after : Prop) :
    AyBUPQEquisat before after -> after -> before :=
  fun equisat =>
    ay_bupq_conj_right (before -> after) (after -> before) equisat

theorem ay_bupq_queue_cert_intro
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    unitPropagation ->
    watchEvidence ->
    queueOrder ->
    trailPrefix ->
    clauseEpoch ->
    checkerReplay ->
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay :=
  fun unitH watchH orderH trailH epochH checkerH =>
    ay_bupq_conj_intro unitPropagation
      (AyBUPQConj watchEvidence
        (AyBUPQConj queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))))
      unitH
      (ay_bupq_conj_intro watchEvidence
        (AyBUPQConj queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay)))
        watchH
        (ay_bupq_conj_intro queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))
          orderH
          (ay_bupq_conj_intro trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay)
            trailH
            (ay_bupq_conj_intro clauseEpoch checkerReplay
              epochH checkerH))))

theorem ay_bupq_queue_cert_unit
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    unitPropagation :=
  fun cert =>
    ay_bupq_conj_left unitPropagation
      (AyBUPQConj watchEvidence
        (AyBUPQConj queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))))
      cert

theorem ay_bupq_queue_cert_tail
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    AyBUPQConj watchEvidence
      (AyBUPQConj queueOrder
        (AyBUPQConj trailPrefix
          (AyBUPQConj clauseEpoch checkerReplay))) :=
  fun cert =>
    ay_bupq_conj_right unitPropagation
      (AyBUPQConj watchEvidence
        (AyBUPQConj queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))))
      cert

theorem ay_bupq_queue_cert_watch
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    watchEvidence :=
  fun cert =>
    ay_bupq_conj_left watchEvidence
      (AyBUPQConj queueOrder
        (AyBUPQConj trailPrefix
          (AyBUPQConj clauseEpoch checkerReplay)))
      (ay_bupq_queue_cert_tail unitPropagation watchEvidence queueOrder
        trailPrefix clauseEpoch checkerReplay cert)

theorem ay_bupq_queue_cert_order
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    queueOrder :=
  fun cert =>
    ay_bupq_conj_left queueOrder
      (AyBUPQConj trailPrefix
        (AyBUPQConj clauseEpoch checkerReplay))
      (ay_bupq_conj_right watchEvidence
        (AyBUPQConj queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay)))
        (ay_bupq_queue_cert_tail unitPropagation watchEvidence
          queueOrder trailPrefix clauseEpoch checkerReplay cert))

theorem ay_bupq_queue_cert_trail
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    trailPrefix :=
  fun cert =>
    ay_bupq_conj_left trailPrefix
      (AyBUPQConj clauseEpoch checkerReplay)
      (ay_bupq_conj_right queueOrder
        (AyBUPQConj trailPrefix
          (AyBUPQConj clauseEpoch checkerReplay))
        (ay_bupq_conj_right watchEvidence
          (AyBUPQConj queueOrder
            (AyBUPQConj trailPrefix
              (AyBUPQConj clauseEpoch checkerReplay)))
          (ay_bupq_queue_cert_tail unitPropagation watchEvidence
            queueOrder trailPrefix clauseEpoch checkerReplay cert)))

theorem ay_bupq_queue_cert_epoch
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    clauseEpoch :=
  fun cert =>
    ay_bupq_conj_left clauseEpoch checkerReplay
      (ay_bupq_conj_right trailPrefix
        (AyBUPQConj clauseEpoch checkerReplay)
        (ay_bupq_conj_right queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))
          (ay_bupq_conj_right watchEvidence
            (AyBUPQConj queueOrder
              (AyBUPQConj trailPrefix
                (AyBUPQConj clauseEpoch checkerReplay)))
            (ay_bupq_queue_cert_tail unitPropagation watchEvidence
              queueOrder trailPrefix clauseEpoch checkerReplay cert))))

theorem ay_bupq_queue_cert_checker
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    checkerReplay :=
  fun cert =>
    ay_bupq_conj_right clauseEpoch checkerReplay
      (ay_bupq_conj_right trailPrefix
        (AyBUPQConj clauseEpoch checkerReplay)
        (ay_bupq_conj_right queueOrder
          (AyBUPQConj trailPrefix
            (AyBUPQConj clauseEpoch checkerReplay))
          (ay_bupq_conj_right watchEvidence
            (AyBUPQConj queueOrder
              (AyBUPQConj trailPrefix
                (AyBUPQConj clauseEpoch checkerReplay)))
            (ay_bupq_queue_cert_tail unitPropagation watchEvidence
              queueOrder trailPrefix clauseEpoch checkerReplay cert))))

theorem ay_bupq_agreement_intro
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    watchMatch ->
    orderMatch ->
    trailMatch ->
    epochMatch ->
    checkerMatch ->
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch :=
  fun watchH orderH trailH epochH checkerH =>
    ay_bupq_conj_intro watchMatch
      (AyBUPQConj orderMatch
        (AyBUPQConj trailMatch
          (AyBUPQConj epochMatch checkerMatch)))
      watchH
      (ay_bupq_conj_intro orderMatch
        (AyBUPQConj trailMatch
          (AyBUPQConj epochMatch checkerMatch))
        orderH
        (ay_bupq_conj_intro trailMatch
          (AyBUPQConj epochMatch checkerMatch)
          trailH
          (ay_bupq_conj_intro epochMatch checkerMatch
            epochH checkerH)))

theorem ay_bupq_agreement_watch
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    watchMatch :=
  fun agreement =>
    ay_bupq_conj_left watchMatch
      (AyBUPQConj orderMatch
        (AyBUPQConj trailMatch
          (AyBUPQConj epochMatch checkerMatch)))
      agreement

theorem ay_bupq_agreement_tail
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    AyBUPQConj orderMatch
      (AyBUPQConj trailMatch
        (AyBUPQConj epochMatch checkerMatch)) :=
  fun agreement =>
    ay_bupq_conj_right watchMatch
      (AyBUPQConj orderMatch
        (AyBUPQConj trailMatch
          (AyBUPQConj epochMatch checkerMatch)))
      agreement

theorem ay_bupq_agreement_order
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    orderMatch :=
  fun agreement =>
    ay_bupq_conj_left orderMatch
      (AyBUPQConj trailMatch
        (AyBUPQConj epochMatch checkerMatch))
      (ay_bupq_agreement_tail watchMatch orderMatch trailMatch
        epochMatch checkerMatch agreement)

theorem ay_bupq_agreement_trail
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    trailMatch :=
  fun agreement =>
    ay_bupq_conj_left trailMatch
      (AyBUPQConj epochMatch checkerMatch)
      (ay_bupq_conj_right orderMatch
        (AyBUPQConj trailMatch
          (AyBUPQConj epochMatch checkerMatch))
        (ay_bupq_agreement_tail watchMatch orderMatch trailMatch
          epochMatch checkerMatch agreement))

theorem ay_bupq_agreement_epoch
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    epochMatch :=
  fun agreement =>
    ay_bupq_conj_left epochMatch checkerMatch
      (ay_bupq_conj_right trailMatch
        (AyBUPQConj epochMatch checkerMatch)
        (ay_bupq_conj_right orderMatch
          (AyBUPQConj trailMatch
            (AyBUPQConj epochMatch checkerMatch))
          (ay_bupq_agreement_tail watchMatch orderMatch trailMatch
            epochMatch checkerMatch agreement)))

theorem ay_bupq_agreement_checker
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) :
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_bupq_conj_right epochMatch checkerMatch
      (ay_bupq_conj_right trailMatch
        (AyBUPQConj epochMatch checkerMatch)
        (ay_bupq_conj_right orderMatch
          (AyBUPQConj trailMatch
            (AyBUPQConj epochMatch checkerMatch))
          (ay_bupq_agreement_tail watchMatch orderMatch trailMatch
            epochMatch checkerMatch agreement)))

theorem ay_bupq_accepted_propagation_intro
    (queueCert : Prop) (agreement : Prop) (learnedClause : Prop) :
    queueCert ->
    agreement ->
    learnedClause ->
    AyBUPQAcceptedPropagation queueCert agreement learnedClause :=
  fun certH agreementH learnedH =>
    ay_bupq_conj_intro queueCert
      (AyBUPQConj agreement learnedClause)
      certH
      (ay_bupq_conj_intro agreement learnedClause
        agreementH learnedH)

theorem ay_bupq_accepted_propagation_cert
    (queueCert : Prop) (agreement : Prop) (learnedClause : Prop) :
    AyBUPQAcceptedPropagation queueCert agreement learnedClause ->
    queueCert :=
  fun accepted =>
    ay_bupq_conj_left queueCert
      (AyBUPQConj agreement learnedClause)
      accepted

theorem ay_bupq_accepted_propagation_agreement
    (queueCert : Prop) (agreement : Prop) (learnedClause : Prop) :
    AyBUPQAcceptedPropagation queueCert agreement learnedClause ->
    agreement :=
  fun accepted =>
    ay_bupq_conj_left agreement learnedClause
      (ay_bupq_conj_right queueCert
        (AyBUPQConj agreement learnedClause)
        accepted)

theorem ay_bupq_accepted_propagation_learned
    (queueCert : Prop) (agreement : Prop) (learnedClause : Prop) :
    AyBUPQAcceptedPropagation queueCert agreement learnedClause ->
    learnedClause :=
  fun accepted =>
    ay_bupq_conj_right agreement learnedClause
      (ay_bupq_conj_right queueCert
        (AyBUPQConj agreement learnedClause)
        accepted)

theorem ay_bupq_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBUPQPublicReport (AyBUPQOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bupq_conj_intro (AyBUPQOutcome model conflict) formula
      (ay_bupq_disj_left model conflict modelH)
      formulaH

theorem ay_bupq_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBUPQPublicReport (AyBUPQOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bupq_conj_intro (AyBUPQOutcome model conflict) formula
      (ay_bupq_disj_right model conflict conflictH)
      formulaH

theorem ay_bupq_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBUPQAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_bupq_conj_intro evidence public evidenceH publicH

theorem ay_bupq_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBUPQAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_bupq_conj_left evidence public report

theorem ay_bupq_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBUPQAcceptedReport evidence public -> public :=
  fun report =>
    ay_bupq_conj_right evidence public report

theorem ay_bupq_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBUPQNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bupq_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bupq_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBUPQNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bupq_conj_left fallbackPublic diagnostic noClaim

theorem ay_bupq_stale_queue_no_claim
    (staleQueue : Prop) (fallbackPublic : Prop) :
    staleQueue ->
    fallbackPublic ->
    AyBUPQNoClaim staleQueue fallbackPublic :=
  fun staleH fallbackH =>
    ay_bupq_no_claim_intro staleQueue fallbackPublic staleH fallbackH

theorem ay_bupq_reordered_queue_no_claim
    (reorderedQueue : Prop) (fallbackPublic : Prop) :
    reorderedQueue ->
    fallbackPublic ->
    AyBUPQNoClaim reorderedQueue fallbackPublic :=
  fun reorderedH fallbackH =>
    ay_bupq_no_claim_intro reorderedQueue fallbackPublic
      reorderedH fallbackH

theorem ay_bupq_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    AyBUPQNoClaim epochMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bupq_no_claim_intro epochMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bupq_checker_mismatch_no_claim
    (checkerMismatch : Prop) (fallbackPublic : Prop) :
    checkerMismatch ->
    fallbackPublic ->
    AyBUPQNoClaim checkerMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bupq_no_claim_intro checkerMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bupq_stale_queue_cannot_justify_learned
    (staleQueue : Prop) (fallbackPublic : Prop) :
    staleQueue ->
    fallbackPublic ->
    AyBUPQNoClaim staleQueue fallbackPublic :=
  fun staleH fallbackH =>
    ay_bupq_stale_queue_no_claim staleQueue fallbackPublic
      staleH fallbackH

theorem ay_bupq_accepted_queue_guides_sat
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop)
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) (learnedClause : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    learnedClause ->
    model ->
    formula ->
    AyBUPQAcceptedReport
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula) :=
  fun cert agreement learnedH modelH formulaH =>
    ay_bupq_accepted_report_intro
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula)
      (ay_bupq_accepted_propagation_intro
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause
        cert agreement learnedH)
      (ay_bupq_public_sat_report model conflict formula modelH formulaH)

theorem ay_bupq_accepted_queue_guides_unsat
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop)
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) (learnedClause : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBUPQQueueCert unitPropagation watchEvidence queueOrder
      trailPrefix clauseEpoch checkerReplay ->
    AyBUPQAgreement watchMatch orderMatch trailMatch
      epochMatch checkerMatch ->
    learnedClause ->
    conflict ->
    formula ->
    AyBUPQAcceptedReport
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula) :=
  fun cert agreement learnedH conflictH formulaH =>
    ay_bupq_accepted_report_intro
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula)
      (ay_bupq_accepted_propagation_intro
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause
        cert agreement learnedH)
      (ay_bupq_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bupq_accepted_queue_report_soundness
    (unitPropagation : Prop) (watchEvidence : Prop)
    (queueOrder : Prop) (trailPrefix : Prop)
    (clauseEpoch : Prop) (checkerReplay : Prop)
    (watchMatch : Prop) (orderMatch : Prop)
    (trailMatch : Prop) (epochMatch : Prop)
    (checkerMatch : Prop) (learnedClause : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBUPQAcceptedReport
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula) ->
    AyBUPQPublicReport (AyBUPQOutcome model conflict) formula :=
  fun report =>
    ay_bupq_accepted_report_public
      (AyBUPQAcceptedPropagation
        (AyBUPQQueueCert unitPropagation watchEvidence queueOrder
          trailPrefix clauseEpoch checkerReplay)
        (AyBUPQAgreement watchMatch orderMatch trailMatch
          epochMatch checkerMatch)
        learnedClause)
      (AyBUPQPublicReport (AyBUPQOutcome model conflict) formula)
      report

theorem ay_bupq_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBUPQNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bupq_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
