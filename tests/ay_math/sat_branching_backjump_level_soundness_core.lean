-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded backjump-level soundness skeleton for ay SAT solving.
-- Non-chronological backjump targets produced by conflict analysis are
-- admissible only when the learned clause is asserting at the target level,
-- the trail prefix and implication graph agree, and checker replay validates
-- the derivation. Bad targets fall back to no-claim/recompute and cannot
-- justify propagation or public UNSAT.

def AyBBLSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBBLSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBBLSEquisat (before : Prop) (after : Prop) :=
  AyBBLSConj (before -> after) (after -> before)

def AyBBLSBackjumpCert
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :=
  AyBBLSConj learnedClause
    (AyBBLSConj targetLevel
      (AyBBLSConj assertingAtTarget
        (AyBBLSConj trailPrefix
          (AyBBLSConj implicationGraph checkerReplay))))

def AyBBLSAgreement
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :=
  AyBBLSConj assertingMatch
    (AyBBLSConj trailMatch (AyBBLSConj graphMatch replayMatch))

def AyBBLSAcceptedBackjump
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :=
  AyBBLSConj certificate (AyBBLSConj agreement propagation)

def AyBBLSOutcome (model : Prop) (conflict : Prop) :=
  AyBBLSDisj model conflict

def AyBBLSPublicReport (outcome : Prop) (formula : Prop) :=
  AyBBLSConj outcome formula

def AyBBLSAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBBLSConj evidence public

def AyBBLSNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBBLSConj fallbackPublic diagnostic

theorem ay_bbls_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBBLSConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bbls_conj_left
    (left : Prop) (right : Prop) :
    AyBBLSConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bbls_conj_right
    (left : Prop) (right : Prop) :
    AyBBLSConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bbls_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBBLSDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bbls_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBBLSDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bbls_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBBLSEquisat before after :=
  fun forward backward =>
    ay_bbls_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bbls_equisat_forward
    (before : Prop) (after : Prop) :
    AyBBLSEquisat before after -> before -> after :=
  fun equisat =>
    ay_bbls_conj_left (before -> after) (after -> before) equisat

theorem ay_bbls_equisat_backward
    (before : Prop) (after : Prop) :
    AyBBLSEquisat before after -> after -> before :=
  fun equisat =>
    ay_bbls_conj_right (before -> after) (after -> before) equisat

theorem ay_bbls_backjump_cert_intro
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    learnedClause ->
    targetLevel ->
    assertingAtTarget ->
    trailPrefix ->
    implicationGraph ->
    checkerReplay ->
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay :=
  fun learnedH targetH assertingH trailH graphH replayH =>
    ay_bbls_conj_intro learnedClause
      (AyBBLSConj targetLevel
        (AyBBLSConj assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))))
      learnedH
      (ay_bbls_conj_intro targetLevel
        (AyBBLSConj assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay)))
        targetH
        (ay_bbls_conj_intro assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))
          assertingH
          (ay_bbls_conj_intro trailPrefix
            (AyBBLSConj implicationGraph checkerReplay)
            trailH
            (ay_bbls_conj_intro implicationGraph checkerReplay
              graphH replayH))))

theorem ay_bbls_backjump_cert_learned
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    learnedClause :=
  fun cert =>
    ay_bbls_conj_left learnedClause
      (AyBBLSConj targetLevel
        (AyBBLSConj assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))))
      cert

theorem ay_bbls_backjump_cert_tail
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    AyBBLSConj targetLevel
      (AyBBLSConj assertingAtTarget
        (AyBBLSConj trailPrefix
          (AyBBLSConj implicationGraph checkerReplay))) :=
  fun cert =>
    ay_bbls_conj_right learnedClause
      (AyBBLSConj targetLevel
        (AyBBLSConj assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))))
      cert

theorem ay_bbls_backjump_cert_target
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    targetLevel :=
  fun cert =>
    ay_bbls_conj_left targetLevel
      (AyBBLSConj assertingAtTarget
        (AyBBLSConj trailPrefix
          (AyBBLSConj implicationGraph checkerReplay)))
      (ay_bbls_backjump_cert_tail learnedClause targetLevel
        assertingAtTarget trailPrefix implicationGraph checkerReplay cert)

theorem ay_bbls_backjump_cert_asserting
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    assertingAtTarget :=
  fun cert =>
    ay_bbls_conj_left assertingAtTarget
      (AyBBLSConj trailPrefix
        (AyBBLSConj implicationGraph checkerReplay))
      (ay_bbls_conj_right targetLevel
        (AyBBLSConj assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay)))
        (ay_bbls_backjump_cert_tail learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay cert))

theorem ay_bbls_backjump_cert_trail
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    trailPrefix :=
  fun cert =>
    ay_bbls_conj_left trailPrefix
      (AyBBLSConj implicationGraph checkerReplay)
      (ay_bbls_conj_right assertingAtTarget
        (AyBBLSConj trailPrefix
          (AyBBLSConj implicationGraph checkerReplay))
        (ay_bbls_conj_right targetLevel
          (AyBBLSConj assertingAtTarget
            (AyBBLSConj trailPrefix
              (AyBBLSConj implicationGraph checkerReplay)))
          (ay_bbls_backjump_cert_tail learnedClause targetLevel
            assertingAtTarget trailPrefix implicationGraph checkerReplay
            cert)))

theorem ay_bbls_backjump_cert_graph
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    implicationGraph :=
  fun cert =>
    ay_bbls_conj_left implicationGraph checkerReplay
      (ay_bbls_conj_right trailPrefix
        (AyBBLSConj implicationGraph checkerReplay)
        (ay_bbls_conj_right assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))
          (ay_bbls_conj_right targetLevel
            (AyBBLSConj assertingAtTarget
              (AyBBLSConj trailPrefix
                (AyBBLSConj implicationGraph checkerReplay)))
            (ay_bbls_backjump_cert_tail learnedClause targetLevel
              assertingAtTarget trailPrefix implicationGraph checkerReplay
              cert))))

theorem ay_bbls_backjump_cert_checker
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    checkerReplay :=
  fun cert =>
    ay_bbls_conj_right implicationGraph checkerReplay
      (ay_bbls_conj_right trailPrefix
        (AyBBLSConj implicationGraph checkerReplay)
        (ay_bbls_conj_right assertingAtTarget
          (AyBBLSConj trailPrefix
            (AyBBLSConj implicationGraph checkerReplay))
          (ay_bbls_conj_right targetLevel
            (AyBBLSConj assertingAtTarget
              (AyBBLSConj trailPrefix
                (AyBBLSConj implicationGraph checkerReplay)))
            (ay_bbls_backjump_cert_tail learnedClause targetLevel
              assertingAtTarget trailPrefix implicationGraph checkerReplay
              cert))))

theorem ay_bbls_agreement_intro
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    assertingMatch ->
    trailMatch ->
    graphMatch ->
    replayMatch ->
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch :=
  fun assertingH trailH graphH replayH =>
    ay_bbls_conj_intro assertingMatch
      (AyBBLSConj trailMatch (AyBBLSConj graphMatch replayMatch))
      assertingH
      (ay_bbls_conj_intro trailMatch
        (AyBBLSConj graphMatch replayMatch)
        trailH
        (ay_bbls_conj_intro graphMatch replayMatch graphH replayH))

theorem ay_bbls_agreement_asserting
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    assertingMatch :=
  fun agreement =>
    ay_bbls_conj_left assertingMatch
      (AyBBLSConj trailMatch (AyBBLSConj graphMatch replayMatch))
      agreement

theorem ay_bbls_agreement_tail
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    AyBBLSConj trailMatch (AyBBLSConj graphMatch replayMatch) :=
  fun agreement =>
    ay_bbls_conj_right assertingMatch
      (AyBBLSConj trailMatch (AyBBLSConj graphMatch replayMatch))
      agreement

theorem ay_bbls_agreement_trail
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    trailMatch :=
  fun agreement =>
    ay_bbls_conj_left trailMatch (AyBBLSConj graphMatch replayMatch)
      (ay_bbls_agreement_tail assertingMatch trailMatch graphMatch
        replayMatch agreement)

theorem ay_bbls_agreement_graph
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    graphMatch :=
  fun agreement =>
    ay_bbls_conj_left graphMatch replayMatch
      (ay_bbls_conj_right trailMatch
        (AyBBLSConj graphMatch replayMatch)
        (ay_bbls_agreement_tail assertingMatch trailMatch graphMatch
          replayMatch agreement))

theorem ay_bbls_agreement_replay
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop) :
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    replayMatch :=
  fun agreement =>
    ay_bbls_conj_right graphMatch replayMatch
      (ay_bbls_conj_right trailMatch
        (AyBBLSConj graphMatch replayMatch)
        (ay_bbls_agreement_tail assertingMatch trailMatch graphMatch
          replayMatch agreement))

theorem ay_bbls_accepted_backjump_intro
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    certificate ->
    agreement ->
    propagation ->
    AyBBLSAcceptedBackjump certificate agreement propagation :=
  fun certH agreementH propagationH =>
    ay_bbls_conj_intro certificate (AyBBLSConj agreement propagation)
      certH
      (ay_bbls_conj_intro agreement propagation
        agreementH propagationH)

theorem ay_bbls_accepted_backjump_certificate
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBBLSAcceptedBackjump certificate agreement propagation ->
    certificate :=
  fun accepted =>
    ay_bbls_conj_left certificate (AyBBLSConj agreement propagation)
      accepted

theorem ay_bbls_accepted_backjump_agreement
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBBLSAcceptedBackjump certificate agreement propagation ->
    agreement :=
  fun accepted =>
    ay_bbls_conj_left agreement propagation
      (ay_bbls_conj_right certificate
        (AyBBLSConj agreement propagation)
        accepted)

theorem ay_bbls_accepted_backjump_propagation
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBBLSAcceptedBackjump certificate agreement propagation ->
    propagation :=
  fun accepted =>
    ay_bbls_conj_right agreement propagation
      (ay_bbls_conj_right certificate
        (AyBBLSConj agreement propagation)
        accepted)

theorem ay_bbls_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBBLSPublicReport (AyBBLSOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bbls_conj_intro (AyBBLSOutcome model conflict) formula
      (ay_bbls_disj_left model conflict modelH)
      formulaH

theorem ay_bbls_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBBLSPublicReport (AyBBLSOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bbls_conj_intro (AyBBLSOutcome model conflict) formula
      (ay_bbls_disj_right model conflict conflictH)
      formulaH

theorem ay_bbls_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBBLSAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_bbls_conj_intro evidence public evidenceH publicH

theorem ay_bbls_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBBLSAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_bbls_conj_left evidence public report

theorem ay_bbls_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBBLSAcceptedReport evidence public -> public :=
  fun report =>
    ay_bbls_conj_right evidence public report

theorem ay_bbls_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBBLSNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bbls_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bbls_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBBLSNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bbls_conj_left fallbackPublic diagnostic noClaim

theorem ay_bbls_bad_target_no_claim
    (badTarget : Prop) (fallbackPublic : Prop) :
    badTarget ->
    fallbackPublic ->
    AyBBLSNoClaim badTarget fallbackPublic :=
  fun badH fallbackH =>
    ay_bbls_no_claim_intro badTarget fallbackPublic badH fallbackH

theorem ay_bbls_non_asserting_no_claim
    (nonAsserting : Prop) (fallbackPublic : Prop) :
    nonAsserting ->
    fallbackPublic ->
    AyBBLSNoClaim nonAsserting fallbackPublic :=
  fun badH fallbackH =>
    ay_bbls_no_claim_intro nonAsserting fallbackPublic badH fallbackH

theorem ay_bbls_trail_graph_mismatch_no_claim
    (mismatch : Prop) (fallbackPublic : Prop) :
    mismatch ->
    fallbackPublic ->
    AyBBLSNoClaim mismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bbls_no_claim_intro mismatch fallbackPublic mismatchH fallbackH

theorem ay_bbls_replay_mismatch_no_claim
    (replayMismatch : Prop) (fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    AyBBLSNoClaim replayMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bbls_no_claim_intro replayMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bbls_bad_target_cannot_justify_propagation
    (badTarget : Prop) (fallbackPublic : Prop) :
    badTarget ->
    fallbackPublic ->
    AyBBLSNoClaim badTarget fallbackPublic :=
  fun badH fallbackH =>
    ay_bbls_bad_target_no_claim badTarget fallbackPublic badH fallbackH

theorem ay_bbls_accepted_backjump_guides_sat
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop)
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop)
    (propagation : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    propagation ->
    model ->
    formula ->
    AyBBLSAcceptedReport
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula) :=
  fun cert agreement propagationH modelH formulaH =>
    ay_bbls_accepted_report_intro
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula)
      (ay_bbls_accepted_backjump_intro
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation
        cert agreement propagationH)
      (ay_bbls_public_sat_report model conflict formula modelH formulaH)

theorem ay_bbls_accepted_backjump_guides_unsat
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop)
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop)
    (propagation : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBBLSBackjumpCert learnedClause targetLevel assertingAtTarget
      trailPrefix implicationGraph checkerReplay ->
    AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch ->
    propagation ->
    conflict ->
    formula ->
    AyBBLSAcceptedReport
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula) :=
  fun cert agreement propagationH conflictH formulaH =>
    ay_bbls_accepted_report_intro
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula)
      (ay_bbls_accepted_backjump_intro
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation
        cert agreement propagationH)
      (ay_bbls_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bbls_accepted_backjump_report_soundness
    (learnedClause : Prop) (targetLevel : Prop)
    (assertingAtTarget : Prop) (trailPrefix : Prop)
    (implicationGraph : Prop) (checkerReplay : Prop)
    (assertingMatch : Prop) (trailMatch : Prop)
    (graphMatch : Prop) (replayMatch : Prop)
    (propagation : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBBLSAcceptedReport
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula) ->
    AyBBLSPublicReport (AyBBLSOutcome model conflict) formula :=
  fun report =>
    ay_bbls_accepted_report_public
      (AyBBLSAcceptedBackjump
        (AyBBLSBackjumpCert learnedClause targetLevel
          assertingAtTarget trailPrefix implicationGraph checkerReplay)
        (AyBBLSAgreement assertingMatch trailMatch graphMatch replayMatch)
        propagation)
      (AyBBLSPublicReport (AyBBLSOutcome model conflict) formula)
      report

theorem ay_bbls_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBBLSNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bbls_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
