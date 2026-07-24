-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded first-UIP conflict-analysis certificate soundness skeleton for ay
-- SAT solving. First-UIP learned clauses may be retained and guide search only
-- when implication graph evidence, trail prefix, cut witness, clause
-- derivation, database epoch, and checker replay agree. Malformed conflict
-- analysis falls back to no-claim/recompute and cannot justify learned clauses
-- or public UNSAT.

def AyBUIPConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBUIPDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBUIPEquisat (before : Prop) (after : Prop) :=
  AyBUIPConj (before -> after) (after -> before)

def AyBUIPConflictCert
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :=
  AyBUIPConj implicationGraph
    (AyBUIPConj trailPrefix
      (AyBUIPConj cutWitness
        (AyBUIPConj clauseDerivation
          (AyBUIPConj databaseEpoch checkerReplay))))

def AyBUIPAgreement
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :=
  AyBUIPConj graphMatch
    (AyBUIPConj trailMatch
      (AyBUIPConj cutMatch
        (AyBUIPConj derivationMatch
          (AyBUIPConj epochMatch checkerMatch))))

def AyBUIPLearnedClause
    (learnedClause : Prop) (assertingLevel : Prop) (backjumpTarget : Prop) :=
  AyBUIPConj learnedClause
    (AyBUIPConj assertingLevel backjumpTarget)

def AyBUIPAcceptedAnalysis
    (conflictCert : Prop) (agreement : Prop) (learned : Prop) :=
  AyBUIPConj conflictCert (AyBUIPConj agreement learned)

def AyBUIPOutcome (model : Prop) (conflict : Prop) :=
  AyBUIPDisj model conflict

def AyBUIPPublicReport (outcome : Prop) (formula : Prop) :=
  AyBUIPConj outcome formula

def AyBUIPAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBUIPConj evidence public

def AyBUIPNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBUIPConj fallbackPublic diagnostic

theorem ay_buip_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBUIPConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_buip_conj_left
    (left : Prop) (right : Prop) :
    AyBUIPConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_buip_conj_right
    (left : Prop) (right : Prop) :
    AyBUIPConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_buip_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBUIPDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_buip_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBUIPDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_buip_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBUIPEquisat before after :=
  fun forward backward =>
    ay_buip_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_buip_equisat_forward
    (before : Prop) (after : Prop) :
    AyBUIPEquisat before after -> before -> after :=
  fun equisat =>
    ay_buip_conj_left (before -> after) (after -> before) equisat

theorem ay_buip_equisat_backward
    (before : Prop) (after : Prop) :
    AyBUIPEquisat before after -> after -> before :=
  fun equisat =>
    ay_buip_conj_right (before -> after) (after -> before) equisat

theorem ay_buip_conflict_cert_intro
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    implicationGraph ->
    trailPrefix ->
    cutWitness ->
    clauseDerivation ->
    databaseEpoch ->
    checkerReplay ->
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay :=
  fun graphH trailH cutH derivationH epochH checkerH =>
    ay_buip_conj_intro implicationGraph
      (AyBUIPConj trailPrefix
        (AyBUIPConj cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))))
      graphH
      (ay_buip_conj_intro trailPrefix
        (AyBUIPConj cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay)))
        trailH
        (ay_buip_conj_intro cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))
          cutH
          (ay_buip_conj_intro clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay)
            derivationH
            (ay_buip_conj_intro databaseEpoch checkerReplay
              epochH checkerH))))

theorem ay_buip_conflict_cert_graph
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    implicationGraph :=
  fun cert =>
    ay_buip_conj_left implicationGraph
      (AyBUIPConj trailPrefix
        (AyBUIPConj cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))))
      cert

theorem ay_buip_conflict_cert_tail
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    AyBUIPConj trailPrefix
      (AyBUIPConj cutWitness
        (AyBUIPConj clauseDerivation
          (AyBUIPConj databaseEpoch checkerReplay))) :=
  fun cert =>
    ay_buip_conj_right implicationGraph
      (AyBUIPConj trailPrefix
        (AyBUIPConj cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))))
      cert

theorem ay_buip_conflict_cert_trail
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    trailPrefix :=
  fun cert =>
    ay_buip_conj_left trailPrefix
      (AyBUIPConj cutWitness
        (AyBUIPConj clauseDerivation
          (AyBUIPConj databaseEpoch checkerReplay)))
      (ay_buip_conflict_cert_tail implicationGraph trailPrefix
        cutWitness clauseDerivation databaseEpoch checkerReplay cert)

theorem ay_buip_conflict_cert_cut
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    cutWitness :=
  fun cert =>
    ay_buip_conj_left cutWitness
      (AyBUIPConj clauseDerivation
        (AyBUIPConj databaseEpoch checkerReplay))
      (ay_buip_conj_right trailPrefix
        (AyBUIPConj cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay)))
        (ay_buip_conflict_cert_tail implicationGraph trailPrefix
          cutWitness clauseDerivation databaseEpoch checkerReplay cert))

theorem ay_buip_conflict_cert_derivation
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    clauseDerivation :=
  fun cert =>
    ay_buip_conj_left clauseDerivation
      (AyBUIPConj databaseEpoch checkerReplay)
      (ay_buip_conj_right cutWitness
        (AyBUIPConj clauseDerivation
          (AyBUIPConj databaseEpoch checkerReplay))
        (ay_buip_conj_right trailPrefix
          (AyBUIPConj cutWitness
            (AyBUIPConj clauseDerivation
              (AyBUIPConj databaseEpoch checkerReplay)))
          (ay_buip_conflict_cert_tail implicationGraph trailPrefix
            cutWitness clauseDerivation databaseEpoch checkerReplay cert)))

theorem ay_buip_conflict_cert_epoch
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    databaseEpoch :=
  fun cert =>
    ay_buip_conj_left databaseEpoch checkerReplay
      (ay_buip_conj_right clauseDerivation
        (AyBUIPConj databaseEpoch checkerReplay)
        (ay_buip_conj_right cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))
          (ay_buip_conj_right trailPrefix
            (AyBUIPConj cutWitness
              (AyBUIPConj clauseDerivation
                (AyBUIPConj databaseEpoch checkerReplay)))
            (ay_buip_conflict_cert_tail implicationGraph trailPrefix
              cutWitness clauseDerivation databaseEpoch checkerReplay
              cert))))

theorem ay_buip_conflict_cert_checker
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    checkerReplay :=
  fun cert =>
    ay_buip_conj_right databaseEpoch checkerReplay
      (ay_buip_conj_right clauseDerivation
        (AyBUIPConj databaseEpoch checkerReplay)
        (ay_buip_conj_right cutWitness
          (AyBUIPConj clauseDerivation
            (AyBUIPConj databaseEpoch checkerReplay))
          (ay_buip_conj_right trailPrefix
            (AyBUIPConj cutWitness
              (AyBUIPConj clauseDerivation
                (AyBUIPConj databaseEpoch checkerReplay)))
            (ay_buip_conflict_cert_tail implicationGraph trailPrefix
              cutWitness clauseDerivation databaseEpoch checkerReplay
              cert))))

theorem ay_buip_agreement_intro
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    graphMatch ->
    trailMatch ->
    cutMatch ->
    derivationMatch ->
    epochMatch ->
    checkerMatch ->
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch :=
  fun graphH trailH cutH derivationH epochH checkerH =>
    ay_buip_conj_intro graphMatch
      (AyBUIPConj trailMatch
        (AyBUIPConj cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))))
      graphH
      (ay_buip_conj_intro trailMatch
        (AyBUIPConj cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch)))
        trailH
        (ay_buip_conj_intro cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))
          cutH
          (ay_buip_conj_intro derivationMatch
            (AyBUIPConj epochMatch checkerMatch)
            derivationH
            (ay_buip_conj_intro epochMatch checkerMatch
              epochH checkerH))))

theorem ay_buip_agreement_graph
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    graphMatch :=
  fun agreement =>
    ay_buip_conj_left graphMatch
      (AyBUIPConj trailMatch
        (AyBUIPConj cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))))
      agreement

theorem ay_buip_agreement_tail
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    AyBUIPConj trailMatch
      (AyBUIPConj cutMatch
        (AyBUIPConj derivationMatch
          (AyBUIPConj epochMatch checkerMatch))) :=
  fun agreement =>
    ay_buip_conj_right graphMatch
      (AyBUIPConj trailMatch
        (AyBUIPConj cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))))
      agreement

theorem ay_buip_agreement_trail
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    trailMatch :=
  fun agreement =>
    ay_buip_conj_left trailMatch
      (AyBUIPConj cutMatch
        (AyBUIPConj derivationMatch
          (AyBUIPConj epochMatch checkerMatch)))
      (ay_buip_agreement_tail graphMatch trailMatch cutMatch
        derivationMatch epochMatch checkerMatch agreement)

theorem ay_buip_agreement_cut
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    cutMatch :=
  fun agreement =>
    ay_buip_conj_left cutMatch
      (AyBUIPConj derivationMatch
        (AyBUIPConj epochMatch checkerMatch))
      (ay_buip_conj_right trailMatch
        (AyBUIPConj cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch)))
        (ay_buip_agreement_tail graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch agreement))

theorem ay_buip_agreement_derivation
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    derivationMatch :=
  fun agreement =>
    ay_buip_conj_left derivationMatch
      (AyBUIPConj epochMatch checkerMatch)
      (ay_buip_conj_right cutMatch
        (AyBUIPConj derivationMatch
          (AyBUIPConj epochMatch checkerMatch))
        (ay_buip_conj_right trailMatch
          (AyBUIPConj cutMatch
            (AyBUIPConj derivationMatch
              (AyBUIPConj epochMatch checkerMatch)))
          (ay_buip_agreement_tail graphMatch trailMatch cutMatch
            derivationMatch epochMatch checkerMatch agreement)))

theorem ay_buip_agreement_epoch
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    epochMatch :=
  fun agreement =>
    ay_buip_conj_left epochMatch checkerMatch
      (ay_buip_conj_right derivationMatch
        (AyBUIPConj epochMatch checkerMatch)
        (ay_buip_conj_right cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))
          (ay_buip_conj_right trailMatch
            (AyBUIPConj cutMatch
              (AyBUIPConj derivationMatch
                (AyBUIPConj epochMatch checkerMatch)))
            (ay_buip_agreement_tail graphMatch trailMatch cutMatch
              derivationMatch epochMatch checkerMatch agreement))))

theorem ay_buip_agreement_checker
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop) :
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_buip_conj_right epochMatch checkerMatch
      (ay_buip_conj_right derivationMatch
        (AyBUIPConj epochMatch checkerMatch)
        (ay_buip_conj_right cutMatch
          (AyBUIPConj derivationMatch
            (AyBUIPConj epochMatch checkerMatch))
          (ay_buip_conj_right trailMatch
            (AyBUIPConj cutMatch
              (AyBUIPConj derivationMatch
                (AyBUIPConj epochMatch checkerMatch)))
            (ay_buip_agreement_tail graphMatch trailMatch cutMatch
              derivationMatch epochMatch checkerMatch agreement))))

theorem ay_buip_learned_clause_intro
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) :
    learnedClause ->
    assertingLevel ->
    backjumpTarget ->
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget :=
  fun learnedH assertingH backjumpH =>
    ay_buip_conj_intro learnedClause
      (AyBUIPConj assertingLevel backjumpTarget)
      learnedH
      (ay_buip_conj_intro assertingLevel backjumpTarget
        assertingH backjumpH)

theorem ay_buip_learned_clause_clause
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) :
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget ->
    learnedClause :=
  fun learned =>
    ay_buip_conj_left learnedClause
      (AyBUIPConj assertingLevel backjumpTarget)
      learned

theorem ay_buip_learned_clause_asserting
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) :
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget ->
    assertingLevel :=
  fun learned =>
    ay_buip_conj_left assertingLevel backjumpTarget
      (ay_buip_conj_right learnedClause
        (AyBUIPConj assertingLevel backjumpTarget)
        learned)

theorem ay_buip_learned_clause_backjump
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) :
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget ->
    backjumpTarget :=
  fun learned =>
    ay_buip_conj_right assertingLevel backjumpTarget
      (ay_buip_conj_right learnedClause
        (AyBUIPConj assertingLevel backjumpTarget)
        learned)

theorem ay_buip_accepted_analysis_intro
    (conflictCert : Prop) (agreement : Prop) (learned : Prop) :
    conflictCert ->
    agreement ->
    learned ->
    AyBUIPAcceptedAnalysis conflictCert agreement learned :=
  fun certH agreementH learnedH =>
    ay_buip_conj_intro conflictCert (AyBUIPConj agreement learned)
      certH
      (ay_buip_conj_intro agreement learned agreementH learnedH)

theorem ay_buip_accepted_analysis_cert
    (conflictCert : Prop) (agreement : Prop) (learned : Prop) :
    AyBUIPAcceptedAnalysis conflictCert agreement learned ->
    conflictCert :=
  fun accepted =>
    ay_buip_conj_left conflictCert (AyBUIPConj agreement learned)
      accepted

theorem ay_buip_accepted_analysis_agreement
    (conflictCert : Prop) (agreement : Prop) (learned : Prop) :
    AyBUIPAcceptedAnalysis conflictCert agreement learned -> agreement :=
  fun accepted =>
    ay_buip_conj_left agreement learned
      (ay_buip_conj_right conflictCert
        (AyBUIPConj agreement learned)
        accepted)

theorem ay_buip_accepted_analysis_learned
    (conflictCert : Prop) (agreement : Prop) (learned : Prop) :
    AyBUIPAcceptedAnalysis conflictCert agreement learned -> learned :=
  fun accepted =>
    ay_buip_conj_right agreement learned
      (ay_buip_conj_right conflictCert
        (AyBUIPConj agreement learned)
        accepted)

theorem ay_buip_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBUIPPublicReport (AyBUIPOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_buip_conj_intro (AyBUIPOutcome model conflict) formula
      (ay_buip_disj_left model conflict modelH)
      formulaH

theorem ay_buip_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBUIPPublicReport (AyBUIPOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_buip_conj_intro (AyBUIPOutcome model conflict) formula
      (ay_buip_disj_right model conflict conflictH)
      formulaH

theorem ay_buip_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBUIPAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_buip_conj_intro evidence public evidenceH publicH

theorem ay_buip_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBUIPAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_buip_conj_left evidence public report

theorem ay_buip_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBUIPAcceptedReport evidence public -> public :=
  fun report =>
    ay_buip_conj_right evidence public report

theorem ay_buip_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBUIPNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_buip_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_buip_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBUIPNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_buip_conj_left fallbackPublic diagnostic noClaim

theorem ay_buip_malformed_graph_no_claim
    (malformedGraph : Prop) (fallbackPublic : Prop) :
    malformedGraph ->
    fallbackPublic ->
    AyBUIPNoClaim malformedGraph fallbackPublic :=
  fun malformedH fallbackH =>
    ay_buip_no_claim_intro malformedGraph fallbackPublic
      malformedH fallbackH

theorem ay_buip_cut_mismatch_no_claim
    (cutMismatch : Prop) (fallbackPublic : Prop) :
    cutMismatch ->
    fallbackPublic ->
    AyBUIPNoClaim cutMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_buip_no_claim_intro cutMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_buip_derivation_mismatch_no_claim
    (derivationMismatch : Prop) (fallbackPublic : Prop) :
    derivationMismatch ->
    fallbackPublic ->
    AyBUIPNoClaim derivationMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_buip_no_claim_intro derivationMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_buip_epoch_mismatch_no_claim
    (epochMismatch : Prop) (fallbackPublic : Prop) :
    epochMismatch ->
    fallbackPublic ->
    AyBUIPNoClaim epochMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_buip_no_claim_intro epochMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_buip_checker_mismatch_no_claim
    (checkerMismatch : Prop) (fallbackPublic : Prop) :
    checkerMismatch ->
    fallbackPublic ->
    AyBUIPNoClaim checkerMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_buip_no_claim_intro checkerMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_buip_malformed_cannot_justify_learned
    (malformedAnalysis : Prop) (fallbackPublic : Prop) :
    malformedAnalysis ->
    fallbackPublic ->
    AyBUIPNoClaim malformedAnalysis fallbackPublic :=
  fun malformedH fallbackH =>
    ay_buip_no_claim_intro malformedAnalysis fallbackPublic
      malformedH fallbackH

theorem ay_buip_accepted_analysis_guides_sat
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop)
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget ->
    model ->
    formula ->
    AyBUIPAcceptedReport
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula) :=
  fun cert agreement learned modelH formulaH =>
    ay_buip_accepted_report_intro
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula)
      (ay_buip_accepted_analysis_intro
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget)
        cert agreement learned)
      (ay_buip_public_sat_report model conflict formula modelH formulaH)

theorem ay_buip_accepted_analysis_guides_unsat
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop)
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBUIPConflictCert implicationGraph trailPrefix cutWitness
      clauseDerivation databaseEpoch checkerReplay ->
    AyBUIPAgreement graphMatch trailMatch cutMatch
      derivationMatch epochMatch checkerMatch ->
    AyBUIPLearnedClause learnedClause assertingLevel backjumpTarget ->
    conflict ->
    formula ->
    AyBUIPAcceptedReport
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula) :=
  fun cert agreement learned conflictH formulaH =>
    ay_buip_accepted_report_intro
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula)
      (ay_buip_accepted_analysis_intro
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget)
        cert agreement learned)
      (ay_buip_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_buip_accepted_conflict_report_soundness
    (implicationGraph : Prop) (trailPrefix : Prop)
    (cutWitness : Prop) (clauseDerivation : Prop)
    (databaseEpoch : Prop) (checkerReplay : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (cutMatch : Prop) (derivationMatch : Prop)
    (epochMatch : Prop) (checkerMatch : Prop)
    (learnedClause : Prop) (assertingLevel : Prop)
    (backjumpTarget : Prop) (formula : Prop)
    (model : Prop) (conflict : Prop) :
    AyBUIPAcceptedReport
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula) ->
    AyBUIPPublicReport (AyBUIPOutcome model conflict) formula :=
  fun report =>
    ay_buip_accepted_report_public
      (AyBUIPAcceptedAnalysis
        (AyBUIPConflictCert implicationGraph trailPrefix cutWitness
          clauseDerivation databaseEpoch checkerReplay)
        (AyBUIPAgreement graphMatch trailMatch cutMatch
          derivationMatch epochMatch checkerMatch)
        (AyBUIPLearnedClause learnedClause assertingLevel
          backjumpTarget))
      (AyBUIPPublicReport (AyBUIPOutcome model conflict) formula)
      report

theorem ay_buip_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBUIPNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_buip_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
