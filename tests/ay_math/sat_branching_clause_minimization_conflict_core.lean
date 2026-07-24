-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded learned-clause minimization conflict soundness skeleton for ay SAT
-- solving. Minimizing learned clauses after conflict analysis is admissible
-- only when removed literals have redundancy witnesses, implication graph and
-- trail evidence agree, and checker replay validates the minimized clause.
-- Bad minimization falls back to no-claim/recompute and cannot justify
-- propagation or public UNSAT.

def AyBCMCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBCMCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBCMCEquisat (before : Prop) (after : Prop) :=
  AyBCMCConj (before -> after) (after -> before)

def AyBCMCMinimizationCert
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :=
  AyBCMCConj originalClause
    (AyBCMCConj minimizedClause
      (AyBCMCConj removedLiterals
        (AyBCMCConj redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay)))))

def AyBCMCAgreement
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :=
  AyBCMCConj redundancyMatch
    (AyBCMCConj graphMatch (AyBCMCConj trailMatch checkerMatch))

def AyBCMCAcceptedMinimization
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :=
  AyBCMCConj certificate (AyBCMCConj agreement propagation)

def AyBCMCOutcome (model : Prop) (conflict : Prop) :=
  AyBCMCDisj model conflict

def AyBCMCPublicReport (outcome : Prop) (formula : Prop) :=
  AyBCMCConj outcome formula

def AyBCMCAcceptedReport (evidence : Prop) (public : Prop) :=
  AyBCMCConj evidence public

def AyBCMCNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBCMCConj fallbackPublic diagnostic

theorem ay_bcmc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBCMCConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcmc_conj_left
    (left : Prop) (right : Prop) :
    AyBCMCConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcmc_conj_right
    (left : Prop) (right : Prop) :
    AyBCMCConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcmc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBCMCDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcmc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBCMCDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcmc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBCMCEquisat before after :=
  fun forward backward =>
    ay_bcmc_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcmc_equisat_forward
    (before : Prop) (after : Prop) :
    AyBCMCEquisat before after -> before -> after :=
  fun equisat =>
    ay_bcmc_conj_left (before -> after) (after -> before) equisat

theorem ay_bcmc_equisat_backward
    (before : Prop) (after : Prop) :
    AyBCMCEquisat before after -> after -> before :=
  fun equisat =>
    ay_bcmc_conj_right (before -> after) (after -> before) equisat

theorem ay_bcmc_minimization_cert_intro
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    originalClause ->
    minimizedClause ->
    removedLiterals ->
    redundancyWitness ->
    implicationGraph ->
    trailEvidence ->
    checkerReplay ->
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay :=
  fun originalH minimizedH removedH redundancyH graphH trailH checkerH =>
    ay_bcmc_conj_intro originalClause
      (AyBCMCConj minimizedClause
        (AyBCMCConj removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)))))
      originalH
      (ay_bcmc_conj_intro minimizedClause
        (AyBCMCConj removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay))))
        minimizedH
        (ay_bcmc_conj_intro removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)))
          removedH
          (ay_bcmc_conj_intro redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay))
            redundancyH
            (ay_bcmc_conj_intro implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)
              graphH
              (ay_bcmc_conj_intro trailEvidence checkerReplay
                trailH checkerH)))))

theorem ay_bcmc_minimization_cert_original
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    originalClause :=
  fun cert =>
    ay_bcmc_conj_left originalClause
      (AyBCMCConj minimizedClause
        (AyBCMCConj removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)))))
      cert

theorem ay_bcmc_minimization_cert_tail
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    AyBCMCConj minimizedClause
      (AyBCMCConj removedLiterals
        (AyBCMCConj redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay)))) :=
  fun cert =>
    ay_bcmc_conj_right originalClause
      (AyBCMCConj minimizedClause
        (AyBCMCConj removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)))))
      cert

theorem ay_bcmc_minimization_cert_minimized
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    minimizedClause :=
  fun cert =>
    ay_bcmc_conj_left minimizedClause
      (AyBCMCConj removedLiterals
        (AyBCMCConj redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay))))
      (ay_bcmc_minimization_cert_tail originalClause minimizedClause
        removedLiterals redundancyWitness implicationGraph trailEvidence
        checkerReplay cert)

theorem ay_bcmc_minimization_cert_removed
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    removedLiterals :=
  fun cert =>
    ay_bcmc_conj_left removedLiterals
      (AyBCMCConj redundancyWitness
        (AyBCMCConj implicationGraph
          (AyBCMCConj trailEvidence checkerReplay)))
      (ay_bcmc_conj_right minimizedClause
        (AyBCMCConj removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay))))
        (ay_bcmc_minimization_cert_tail originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay cert))

theorem ay_bcmc_minimization_cert_redundancy
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    redundancyWitness :=
  fun cert =>
    ay_bcmc_conj_left redundancyWitness
      (AyBCMCConj implicationGraph
        (AyBCMCConj trailEvidence checkerReplay))
      (ay_bcmc_conj_right removedLiterals
        (AyBCMCConj redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay)))
        (ay_bcmc_conj_right minimizedClause
          (AyBCMCConj removedLiterals
            (AyBCMCConj redundancyWitness
              (AyBCMCConj implicationGraph
                (AyBCMCConj trailEvidence checkerReplay))))
          (ay_bcmc_minimization_cert_tail originalClause minimizedClause
            removedLiterals redundancyWitness implicationGraph trailEvidence
            checkerReplay cert)))

theorem ay_bcmc_minimization_cert_graph
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    implicationGraph :=
  fun cert =>
    ay_bcmc_conj_left implicationGraph
      (AyBCMCConj trailEvidence checkerReplay)
      (ay_bcmc_conj_right redundancyWitness
        (AyBCMCConj implicationGraph
          (AyBCMCConj trailEvidence checkerReplay))
        (ay_bcmc_conj_right removedLiterals
          (AyBCMCConj redundancyWitness
            (AyBCMCConj implicationGraph
              (AyBCMCConj trailEvidence checkerReplay)))
          (ay_bcmc_conj_right minimizedClause
            (AyBCMCConj removedLiterals
              (AyBCMCConj redundancyWitness
                (AyBCMCConj implicationGraph
                  (AyBCMCConj trailEvidence checkerReplay))))
            (ay_bcmc_minimization_cert_tail originalClause minimizedClause
              removedLiterals redundancyWitness implicationGraph
              trailEvidence checkerReplay cert))))

theorem ay_bcmc_minimization_cert_trail
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    trailEvidence :=
  fun cert =>
    ay_bcmc_conj_left trailEvidence checkerReplay
      (ay_bcmc_conj_right implicationGraph
        (AyBCMCConj trailEvidence checkerReplay)
        (ay_bcmc_conj_right redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay))
          (ay_bcmc_conj_right removedLiterals
            (AyBCMCConj redundancyWitness
              (AyBCMCConj implicationGraph
                (AyBCMCConj trailEvidence checkerReplay)))
            (ay_bcmc_conj_right minimizedClause
              (AyBCMCConj removedLiterals
                (AyBCMCConj redundancyWitness
                  (AyBCMCConj implicationGraph
                    (AyBCMCConj trailEvidence checkerReplay))))
              (ay_bcmc_minimization_cert_tail originalClause
                minimizedClause removedLiterals redundancyWitness
                implicationGraph trailEvidence checkerReplay cert)))))

theorem ay_bcmc_minimization_cert_checker
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    checkerReplay :=
  fun cert =>
    ay_bcmc_conj_right trailEvidence checkerReplay
      (ay_bcmc_conj_right implicationGraph
        (AyBCMCConj trailEvidence checkerReplay)
        (ay_bcmc_conj_right redundancyWitness
          (AyBCMCConj implicationGraph
            (AyBCMCConj trailEvidence checkerReplay))
          (ay_bcmc_conj_right removedLiterals
            (AyBCMCConj redundancyWitness
              (AyBCMCConj implicationGraph
                (AyBCMCConj trailEvidence checkerReplay)))
            (ay_bcmc_conj_right minimizedClause
              (AyBCMCConj removedLiterals
                (AyBCMCConj redundancyWitness
                  (AyBCMCConj implicationGraph
                    (AyBCMCConj trailEvidence checkerReplay))))
              (ay_bcmc_minimization_cert_tail originalClause
                minimizedClause removedLiterals redundancyWitness
                implicationGraph trailEvidence checkerReplay cert)))))

theorem ay_bcmc_agreement_intro
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    redundancyMatch ->
    graphMatch ->
    trailMatch ->
    checkerMatch ->
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch :=
  fun redundancyH graphH trailH checkerH =>
    ay_bcmc_conj_intro redundancyMatch
      (AyBCMCConj graphMatch (AyBCMCConj trailMatch checkerMatch))
      redundancyH
      (ay_bcmc_conj_intro graphMatch
        (AyBCMCConj trailMatch checkerMatch)
        graphH
        (ay_bcmc_conj_intro trailMatch checkerMatch
          trailH checkerH))

theorem ay_bcmc_agreement_redundancy
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch ->
    redundancyMatch :=
  fun agreement =>
    ay_bcmc_conj_left redundancyMatch
      (AyBCMCConj graphMatch (AyBCMCConj trailMatch checkerMatch))
      agreement

theorem ay_bcmc_agreement_tail
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch ->
    AyBCMCConj graphMatch (AyBCMCConj trailMatch checkerMatch) :=
  fun agreement =>
    ay_bcmc_conj_right redundancyMatch
      (AyBCMCConj graphMatch (AyBCMCConj trailMatch checkerMatch))
      agreement

theorem ay_bcmc_agreement_graph
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch ->
    graphMatch :=
  fun agreement =>
    ay_bcmc_conj_left graphMatch (AyBCMCConj trailMatch checkerMatch)
      (ay_bcmc_agreement_tail redundancyMatch graphMatch trailMatch
        checkerMatch agreement)

theorem ay_bcmc_agreement_trail
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch ->
    trailMatch :=
  fun agreement =>
    ay_bcmc_conj_left trailMatch checkerMatch
      (ay_bcmc_conj_right graphMatch
        (AyBCMCConj trailMatch checkerMatch)
        (ay_bcmc_agreement_tail redundancyMatch graphMatch trailMatch
          checkerMatch agreement))

theorem ay_bcmc_agreement_checker
    (redundancyMatch : Prop) (graphMatch : Prop)
    (trailMatch : Prop) (checkerMatch : Prop) :
    AyBCMCAgreement redundancyMatch graphMatch
      trailMatch checkerMatch ->
    checkerMatch :=
  fun agreement =>
    ay_bcmc_conj_right trailMatch checkerMatch
      (ay_bcmc_conj_right graphMatch
        (AyBCMCConj trailMatch checkerMatch)
        (ay_bcmc_agreement_tail redundancyMatch graphMatch trailMatch
          checkerMatch agreement))

theorem ay_bcmc_accepted_minimization_intro
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    certificate ->
    agreement ->
    propagation ->
    AyBCMCAcceptedMinimization certificate agreement propagation :=
  fun certH agreementH propagationH =>
    ay_bcmc_conj_intro certificate
      (AyBCMCConj agreement propagation)
      certH
      (ay_bcmc_conj_intro agreement propagation
        agreementH propagationH)

theorem ay_bcmc_accepted_minimization_certificate
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBCMCAcceptedMinimization certificate agreement propagation ->
    certificate :=
  fun accepted =>
    ay_bcmc_conj_left certificate
      (AyBCMCConj agreement propagation)
      accepted

theorem ay_bcmc_accepted_minimization_agreement
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBCMCAcceptedMinimization certificate agreement propagation ->
    agreement :=
  fun accepted =>
    ay_bcmc_conj_left agreement propagation
      (ay_bcmc_conj_right certificate
        (AyBCMCConj agreement propagation)
        accepted)

theorem ay_bcmc_accepted_minimization_propagation
    (certificate : Prop) (agreement : Prop) (propagation : Prop) :
    AyBCMCAcceptedMinimization certificate agreement propagation ->
    propagation :=
  fun accepted =>
    ay_bcmc_conj_right agreement propagation
      (ay_bcmc_conj_right certificate
        (AyBCMCConj agreement propagation)
        accepted)

theorem ay_bcmc_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBCMCPublicReport (AyBCMCOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcmc_conj_intro (AyBCMCOutcome model conflict) formula
      (ay_bcmc_disj_left model conflict modelH)
      formulaH

theorem ay_bcmc_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBCMCPublicReport (AyBCMCOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcmc_conj_intro (AyBCMCOutcome model conflict) formula
      (ay_bcmc_disj_right model conflict conflictH)
      formulaH

theorem ay_bcmc_accepted_report_intro
    (evidence : Prop) (public : Prop) :
    evidence -> public -> AyBCMCAcceptedReport evidence public :=
  fun evidenceH publicH =>
    ay_bcmc_conj_intro evidence public evidenceH publicH

theorem ay_bcmc_accepted_report_evidence
    (evidence : Prop) (public : Prop) :
    AyBCMCAcceptedReport evidence public -> evidence :=
  fun report =>
    ay_bcmc_conj_left evidence public report

theorem ay_bcmc_accepted_report_public
    (evidence : Prop) (public : Prop) :
    AyBCMCAcceptedReport evidence public -> public :=
  fun report =>
    ay_bcmc_conj_right evidence public report

theorem ay_bcmc_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBCMCNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcmc_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcmc_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCMCNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcmc_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcmc_bad_redundancy_no_claim
    (badRedundancy : Prop) (fallbackPublic : Prop) :
    badRedundancy ->
    fallbackPublic ->
    AyBCMCNoClaim badRedundancy fallbackPublic :=
  fun badH fallbackH =>
    ay_bcmc_no_claim_intro badRedundancy fallbackPublic badH fallbackH

theorem ay_bcmc_graph_trail_mismatch_no_claim
    (mismatch : Prop) (fallbackPublic : Prop) :
    mismatch ->
    fallbackPublic ->
    AyBCMCNoClaim mismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcmc_no_claim_intro mismatch fallbackPublic mismatchH fallbackH

theorem ay_bcmc_checker_mismatch_no_claim
    (checkerMismatch : Prop) (fallbackPublic : Prop) :
    checkerMismatch ->
    fallbackPublic ->
    AyBCMCNoClaim checkerMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcmc_no_claim_intro checkerMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcmc_bad_minimization_cannot_justify_propagation
    (badMinimization : Prop) (fallbackPublic : Prop) :
    badMinimization ->
    fallbackPublic ->
    AyBCMCNoClaim badMinimization fallbackPublic :=
  fun badH fallbackH =>
    ay_bcmc_no_claim_intro badMinimization fallbackPublic
      badH fallbackH

theorem ay_bcmc_accepted_minimization_guides_sat
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) (redundancyMatch : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (propagation : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    AyBCMCAgreement redundancyMatch graphMatch trailMatch checkerMatch ->
    propagation ->
    model ->
    formula ->
    AyBCMCAcceptedReport
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula) :=
  fun cert agreement propagationH modelH formulaH =>
    ay_bcmc_accepted_report_intro
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula)
      (ay_bcmc_accepted_minimization_intro
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation
        cert agreement propagationH)
      (ay_bcmc_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcmc_accepted_minimization_guides_unsat
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) (redundancyMatch : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (propagation : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBCMCMinimizationCert originalClause minimizedClause
      removedLiterals redundancyWitness implicationGraph trailEvidence
      checkerReplay ->
    AyBCMCAgreement redundancyMatch graphMatch trailMatch checkerMatch ->
    propagation ->
    conflict ->
    formula ->
    AyBCMCAcceptedReport
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula) :=
  fun cert agreement propagationH conflictH formulaH =>
    ay_bcmc_accepted_report_intro
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula)
      (ay_bcmc_accepted_minimization_intro
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation
        cert agreement propagationH)
      (ay_bcmc_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bcmc_accepted_minimization_report_soundness
    (originalClause : Prop) (minimizedClause : Prop)
    (removedLiterals : Prop) (redundancyWitness : Prop)
    (implicationGraph : Prop) (trailEvidence : Prop)
    (checkerReplay : Prop) (redundancyMatch : Prop)
    (graphMatch : Prop) (trailMatch : Prop)
    (checkerMatch : Prop) (propagation : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBCMCAcceptedReport
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula) ->
    AyBCMCPublicReport (AyBCMCOutcome model conflict) formula :=
  fun report =>
    ay_bcmc_accepted_report_public
      (AyBCMCAcceptedMinimization
        (AyBCMCMinimizationCert originalClause minimizedClause
          removedLiterals redundancyWitness implicationGraph trailEvidence
          checkerReplay)
        (AyBCMCAgreement redundancyMatch graphMatch trailMatch
          checkerMatch)
        propagation)
      (AyBCMCPublicReport (AyBCMCOutcome model conflict) formula)
      report

theorem ay_bcmc_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCMCNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcmc_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
