-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded implication graph replay soundness skeleton for ay SAT solving.
-- Implication graph snapshots used for conflict analysis and branching are
-- admissible only when antecedent clauses, assignment trail, decision levels,
-- learned-clause ids, deterministic replay, dependency guard, and public
-- soundness guard agree.

def ay_bigr_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bigr_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bigr_equisat (before : Prop) (after : Prop) :=
  ay_bigr_conj (before -> after) (after -> before)

def ay_bigr_graph_evidence
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :=
  ay_bigr_conj antecedentClauses
    (ay_bigr_conj assignmentTrail
      (ay_bigr_conj decisionLevels
        (ay_bigr_conj learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard)))))

def ay_bigr_agreement
    (antecedentMatch : Prop) (trailMatch : Prop)
    (levelMatch : Prop) (learnedIdMatch : Prop)
    (replayAccepted : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :=
  ay_bigr_conj antecedentMatch
    (ay_bigr_conj trailMatch
      (ay_bigr_conj levelMatch
        (ay_bigr_conj learnedIdMatch
          (ay_bigr_conj replayAccepted
            (ay_bigr_conj dependencyMatch publicGuardMatch)))))

def ay_bigr_accepted_replay
    (graph : Prop) (agreement : Prop) (analysisHint : Prop) :=
  ay_bigr_conj graph (ay_bigr_conj agreement analysisHint)

def ay_bigr_outcome (model : Prop) (conflict : Prop) :=
  ay_bigr_disj model conflict

def ay_bigr_public_report (outcome : Prop) (formula : Prop) :=
  ay_bigr_conj outcome formula

def ay_bigr_accepted_report (replay : Prop) (public : Prop) :=
  ay_bigr_conj replay public

def ay_bigr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_bigr_conj fallbackPublic diagnostic

theorem ay_bigr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bigr_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bigr_conj_left
    (left : Prop) (right : Prop) :
    ay_bigr_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bigr_conj_right
    (left : Prop) (right : Prop) :
    ay_bigr_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bigr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bigr_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bigr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bigr_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bigr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_bigr_equisat before after :=
  fun forward backward =>
    ay_bigr_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bigr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_bigr_equisat before after -> before -> after :=
  fun equisat =>
    ay_bigr_conj_left (before -> after) (after -> before) equisat

theorem ay_bigr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_bigr_equisat before after -> after -> before :=
  fun equisat =>
    ay_bigr_conj_right (before -> after) (after -> before) equisat

theorem ay_bigr_graph_evidence_intro
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    antecedentClauses ->
    assignmentTrail ->
    decisionLevels ->
    learnedClauseIds ->
    deterministicReplay ->
    dependencyGuard ->
    publicSoundnessGuard ->
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard :=
  fun antecedentH trailH levelH learnedH replayH dependencyH publicH =>
    ay_bigr_conj_intro antecedentClauses
      (ay_bigr_conj assignmentTrail
        (ay_bigr_conj decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)))))
      antecedentH
      (ay_bigr_conj_intro assignmentTrail
        (ay_bigr_conj decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
        trailH
        (ay_bigr_conj_intro decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
          levelH
          (ay_bigr_conj_intro learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard))
            learnedH
            (ay_bigr_conj_intro deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)
              replayH
              (ay_bigr_conj_intro dependencyGuard publicSoundnessGuard
                dependencyH publicH)))))

theorem ay_bigr_graph_evidence_antecedents
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    antecedentClauses :=
  fun evidence =>
    ay_bigr_conj_left antecedentClauses
      (ay_bigr_conj assignmentTrail
        (ay_bigr_conj decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bigr_graph_evidence_tail
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    ay_bigr_conj assignmentTrail
      (ay_bigr_conj decisionLevels
        (ay_bigr_conj learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard)))) :=
  fun evidence =>
    ay_bigr_conj_right antecedentClauses
      (ay_bigr_conj assignmentTrail
        (ay_bigr_conj decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bigr_graph_evidence_trail
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    assignmentTrail :=
  fun evidence =>
    ay_bigr_conj_left assignmentTrail
      (ay_bigr_conj decisionLevels
        (ay_bigr_conj learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
      (ay_bigr_graph_evidence_tail antecedentClauses assignmentTrail
        decisionLevels learnedClauseIds deterministicReplay dependencyGuard
        publicSoundnessGuard evidence)

theorem ay_bigr_graph_evidence_levels
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    decisionLevels :=
  fun evidence =>
    ay_bigr_conj_left decisionLevels
      (ay_bigr_conj learnedClauseIds
        (ay_bigr_conj deterministicReplay
          (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
      (ay_bigr_conj_right assignmentTrail
        (ay_bigr_conj decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
        (ay_bigr_graph_evidence_tail antecedentClauses assignmentTrail
          decisionLevels learnedClauseIds deterministicReplay dependencyGuard
          publicSoundnessGuard evidence))

theorem ay_bigr_graph_evidence_learned_ids
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    learnedClauseIds :=
  fun evidence =>
    ay_bigr_conj_left learnedClauseIds
      (ay_bigr_conj deterministicReplay
        (ay_bigr_conj dependencyGuard publicSoundnessGuard))
      (ay_bigr_conj_right decisionLevels
        (ay_bigr_conj learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
        (ay_bigr_conj_right assignmentTrail
          (ay_bigr_conj decisionLevels
            (ay_bigr_conj learnedClauseIds
              (ay_bigr_conj deterministicReplay
                (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
          (ay_bigr_graph_evidence_tail antecedentClauses assignmentTrail
            decisionLevels learnedClauseIds deterministicReplay
            dependencyGuard publicSoundnessGuard evidence)))

theorem ay_bigr_graph_evidence_replay
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    deterministicReplay :=
  fun evidence =>
    ay_bigr_conj_left deterministicReplay
      (ay_bigr_conj dependencyGuard publicSoundnessGuard)
      (ay_bigr_conj_right learnedClauseIds
        (ay_bigr_conj deterministicReplay
          (ay_bigr_conj dependencyGuard publicSoundnessGuard))
        (ay_bigr_conj_right decisionLevels
          (ay_bigr_conj learnedClauseIds
            (ay_bigr_conj deterministicReplay
              (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
          (ay_bigr_conj_right assignmentTrail
            (ay_bigr_conj decisionLevels
              (ay_bigr_conj learnedClauseIds
                (ay_bigr_conj deterministicReplay
                  (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
            (ay_bigr_graph_evidence_tail antecedentClauses assignmentTrail
              decisionLevels learnedClauseIds deterministicReplay
              dependencyGuard publicSoundnessGuard evidence))))

theorem ay_bigr_graph_evidence_dependency
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    dependencyGuard :=
  fun evidence =>
    ay_bigr_conj_left dependencyGuard publicSoundnessGuard
      (ay_bigr_conj_right deterministicReplay
        (ay_bigr_conj dependencyGuard publicSoundnessGuard)
        (ay_bigr_conj_right learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard))
          (ay_bigr_conj_right decisionLevels
            (ay_bigr_conj learnedClauseIds
              (ay_bigr_conj deterministicReplay
                (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
            (ay_bigr_conj_right assignmentTrail
              (ay_bigr_conj decisionLevels
                (ay_bigr_conj learnedClauseIds
                  (ay_bigr_conj deterministicReplay
                    (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
              (ay_bigr_graph_evidence_tail antecedentClauses
                assignmentTrail decisionLevels learnedClauseIds
                deterministicReplay dependencyGuard publicSoundnessGuard
                evidence)))))

theorem ay_bigr_graph_evidence_public
    (antecedentClauses : Prop) (assignmentTrail : Prop)
    (decisionLevels : Prop) (learnedClauseIds : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    ay_bigr_graph_evidence antecedentClauses assignmentTrail
      decisionLevels learnedClauseIds deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_bigr_conj_right dependencyGuard publicSoundnessGuard
      (ay_bigr_conj_right deterministicReplay
        (ay_bigr_conj dependencyGuard publicSoundnessGuard)
        (ay_bigr_conj_right learnedClauseIds
          (ay_bigr_conj deterministicReplay
            (ay_bigr_conj dependencyGuard publicSoundnessGuard))
          (ay_bigr_conj_right decisionLevels
            (ay_bigr_conj learnedClauseIds
              (ay_bigr_conj deterministicReplay
                (ay_bigr_conj dependencyGuard publicSoundnessGuard)))
            (ay_bigr_conj_right assignmentTrail
              (ay_bigr_conj decisionLevels
                (ay_bigr_conj learnedClauseIds
                  (ay_bigr_conj deterministicReplay
                    (ay_bigr_conj dependencyGuard publicSoundnessGuard))))
              (ay_bigr_graph_evidence_tail antecedentClauses
                assignmentTrail decisionLevels learnedClauseIds
                deterministicReplay dependencyGuard publicSoundnessGuard
                evidence)))))

theorem ay_bigr_agreement_intro
    (antecedentMatch : Prop) (trailMatch : Prop)
    (levelMatch : Prop) (learnedIdMatch : Prop)
    (replayAccepted : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    antecedentMatch ->
    trailMatch ->
    levelMatch ->
    learnedIdMatch ->
    replayAccepted ->
    dependencyMatch ->
    publicGuardMatch ->
    ay_bigr_agreement antecedentMatch trailMatch levelMatch
      learnedIdMatch replayAccepted dependencyMatch publicGuardMatch :=
  fun antecedentH trailH levelH learnedH replayH dependencyH publicH =>
    ay_bigr_conj_intro antecedentMatch
      (ay_bigr_conj trailMatch
        (ay_bigr_conj levelMatch
          (ay_bigr_conj learnedIdMatch
            (ay_bigr_conj replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch)))))
      antecedentH
      (ay_bigr_conj_intro trailMatch
        (ay_bigr_conj levelMatch
          (ay_bigr_conj learnedIdMatch
            (ay_bigr_conj replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch))))
        trailH
        (ay_bigr_conj_intro levelMatch
          (ay_bigr_conj learnedIdMatch
            (ay_bigr_conj replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch)))
          levelH
          (ay_bigr_conj_intro learnedIdMatch
            (ay_bigr_conj replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch))
            learnedH
            (ay_bigr_conj_intro replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch)
              replayH
              (ay_bigr_conj_intro dependencyMatch publicGuardMatch
                dependencyH publicH)))))

theorem ay_bigr_agreement_antecedent
    (antecedentMatch : Prop) (trailMatch : Prop)
    (levelMatch : Prop) (learnedIdMatch : Prop)
    (replayAccepted : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    ay_bigr_agreement antecedentMatch trailMatch levelMatch
      learnedIdMatch replayAccepted dependencyMatch publicGuardMatch ->
    antecedentMatch :=
  fun agreement =>
    ay_bigr_conj_left antecedentMatch
      (ay_bigr_conj trailMatch
        (ay_bigr_conj levelMatch
          (ay_bigr_conj learnedIdMatch
            (ay_bigr_conj replayAccepted
              (ay_bigr_conj dependencyMatch publicGuardMatch)))))
      agreement

theorem ay_bigr_accepted_replay_intro
    (graph : Prop) (agreement : Prop) (analysisHint : Prop) :
    graph ->
    agreement ->
    analysisHint ->
    ay_bigr_accepted_replay graph agreement analysisHint :=
  fun graphH agreementH hintH =>
    ay_bigr_conj_intro graph (ay_bigr_conj agreement analysisHint)
      graphH
      (ay_bigr_conj_intro agreement analysisHint agreementH hintH)

theorem ay_bigr_accepted_replay_graph
    (graph : Prop) (agreement : Prop) (analysisHint : Prop) :
    ay_bigr_accepted_replay graph agreement analysisHint -> graph :=
  fun accepted =>
    ay_bigr_conj_left graph (ay_bigr_conj agreement analysisHint)
      accepted

theorem ay_bigr_accepted_replay_agreement
    (graph : Prop) (agreement : Prop) (analysisHint : Prop) :
    ay_bigr_accepted_replay graph agreement analysisHint -> agreement :=
  fun accepted =>
    ay_bigr_conj_left agreement analysisHint
      (ay_bigr_conj_right graph (ay_bigr_conj agreement analysisHint)
        accepted)

theorem ay_bigr_accepted_replay_hint
    (graph : Prop) (agreement : Prop) (analysisHint : Prop) :
    ay_bigr_accepted_replay graph agreement analysisHint ->
    analysisHint :=
  fun accepted =>
    ay_bigr_conj_right agreement analysisHint
      (ay_bigr_conj_right graph (ay_bigr_conj agreement analysisHint)
        accepted)

theorem ay_bigr_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_bigr_public_report (ay_bigr_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bigr_conj_intro (ay_bigr_outcome model conflict) formula
      (ay_bigr_disj_left model conflict modelH)
      formulaH

theorem ay_bigr_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_bigr_public_report (ay_bigr_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bigr_conj_intro (ay_bigr_outcome model conflict) formula
      (ay_bigr_disj_right model conflict conflictH)
      formulaH

theorem ay_bigr_accepted_report_intro
    (replay : Prop) (public : Prop) :
    replay -> public -> ay_bigr_accepted_report replay public :=
  fun replayH publicH =>
    ay_bigr_conj_intro replay public replayH publicH

theorem ay_bigr_accepted_report_public
    (replay : Prop) (public : Prop) :
    ay_bigr_accepted_report replay public -> public :=
  fun report =>
    ay_bigr_conj_right replay public report

theorem ay_bigr_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_bigr_no_claim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bigr_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bigr_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bigr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bigr_conj_left fallbackPublic diagnostic noClaim

theorem ay_bigr_stale_antecedent_no_claim
    (staleAntecedent : Prop) (fallbackPublic : Prop) :
    staleAntecedent ->
    fallbackPublic ->
    ay_bigr_no_claim staleAntecedent fallbackPublic :=
  fun staleH fallbackH =>
    ay_bigr_no_claim_intro staleAntecedent fallbackPublic
      staleH fallbackH

theorem ay_bigr_trail_mismatch_no_claim
    (trailMismatch : Prop) (fallbackPublic : Prop) :
    trailMismatch ->
    fallbackPublic ->
    ay_bigr_no_claim trailMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bigr_no_claim_intro trailMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bigr_level_mismatch_no_claim
    (levelMismatch : Prop) (fallbackPublic : Prop) :
    levelMismatch ->
    fallbackPublic ->
    ay_bigr_no_claim levelMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bigr_no_claim_intro levelMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bigr_missing_learned_id_no_claim
    (missingLearnedId : Prop) (fallbackPublic : Prop) :
    missingLearnedId ->
    fallbackPublic ->
    ay_bigr_no_claim missingLearnedId fallbackPublic :=
  fun missingH fallbackH =>
    ay_bigr_no_claim_intro missingLearnedId fallbackPublic
      missingH fallbackH

theorem ay_bigr_replay_rejection_no_claim
    (replayRejected : Prop) (fallbackPublic : Prop) :
    replayRejected ->
    fallbackPublic ->
    ay_bigr_no_claim replayRejected fallbackPublic :=
  fun rejectedH fallbackH =>
    ay_bigr_no_claim_intro replayRejected fallbackPublic
      rejectedH fallbackH

theorem ay_bigr_bad_graph_cannot_publish
    (badGraph : Prop) (fallbackPublic : Prop) :
    badGraph ->
    fallbackPublic ->
    ay_bigr_no_claim badGraph fallbackPublic :=
  fun badH fallbackH =>
    ay_bigr_no_claim_intro badGraph fallbackPublic badH fallbackH

theorem ay_bigr_accepted_replay_guides_sat
    (graph : Prop) (agreement : Prop) (analysisHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    graph ->
    agreement ->
    analysisHint ->
    model ->
    formula ->
    ay_bigr_accepted_report
      (ay_bigr_accepted_replay graph agreement analysisHint)
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula) :=
  fun graphH agreementH hintH modelH formulaH =>
    ay_bigr_accepted_report_intro
      (ay_bigr_accepted_replay graph agreement analysisHint)
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula)
      (ay_bigr_accepted_replay_intro graph agreement analysisHint
        graphH agreementH hintH)
      (ay_bigr_public_sat_report model conflict formula modelH formulaH)

theorem ay_bigr_accepted_replay_guides_unsat
    (graph : Prop) (agreement : Prop) (analysisHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    graph ->
    agreement ->
    analysisHint ->
    conflict ->
    formula ->
    ay_bigr_accepted_report
      (ay_bigr_accepted_replay graph agreement analysisHint)
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula) :=
  fun graphH agreementH hintH conflictH formulaH =>
    ay_bigr_accepted_report_intro
      (ay_bigr_accepted_replay graph agreement analysisHint)
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula)
      (ay_bigr_accepted_replay_intro graph agreement analysisHint
        graphH agreementH hintH)
      (ay_bigr_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bigr_accepted_replay_report_soundness
    (replay : Prop) (formula : Prop) (model : Prop) (conflict : Prop) :
    ay_bigr_accepted_report replay
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula) ->
    ay_bigr_public_report (ay_bigr_outcome model conflict) formula :=
  fun report =>
    ay_bigr_accepted_report_public replay
      (ay_bigr_public_report (ay_bigr_outcome model conflict) formula)
      report

theorem ay_bigr_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_bigr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bigr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
