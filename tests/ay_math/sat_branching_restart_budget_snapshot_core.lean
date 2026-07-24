-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded restart-budget snapshot soundness skeleton for ay SAT solving.
-- Learned restart and branching schedule changes are admissible heuristics
-- only when conflict budgets, propagation budgets, decision-level snapshots,
-- LBD/activity replay, fallback baseline, original instance, and solver build
-- all agree.

def ay_brbs_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brbs_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brbs_equisat (before : Prop) (after : Prop) :=
  ay_brbs_conj (before -> after) (after -> before)

def ay_brbs_snapshot_evidence
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :=
  ay_brbs_conj conflictBudgetLedger
    (ay_brbs_conj propagationBudgetLedger
      (ay_brbs_conj decisionLevelSnapshot
        (ay_brbs_conj lbdActivityReplay
          (ay_brbs_conj fallbackBaseline
            (ay_brbs_conj originalInstanceLink solverBuildLink)))))

def ay_brbs_snapshot_agreement
    (conflictBudgetMatch : Prop) (propagationBudgetMatch : Prop)
    (decisionLevelMatch : Prop) (lbdActivityMatch : Prop)
    (fallbackMatch : Prop) (instanceMatch : Prop)
    (buildMatch : Prop) :=
  ay_brbs_conj conflictBudgetMatch
    (ay_brbs_conj propagationBudgetMatch
      (ay_brbs_conj decisionLevelMatch
        (ay_brbs_conj lbdActivityMatch
          (ay_brbs_conj fallbackMatch
            (ay_brbs_conj instanceMatch buildMatch)))))

def ay_brbs_accepted_snapshot
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop) :=
  ay_brbs_conj evidence (ay_brbs_conj agreement heuristicGuidance)

def ay_brbs_outcome (model : Prop) (conflict : Prop) :=
  ay_brbs_disj model conflict

def ay_brbs_public_report (outcome : Prop) (formula : Prop) :=
  ay_brbs_conj outcome formula

def ay_brbs_accepted_report (snapshotCert : Prop) (public : Prop) :=
  ay_brbs_conj snapshotCert public

def ay_brbs_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_brbs_conj fallbackPublic diagnostic

theorem ay_brbs_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_brbs_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_brbs_conj_left
    (left : Prop) (right : Prop) :
    ay_brbs_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_brbs_conj_right
    (left : Prop) (right : Prop) :
    ay_brbs_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_brbs_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_brbs_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_brbs_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_brbs_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_brbs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_brbs_equisat before after :=
  fun forward backward =>
    ay_brbs_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_brbs_equisat_forward
    (before : Prop) (after : Prop) :
    ay_brbs_equisat before after -> before -> after :=
  fun equisat =>
    ay_brbs_conj_left (before -> after) (after -> before) equisat

theorem ay_brbs_equisat_backward
    (before : Prop) (after : Prop) :
    ay_brbs_equisat before after -> after -> before :=
  fun equisat =>
    ay_brbs_conj_right (before -> after) (after -> before) equisat

theorem ay_brbs_snapshot_evidence_intro
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    conflictBudgetLedger ->
    propagationBudgetLedger ->
    decisionLevelSnapshot ->
    lbdActivityReplay ->
    fallbackBaseline ->
    originalInstanceLink ->
    solverBuildLink ->
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink :=
  fun conflictH propagationH levelH replayH fallbackH instanceH buildH =>
    ay_brbs_conj_intro conflictBudgetLedger
      (ay_brbs_conj propagationBudgetLedger
        (ay_brbs_conj decisionLevelSnapshot
          (ay_brbs_conj lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink)))))
      conflictH
      (ay_brbs_conj_intro propagationBudgetLedger
        (ay_brbs_conj decisionLevelSnapshot
          (ay_brbs_conj lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink))))
        propagationH
        (ay_brbs_conj_intro decisionLevelSnapshot
          (ay_brbs_conj lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink)))
          levelH
          (ay_brbs_conj_intro lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink))
            replayH
            (ay_brbs_conj_intro fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink)
              fallbackH
              (ay_brbs_conj_intro originalInstanceLink solverBuildLink
                instanceH buildH)))))

theorem ay_brbs_snapshot_evidence_conflict_budget
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    conflictBudgetLedger :=
  fun evidence =>
    ay_brbs_conj_left conflictBudgetLedger
      (ay_brbs_conj propagationBudgetLedger
        (ay_brbs_conj decisionLevelSnapshot
          (ay_brbs_conj lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink)))))
      evidence

theorem ay_brbs_snapshot_evidence_tail
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    ay_brbs_conj propagationBudgetLedger
      (ay_brbs_conj decisionLevelSnapshot
        (ay_brbs_conj lbdActivityReplay
          (ay_brbs_conj fallbackBaseline
            (ay_brbs_conj originalInstanceLink solverBuildLink)))) :=
  fun evidence =>
    ay_brbs_conj_right conflictBudgetLedger
      (ay_brbs_conj propagationBudgetLedger
        (ay_brbs_conj decisionLevelSnapshot
          (ay_brbs_conj lbdActivityReplay
            (ay_brbs_conj fallbackBaseline
              (ay_brbs_conj originalInstanceLink solverBuildLink)))))
      evidence

theorem ay_brbs_snapshot_evidence_propagation_budget
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    propagationBudgetLedger :=
  fun evidence =>
    ay_brbs_conj_left propagationBudgetLedger
      (ay_brbs_conj decisionLevelSnapshot
        (ay_brbs_conj lbdActivityReplay
          (ay_brbs_conj fallbackBaseline
            (ay_brbs_conj originalInstanceLink solverBuildLink))))
      (ay_brbs_snapshot_evidence_tail conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_after_propagation
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    ay_brbs_conj decisionLevelSnapshot
      (ay_brbs_conj lbdActivityReplay
        (ay_brbs_conj fallbackBaseline
          (ay_brbs_conj originalInstanceLink solverBuildLink))) :=
  fun evidence =>
    ay_brbs_conj_right propagationBudgetLedger
      (ay_brbs_conj decisionLevelSnapshot
        (ay_brbs_conj lbdActivityReplay
          (ay_brbs_conj fallbackBaseline
            (ay_brbs_conj originalInstanceLink solverBuildLink))))
      (ay_brbs_snapshot_evidence_tail conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_decision_level
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    decisionLevelSnapshot :=
  fun evidence =>
    ay_brbs_conj_left decisionLevelSnapshot
      (ay_brbs_conj lbdActivityReplay
        (ay_brbs_conj fallbackBaseline
          (ay_brbs_conj originalInstanceLink solverBuildLink)))
      (ay_brbs_snapshot_evidence_after_propagation conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_after_level
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    ay_brbs_conj lbdActivityReplay
      (ay_brbs_conj fallbackBaseline
        (ay_brbs_conj originalInstanceLink solverBuildLink)) :=
  fun evidence =>
    ay_brbs_conj_right decisionLevelSnapshot
      (ay_brbs_conj lbdActivityReplay
        (ay_brbs_conj fallbackBaseline
          (ay_brbs_conj originalInstanceLink solverBuildLink)))
      (ay_brbs_snapshot_evidence_after_propagation conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_lbd_activity
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    lbdActivityReplay :=
  fun evidence =>
    ay_brbs_conj_left lbdActivityReplay
      (ay_brbs_conj fallbackBaseline
        (ay_brbs_conj originalInstanceLink solverBuildLink))
      (ay_brbs_snapshot_evidence_after_level conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_after_replay
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    ay_brbs_conj fallbackBaseline
      (ay_brbs_conj originalInstanceLink solverBuildLink) :=
  fun evidence =>
    ay_brbs_conj_right lbdActivityReplay
      (ay_brbs_conj fallbackBaseline
        (ay_brbs_conj originalInstanceLink solverBuildLink))
      (ay_brbs_snapshot_evidence_after_level conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_fallback
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    fallbackBaseline :=
  fun evidence =>
    ay_brbs_conj_left fallbackBaseline
      (ay_brbs_conj originalInstanceLink solverBuildLink)
      (ay_brbs_snapshot_evidence_after_replay conflictBudgetLedger
        propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
        fallbackBaseline originalInstanceLink solverBuildLink evidence)

theorem ay_brbs_snapshot_evidence_instance
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    originalInstanceLink :=
  fun evidence =>
    ay_brbs_conj_left originalInstanceLink solverBuildLink
      (ay_brbs_conj_right fallbackBaseline
        (ay_brbs_conj originalInstanceLink solverBuildLink)
        (ay_brbs_snapshot_evidence_after_replay conflictBudgetLedger
          propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
          fallbackBaseline originalInstanceLink solverBuildLink evidence))

theorem ay_brbs_snapshot_evidence_solver_build
    (conflictBudgetLedger : Prop) (propagationBudgetLedger : Prop)
    (decisionLevelSnapshot : Prop) (lbdActivityReplay : Prop)
    (fallbackBaseline : Prop) (originalInstanceLink : Prop)
    (solverBuildLink : Prop) :
    ay_brbs_snapshot_evidence conflictBudgetLedger propagationBudgetLedger
      decisionLevelSnapshot lbdActivityReplay fallbackBaseline
      originalInstanceLink solverBuildLink ->
    solverBuildLink :=
  fun evidence =>
    ay_brbs_conj_right originalInstanceLink solverBuildLink
      (ay_brbs_conj_right fallbackBaseline
        (ay_brbs_conj originalInstanceLink solverBuildLink)
        (ay_brbs_snapshot_evidence_after_replay conflictBudgetLedger
          propagationBudgetLedger decisionLevelSnapshot lbdActivityReplay
          fallbackBaseline originalInstanceLink solverBuildLink evidence))

theorem ay_brbs_snapshot_agreement_intro
    (conflictBudgetMatch : Prop) (propagationBudgetMatch : Prop)
    (decisionLevelMatch : Prop) (lbdActivityMatch : Prop)
    (fallbackMatch : Prop) (instanceMatch : Prop)
    (buildMatch : Prop) :
    conflictBudgetMatch ->
    propagationBudgetMatch ->
    decisionLevelMatch ->
    lbdActivityMatch ->
    fallbackMatch ->
    instanceMatch ->
    buildMatch ->
    ay_brbs_snapshot_agreement conflictBudgetMatch propagationBudgetMatch
      decisionLevelMatch lbdActivityMatch fallbackMatch instanceMatch
      buildMatch :=
  fun conflictH propagationH levelH replayH fallbackH instanceH buildH =>
    ay_brbs_snapshot_evidence_intro conflictBudgetMatch propagationBudgetMatch
      decisionLevelMatch lbdActivityMatch fallbackMatch instanceMatch buildMatch
      conflictH propagationH levelH replayH fallbackH instanceH buildH

theorem ay_brbs_snapshot_agreement_conflict_budget
    (conflictBudgetMatch : Prop) (propagationBudgetMatch : Prop)
    (decisionLevelMatch : Prop) (lbdActivityMatch : Prop)
    (fallbackMatch : Prop) (instanceMatch : Prop)
    (buildMatch : Prop) :
    ay_brbs_snapshot_agreement conflictBudgetMatch propagationBudgetMatch
      decisionLevelMatch lbdActivityMatch fallbackMatch instanceMatch
      buildMatch ->
    conflictBudgetMatch :=
  fun agreement =>
    ay_brbs_snapshot_evidence_conflict_budget conflictBudgetMatch
      propagationBudgetMatch decisionLevelMatch lbdActivityMatch fallbackMatch
      instanceMatch buildMatch agreement

theorem ay_brbs_accepted_snapshot_intro
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop) :
    evidence ->
    agreement ->
    heuristicGuidance ->
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance :=
  fun evidenceH agreementH guidanceH =>
    ay_brbs_conj_intro evidence (ay_brbs_conj agreement heuristicGuidance)
      evidenceH
      (ay_brbs_conj_intro agreement heuristicGuidance agreementH guidanceH)

theorem ay_brbs_accepted_snapshot_evidence
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop) :
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance -> evidence :=
  fun accepted =>
    ay_brbs_conj_left evidence (ay_brbs_conj agreement heuristicGuidance)
      accepted

theorem ay_brbs_accepted_snapshot_agreement
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop) :
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance ->
    agreement :=
  fun accepted =>
    ay_brbs_conj_left agreement heuristicGuidance
      (ay_brbs_conj_right evidence
        (ay_brbs_conj agreement heuristicGuidance) accepted)

theorem ay_brbs_accepted_snapshot_guidance
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop) :
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance ->
    heuristicGuidance :=
  fun accepted =>
    ay_brbs_conj_right agreement heuristicGuidance
      (ay_brbs_conj_right evidence
        (ay_brbs_conj agreement heuristicGuidance) accepted)

theorem ay_brbs_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    ay_brbs_public_report (ay_brbs_outcome model conflict) formula :=
  fun modelH formulaH =>
    ay_brbs_conj_intro (ay_brbs_outcome model conflict) formula
      (ay_brbs_disj_left model conflict modelH)
      formulaH

theorem ay_brbs_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    ay_brbs_public_report (ay_brbs_outcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_brbs_conj_intro (ay_brbs_outcome model conflict) formula
      (ay_brbs_disj_right model conflict conflictH)
      formulaH

theorem ay_brbs_accepted_report_intro
    (snapshotCert : Prop) (public : Prop) :
    snapshotCert ->
    public ->
    ay_brbs_accepted_report snapshotCert public :=
  fun snapshotH publicH =>
    ay_brbs_conj_intro snapshotCert public snapshotH publicH

theorem ay_brbs_accepted_report_public
    (snapshotCert : Prop) (public : Prop) :
    ay_brbs_accepted_report snapshotCert public -> public :=
  fun accepted =>
    ay_brbs_conj_right snapshotCert public accepted

theorem ay_brbs_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_brbs_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_brbs_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_brbs_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brbs_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brbs_conj_left fallbackPublic diagnostic noClaim

theorem ay_brbs_stale_conflict_budget_no_claim
    (staleConflictBudget : Prop) (fallbackPublic : Prop) :
    staleConflictBudget ->
    fallbackPublic ->
    ay_brbs_no_claim staleConflictBudget fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbs_no_claim_intro staleConflictBudget fallbackPublic
      fallbackH diagnosticH

theorem ay_brbs_stale_propagation_budget_no_claim
    (stalePropagationBudget : Prop) (fallbackPublic : Prop) :
    stalePropagationBudget ->
    fallbackPublic ->
    ay_brbs_no_claim stalePropagationBudget fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbs_no_claim_intro stalePropagationBudget fallbackPublic
      fallbackH diagnosticH

theorem ay_brbs_missing_replay_no_claim
    (missingReplay : Prop) (fallbackPublic : Prop) :
    missingReplay ->
    fallbackPublic ->
    ay_brbs_no_claim missingReplay fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbs_no_claim_intro missingReplay fallbackPublic fallbackH diagnosticH

theorem ay_brbs_solver_build_drift_no_claim
    (solverBuildDrift : Prop) (fallbackPublic : Prop) :
    solverBuildDrift ->
    fallbackPublic ->
    ay_brbs_no_claim solverBuildDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbs_no_claim_intro solverBuildDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_brbs_contradictory_audit_no_claim
    (contradictoryAudit : Prop) (fallbackPublic : Prop) :
    contradictoryAudit ->
    fallbackPublic ->
    ay_brbs_no_claim contradictoryAudit fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_brbs_no_claim_intro contradictoryAudit fallbackPublic
      fallbackH diagnosticH

theorem ay_brbs_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_brbs_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_brbs_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_brbs_accepted_snapshot_guides_sat
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance ->
    model ->
    formula ->
    ay_brbs_accepted_report
      (ay_brbs_accepted_snapshot evidence agreement heuristicGuidance)
      (ay_brbs_public_report (ay_brbs_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_brbs_accepted_report_intro
      (ay_brbs_accepted_snapshot evidence agreement heuristicGuidance)
      (ay_brbs_public_report (ay_brbs_outcome model conflict) formula)
      accepted
      (ay_brbs_public_sat_report model conflict formula modelH formulaH)

theorem ay_brbs_accepted_snapshot_guides_unsat
    (evidence : Prop) (agreement : Prop) (heuristicGuidance : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_brbs_accepted_snapshot evidence agreement heuristicGuidance ->
    conflict ->
    formula ->
    ay_brbs_accepted_report
      (ay_brbs_accepted_snapshot evidence agreement heuristicGuidance)
      (ay_brbs_public_report (ay_brbs_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_brbs_accepted_report_intro
      (ay_brbs_accepted_snapshot evidence agreement heuristicGuidance)
      (ay_brbs_public_report (ay_brbs_outcome model conflict) formula)
      accepted
      (ay_brbs_public_unsat_report model conflict formula conflictH formulaH)

theorem ay_brbs_accepted_snapshot_preserves_public_soundness
    (snapshotCert : Prop) (public : Prop) :
    ay_brbs_accepted_report snapshotCert public -> public :=
  fun accepted =>
    ay_brbs_accepted_report_public snapshotCert public accepted

theorem ay_brbs_schedule_change_equisat_transport
    (beforeSchedule : Prop) (afterSchedule : Prop) :
    ay_brbs_equisat beforeSchedule afterSchedule ->
    beforeSchedule ->
    afterSchedule :=
  fun equisat beforeH =>
    ay_brbs_equisat_forward beforeSchedule afterSchedule equisat beforeH
