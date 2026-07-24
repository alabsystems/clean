-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked restart-budget policy soundness skeleton for SAT-COMP SAT solving.
-- Budget, cutoff, and phase choices are search-order guidance only: they may
-- be preserved with a checked result, but they do not create SAT/UNSAT
-- evidence. Learned-clause reuse remains gated by a current-frame guard match.

def AyBudgetConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBudgetDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBudgetEquisat (before : Prop) (after : Prop) :=
  AyBudgetConj (before -> after) (after -> before)

def AyBudgetScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyBudgetState (formula : Prop) (frame : Prop) :=
  AyBudgetConj formula frame

def AyBudgetPolicy (budget : Prop) (cutoff : Prop) (phase : Prop) :=
  AyBudgetConj budget (AyBudgetConj cutoff phase)

def AyBudgetGuardMatch (guard : Prop) (frame : Prop) :=
  AyBudgetConj guard frame

def AyBudgetLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyBudgetConj guard (AyBudgetConj learnedClause checker)

def AyBudgetAcceptedLearned
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyBudgetConj (AyBudgetGuardMatch guard frame)
    (AyBudgetLearnedEntry guard learnedClause checker)

def AyBudgetBranchOutcome (model : Prop) (conflict : Prop) :=
  AyBudgetDisj model conflict

def AyBudgetPublicResult (outcome : Prop) (frame : Prop) :=
  AyBudgetConj outcome frame

def AyBudgetPolicyResult (policy : Prop) (public : Prop) :=
  AyBudgetConj policy public

theorem ay_budget_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBudgetConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_budget_conj_left
    (left : Prop) (right : Prop) :
    AyBudgetConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_budget_conj_right
    (left : Prop) (right : Prop) :
    AyBudgetConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_budget_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBudgetDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_budget_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBudgetDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_budget_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBudgetEquisat before after :=
  fun forward backward =>
    ay_budget_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_budget_equisat_forward
    (before : Prop) (after : Prop) :
    AyBudgetEquisat before after -> before -> after :=
  fun equisat =>
    ay_budget_conj_left (before -> after) (after -> before)
      equisat

theorem ay_budget_equisat_backward
    (before : Prop) (after : Prop) :
    AyBudgetEquisat before after -> after -> before :=
  fun equisat =>
    ay_budget_conj_right (before -> after) (after -> before)
      equisat

theorem ay_budget_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyBudgetScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_budget_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBudgetState formula base ->
    assumption ->
    AyBudgetState formula (AyBudgetScope base assumption) :=
  fun state assumptionH =>
    ay_budget_conj_intro formula (AyBudgetScope base assumption)
      (ay_budget_conj_left formula base state)
      (ay_budget_scope_push base assumption
        (ay_budget_conj_right formula base state)
        assumptionH)

theorem ay_budget_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyBudgetEquisat original preprocessed ->
    AyBudgetState original frame ->
    AyBudgetState preprocessed frame :=
  fun preprocess state =>
    ay_budget_conj_intro preprocessed frame
      (ay_budget_equisat_forward original preprocessed preprocess
        (ay_budget_conj_left original frame state))
      (ay_budget_conj_right original frame state)

theorem ay_budget_policy_intro
    (budget : Prop) (cutoff : Prop) (phase : Prop) :
    budget -> cutoff -> phase -> AyBudgetPolicy budget cutoff phase :=
  fun budgetH cutoffH phaseH =>
    ay_budget_conj_intro budget (AyBudgetConj cutoff phase)
      budgetH
      (ay_budget_conj_intro cutoff phase cutoffH phaseH)

theorem ay_budget_policy_budget
    (budget : Prop) (cutoff : Prop) (phase : Prop) :
    AyBudgetPolicy budget cutoff phase -> budget :=
  fun policy =>
    ay_budget_conj_left budget (AyBudgetConj cutoff phase)
      policy

theorem ay_budget_policy_cutoff
    (budget : Prop) (cutoff : Prop) (phase : Prop) :
    AyBudgetPolicy budget cutoff phase -> cutoff :=
  fun policy =>
    ay_budget_conj_left cutoff phase
      (ay_budget_conj_right budget (AyBudgetConj cutoff phase)
        policy)

theorem ay_budget_policy_phase
    (budget : Prop) (cutoff : Prop) (phase : Prop) :
    AyBudgetPolicy budget cutoff phase -> phase :=
  fun policy =>
    ay_budget_conj_right cutoff phase
      (ay_budget_conj_right budget (AyBudgetConj cutoff phase)
        policy)

theorem ay_budget_policy_preserved_with_sat
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyBudgetPolicy budget cutoff phase ->
    model ->
    frame ->
    AyBudgetPolicyResult
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        frame) :=
  fun policy modelH frameH =>
    ay_budget_conj_intro
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        frame)
      policy
      (ay_budget_conj_intro
        (AyBudgetBranchOutcome model conflict)
        frame
        (ay_budget_disj_left model conflict modelH)
        frameH)

theorem ay_budget_policy_preserved_with_unsat
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyBudgetPolicy budget cutoff phase ->
    conflict ->
    frame ->
    AyBudgetPolicyResult
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        frame) :=
  fun policy conflictH frameH =>
    ay_budget_conj_intro
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        frame)
      policy
      (ay_budget_conj_intro
        (AyBudgetBranchOutcome model conflict)
        frame
        (ay_budget_disj_right model conflict conflictH)
        frameH)

theorem ay_budget_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyBudgetGuardMatch guard frame :=
  fun guardH frameH =>
    ay_budget_conj_intro guard frame guardH frameH

theorem ay_budget_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyBudgetGuardMatch guard frame -> guard :=
  fun matched =>
    ay_budget_conj_left guard frame matched

theorem ay_budget_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyBudgetGuardMatch guard frame -> frame :=
  fun matched =>
    ay_budget_conj_right guard frame matched

theorem ay_budget_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyBudgetLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_budget_conj_intro guard
      (AyBudgetConj learnedClause checker)
      guardH
      (ay_budget_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_budget_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyBudgetLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_budget_conj_left learnedClause checker
      (ay_budget_conj_right guard
        (AyBudgetConj learnedClause checker)
        entry)

theorem ay_budget_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyBudgetLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_budget_conj_right learnedClause checker
      (ay_budget_conj_right guard
        (AyBudgetConj learnedClause checker)
        entry)

theorem ay_budget_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetGuardMatch guard frame ->
    AyBudgetLearnedEntry guard learnedClause checker ->
    AyBudgetAcceptedLearned frame guard learnedClause checker :=
  fun matched entry =>
    ay_budget_conj_intro (AyBudgetGuardMatch guard frame)
      (AyBudgetLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_budget_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    AyBudgetGuardMatch guard frame :=
  fun reuse =>
    ay_budget_conj_left (AyBudgetGuardMatch guard frame)
      (AyBudgetLearnedEntry guard learnedClause checker)
      reuse

theorem ay_budget_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    AyBudgetLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_budget_conj_right (AyBudgetGuardMatch guard frame)
      (AyBudgetLearnedEntry guard learnedClause checker)
      reuse

theorem ay_budget_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    guard :=
  fun reuse =>
    ay_budget_guard_match_guard guard frame
      (ay_budget_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_budget_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    frame :=
  fun reuse =>
    ay_budget_guard_match_frame guard frame
      (ay_budget_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_budget_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_budget_learned_entry_clause guard learnedClause checker
      (ay_budget_reuse_entry frame guard learnedClause checker reuse)

theorem ay_budget_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBudgetAcceptedLearned frame guard learnedClause checker ->
    checker :=
  fun reuse =>
    ay_budget_learned_entry_checker guard learnedClause checker
      (ay_budget_reuse_entry frame guard learnedClause checker reuse)

theorem ay_budget_policy_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (model conflict : Prop) :
    AyBudgetEquisat original preprocessed ->
    assumption ->
    AyBudgetPolicy budget cutoff phase ->
    (preprocessed -> model) ->
    AyBudgetState original base ->
    AyBudgetPolicyResult
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        (AyBudgetScope base assumption)) :=
  fun preprocess assumptionH policy sat state =>
    ay_budget_policy_preserved_with_sat
      budget cutoff phase model conflict (AyBudgetScope base assumption)
      policy
      (sat
        (ay_budget_conj_left preprocessed
          (AyBudgetScope base assumption)
          (ay_budget_preprocess_forward original preprocessed
            (AyBudgetScope base assumption)
            preprocess
            (ay_budget_state_push original base assumption
              state assumptionH))))
      (ay_budget_scope_push base assumption
        (ay_budget_conj_right original base state)
        assumptionH)

theorem ay_budget_policy_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (model conflict : Prop) :
    assumption ->
    AyBudgetPolicy budget cutoff phase ->
    conflict ->
    base ->
    AyBudgetPolicyResult
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        (AyBudgetScope base assumption)) :=
  fun assumptionH policy conflictH baseH =>
    ay_budget_policy_preserved_with_unsat
      budget cutoff phase model conflict (AyBudgetScope base assumption)
      policy
      conflictH
      (ay_budget_scope_push base assumption baseH assumptionH)

theorem ay_budget_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBudgetAcceptedLearned
      (AyBudgetScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBudgetPublicResult
      (AyBudgetBranchOutcome model conflict)
      (AyBudgetScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_budget_conj_intro
      (AyBudgetBranchOutcome model conflict)
      (AyBudgetScope base assumption)
      (ay_budget_disj_right model conflict
        (learnedToConflict
          (ay_budget_reuse_learned_clause
            (AyBudgetScope base assumption)
            guard learnedClause checker reuse)))
      (ay_budget_reuse_current_frame
        (AyBudgetScope base assumption)
        guard learnedClause checker reuse)

theorem ay_budget_learned_reuse_with_policy_sound
    (base : Prop) (assumption : Prop)
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBudgetPolicy budget cutoff phase ->
    AyBudgetAcceptedLearned
      (AyBudgetScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBudgetPolicyResult
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        (AyBudgetScope base assumption)) :=
  fun policy reuse learnedToConflict =>
    ay_budget_conj_intro
      (AyBudgetPolicy budget cutoff phase)
      (AyBudgetPublicResult
        (AyBudgetBranchOutcome model conflict)
        (AyBudgetScope base assumption))
      policy
      (ay_budget_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_budget_full_policy_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (budget : Prop) (cutoff : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBudgetEquisat original preprocessed ->
    assumption ->
    AyBudgetPolicy budget cutoff phase ->
    AyBudgetAcceptedLearned
      (AyBudgetScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyBudgetState original base ->
    AyBudgetConj
      (AyBudgetPolicyResult
        (AyBudgetPolicy budget cutoff phase)
        (AyBudgetPublicResult
          (AyBudgetBranchOutcome model conflict)
          (AyBudgetScope base assumption)))
      (AyBudgetPolicyResult
        (AyBudgetPolicy budget cutoff phase)
        (AyBudgetPublicResult
          (AyBudgetBranchOutcome model conflict)
          (AyBudgetScope base assumption))) :=
  fun preprocess assumptionH policy reuse sat learnedToConflict state =>
    ay_budget_conj_intro
      (AyBudgetPolicyResult
        (AyBudgetPolicy budget cutoff phase)
        (AyBudgetPublicResult
          (AyBudgetBranchOutcome model conflict)
          (AyBudgetScope base assumption)))
      (AyBudgetPolicyResult
        (AyBudgetPolicy budget cutoff phase)
        (AyBudgetPublicResult
          (AyBudgetBranchOutcome model conflict)
          (AyBudgetScope base assumption)))
      (ay_budget_policy_guides_sat_without_changing_soundness
        original preprocessed base assumption budget cutoff phase
        model conflict preprocess assumptionH policy sat state)
      (ay_budget_learned_reuse_with_policy_sound
        base assumption budget cutoff phase guard learnedClause checker
        model conflict policy reuse learnedToConflict)
