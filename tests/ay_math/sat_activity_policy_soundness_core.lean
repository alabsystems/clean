-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked activity/EVSIDS guidance soundness skeleton for SAT-COMP SAT
-- solving. Activity bumps, decay, and branching decisions can steer search
-- order, but public SAT/UNSAT soundness comes only from checked branch
-- outcomes. Retained learned-artifact reuse still requires guard matching.

def AyActivityConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyActivityDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyActivityEquisat (before : Prop) (after : Prop) :=
  AyActivityConj (before -> after) (after -> before)

def AyActivityScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyActivityState (formula : Prop) (frame : Prop) :=
  AyActivityConj formula frame

def AyActivityPolicy (bump : Prop) (decay : Prop) (branch : Prop) :=
  AyActivityConj bump (AyActivityConj decay branch)

def AyActivityGuardMatch (guard : Prop) (frame : Prop) :=
  AyActivityConj guard frame

def AyActivityRetainedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyActivityConj guard (AyActivityConj learnedClause checker)

def AyActivityAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyActivityConj (AyActivityGuardMatch guard frame)
    (AyActivityRetainedEntry guard learnedClause checker)

def AyActivityBranchOutcome (model : Prop) (conflict : Prop) :=
  AyActivityDisj model conflict

def AyActivityPublicResult (outcome : Prop) (frame : Prop) :=
  AyActivityConj outcome frame

def AyActivityPolicyResult (policy : Prop) (public : Prop) :=
  AyActivityConj policy public

theorem ay_activity_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyActivityConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_activity_conj_left
    (left : Prop) (right : Prop) :
    AyActivityConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_activity_conj_right
    (left : Prop) (right : Prop) :
    AyActivityConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_activity_disj_left
    (left : Prop) (right : Prop) :
    left -> AyActivityDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_activity_disj_right
    (left : Prop) (right : Prop) :
    right -> AyActivityDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_activity_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyActivityEquisat before after :=
  fun forward backward =>
    ay_activity_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_activity_equisat_forward
    (before : Prop) (after : Prop) :
    AyActivityEquisat before after -> before -> after :=
  fun equisat =>
    ay_activity_conj_left (before -> after) (after -> before)
      equisat

theorem ay_activity_equisat_backward
    (before : Prop) (after : Prop) :
    AyActivityEquisat before after -> after -> before :=
  fun equisat =>
    ay_activity_conj_right (before -> after) (after -> before)
      equisat

theorem ay_activity_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyActivityScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_activity_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyActivityState formula base ->
    assumption ->
    AyActivityState formula (AyActivityScope base assumption) :=
  fun state assumptionH =>
    ay_activity_conj_intro formula (AyActivityScope base assumption)
      (ay_activity_conj_left formula base state)
      (ay_activity_scope_push base assumption
        (ay_activity_conj_right formula base state)
        assumptionH)

theorem ay_activity_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyActivityEquisat original preprocessed ->
    AyActivityState original frame ->
    AyActivityState preprocessed frame :=
  fun preprocess state =>
    ay_activity_conj_intro preprocessed frame
      (ay_activity_equisat_forward original preprocessed preprocess
        (ay_activity_conj_left original frame state))
      (ay_activity_conj_right original frame state)

theorem ay_activity_policy_intro
    (bump : Prop) (decay : Prop) (branch : Prop) :
    bump -> decay -> branch -> AyActivityPolicy bump decay branch :=
  fun bumpH decayH branchH =>
    ay_activity_conj_intro bump (AyActivityConj decay branch)
      bumpH
      (ay_activity_conj_intro decay branch decayH branchH)

theorem ay_activity_policy_bump
    (bump : Prop) (decay : Prop) (branch : Prop) :
    AyActivityPolicy bump decay branch -> bump :=
  fun policy =>
    ay_activity_conj_left bump (AyActivityConj decay branch)
      policy

theorem ay_activity_policy_decay
    (bump : Prop) (decay : Prop) (branch : Prop) :
    AyActivityPolicy bump decay branch -> decay :=
  fun policy =>
    ay_activity_conj_left decay branch
      (ay_activity_conj_right bump (AyActivityConj decay branch)
        policy)

theorem ay_activity_policy_branch
    (bump : Prop) (decay : Prop) (branch : Prop) :
    AyActivityPolicy bump decay branch -> branch :=
  fun policy =>
    ay_activity_conj_right decay branch
      (ay_activity_conj_right bump (AyActivityConj decay branch)
        policy)

theorem ay_activity_policy_preserved_with_sat
    (bump : Prop) (decay : Prop) (branch : Prop)
    (model conflict frame : Prop) :
    AyActivityPolicy bump decay branch ->
    model ->
    frame ->
    AyActivityPolicyResult
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        frame) :=
  fun policy modelH frameH =>
    ay_activity_conj_intro
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        frame)
      policy
      (ay_activity_conj_intro
        (AyActivityBranchOutcome model conflict)
        frame
        (ay_activity_disj_left model conflict modelH)
        frameH)

theorem ay_activity_policy_preserved_with_unsat
    (bump : Prop) (decay : Prop) (branch : Prop)
    (model conflict frame : Prop) :
    AyActivityPolicy bump decay branch ->
    conflict ->
    frame ->
    AyActivityPolicyResult
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        frame) :=
  fun policy conflictH frameH =>
    ay_activity_conj_intro
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        frame)
      policy
      (ay_activity_conj_intro
        (AyActivityBranchOutcome model conflict)
        frame
        (ay_activity_disj_right model conflict conflictH)
        frameH)

theorem ay_activity_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyActivityGuardMatch guard frame :=
  fun guardH frameH =>
    ay_activity_conj_intro guard frame guardH frameH

theorem ay_activity_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyActivityGuardMatch guard frame -> guard :=
  fun matched =>
    ay_activity_conj_left guard frame matched

theorem ay_activity_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyActivityGuardMatch guard frame -> frame :=
  fun matched =>
    ay_activity_conj_right guard frame matched

theorem ay_activity_retained_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyActivityRetainedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_activity_conj_intro guard
      (AyActivityConj learnedClause checker)
      guardH
      (ay_activity_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_activity_retained_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyActivityRetainedEntry guard learnedClause checker ->
    learnedClause :=
  fun entry =>
    ay_activity_conj_left learnedClause checker
      (ay_activity_conj_right guard
        (AyActivityConj learnedClause checker)
        entry)

theorem ay_activity_retained_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyActivityRetainedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_activity_conj_right learnedClause checker
      (ay_activity_conj_right guard
        (AyActivityConj learnedClause checker)
        entry)

theorem ay_activity_accept_retained_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityGuardMatch guard frame ->
    AyActivityRetainedEntry guard learnedClause checker ->
    AyActivityAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_activity_conj_intro (AyActivityGuardMatch guard frame)
      (AyActivityRetainedEntry guard learnedClause checker)
      matched entry

theorem ay_activity_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker ->
    AyActivityGuardMatch guard frame :=
  fun reuse =>
    ay_activity_conj_left (AyActivityGuardMatch guard frame)
      (AyActivityRetainedEntry guard learnedClause checker)
      reuse

theorem ay_activity_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker ->
    AyActivityRetainedEntry guard learnedClause checker :=
  fun reuse =>
    ay_activity_conj_right (AyActivityGuardMatch guard frame)
      (AyActivityRetainedEntry guard learnedClause checker)
      reuse

theorem ay_activity_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_activity_guard_match_guard guard frame
      (ay_activity_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_activity_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_activity_guard_match_frame guard frame
      (ay_activity_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_activity_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_activity_retained_entry_clause guard learnedClause checker
      (ay_activity_reuse_entry frame guard learnedClause checker reuse)

theorem ay_activity_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyActivityAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_activity_retained_entry_checker guard learnedClause checker
      (ay_activity_reuse_entry frame guard learnedClause checker reuse)

theorem ay_activity_policy_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (bump : Prop) (decay : Prop) (branch : Prop)
    (model conflict : Prop) :
    AyActivityEquisat original preprocessed ->
    assumption ->
    AyActivityPolicy bump decay branch ->
    (preprocessed -> model) ->
    AyActivityState original base ->
    AyActivityPolicyResult
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        (AyActivityScope base assumption)) :=
  fun preprocess assumptionH policy sat state =>
    ay_activity_policy_preserved_with_sat
      bump decay branch model conflict (AyActivityScope base assumption)
      policy
      (sat
        (ay_activity_conj_left preprocessed
          (AyActivityScope base assumption)
          (ay_activity_preprocess_forward original preprocessed
            (AyActivityScope base assumption)
            preprocess
            (ay_activity_state_push original base assumption
              state assumptionH))))
      (ay_activity_scope_push base assumption
        (ay_activity_conj_right original base state)
        assumptionH)

theorem ay_activity_policy_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (bump : Prop) (decay : Prop) (branch : Prop)
    (model conflict : Prop) :
    assumption ->
    AyActivityPolicy bump decay branch ->
    conflict ->
    base ->
    AyActivityPolicyResult
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        (AyActivityScope base assumption)) :=
  fun assumptionH policy conflictH baseH =>
    ay_activity_policy_preserved_with_unsat
      bump decay branch model conflict (AyActivityScope base assumption)
      policy
      conflictH
      (ay_activity_scope_push base assumption baseH assumptionH)

theorem ay_activity_retained_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyActivityAcceptedReuse
      (AyActivityScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyActivityPublicResult
      (AyActivityBranchOutcome model conflict)
      (AyActivityScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_activity_conj_intro
      (AyActivityBranchOutcome model conflict)
      (AyActivityScope base assumption)
      (ay_activity_disj_right model conflict
        (learnedToConflict
          (ay_activity_reuse_learned_clause
            (AyActivityScope base assumption)
            guard learnedClause checker reuse)))
      (ay_activity_reuse_current_frame
        (AyActivityScope base assumption)
        guard learnedClause checker reuse)

theorem ay_activity_retained_reuse_with_policy_sound
    (base : Prop) (assumption : Prop)
    (bump : Prop) (decay : Prop) (branch : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyActivityPolicy bump decay branch ->
    AyActivityAcceptedReuse
      (AyActivityScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyActivityPolicyResult
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        (AyActivityScope base assumption)) :=
  fun policy reuse learnedToConflict =>
    ay_activity_conj_intro
      (AyActivityPolicy bump decay branch)
      (AyActivityPublicResult
        (AyActivityBranchOutcome model conflict)
        (AyActivityScope base assumption))
      policy
      (ay_activity_retained_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_activity_policy_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (bump : Prop) (decay : Prop) (branch : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyActivityEquisat original preprocessed ->
    assumption ->
    AyActivityPolicy bump decay branch ->
    AyActivityAcceptedReuse
      (AyActivityScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyActivityState original base ->
    AyActivityConj
      (AyActivityPolicyResult
        (AyActivityPolicy bump decay branch)
        (AyActivityPublicResult
          (AyActivityBranchOutcome model conflict)
          (AyActivityScope base assumption)))
      (AyActivityPolicyResult
        (AyActivityPolicy bump decay branch)
        (AyActivityPublicResult
          (AyActivityBranchOutcome model conflict)
          (AyActivityScope base assumption))) :=
  fun preprocess assumptionH policy reuse sat learnedToConflict state =>
    ay_activity_conj_intro
      (AyActivityPolicyResult
        (AyActivityPolicy bump decay branch)
        (AyActivityPublicResult
          (AyActivityBranchOutcome model conflict)
          (AyActivityScope base assumption)))
      (AyActivityPolicyResult
        (AyActivityPolicy bump decay branch)
        (AyActivityPublicResult
          (AyActivityBranchOutcome model conflict)
          (AyActivityScope base assumption)))
      (ay_activity_policy_guides_sat_without_changing_soundness
        original preprocessed base assumption bump decay branch
        model conflict preprocess assumptionH policy sat state)
      (ay_activity_retained_reuse_with_policy_sound
        base assumption bump decay branch guard learnedClause checker
        model conflict policy reuse learnedToConflict)
