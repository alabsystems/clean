-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked learned-clause database reduction soundness skeleton for SAT-COMP
-- SAT solving. Reduction policies may retain or delete learned clauses and
-- affect search guidance, but public SAT/UNSAT soundness comes only from
-- checked branch outcomes. Reused retained clauses still require a guard
-- matched to the current assumption frame.

def AyDbConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDbDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyDbEquisat (before : Prop) (after : Prop) :=
  AyDbConj (before -> after) (after -> before)

def AyDbScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyDbState (formula : Prop) (frame : Prop) :=
  AyDbConj formula frame

def AyDbReductionPolicy
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop) :=
  AyDbConj retained (AyDbConj deletedUnused restartLbd)

def AyDbGuardMatch (guard : Prop) (frame : Prop) :=
  AyDbConj guard frame

def AyDbRetainedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyDbConj guard (AyDbConj learnedClause checker)

def AyDbAcceptedRetainedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyDbConj (AyDbGuardMatch guard frame)
    (AyDbRetainedEntry guard learnedClause checker)

def AyDbBranchOutcome (model : Prop) (conflict : Prop) :=
  AyDbDisj model conflict

def AyDbPublicResult (outcome : Prop) (frame : Prop) :=
  AyDbConj outcome frame

def AyDbPolicyResult (policy : Prop) (public : Prop) :=
  AyDbConj policy public

theorem ay_db_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyDbConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_db_conj_left
    (left : Prop) (right : Prop) :
    AyDbConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_db_conj_right
    (left : Prop) (right : Prop) :
    AyDbConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_db_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDbDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_db_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDbDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_db_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyDbEquisat before after :=
  fun forward backward =>
    ay_db_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_db_equisat_forward
    (before : Prop) (after : Prop) :
    AyDbEquisat before after -> before -> after :=
  fun equisat =>
    ay_db_conj_left (before -> after) (after -> before)
      equisat

theorem ay_db_equisat_backward
    (before : Prop) (after : Prop) :
    AyDbEquisat before after -> after -> before :=
  fun equisat =>
    ay_db_conj_right (before -> after) (after -> before)
      equisat

theorem ay_db_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyDbScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_db_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyDbState formula base ->
    assumption ->
    AyDbState formula (AyDbScope base assumption) :=
  fun state assumptionH =>
    ay_db_conj_intro formula (AyDbScope base assumption)
      (ay_db_conj_left formula base state)
      (ay_db_scope_push base assumption
        (ay_db_conj_right formula base state)
        assumptionH)

theorem ay_db_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyDbEquisat original preprocessed ->
    AyDbState original frame ->
    AyDbState preprocessed frame :=
  fun preprocess state =>
    ay_db_conj_intro preprocessed frame
      (ay_db_equisat_forward original preprocessed preprocess
        (ay_db_conj_left original frame state))
      (ay_db_conj_right original frame state)

theorem ay_db_reduction_policy_intro
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop) :
    retained ->
    deletedUnused ->
    restartLbd ->
    AyDbReductionPolicy retained deletedUnused restartLbd :=
  fun retainedH deletedH policyH =>
    ay_db_conj_intro retained (AyDbConj deletedUnused restartLbd)
      retainedH
      (ay_db_conj_intro deletedUnused restartLbd deletedH policyH)

theorem ay_db_reduction_policy_retained
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd -> retained :=
  fun policy =>
    ay_db_conj_left retained (AyDbConj deletedUnused restartLbd)
      policy

theorem ay_db_reduction_policy_deleted
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd -> deletedUnused :=
  fun policy =>
    ay_db_conj_left deletedUnused restartLbd
      (ay_db_conj_right retained (AyDbConj deletedUnused restartLbd)
        policy)

theorem ay_db_reduction_policy_restart_lbd
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd -> restartLbd :=
  fun policy =>
    ay_db_conj_right deletedUnused restartLbd
      (ay_db_conj_right retained (AyDbConj deletedUnused restartLbd)
        policy)

theorem ay_db_deleted_unused_preserved_with_sat
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (model conflict frame : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    model ->
    frame ->
    AyDbPolicyResult
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        frame) :=
  fun policy modelH frameH =>
    ay_db_conj_intro
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        frame)
      policy
      (ay_db_conj_intro
        (AyDbBranchOutcome model conflict)
        frame
        (ay_db_disj_left model conflict modelH)
        frameH)

theorem ay_db_deleted_unused_preserved_with_unsat
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (model conflict frame : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    conflict ->
    frame ->
    AyDbPolicyResult
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        frame) :=
  fun policy conflictH frameH =>
    ay_db_conj_intro
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        frame)
      policy
      (ay_db_conj_intro
        (AyDbBranchOutcome model conflict)
        frame
        (ay_db_disj_right model conflict conflictH)
        frameH)

theorem ay_db_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyDbGuardMatch guard frame :=
  fun guardH frameH =>
    ay_db_conj_intro guard frame guardH frameH

theorem ay_db_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyDbGuardMatch guard frame -> guard :=
  fun matched =>
    ay_db_conj_left guard frame matched

theorem ay_db_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyDbGuardMatch guard frame -> frame :=
  fun matched =>
    ay_db_conj_right guard frame matched

theorem ay_db_retained_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyDbRetainedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_db_conj_intro guard
      (AyDbConj learnedClause checker)
      guardH
      (ay_db_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_db_retained_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyDbRetainedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_db_conj_left learnedClause checker
      (ay_db_conj_right guard
        (AyDbConj learnedClause checker)
        entry)

theorem ay_db_retained_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyDbRetainedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_db_conj_right learnedClause checker
      (ay_db_conj_right guard
        (AyDbConj learnedClause checker)
        entry)

theorem ay_db_accept_retained_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbGuardMatch guard frame ->
    AyDbRetainedEntry guard learnedClause checker ->
    AyDbAcceptedRetainedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_db_conj_intro (AyDbGuardMatch guard frame)
      (AyDbRetainedEntry guard learnedClause checker)
      matched entry

theorem ay_db_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    AyDbGuardMatch guard frame :=
  fun reuse =>
    ay_db_conj_left (AyDbGuardMatch guard frame)
      (AyDbRetainedEntry guard learnedClause checker)
      reuse

theorem ay_db_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    AyDbRetainedEntry guard learnedClause checker :=
  fun reuse =>
    ay_db_conj_right (AyDbGuardMatch guard frame)
      (AyDbRetainedEntry guard learnedClause checker)
      reuse

theorem ay_db_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    guard :=
  fun reuse =>
    ay_db_guard_match_guard guard frame
      (ay_db_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_db_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    frame :=
  fun reuse =>
    ay_db_guard_match_frame guard frame
      (ay_db_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_db_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_db_retained_entry_clause guard learnedClause checker
      (ay_db_reuse_entry frame guard learnedClause checker reuse)

theorem ay_db_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyDbAcceptedRetainedReuse frame guard learnedClause checker ->
    checker :=
  fun reuse =>
    ay_db_retained_entry_checker guard learnedClause checker
      (ay_db_reuse_entry frame guard learnedClause checker reuse)

theorem ay_db_reduction_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (model conflict : Prop) :
    AyDbEquisat original preprocessed ->
    assumption ->
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    (preprocessed -> model) ->
    AyDbState original base ->
    AyDbPolicyResult
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        (AyDbScope base assumption)) :=
  fun preprocess assumptionH policy sat state =>
    ay_db_deleted_unused_preserved_with_sat
      retained deletedUnused restartLbd model conflict
      (AyDbScope base assumption)
      policy
      (sat
        (ay_db_conj_left preprocessed
          (AyDbScope base assumption)
          (ay_db_preprocess_forward original preprocessed
            (AyDbScope base assumption)
            preprocess
            (ay_db_state_push original base assumption
              state assumptionH))))
      (ay_db_scope_push base assumption
        (ay_db_conj_right original base state)
        assumptionH)

theorem ay_db_reduction_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (model conflict : Prop) :
    assumption ->
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    conflict ->
    base ->
    AyDbPolicyResult
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        (AyDbScope base assumption)) :=
  fun assumptionH policy conflictH baseH =>
    ay_db_deleted_unused_preserved_with_unsat
      retained deletedUnused restartLbd model conflict
      (AyDbScope base assumption)
      policy
      conflictH
      (ay_db_scope_push base assumption baseH assumptionH)

theorem ay_db_retained_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyDbAcceptedRetainedReuse
      (AyDbScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyDbPublicResult
      (AyDbBranchOutcome model conflict)
      (AyDbScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_db_conj_intro
      (AyDbBranchOutcome model conflict)
      (AyDbScope base assumption)
      (ay_db_disj_right model conflict
        (learnedToConflict
          (ay_db_reuse_learned_clause
            (AyDbScope base assumption)
            guard learnedClause checker reuse)))
      (ay_db_reuse_current_frame
        (AyDbScope base assumption)
        guard learnedClause checker reuse)

theorem ay_db_retained_reuse_with_reduction_policy_sound
    (base : Prop) (assumption : Prop)
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    AyDbAcceptedRetainedReuse
      (AyDbScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyDbPolicyResult
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        (AyDbScope base assumption)) :=
  fun policy reuse learnedToConflict =>
    ay_db_conj_intro
      (AyDbReductionPolicy retained deletedUnused restartLbd)
      (AyDbPublicResult
        (AyDbBranchOutcome model conflict)
        (AyDbScope base assumption))
      policy
      (ay_db_retained_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_db_clause_database_reduction_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (retained : Prop) (deletedUnused : Prop) (restartLbd : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyDbEquisat original preprocessed ->
    assumption ->
    AyDbReductionPolicy retained deletedUnused restartLbd ->
    AyDbAcceptedRetainedReuse
      (AyDbScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyDbState original base ->
    AyDbConj
      (AyDbPolicyResult
        (AyDbReductionPolicy retained deletedUnused restartLbd)
        (AyDbPublicResult
          (AyDbBranchOutcome model conflict)
          (AyDbScope base assumption)))
      (AyDbPolicyResult
        (AyDbReductionPolicy retained deletedUnused restartLbd)
        (AyDbPublicResult
          (AyDbBranchOutcome model conflict)
          (AyDbScope base assumption))) :=
  fun preprocess assumptionH policy reuse sat learnedToConflict state =>
    ay_db_conj_intro
      (AyDbPolicyResult
        (AyDbReductionPolicy retained deletedUnused restartLbd)
        (AyDbPublicResult
          (AyDbBranchOutcome model conflict)
          (AyDbScope base assumption)))
      (AyDbPolicyResult
        (AyDbReductionPolicy retained deletedUnused restartLbd)
        (AyDbPublicResult
          (AyDbBranchOutcome model conflict)
          (AyDbScope base assumption)))
      (ay_db_reduction_guides_sat_without_changing_soundness
        original preprocessed base assumption retained deletedUnused
        restartLbd model conflict preprocess assumptionH policy sat state)
      (ay_db_retained_reuse_with_reduction_policy_sound
        base assumption retained deletedUnused restartLbd guard learnedClause
        checker model conflict policy reuse learnedToConflict)
