-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked LBD-style restart policy soundness skeleton for SAT-COMP SAT
-- solving. Learnt-clause quality metrics, restart triggers, and phase guidance
-- can guide search order but do not create certificate evidence. Accepted
-- learned reuse still requires a guard matched to the current assumption frame.

def AyLbdConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLbdDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLbdEquisat (before : Prop) (after : Prop) :=
  AyLbdConj (before -> after) (after -> before)

def AyLbdScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyLbdState (formula : Prop) (frame : Prop) :=
  AyLbdConj formula frame

def AyLbdPolicy (metric : Prop) (trigger : Prop) (phase : Prop) :=
  AyLbdConj metric (AyLbdConj trigger phase)

def AyLbdGuardMatch (guard : Prop) (frame : Prop) :=
  AyLbdConj guard frame

def AyLbdLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyLbdConj guard (AyLbdConj learnedClause checker)

def AyLbdAcceptedLearned
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyLbdConj (AyLbdGuardMatch guard frame)
    (AyLbdLearnedEntry guard learnedClause checker)

def AyLbdBranchOutcome (model : Prop) (conflict : Prop) :=
  AyLbdDisj model conflict

def AyLbdPublicResult (outcome : Prop) (frame : Prop) :=
  AyLbdConj outcome frame

def AyLbdPolicyResult (policy : Prop) (public : Prop) :=
  AyLbdConj policy public

theorem ay_lbd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLbdConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_lbd_conj_left
    (left : Prop) (right : Prop) :
    AyLbdConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_lbd_conj_right
    (left : Prop) (right : Prop) :
    AyLbdConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_lbd_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLbdDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_lbd_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLbdDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_lbd_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyLbdEquisat before after :=
  fun forward backward =>
    ay_lbd_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_lbd_equisat_forward
    (before : Prop) (after : Prop) :
    AyLbdEquisat before after -> before -> after :=
  fun equisat =>
    ay_lbd_conj_left (before -> after) (after -> before)
      equisat

theorem ay_lbd_equisat_backward
    (before : Prop) (after : Prop) :
    AyLbdEquisat before after -> after -> before :=
  fun equisat =>
    ay_lbd_conj_right (before -> after) (after -> before)
      equisat

theorem ay_lbd_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyLbdScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_lbd_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyLbdState formula base ->
    assumption ->
    AyLbdState formula (AyLbdScope base assumption) :=
  fun state assumptionH =>
    ay_lbd_conj_intro formula (AyLbdScope base assumption)
      (ay_lbd_conj_left formula base state)
      (ay_lbd_scope_push base assumption
        (ay_lbd_conj_right formula base state)
        assumptionH)

theorem ay_lbd_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyLbdEquisat original preprocessed ->
    AyLbdState original frame ->
    AyLbdState preprocessed frame :=
  fun preprocess state =>
    ay_lbd_conj_intro preprocessed frame
      (ay_lbd_equisat_forward original preprocessed preprocess
        (ay_lbd_conj_left original frame state))
      (ay_lbd_conj_right original frame state)

theorem ay_lbd_policy_intro
    (metric : Prop) (trigger : Prop) (phase : Prop) :
    metric -> trigger -> phase -> AyLbdPolicy metric trigger phase :=
  fun metricH triggerH phaseH =>
    ay_lbd_conj_intro metric (AyLbdConj trigger phase)
      metricH
      (ay_lbd_conj_intro trigger phase triggerH phaseH)

theorem ay_lbd_policy_metric
    (metric : Prop) (trigger : Prop) (phase : Prop) :
    AyLbdPolicy metric trigger phase -> metric :=
  fun policy =>
    ay_lbd_conj_left metric (AyLbdConj trigger phase)
      policy

theorem ay_lbd_policy_trigger
    (metric : Prop) (trigger : Prop) (phase : Prop) :
    AyLbdPolicy metric trigger phase -> trigger :=
  fun policy =>
    ay_lbd_conj_left trigger phase
      (ay_lbd_conj_right metric (AyLbdConj trigger phase)
        policy)

theorem ay_lbd_policy_phase
    (metric : Prop) (trigger : Prop) (phase : Prop) :
    AyLbdPolicy metric trigger phase -> phase :=
  fun policy =>
    ay_lbd_conj_right trigger phase
      (ay_lbd_conj_right metric (AyLbdConj trigger phase)
        policy)

theorem ay_lbd_policy_preserved_with_sat
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyLbdPolicy metric trigger phase ->
    model ->
    frame ->
    AyLbdPolicyResult
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        frame) :=
  fun policy modelH frameH =>
    ay_lbd_conj_intro
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        frame)
      policy
      (ay_lbd_conj_intro
        (AyLbdBranchOutcome model conflict)
        frame
        (ay_lbd_disj_left model conflict modelH)
        frameH)

theorem ay_lbd_policy_preserved_with_unsat
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyLbdPolicy metric trigger phase ->
    conflict ->
    frame ->
    AyLbdPolicyResult
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        frame) :=
  fun policy conflictH frameH =>
    ay_lbd_conj_intro
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        frame)
      policy
      (ay_lbd_conj_intro
        (AyLbdBranchOutcome model conflict)
        frame
        (ay_lbd_disj_right model conflict conflictH)
        frameH)

theorem ay_lbd_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyLbdGuardMatch guard frame :=
  fun guardH frameH =>
    ay_lbd_conj_intro guard frame guardH frameH

theorem ay_lbd_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyLbdGuardMatch guard frame -> guard :=
  fun matched =>
    ay_lbd_conj_left guard frame matched

theorem ay_lbd_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyLbdGuardMatch guard frame -> frame :=
  fun matched =>
    ay_lbd_conj_right guard frame matched

theorem ay_lbd_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyLbdLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_lbd_conj_intro guard
      (AyLbdConj learnedClause checker)
      guardH
      (ay_lbd_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_lbd_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyLbdLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_lbd_conj_left learnedClause checker
      (ay_lbd_conj_right guard
        (AyLbdConj learnedClause checker)
        entry)

theorem ay_lbd_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyLbdLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_lbd_conj_right learnedClause checker
      (ay_lbd_conj_right guard
        (AyLbdConj learnedClause checker)
        entry)

theorem ay_lbd_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdGuardMatch guard frame ->
    AyLbdLearnedEntry guard learnedClause checker ->
    AyLbdAcceptedLearned frame guard learnedClause checker :=
  fun matched entry =>
    ay_lbd_conj_intro (AyLbdGuardMatch guard frame)
      (AyLbdLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_lbd_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    AyLbdGuardMatch guard frame :=
  fun reuse =>
    ay_lbd_conj_left (AyLbdGuardMatch guard frame)
      (AyLbdLearnedEntry guard learnedClause checker)
      reuse

theorem ay_lbd_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    AyLbdLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_lbd_conj_right (AyLbdGuardMatch guard frame)
      (AyLbdLearnedEntry guard learnedClause checker)
      reuse

theorem ay_lbd_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    guard :=
  fun reuse =>
    ay_lbd_guard_match_guard guard frame
      (ay_lbd_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_lbd_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    frame :=
  fun reuse =>
    ay_lbd_guard_match_frame guard frame
      (ay_lbd_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_lbd_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_lbd_learned_entry_clause guard learnedClause checker
      (ay_lbd_reuse_entry frame guard learnedClause checker reuse)

theorem ay_lbd_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyLbdAcceptedLearned frame guard learnedClause checker ->
    checker :=
  fun reuse =>
    ay_lbd_learned_entry_checker guard learnedClause checker
      (ay_lbd_reuse_entry frame guard learnedClause checker reuse)

theorem ay_lbd_policy_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (model conflict : Prop) :
    AyLbdEquisat original preprocessed ->
    assumption ->
    AyLbdPolicy metric trigger phase ->
    (preprocessed -> model) ->
    AyLbdState original base ->
    AyLbdPolicyResult
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        (AyLbdScope base assumption)) :=
  fun preprocess assumptionH policy sat state =>
    ay_lbd_policy_preserved_with_sat
      metric trigger phase model conflict (AyLbdScope base assumption)
      policy
      (sat
        (ay_lbd_conj_left preprocessed
          (AyLbdScope base assumption)
          (ay_lbd_preprocess_forward original preprocessed
            (AyLbdScope base assumption)
            preprocess
            (ay_lbd_state_push original base assumption
              state assumptionH))))
      (ay_lbd_scope_push base assumption
        (ay_lbd_conj_right original base state)
        assumptionH)

theorem ay_lbd_policy_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (model conflict : Prop) :
    assumption ->
    AyLbdPolicy metric trigger phase ->
    conflict ->
    base ->
    AyLbdPolicyResult
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        (AyLbdScope base assumption)) :=
  fun assumptionH policy conflictH baseH =>
    ay_lbd_policy_preserved_with_unsat
      metric trigger phase model conflict (AyLbdScope base assumption)
      policy
      conflictH
      (ay_lbd_scope_push base assumption baseH assumptionH)

theorem ay_lbd_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyLbdAcceptedLearned
      (AyLbdScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyLbdPublicResult
      (AyLbdBranchOutcome model conflict)
      (AyLbdScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_lbd_conj_intro
      (AyLbdBranchOutcome model conflict)
      (AyLbdScope base assumption)
      (ay_lbd_disj_right model conflict
        (learnedToConflict
          (ay_lbd_reuse_learned_clause
            (AyLbdScope base assumption)
            guard learnedClause checker reuse)))
      (ay_lbd_reuse_current_frame
        (AyLbdScope base assumption)
        guard learnedClause checker reuse)

theorem ay_lbd_learned_reuse_with_policy_sound
    (base : Prop) (assumption : Prop)
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyLbdPolicy metric trigger phase ->
    AyLbdAcceptedLearned
      (AyLbdScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyLbdPolicyResult
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        (AyLbdScope base assumption)) :=
  fun policy reuse learnedToConflict =>
    ay_lbd_conj_intro
      (AyLbdPolicy metric trigger phase)
      (AyLbdPublicResult
        (AyLbdBranchOutcome model conflict)
        (AyLbdScope base assumption))
      policy
      (ay_lbd_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_lbd_metric_trigger_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (metric : Prop) (trigger : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyLbdEquisat original preprocessed ->
    assumption ->
    AyLbdPolicy metric trigger phase ->
    AyLbdAcceptedLearned
      (AyLbdScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyLbdState original base ->
    AyLbdConj
      (AyLbdPolicyResult
        (AyLbdPolicy metric trigger phase)
        (AyLbdPublicResult
          (AyLbdBranchOutcome model conflict)
          (AyLbdScope base assumption)))
      (AyLbdPolicyResult
        (AyLbdPolicy metric trigger phase)
        (AyLbdPublicResult
          (AyLbdBranchOutcome model conflict)
          (AyLbdScope base assumption))) :=
  fun preprocess assumptionH policy reuse sat learnedToConflict state =>
    ay_lbd_conj_intro
      (AyLbdPolicyResult
        (AyLbdPolicy metric trigger phase)
        (AyLbdPublicResult
          (AyLbdBranchOutcome model conflict)
          (AyLbdScope base assumption)))
      (AyLbdPolicyResult
        (AyLbdPolicy metric trigger phase)
        (AyLbdPublicResult
          (AyLbdBranchOutcome model conflict)
          (AyLbdScope base assumption)))
      (ay_lbd_policy_guides_sat_without_changing_soundness
        original preprocessed base assumption metric trigger phase
        model conflict preprocess assumptionH policy sat state)
      (ay_lbd_learned_reuse_with_policy_sound
        base assumption metric trigger phase guard learnedClause checker
        model conflict policy reuse learnedToConflict)
