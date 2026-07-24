-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked branching-heuristic policy soundness skeleton for SAT-COMP SAT
-- solving. Variable scores, polarity hints, randomization, phase policy, and
-- activity guidance can steer search order, but public SAT/UNSAT soundness
-- comes only from checked branch outcomes. Learned-artifact reuse still
-- requires a guard matched to the current assumption frame.

def AyBranchConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBranchDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBranchEquisat (before : Prop) (after : Prop) :=
  AyBranchConj (before -> after) (after -> before)

def AyBranchScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyBranchState (formula : Prop) (frame : Prop) :=
  AyBranchConj formula frame

def AyBranchHeuristicPolicy
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :=
  AyBranchConj scores
    (AyBranchConj polarity
      (AyBranchConj randomization
        (AyBranchConj phase activity)))

def AyBranchGuardMatch (guard : Prop) (frame : Prop) :=
  AyBranchConj guard frame

def AyBranchLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyBranchConj guard (AyBranchConj learnedClause checker)

def AyBranchAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyBranchConj (AyBranchGuardMatch guard frame)
    (AyBranchLearnedEntry guard learnedClause checker)

def AyBranchOutcome (model : Prop) (conflict : Prop) :=
  AyBranchDisj model conflict

def AyBranchPublicResult (outcome : Prop) (frame : Prop) :=
  AyBranchConj outcome frame

def AyBranchPolicyResult (policy : Prop) (public : Prop) :=
  AyBranchConj policy public

theorem ay_branch_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBranchConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_branch_conj_left
    (left : Prop) (right : Prop) :
    AyBranchConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_branch_conj_right
    (left : Prop) (right : Prop) :
    AyBranchConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_branch_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBranchDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_branch_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBranchDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_branch_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBranchEquisat before after :=
  fun forward backward =>
    ay_branch_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_branch_equisat_forward
    (before : Prop) (after : Prop) :
    AyBranchEquisat before after -> before -> after :=
  fun equisat =>
    ay_branch_conj_left (before -> after) (after -> before)
      equisat

theorem ay_branch_equisat_backward
    (before : Prop) (after : Prop) :
    AyBranchEquisat before after -> after -> before :=
  fun equisat =>
    ay_branch_conj_right (before -> after) (after -> before)
      equisat

theorem ay_branch_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyBranchScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_branch_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyBranchState formula base ->
    assumption ->
    AyBranchState formula (AyBranchScope base assumption) :=
  fun state assumptionH =>
    ay_branch_conj_intro formula (AyBranchScope base assumption)
      (ay_branch_conj_left formula base state)
      (ay_branch_scope_push base assumption
        (ay_branch_conj_right formula base state)
        assumptionH)

theorem ay_branch_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyBranchEquisat original preprocessed ->
    AyBranchState original frame ->
    AyBranchState preprocessed frame :=
  fun preprocess state =>
    ay_branch_conj_intro preprocessed frame
      (ay_branch_equisat_forward original preprocessed preprocess
        (ay_branch_conj_left original frame state))
      (ay_branch_conj_right original frame state)

theorem ay_branch_policy_intro
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    scores ->
    polarity ->
    randomization ->
    phase ->
    activity ->
    AyBranchHeuristicPolicy scores polarity randomization phase activity :=
  fun scoresH polarityH randomH phaseH activityH =>
    ay_branch_conj_intro scores
      (AyBranchConj polarity
        (AyBranchConj randomization
          (AyBranchConj phase activity)))
      scoresH
      (ay_branch_conj_intro polarity
        (AyBranchConj randomization
          (AyBranchConj phase activity))
        polarityH
        (ay_branch_conj_intro randomization
          (AyBranchConj phase activity)
          randomH
          (ay_branch_conj_intro phase activity phaseH activityH)))

theorem ay_branch_policy_scores
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    scores :=
  fun policy =>
    ay_branch_conj_left scores
      (AyBranchConj polarity
        (AyBranchConj randomization
          (AyBranchConj phase activity)))
      policy

theorem ay_branch_policy_polarity
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    polarity :=
  fun policy =>
    ay_branch_conj_left polarity
      (AyBranchConj randomization (AyBranchConj phase activity))
      (ay_branch_conj_right scores
        (AyBranchConj polarity
          (AyBranchConj randomization
            (AyBranchConj phase activity)))
        policy)

theorem ay_branch_policy_randomization
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    randomization :=
  fun policy =>
    ay_branch_conj_left randomization (AyBranchConj phase activity)
      (ay_branch_conj_right polarity
        (AyBranchConj randomization (AyBranchConj phase activity))
        (ay_branch_conj_right scores
          (AyBranchConj polarity
            (AyBranchConj randomization
              (AyBranchConj phase activity)))
          policy))

theorem ay_branch_policy_phase
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    phase :=
  fun policy =>
    ay_branch_conj_left phase activity
      (ay_branch_conj_right randomization
        (AyBranchConj phase activity)
        (ay_branch_conj_right polarity
          (AyBranchConj randomization (AyBranchConj phase activity))
          (ay_branch_conj_right scores
            (AyBranchConj polarity
              (AyBranchConj randomization
                (AyBranchConj phase activity)))
            policy)))

theorem ay_branch_policy_activity
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    activity :=
  fun policy =>
    ay_branch_conj_right phase activity
      (ay_branch_conj_right randomization
        (AyBranchConj phase activity)
        (ay_branch_conj_right polarity
          (AyBranchConj randomization (AyBranchConj phase activity))
          (ay_branch_conj_right scores
            (AyBranchConj polarity
              (AyBranchConj randomization
                (AyBranchConj phase activity)))
            policy)))

theorem ay_branch_policy_preserved_with_sat
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (model conflict frame : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    model ->
    frame ->
    AyBranchPolicyResult
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult (AyBranchOutcome model conflict) frame) :=
  fun policy modelH frameH =>
    ay_branch_conj_intro
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult (AyBranchOutcome model conflict) frame)
      policy
      (ay_branch_conj_intro
        (AyBranchOutcome model conflict)
        frame
        (ay_branch_disj_left model conflict modelH)
        frameH)

theorem ay_branch_policy_preserved_with_unsat
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (model conflict frame : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    conflict ->
    frame ->
    AyBranchPolicyResult
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult (AyBranchOutcome model conflict) frame) :=
  fun policy conflictH frameH =>
    ay_branch_conj_intro
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult (AyBranchOutcome model conflict) frame)
      policy
      (ay_branch_conj_intro
        (AyBranchOutcome model conflict)
        frame
        (ay_branch_disj_right model conflict conflictH)
        frameH)

theorem ay_branch_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyBranchGuardMatch guard frame :=
  fun guardH frameH =>
    ay_branch_conj_intro guard frame guardH frameH

theorem ay_branch_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyBranchGuardMatch guard frame -> guard :=
  fun matched =>
    ay_branch_conj_left guard frame matched

theorem ay_branch_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyBranchGuardMatch guard frame -> frame :=
  fun matched =>
    ay_branch_conj_right guard frame matched

theorem ay_branch_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyBranchLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_branch_conj_intro guard
      (AyBranchConj learnedClause checker)
      guardH
      (ay_branch_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_branch_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyBranchLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_branch_conj_left learnedClause checker
      (ay_branch_conj_right guard
        (AyBranchConj learnedClause checker)
        entry)

theorem ay_branch_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyBranchLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_branch_conj_right learnedClause checker
      (ay_branch_conj_right guard
        (AyBranchConj learnedClause checker)
        entry)

theorem ay_branch_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchGuardMatch guard frame ->
    AyBranchLearnedEntry guard learnedClause checker ->
    AyBranchAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_branch_conj_intro (AyBranchGuardMatch guard frame)
      (AyBranchLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_branch_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker ->
    AyBranchGuardMatch guard frame :=
  fun reuse =>
    ay_branch_conj_left (AyBranchGuardMatch guard frame)
      (AyBranchLearnedEntry guard learnedClause checker)
      reuse

theorem ay_branch_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker ->
    AyBranchLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_branch_conj_right (AyBranchGuardMatch guard frame)
      (AyBranchLearnedEntry guard learnedClause checker)
      reuse

theorem ay_branch_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_branch_guard_match_guard guard frame
      (ay_branch_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_branch_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_branch_guard_match_frame guard frame
      (ay_branch_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_branch_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_branch_learned_entry_clause guard learnedClause checker
      (ay_branch_reuse_entry frame guard learnedClause checker reuse)

theorem ay_branch_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyBranchAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_branch_learned_entry_checker guard learnedClause checker
      (ay_branch_reuse_entry frame guard learnedClause checker reuse)

theorem ay_branch_heuristic_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (model conflict : Prop) :
    AyBranchEquisat original preprocessed ->
    assumption ->
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    (preprocessed -> model) ->
    AyBranchState original base ->
    AyBranchPolicyResult
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult
        (AyBranchOutcome model conflict)
        (AyBranchScope base assumption)) :=
  fun preprocess assumptionH policy sat state =>
    ay_branch_policy_preserved_with_sat
      scores polarity randomization phase activity model conflict
      (AyBranchScope base assumption)
      policy
      (sat
        (ay_branch_conj_left preprocessed
          (AyBranchScope base assumption)
          (ay_branch_preprocess_forward original preprocessed
            (AyBranchScope base assumption)
            preprocess
            (ay_branch_state_push original base assumption
              state assumptionH))))
      (ay_branch_scope_push base assumption
        (ay_branch_conj_right original base state)
        assumptionH)

theorem ay_branch_heuristic_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (model conflict : Prop) :
    assumption ->
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    conflict ->
    base ->
    AyBranchPolicyResult
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult
        (AyBranchOutcome model conflict)
        (AyBranchScope base assumption)) :=
  fun assumptionH policy conflictH baseH =>
    ay_branch_policy_preserved_with_unsat
      scores polarity randomization phase activity model conflict
      (AyBranchScope base assumption)
      policy
      conflictH
      (ay_branch_scope_push base assumption baseH assumptionH)

theorem ay_branch_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBranchAcceptedReuse
      (AyBranchScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBranchPublicResult
      (AyBranchOutcome model conflict)
      (AyBranchScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_branch_conj_intro
      (AyBranchOutcome model conflict)
      (AyBranchScope base assumption)
      (ay_branch_disj_right model conflict
        (learnedToConflict
          (ay_branch_reuse_learned_clause
            (AyBranchScope base assumption)
            guard learnedClause checker reuse)))
      (ay_branch_reuse_current_frame
        (AyBranchScope base assumption)
        guard learnedClause checker reuse)

theorem ay_branch_learned_reuse_with_policy_sound
    (base : Prop) (assumption : Prop)
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    AyBranchAcceptedReuse
      (AyBranchScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyBranchPolicyResult
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult
        (AyBranchOutcome model conflict)
        (AyBranchScope base assumption)) :=
  fun policy reuse learnedToConflict =>
    ay_branch_conj_intro
      (AyBranchHeuristicPolicy scores polarity randomization phase activity)
      (AyBranchPublicResult
        (AyBranchOutcome model conflict)
        (AyBranchScope base assumption))
      policy
      (ay_branch_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_branch_heuristic_policy_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (scores : Prop) (polarity : Prop) (randomization : Prop)
    (phase : Prop) (activity : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyBranchEquisat original preprocessed ->
    assumption ->
    AyBranchHeuristicPolicy scores polarity randomization phase activity ->
    AyBranchAcceptedReuse
      (AyBranchScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyBranchState original base ->
    AyBranchConj
      (AyBranchPolicyResult
        (AyBranchHeuristicPolicy scores polarity randomization phase activity)
        (AyBranchPublicResult
          (AyBranchOutcome model conflict)
          (AyBranchScope base assumption)))
      (AyBranchPolicyResult
        (AyBranchHeuristicPolicy scores polarity randomization phase activity)
        (AyBranchPublicResult
          (AyBranchOutcome model conflict)
          (AyBranchScope base assumption))) :=
  fun preprocess assumptionH policy reuse sat learnedToConflict state =>
    ay_branch_conj_intro
      (AyBranchPolicyResult
        (AyBranchHeuristicPolicy scores polarity randomization phase activity)
        (AyBranchPublicResult
          (AyBranchOutcome model conflict)
          (AyBranchScope base assumption)))
      (AyBranchPolicyResult
        (AyBranchHeuristicPolicy scores polarity randomization phase activity)
        (AyBranchPublicResult
          (AyBranchOutcome model conflict)
          (AyBranchScope base assumption)))
      (ay_branch_heuristic_guides_sat_without_changing_soundness
        original preprocessed base assumption scores polarity randomization
        phase activity model conflict preprocess assumptionH policy sat state)
      (ay_branch_learned_reuse_with_policy_sound
        base assumption scores polarity randomization phase activity
        guard learnedClause checker model conflict policy reuse
        learnedToConflict)
