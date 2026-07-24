-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked restart/phase cache soundness skeleton for SAT-COMP SAT solving.
-- Restart snapshots and phase-saving assignments are search guidance only:
-- they can be carried through a checked branch result, but do not create SAT
-- or UNSAT evidence. Learned-clause cache reuse remains guarded by an explicit
-- match with the current assumption frame.

def AyRestartConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRestartDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRestartEquisat (before : Prop) (after : Prop) :=
  AyRestartConj (before -> after) (after -> before)

def AyRestartScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyRestartState (formula : Prop) (frame : Prop) :=
  AyRestartConj formula frame

def AyRestartGuidance (snapshot : Prop) (phase : Prop) :=
  AyRestartConj snapshot phase

def AyRestartGuardMatch (guard : Prop) (frame : Prop) :=
  AyRestartConj guard frame

def AyRestartLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyRestartConj guard (AyRestartConj learnedClause checker)

def AyRestartAcceptedLearned
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyRestartConj (AyRestartGuardMatch guard frame)
    (AyRestartLearnedEntry guard learnedClause checker)

def AyRestartBranchOutcome (model : Prop) (conflict : Prop) :=
  AyRestartDisj model conflict

def AyRestartPublicResult (outcome : Prop) (frame : Prop) :=
  AyRestartConj outcome frame

def AyRestartGuidedResult (guidance : Prop) (public : Prop) :=
  AyRestartConj guidance public

theorem ay_restart_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRestartConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_restart_conj_left
    (left : Prop) (right : Prop) :
    AyRestartConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_restart_conj_right
    (left : Prop) (right : Prop) :
    AyRestartConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_restart_disj_left
    (left : Prop) (right : Prop) :
    left -> AyRestartDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_restart_disj_right
    (left : Prop) (right : Prop) :
    right -> AyRestartDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_restart_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyRestartEquisat before after :=
  fun forward backward =>
    ay_restart_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_restart_equisat_forward
    (before : Prop) (after : Prop) :
    AyRestartEquisat before after -> before -> after :=
  fun equisat =>
    ay_restart_conj_left (before -> after) (after -> before)
      equisat

theorem ay_restart_equisat_backward
    (before : Prop) (after : Prop) :
    AyRestartEquisat before after -> after -> before :=
  fun equisat =>
    ay_restart_conj_right (before -> after) (after -> before)
      equisat

theorem ay_restart_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyRestartScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_restart_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyRestartState formula base ->
    assumption ->
    AyRestartState formula (AyRestartScope base assumption) :=
  fun state assumptionH =>
    ay_restart_conj_intro formula (AyRestartScope base assumption)
      (ay_restart_conj_left formula base state)
      (ay_restart_scope_push base assumption
        (ay_restart_conj_right formula base state)
        assumptionH)

theorem ay_restart_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyRestartEquisat original preprocessed ->
    AyRestartState original frame ->
    AyRestartState preprocessed frame :=
  fun preprocess state =>
    ay_restart_conj_intro preprocessed frame
      (ay_restart_equisat_forward original preprocessed preprocess
        (ay_restart_conj_left original frame state))
      (ay_restart_conj_right original frame state)

theorem ay_restart_guidance_intro
    (snapshot : Prop) (phase : Prop) :
    snapshot -> phase -> AyRestartGuidance snapshot phase :=
  fun snapshotH phaseH =>
    ay_restart_conj_intro snapshot phase snapshotH phaseH

theorem ay_restart_guidance_snapshot
    (snapshot : Prop) (phase : Prop) :
    AyRestartGuidance snapshot phase -> snapshot :=
  fun guidance =>
    ay_restart_conj_left snapshot phase guidance

theorem ay_restart_guidance_phase
    (snapshot : Prop) (phase : Prop) :
    AyRestartGuidance snapshot phase -> phase :=
  fun guidance =>
    ay_restart_conj_right snapshot phase guidance

theorem ay_restart_guidance_preserved_with_sat
    (snapshot : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyRestartGuidance snapshot phase ->
    model ->
    frame ->
    AyRestartGuidedResult
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        frame) :=
  fun guidance modelH frameH =>
    ay_restart_conj_intro
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        frame)
      guidance
      (ay_restart_conj_intro
        (AyRestartBranchOutcome model conflict)
        frame
        (ay_restart_disj_left model conflict modelH)
        frameH)

theorem ay_restart_guidance_preserved_with_unsat
    (snapshot : Prop) (phase : Prop)
    (model conflict frame : Prop) :
    AyRestartGuidance snapshot phase ->
    conflict ->
    frame ->
    AyRestartGuidedResult
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        frame) :=
  fun guidance conflictH frameH =>
    ay_restart_conj_intro
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        frame)
      guidance
      (ay_restart_conj_intro
        (AyRestartBranchOutcome model conflict)
        frame
        (ay_restart_disj_right model conflict conflictH)
        frameH)

theorem ay_restart_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyRestartGuardMatch guard frame :=
  fun guardH frameH =>
    ay_restart_conj_intro guard frame guardH frameH

theorem ay_restart_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyRestartGuardMatch guard frame -> guard :=
  fun matched =>
    ay_restart_conj_left guard frame matched

theorem ay_restart_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyRestartGuardMatch guard frame -> frame :=
  fun matched =>
    ay_restart_conj_right guard frame matched

theorem ay_restart_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyRestartLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_restart_conj_intro guard
      (AyRestartConj learnedClause checker)
      guardH
      (ay_restart_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_restart_learned_entry_guard
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyRestartLearnedEntry guard learnedClause checker -> guard :=
  fun entry =>
    ay_restart_conj_left guard
      (AyRestartConj learnedClause checker)
      entry

theorem ay_restart_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyRestartLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_restart_conj_left learnedClause checker
      (ay_restart_conj_right guard
        (AyRestartConj learnedClause checker)
        entry)

theorem ay_restart_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyRestartLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_restart_conj_right learnedClause checker
      (ay_restart_conj_right guard
        (AyRestartConj learnedClause checker)
        entry)

theorem ay_restart_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartGuardMatch guard frame ->
    AyRestartLearnedEntry guard learnedClause checker ->
    AyRestartAcceptedLearned frame guard learnedClause checker :=
  fun matched entry =>
    ay_restart_conj_intro (AyRestartGuardMatch guard frame)
      (AyRestartLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_restart_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    AyRestartGuardMatch guard frame :=
  fun reuse =>
    ay_restart_conj_left (AyRestartGuardMatch guard frame)
      (AyRestartLearnedEntry guard learnedClause checker)
      reuse

theorem ay_restart_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    AyRestartLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_restart_conj_right (AyRestartGuardMatch guard frame)
      (AyRestartLearnedEntry guard learnedClause checker)
      reuse

theorem ay_restart_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    guard :=
  fun reuse =>
    ay_restart_guard_match_guard guard frame
      (ay_restart_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_restart_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    frame :=
  fun reuse =>
    ay_restart_guard_match_frame guard frame
      (ay_restart_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_restart_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_restart_learned_entry_clause guard learnedClause checker
      (ay_restart_reuse_entry frame guard learnedClause checker reuse)

theorem ay_restart_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartAcceptedLearned frame guard learnedClause checker ->
    checker :=
  fun reuse =>
    ay_restart_learned_entry_checker guard learnedClause checker
      (ay_restart_reuse_entry frame guard learnedClause checker reuse)

theorem ay_restart_phase_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (snapshot : Prop) (phase : Prop)
    (model conflict : Prop) :
    AyRestartEquisat original preprocessed ->
    assumption ->
    AyRestartGuidance snapshot phase ->
    (preprocessed -> model) ->
    AyRestartState original base ->
    AyRestartGuidedResult
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        (AyRestartScope base assumption)) :=
  fun preprocess assumptionH guidance sat state =>
    ay_restart_guidance_preserved_with_sat
      snapshot phase model conflict (AyRestartScope base assumption)
      guidance
      (sat
        (ay_restart_conj_left preprocessed
          (AyRestartScope base assumption)
          (ay_restart_preprocess_forward original preprocessed
            (AyRestartScope base assumption)
            preprocess
            (ay_restart_state_push original base assumption
              state assumptionH))))
      (ay_restart_scope_push base assumption
        (ay_restart_conj_right original base state)
        assumptionH)

theorem ay_restart_phase_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (snapshot : Prop) (phase : Prop)
    (model conflict : Prop) :
    assumption ->
    AyRestartGuidance snapshot phase ->
    conflict ->
    base ->
    AyRestartGuidedResult
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        (AyRestartScope base assumption)) :=
  fun assumptionH guidance conflictH baseH =>
    ay_restart_guidance_preserved_with_unsat
      snapshot phase model conflict (AyRestartScope base assumption)
      guidance
      conflictH
      (ay_restart_scope_push base assumption baseH assumptionH)

theorem ay_restart_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyRestartAcceptedLearned
      (AyRestartScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyRestartPublicResult
      (AyRestartBranchOutcome model conflict)
      (AyRestartScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_restart_conj_intro
      (AyRestartBranchOutcome model conflict)
      (AyRestartScope base assumption)
      (ay_restart_disj_right model conflict
        (learnedToConflict
          (ay_restart_reuse_learned_clause
            (AyRestartScope base assumption)
            guard learnedClause checker reuse)))
      (ay_restart_reuse_current_frame
        (AyRestartScope base assumption)
        guard learnedClause checker reuse)

theorem ay_restart_learned_reuse_with_guidance_sound
    (base : Prop) (assumption : Prop)
    (snapshot : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyRestartGuidance snapshot phase ->
    AyRestartAcceptedLearned
      (AyRestartScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyRestartGuidedResult
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        (AyRestartScope base assumption)) :=
  fun guidance reuse learnedToConflict =>
    ay_restart_conj_intro
      (AyRestartGuidance snapshot phase)
      (AyRestartPublicResult
        (AyRestartBranchOutcome model conflict)
        (AyRestartScope base assumption))
      guidance
      (ay_restart_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_restart_full_cache_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (snapshot : Prop) (phase : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyRestartEquisat original preprocessed ->
    assumption ->
    AyRestartGuidance snapshot phase ->
    AyRestartAcceptedLearned
      (AyRestartScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyRestartState original base ->
    AyRestartConj
      (AyRestartGuidedResult
        (AyRestartGuidance snapshot phase)
        (AyRestartPublicResult
          (AyRestartBranchOutcome model conflict)
          (AyRestartScope base assumption)))
      (AyRestartGuidedResult
        (AyRestartGuidance snapshot phase)
        (AyRestartPublicResult
          (AyRestartBranchOutcome model conflict)
          (AyRestartScope base assumption))) :=
  fun preprocess assumptionH guidance reuse sat learnedToConflict state =>
    ay_restart_conj_intro
      (AyRestartGuidedResult
        (AyRestartGuidance snapshot phase)
        (AyRestartPublicResult
          (AyRestartBranchOutcome model conflict)
          (AyRestartScope base assumption)))
      (AyRestartGuidedResult
        (AyRestartGuidance snapshot phase)
        (AyRestartPublicResult
          (AyRestartBranchOutcome model conflict)
          (AyRestartScope base assumption)))
      (ay_restart_phase_guides_sat_without_changing_soundness
        original preprocessed base assumption snapshot phase
        model conflict preprocess assumptionH guidance sat state)
      (ay_restart_learned_reuse_with_guidance_sound
        base assumption snapshot phase guard learnedClause checker
        model conflict guidance reuse learnedToConflict)
