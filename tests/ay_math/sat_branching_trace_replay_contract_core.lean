-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked branching trace replay contract for SAT-COMP SAT solving. Accepted
-- replay of a seed/digest/decision trace reconstructs search guidance only.
-- Public SAT/UNSAT soundness still comes from accepted certificates and from
-- guard-matched reuse of learned artifacts.

def AyTraceConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyTraceDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyTraceEquisat (before : Prop) (after : Prop) :=
  AyTraceConj (before -> after) (after -> before)

def AyTraceScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyTraceState (formula : Prop) (frame : Prop) :=
  AyTraceConj formula frame

def AyTraceGuidance
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyTraceConj digest
    (AyTraceConj seed
      (AyTraceConj variableDecision polarityDecision))

def AyTraceReplayAccepted
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyTraceConj (AyTraceConj digest seed)
    (AyTraceConj variableDecision polarityDecision)

def AyTraceGuardMatch (guard : Prop) (frame : Prop) :=
  AyTraceConj guard frame

def AyTraceLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyTraceConj guard (AyTraceConj learnedClause checker)

def AyTraceAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyTraceConj (AyTraceGuardMatch guard frame)
    (AyTraceLearnedEntry guard learnedClause checker)

def AyTraceOutcome (model : Prop) (conflict : Prop) :=
  AyTraceDisj model conflict

def AyTracePublicResult (outcome : Prop) (frame : Prop) :=
  AyTraceConj outcome frame

def AyTraceGuidedResult (guidance : Prop) (public : Prop) :=
  AyTraceConj guidance public

theorem ay_trace_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyTraceConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_trace_conj_left
    (left : Prop) (right : Prop) :
    AyTraceConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_trace_conj_right
    (left : Prop) (right : Prop) :
    AyTraceConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_trace_disj_left
    (left : Prop) (right : Prop) :
    left -> AyTraceDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_trace_disj_right
    (left : Prop) (right : Prop) :
    right -> AyTraceDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_trace_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyTraceEquisat before after :=
  fun forward backward =>
    ay_trace_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_trace_equisat_forward
    (before : Prop) (after : Prop) :
    AyTraceEquisat before after -> before -> after :=
  fun equisat =>
    ay_trace_conj_left (before -> after) (after -> before)
      equisat

theorem ay_trace_equisat_backward
    (before : Prop) (after : Prop) :
    AyTraceEquisat before after -> after -> before :=
  fun equisat =>
    ay_trace_conj_right (before -> after) (after -> before)
      equisat

theorem ay_trace_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyTraceScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_trace_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyTraceState formula base ->
    assumption ->
    AyTraceState formula (AyTraceScope base assumption) :=
  fun state assumptionH =>
    ay_trace_conj_intro formula (AyTraceScope base assumption)
      (ay_trace_conj_left formula base state)
      (ay_trace_scope_push base assumption
        (ay_trace_conj_right formula base state)
        assumptionH)

theorem ay_trace_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyTraceEquisat original preprocessed ->
    AyTraceState original frame ->
    AyTraceState preprocessed frame :=
  fun preprocess state =>
    ay_trace_conj_intro preprocessed frame
      (ay_trace_equisat_forward original preprocessed preprocess
        (ay_trace_conj_left original frame state))
      (ay_trace_conj_right original frame state)

theorem ay_trace_guidance_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    digest ->
    seed ->
    variableDecision ->
    polarityDecision ->
    AyTraceGuidance digest seed variableDecision polarityDecision :=
  fun digestH seedH variableH polarityH =>
    ay_trace_conj_intro digest
      (AyTraceConj seed
        (AyTraceConj variableDecision polarityDecision))
      digestH
      (ay_trace_conj_intro seed
        (AyTraceConj variableDecision polarityDecision)
        seedH
        (ay_trace_conj_intro variableDecision polarityDecision
          variableH polarityH))

theorem ay_trace_guidance_digest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    digest :=
  fun guidance =>
    ay_trace_conj_left digest
      (AyTraceConj seed
        (AyTraceConj variableDecision polarityDecision))
      guidance

theorem ay_trace_guidance_seed
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    seed :=
  fun guidance =>
    ay_trace_conj_left seed
      (AyTraceConj variableDecision polarityDecision)
      (ay_trace_conj_right digest
        (AyTraceConj seed
          (AyTraceConj variableDecision polarityDecision))
        guidance)

theorem ay_trace_guidance_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun guidance =>
    ay_trace_conj_left variableDecision polarityDecision
      (ay_trace_conj_right seed
        (AyTraceConj variableDecision polarityDecision)
        (ay_trace_conj_right digest
          (AyTraceConj seed
            (AyTraceConj variableDecision polarityDecision))
          guidance))

theorem ay_trace_guidance_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun guidance =>
    ay_trace_conj_right variableDecision polarityDecision
      (ay_trace_conj_right seed
        (AyTraceConj variableDecision polarityDecision)
        (ay_trace_conj_right digest
          (AyTraceConj seed
            (AyTraceConj variableDecision polarityDecision))
          guidance))

theorem ay_trace_replay_accept_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    digest ->
    seed ->
    variableDecision ->
    polarityDecision ->
    AyTraceReplayAccepted digest seed variableDecision polarityDecision :=
  fun digestH seedH variableH polarityH =>
    ay_trace_conj_intro
      (AyTraceConj digest seed)
      (AyTraceConj variableDecision polarityDecision)
      (ay_trace_conj_intro digest seed digestH seedH)
      (ay_trace_conj_intro variableDecision polarityDecision
        variableH polarityH)

theorem ay_trace_replay_digest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    digest :=
  fun replay =>
    ay_trace_conj_left digest seed
      (ay_trace_conj_left
        (AyTraceConj digest seed)
        (AyTraceConj variableDecision polarityDecision)
        replay)

theorem ay_trace_replay_seed
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    seed :=
  fun replay =>
    ay_trace_conj_right digest seed
      (ay_trace_conj_left
        (AyTraceConj digest seed)
        (AyTraceConj variableDecision polarityDecision)
        replay)

theorem ay_trace_replay_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun replay =>
    ay_trace_conj_left variableDecision polarityDecision
      (ay_trace_conj_right
        (AyTraceConj digest seed)
        (AyTraceConj variableDecision polarityDecision)
        replay)

theorem ay_trace_replay_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun replay =>
    ay_trace_conj_right variableDecision polarityDecision
      (ay_trace_conj_right
        (AyTraceConj digest seed)
        (AyTraceConj variableDecision polarityDecision)
        replay)

theorem ay_trace_replay_reproduces_guidance
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    AyTraceGuidance digest seed variableDecision polarityDecision :=
  fun replay =>
    ay_trace_guidance_intro digest seed variableDecision polarityDecision
      (ay_trace_replay_digest digest seed variableDecision
        polarityDecision replay)
      (ay_trace_replay_seed digest seed variableDecision
        polarityDecision replay)
      (ay_trace_replay_variable digest seed variableDecision
        polarityDecision replay)
      (ay_trace_replay_polarity digest seed variableDecision
        polarityDecision replay)

theorem ay_trace_guidance_preserved_with_sat
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) (model conflict frame : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    model ->
    frame ->
    AyTraceGuidedResult
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult (AyTraceOutcome model conflict) frame) :=
  fun guidance modelH frameH =>
    ay_trace_conj_intro
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult (AyTraceOutcome model conflict) frame)
      guidance
      (ay_trace_conj_intro
        (AyTraceOutcome model conflict)
        frame
        (ay_trace_disj_left model conflict modelH)
        frameH)

theorem ay_trace_guidance_preserved_with_unsat
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) (model conflict frame : Prop) :
    AyTraceGuidance digest seed variableDecision polarityDecision ->
    conflict ->
    frame ->
    AyTraceGuidedResult
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult (AyTraceOutcome model conflict) frame) :=
  fun guidance conflictH frameH =>
    ay_trace_conj_intro
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult (AyTraceOutcome model conflict) frame)
      guidance
      (ay_trace_conj_intro
        (AyTraceOutcome model conflict)
        frame
        (ay_trace_disj_right model conflict conflictH)
        frameH)

theorem ay_trace_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyTraceGuardMatch guard frame :=
  fun guardH frameH =>
    ay_trace_conj_intro guard frame guardH frameH

theorem ay_trace_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyTraceGuardMatch guard frame -> guard :=
  fun matched =>
    ay_trace_conj_left guard frame matched

theorem ay_trace_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyTraceGuardMatch guard frame -> frame :=
  fun matched =>
    ay_trace_conj_right guard frame matched

theorem ay_trace_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyTraceLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_trace_conj_intro guard
      (AyTraceConj learnedClause checker)
      guardH
      (ay_trace_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_trace_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyTraceLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_trace_conj_left learnedClause checker
      (ay_trace_conj_right guard
        (AyTraceConj learnedClause checker)
        entry)

theorem ay_trace_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyTraceLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_trace_conj_right learnedClause checker
      (ay_trace_conj_right guard
        (AyTraceConj learnedClause checker)
        entry)

theorem ay_trace_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceGuardMatch guard frame ->
    AyTraceLearnedEntry guard learnedClause checker ->
    AyTraceAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_trace_conj_intro (AyTraceGuardMatch guard frame)
      (AyTraceLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_trace_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker ->
    AyTraceGuardMatch guard frame :=
  fun reuse =>
    ay_trace_conj_left (AyTraceGuardMatch guard frame)
      (AyTraceLearnedEntry guard learnedClause checker)
      reuse

theorem ay_trace_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker ->
    AyTraceLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_trace_conj_right (AyTraceGuardMatch guard frame)
      (AyTraceLearnedEntry guard learnedClause checker)
      reuse

theorem ay_trace_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_trace_guard_match_guard guard frame
      (ay_trace_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_trace_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_trace_guard_match_frame guard frame
      (ay_trace_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_trace_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_trace_learned_entry_clause guard learnedClause checker
      (ay_trace_reuse_entry frame guard learnedClause checker reuse)

theorem ay_trace_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyTraceAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_trace_learned_entry_checker guard learnedClause checker
      (ay_trace_reuse_entry frame guard learnedClause checker reuse)

theorem ay_trace_replay_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict : Prop) :
    AyTraceEquisat original preprocessed ->
    assumption ->
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    (preprocessed -> model) ->
    AyTraceState original base ->
    AyTraceGuidedResult
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult
        (AyTraceOutcome model conflict)
        (AyTraceScope base assumption)) :=
  fun preprocess assumptionH replay sat state =>
    ay_trace_guidance_preserved_with_sat
      digest seed variableDecision polarityDecision model conflict
      (AyTraceScope base assumption)
      (ay_trace_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      (sat
        (ay_trace_conj_left preprocessed
          (AyTraceScope base assumption)
          (ay_trace_preprocess_forward original preprocessed
            (AyTraceScope base assumption)
            preprocess
            (ay_trace_state_push original base assumption
              state assumptionH))))
      (ay_trace_scope_push base assumption
        (ay_trace_conj_right original base state)
        assumptionH)

theorem ay_trace_replay_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict : Prop) :
    assumption ->
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    conflict ->
    base ->
    AyTraceGuidedResult
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult
        (AyTraceOutcome model conflict)
        (AyTraceScope base assumption)) :=
  fun assumptionH replay conflictH baseH =>
    ay_trace_guidance_preserved_with_unsat
      digest seed variableDecision polarityDecision model conflict
      (AyTraceScope base assumption)
      (ay_trace_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      conflictH
      (ay_trace_scope_push base assumption baseH assumptionH)

theorem ay_trace_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyTraceAcceptedReuse
      (AyTraceScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyTracePublicResult
      (AyTraceOutcome model conflict)
      (AyTraceScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_trace_conj_intro
      (AyTraceOutcome model conflict)
      (AyTraceScope base assumption)
      (ay_trace_disj_right model conflict
        (learnedToConflict
          (ay_trace_reuse_learned_clause
            (AyTraceScope base assumption)
            guard learnedClause checker reuse)))
      (ay_trace_reuse_current_frame
        (AyTraceScope base assumption)
        guard learnedClause checker reuse)

theorem ay_trace_learned_reuse_with_replay_sound
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    AyTraceAcceptedReuse
      (AyTraceScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyTraceGuidedResult
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult
        (AyTraceOutcome model conflict)
        (AyTraceScope base assumption)) :=
  fun replay reuse learnedToConflict =>
    ay_trace_conj_intro
      (AyTraceGuidance digest seed variableDecision polarityDecision)
      (AyTracePublicResult
        (AyTraceOutcome model conflict)
        (AyTraceScope base assumption))
      (ay_trace_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      (ay_trace_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_trace_replay_contract_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyTraceEquisat original preprocessed ->
    assumption ->
    AyTraceReplayAccepted digest seed variableDecision polarityDecision ->
    AyTraceAcceptedReuse
      (AyTraceScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyTraceState original base ->
    AyTraceConj
      (AyTraceGuidedResult
        (AyTraceGuidance digest seed variableDecision polarityDecision)
        (AyTracePublicResult
          (AyTraceOutcome model conflict)
          (AyTraceScope base assumption)))
      (AyTraceGuidedResult
        (AyTraceGuidance digest seed variableDecision polarityDecision)
        (AyTracePublicResult
          (AyTraceOutcome model conflict)
          (AyTraceScope base assumption))) :=
  fun preprocess assumptionH replay reuse sat learnedToConflict state =>
    ay_trace_conj_intro
      (AyTraceGuidedResult
        (AyTraceGuidance digest seed variableDecision polarityDecision)
        (AyTracePublicResult
          (AyTraceOutcome model conflict)
          (AyTraceScope base assumption)))
      (AyTraceGuidedResult
        (AyTraceGuidance digest seed variableDecision polarityDecision)
        (AyTracePublicResult
          (AyTraceOutcome model conflict)
          (AyTraceScope base assumption)))
      (ay_trace_replay_guides_sat_without_changing_soundness
        original preprocessed base assumption digest seed variableDecision
        polarityDecision model conflict preprocess assumptionH replay
        sat state)
      (ay_trace_learned_reuse_with_replay_sound
        base assumption digest seed variableDecision polarityDecision
        guard learnedClause checker model conflict replay reuse
        learnedToConflict)
