-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked link between branching trace replay and run manifests. Manifest
-- trace digests, seeds, and branching decisions reconstruct guidance only.
-- Public report SAT/UNSAT soundness remains derived from accepted certificates
-- and guard-matched learned-artifact reuse.

def AyManifestConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyManifestDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyManifestEquisat (before : Prop) (after : Prop) :=
  AyManifestConj (before -> after) (after -> before)

def AyManifestScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyManifestState (formula : Prop) (frame : Prop) :=
  AyManifestConj formula frame

def AyManifestTrace
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyManifestConj digest
    (AyManifestConj seed
      (AyManifestConj variableDecision polarityDecision))

def AyManifestReplayAccepted
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyManifestConj (AyManifestTrace digest seed variableDecision polarityDecision)
    (AyManifestConj variableDecision polarityDecision)

def AyManifestGuardMatch (guard : Prop) (frame : Prop) :=
  AyManifestConj guard frame

def AyManifestLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyManifestConj guard (AyManifestConj learnedClause checker)

def AyManifestAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyManifestConj (AyManifestGuardMatch guard frame)
    (AyManifestLearnedEntry guard learnedClause checker)

def AyManifestOutcome (model : Prop) (conflict : Prop) :=
  AyManifestDisj model conflict

def AyManifestPublicReport (outcome : Prop) (frame : Prop) :=
  AyManifestConj outcome frame

def AyManifestGuidedReport (guidance : Prop) (public : Prop) :=
  AyManifestConj guidance public

theorem ay_manifest_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyManifestConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_manifest_conj_left
    (left : Prop) (right : Prop) :
    AyManifestConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_manifest_conj_right
    (left : Prop) (right : Prop) :
    AyManifestConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_manifest_disj_left
    (left : Prop) (right : Prop) :
    left -> AyManifestDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_manifest_disj_right
    (left : Prop) (right : Prop) :
    right -> AyManifestDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_manifest_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyManifestEquisat before after :=
  fun forward backward =>
    ay_manifest_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_manifest_equisat_forward
    (before : Prop) (after : Prop) :
    AyManifestEquisat before after -> before -> after :=
  fun equisat =>
    ay_manifest_conj_left (before -> after) (after -> before)
      equisat

theorem ay_manifest_equisat_backward
    (before : Prop) (after : Prop) :
    AyManifestEquisat before after -> after -> before :=
  fun equisat =>
    ay_manifest_conj_right (before -> after) (after -> before)
      equisat

theorem ay_manifest_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyManifestScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_manifest_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyManifestState formula base ->
    assumption ->
    AyManifestState formula (AyManifestScope base assumption) :=
  fun state assumptionH =>
    ay_manifest_conj_intro formula (AyManifestScope base assumption)
      (ay_manifest_conj_left formula base state)
      (ay_manifest_scope_push base assumption
        (ay_manifest_conj_right formula base state)
        assumptionH)

theorem ay_manifest_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyManifestEquisat original preprocessed ->
    AyManifestState original frame ->
    AyManifestState preprocessed frame :=
  fun preprocess state =>
    ay_manifest_conj_intro preprocessed frame
      (ay_manifest_equisat_forward original preprocessed preprocess
        (ay_manifest_conj_left original frame state))
      (ay_manifest_conj_right original frame state)

theorem ay_manifest_trace_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    digest ->
    seed ->
    variableDecision ->
    polarityDecision ->
    AyManifestTrace digest seed variableDecision polarityDecision :=
  fun digestH seedH variableH polarityH =>
    ay_manifest_conj_intro digest
      (AyManifestConj seed
        (AyManifestConj variableDecision polarityDecision))
      digestH
      (ay_manifest_conj_intro seed
        (AyManifestConj variableDecision polarityDecision)
        seedH
        (ay_manifest_conj_intro variableDecision polarityDecision
          variableH polarityH))

theorem ay_manifest_trace_digest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    digest :=
  fun trace =>
    ay_manifest_conj_left digest
      (AyManifestConj seed
        (AyManifestConj variableDecision polarityDecision))
      trace

theorem ay_manifest_trace_seed
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision -> seed :=
  fun trace =>
    ay_manifest_conj_left seed
      (AyManifestConj variableDecision polarityDecision)
      (ay_manifest_conj_right digest
        (AyManifestConj seed
          (AyManifestConj variableDecision polarityDecision))
        trace)

theorem ay_manifest_trace_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun trace =>
    ay_manifest_conj_left variableDecision polarityDecision
      (ay_manifest_conj_right seed
        (AyManifestConj variableDecision polarityDecision)
        (ay_manifest_conj_right digest
          (AyManifestConj seed
            (AyManifestConj variableDecision polarityDecision))
          trace))

theorem ay_manifest_trace_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun trace =>
    ay_manifest_conj_right variableDecision polarityDecision
      (ay_manifest_conj_right seed
        (AyManifestConj variableDecision polarityDecision)
        (ay_manifest_conj_right digest
          (AyManifestConj seed
            (AyManifestConj variableDecision polarityDecision))
          trace))

theorem ay_manifest_replay_accept_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    variableDecision ->
    polarityDecision ->
    AyManifestReplayAccepted digest seed variableDecision polarityDecision :=
  fun trace variableH polarityH =>
    ay_manifest_conj_intro
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestConj variableDecision polarityDecision)
      trace
      (ay_manifest_conj_intro variableDecision polarityDecision
        variableH polarityH)

theorem ay_manifest_replay_trace
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    AyManifestTrace digest seed variableDecision polarityDecision :=
  fun replay =>
    ay_manifest_conj_left
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestConj variableDecision polarityDecision)
      replay

theorem ay_manifest_replay_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun replay =>
    ay_manifest_conj_left variableDecision polarityDecision
      (ay_manifest_conj_right
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestConj variableDecision polarityDecision)
        replay)

theorem ay_manifest_replay_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun replay =>
    ay_manifest_conj_right variableDecision polarityDecision
      (ay_manifest_conj_right
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestConj variableDecision polarityDecision)
        replay)

theorem ay_manifest_replay_reproduces_guidance
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    AyManifestTrace digest seed variableDecision polarityDecision :=
  fun replay =>
    ay_manifest_trace_intro digest seed variableDecision polarityDecision
      (ay_manifest_trace_digest digest seed variableDecision polarityDecision
        (ay_manifest_replay_trace digest seed variableDecision
          polarityDecision replay))
      (ay_manifest_trace_seed digest seed variableDecision polarityDecision
        (ay_manifest_replay_trace digest seed variableDecision
          polarityDecision replay))
      (ay_manifest_replay_variable digest seed variableDecision
        polarityDecision replay)
      (ay_manifest_replay_polarity digest seed variableDecision
        polarityDecision replay)

theorem ay_manifest_guidance_preserved_with_sat
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) (model conflict frame : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    model ->
    frame ->
    AyManifestGuidedReport
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport (AyManifestOutcome model conflict) frame) :=
  fun guidance modelH frameH =>
    ay_manifest_conj_intro
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport (AyManifestOutcome model conflict) frame)
      guidance
      (ay_manifest_conj_intro
        (AyManifestOutcome model conflict)
        frame
        (ay_manifest_disj_left model conflict modelH)
        frameH)

theorem ay_manifest_guidance_preserved_with_unsat
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) (model conflict frame : Prop) :
    AyManifestTrace digest seed variableDecision polarityDecision ->
    conflict ->
    frame ->
    AyManifestGuidedReport
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport (AyManifestOutcome model conflict) frame) :=
  fun guidance conflictH frameH =>
    ay_manifest_conj_intro
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport (AyManifestOutcome model conflict) frame)
      guidance
      (ay_manifest_conj_intro
        (AyManifestOutcome model conflict)
        frame
        (ay_manifest_disj_right model conflict conflictH)
        frameH)

theorem ay_manifest_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyManifestGuardMatch guard frame :=
  fun guardH frameH =>
    ay_manifest_conj_intro guard frame guardH frameH

theorem ay_manifest_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyManifestGuardMatch guard frame -> guard :=
  fun matched =>
    ay_manifest_conj_left guard frame matched

theorem ay_manifest_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyManifestGuardMatch guard frame -> frame :=
  fun matched =>
    ay_manifest_conj_right guard frame matched

theorem ay_manifest_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyManifestLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_manifest_conj_intro guard
      (AyManifestConj learnedClause checker)
      guardH
      (ay_manifest_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_manifest_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyManifestLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_manifest_conj_left learnedClause checker
      (ay_manifest_conj_right guard
        (AyManifestConj learnedClause checker)
        entry)

theorem ay_manifest_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyManifestLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_manifest_conj_right learnedClause checker
      (ay_manifest_conj_right guard
        (AyManifestConj learnedClause checker)
        entry)

theorem ay_manifest_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestGuardMatch guard frame ->
    AyManifestLearnedEntry guard learnedClause checker ->
    AyManifestAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_manifest_conj_intro (AyManifestGuardMatch guard frame)
      (AyManifestLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_manifest_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker ->
    AyManifestGuardMatch guard frame :=
  fun reuse =>
    ay_manifest_conj_left (AyManifestGuardMatch guard frame)
      (AyManifestLearnedEntry guard learnedClause checker)
      reuse

theorem ay_manifest_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker ->
    AyManifestLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_manifest_conj_right (AyManifestGuardMatch guard frame)
      (AyManifestLearnedEntry guard learnedClause checker)
      reuse

theorem ay_manifest_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_manifest_guard_match_guard guard frame
      (ay_manifest_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_manifest_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_manifest_guard_match_frame guard frame
      (ay_manifest_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_manifest_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_manifest_learned_entry_clause guard learnedClause checker
      (ay_manifest_reuse_entry frame guard learnedClause checker reuse)

theorem ay_manifest_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyManifestAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_manifest_learned_entry_checker guard learnedClause checker
      (ay_manifest_reuse_entry frame guard learnedClause checker reuse)

theorem ay_manifest_replay_guides_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict : Prop) :
    AyManifestEquisat original preprocessed ->
    assumption ->
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    (preprocessed -> model) ->
    AyManifestState original base ->
    AyManifestGuidedReport
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport
        (AyManifestOutcome model conflict)
        (AyManifestScope base assumption)) :=
  fun preprocess assumptionH replay sat state =>
    ay_manifest_guidance_preserved_with_sat
      digest seed variableDecision polarityDecision model conflict
      (AyManifestScope base assumption)
      (ay_manifest_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      (sat
        (ay_manifest_conj_left preprocessed
          (AyManifestScope base assumption)
          (ay_manifest_preprocess_forward original preprocessed
            (AyManifestScope base assumption)
            preprocess
            (ay_manifest_state_push original base assumption
              state assumptionH))))
      (ay_manifest_scope_push base assumption
        (ay_manifest_conj_right original base state)
        assumptionH)

theorem ay_manifest_replay_guides_unsat_report
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict : Prop) :
    assumption ->
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    conflict ->
    base ->
    AyManifestGuidedReport
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport
        (AyManifestOutcome model conflict)
        (AyManifestScope base assumption)) :=
  fun assumptionH replay conflictH baseH =>
    ay_manifest_guidance_preserved_with_unsat
      digest seed variableDecision polarityDecision model conflict
      (AyManifestScope base assumption)
      (ay_manifest_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      conflictH
      (ay_manifest_scope_push base assumption baseH assumptionH)

theorem ay_manifest_learned_reuse_public_unsat_report
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyManifestAcceptedReuse
      (AyManifestScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyManifestPublicReport
      (AyManifestOutcome model conflict)
      (AyManifestScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_manifest_conj_intro
      (AyManifestOutcome model conflict)
      (AyManifestScope base assumption)
      (ay_manifest_disj_right model conflict
        (learnedToConflict
          (ay_manifest_reuse_learned_clause
            (AyManifestScope base assumption)
            guard learnedClause checker reuse)))
      (ay_manifest_reuse_current_frame
        (AyManifestScope base assumption)
        guard learnedClause checker reuse)

theorem ay_manifest_learned_reuse_with_manifest_sound
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    AyManifestAcceptedReuse
      (AyManifestScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyManifestGuidedReport
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport
        (AyManifestOutcome model conflict)
        (AyManifestScope base assumption)) :=
  fun replay reuse learnedToConflict =>
    ay_manifest_conj_intro
      (AyManifestTrace digest seed variableDecision polarityDecision)
      (AyManifestPublicReport
        (AyManifestOutcome model conflict)
        (AyManifestScope base assumption))
      (ay_manifest_replay_reproduces_guidance
        digest seed variableDecision polarityDecision replay)
      (ay_manifest_learned_reuse_public_unsat_report
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_manifest_trace_link_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyManifestEquisat original preprocessed ->
    assumption ->
    AyManifestReplayAccepted digest seed variableDecision polarityDecision ->
    AyManifestAcceptedReuse
      (AyManifestScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyManifestState original base ->
    AyManifestConj
      (AyManifestGuidedReport
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestPublicReport
          (AyManifestOutcome model conflict)
          (AyManifestScope base assumption)))
      (AyManifestGuidedReport
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestPublicReport
          (AyManifestOutcome model conflict)
          (AyManifestScope base assumption))) :=
  fun preprocess assumptionH replay reuse sat learnedToConflict state =>
    ay_manifest_conj_intro
      (AyManifestGuidedReport
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestPublicReport
          (AyManifestOutcome model conflict)
          (AyManifestScope base assumption)))
      (AyManifestGuidedReport
        (AyManifestTrace digest seed variableDecision polarityDecision)
        (AyManifestPublicReport
          (AyManifestOutcome model conflict)
          (AyManifestScope base assumption)))
      (ay_manifest_replay_guides_sat_report
        original preprocessed base assumption digest seed variableDecision
        polarityDecision model conflict preprocess assumptionH replay
        sat state)
      (ay_manifest_learned_reuse_with_manifest_sound
        base assumption digest seed variableDecision polarityDecision
        guard learnedClause checker model conflict replay reuse
        learnedToConflict)
