-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked randomized branching seed soundness skeleton for SAT-COMP SAT
-- solving. Random seed/state, tie-breaking, phase guidance, and trace digests
-- replay search guidance only; public SAT/UNSAT soundness comes from checked
-- branch outcomes. Learned-artifact reuse still requires a guard matched to
-- the current assumption frame.

def AySeedConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AySeedDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AySeedEquisat (before : Prop) (after : Prop) :=
  AySeedConj (before -> after) (after -> before)

def AySeedScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AySeedState (formula : Prop) (frame : Prop) :=
  AySeedConj formula frame

def AySeedGuidance
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :=
  AySeedConj seed
    (AySeedConj rngState
      (AySeedConj tieBreak
        (AySeedConj phase traceDigest)))

def AySeedDigestMatch (seed : Prop) (traceDigest : Prop) :=
  AySeedConj seed traceDigest

def AySeedGuardMatch (guard : Prop) (frame : Prop) :=
  AySeedConj guard frame

def AySeedLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AySeedConj guard (AySeedConj learnedClause checker)

def AySeedAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AySeedConj (AySeedGuardMatch guard frame)
    (AySeedLearnedEntry guard learnedClause checker)

def AySeedOutcome (model : Prop) (conflict : Prop) :=
  AySeedDisj model conflict

def AySeedPublicResult (outcome : Prop) (frame : Prop) :=
  AySeedConj outcome frame

def AySeedGuidedResult (guidance : Prop) (public : Prop) :=
  AySeedConj guidance public

theorem ay_seed_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AySeedConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_seed_conj_left
    (left : Prop) (right : Prop) :
    AySeedConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_seed_conj_right
    (left : Prop) (right : Prop) :
    AySeedConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_seed_disj_left
    (left : Prop) (right : Prop) :
    left -> AySeedDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_seed_disj_right
    (left : Prop) (right : Prop) :
    right -> AySeedDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_seed_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AySeedEquisat before after :=
  fun forward backward =>
    ay_seed_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_seed_equisat_forward
    (before : Prop) (after : Prop) :
    AySeedEquisat before after -> before -> after :=
  fun equisat =>
    ay_seed_conj_left (before -> after) (after -> before)
      equisat

theorem ay_seed_equisat_backward
    (before : Prop) (after : Prop) :
    AySeedEquisat before after -> after -> before :=
  fun equisat =>
    ay_seed_conj_right (before -> after) (after -> before)
      equisat

theorem ay_seed_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AySeedScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_seed_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AySeedState formula base ->
    assumption ->
    AySeedState formula (AySeedScope base assumption) :=
  fun state assumptionH =>
    ay_seed_conj_intro formula (AySeedScope base assumption)
      (ay_seed_conj_left formula base state)
      (ay_seed_scope_push base assumption
        (ay_seed_conj_right formula base state)
        assumptionH)

theorem ay_seed_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AySeedEquisat original preprocessed ->
    AySeedState original frame ->
    AySeedState preprocessed frame :=
  fun preprocess state =>
    ay_seed_conj_intro preprocessed frame
      (ay_seed_equisat_forward original preprocessed preprocess
        (ay_seed_conj_left original frame state))
      (ay_seed_conj_right original frame state)

theorem ay_seed_guidance_intro
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    seed ->
    rngState ->
    tieBreak ->
    phase ->
    traceDigest ->
    AySeedGuidance seed rngState tieBreak phase traceDigest :=
  fun seedH rngH tieH phaseH digestH =>
    ay_seed_conj_intro seed
      (AySeedConj rngState
        (AySeedConj tieBreak
          (AySeedConj phase traceDigest)))
      seedH
      (ay_seed_conj_intro rngState
        (AySeedConj tieBreak (AySeedConj phase traceDigest))
        rngH
        (ay_seed_conj_intro tieBreak
          (AySeedConj phase traceDigest)
          tieH
          (ay_seed_conj_intro phase traceDigest phaseH digestH)))

theorem ay_seed_guidance_seed
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest -> seed :=
  fun guidance =>
    ay_seed_conj_left seed
      (AySeedConj rngState
        (AySeedConj tieBreak
          (AySeedConj phase traceDigest)))
      guidance

theorem ay_seed_guidance_rng_state
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest -> rngState :=
  fun guidance =>
    ay_seed_conj_left rngState
      (AySeedConj tieBreak (AySeedConj phase traceDigest))
      (ay_seed_conj_right seed
        (AySeedConj rngState
          (AySeedConj tieBreak
            (AySeedConj phase traceDigest)))
        guidance)

theorem ay_seed_guidance_tie_break
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest -> tieBreak :=
  fun guidance =>
    ay_seed_conj_left tieBreak (AySeedConj phase traceDigest)
      (ay_seed_conj_right rngState
        (AySeedConj tieBreak (AySeedConj phase traceDigest))
        (ay_seed_conj_right seed
          (AySeedConj rngState
            (AySeedConj tieBreak
              (AySeedConj phase traceDigest)))
          guidance))

theorem ay_seed_guidance_phase
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest -> phase :=
  fun guidance =>
    ay_seed_conj_left phase traceDigest
      (ay_seed_conj_right tieBreak (AySeedConj phase traceDigest)
        (ay_seed_conj_right rngState
          (AySeedConj tieBreak (AySeedConj phase traceDigest))
          (ay_seed_conj_right seed
            (AySeedConj rngState
              (AySeedConj tieBreak
                (AySeedConj phase traceDigest)))
            guidance)))

theorem ay_seed_guidance_trace_digest
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest -> traceDigest :=
  fun guidance =>
    ay_seed_conj_right phase traceDigest
      (ay_seed_conj_right tieBreak (AySeedConj phase traceDigest)
        (ay_seed_conj_right rngState
          (AySeedConj tieBreak (AySeedConj phase traceDigest))
          (ay_seed_conj_right seed
            (AySeedConj rngState
              (AySeedConj tieBreak
                (AySeedConj phase traceDigest)))
            guidance)))

theorem ay_seed_digest_match_intro
    (seed : Prop) (traceDigest : Prop) :
    seed -> traceDigest -> AySeedDigestMatch seed traceDigest :=
  fun seedH digestH =>
    ay_seed_conj_intro seed traceDigest seedH digestH

theorem ay_seed_digest_match_seed
    (seed : Prop) (traceDigest : Prop) :
    AySeedDigestMatch seed traceDigest -> seed :=
  fun matched =>
    ay_seed_conj_left seed traceDigest matched

theorem ay_seed_digest_match_trace
    (seed : Prop) (traceDigest : Prop) :
    AySeedDigestMatch seed traceDigest -> traceDigest :=
  fun matched =>
    ay_seed_conj_right seed traceDigest matched

theorem ay_seed_matching_digest_replays_guidance
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop) :
    AySeedDigestMatch seed traceDigest ->
    rngState ->
    tieBreak ->
    phase ->
    AySeedGuidance seed rngState tieBreak phase traceDigest :=
  fun matched rngH tieH phaseH =>
    ay_seed_guidance_intro seed rngState tieBreak phase traceDigest
      (ay_seed_digest_match_seed seed traceDigest matched)
      rngH
      tieH
      phaseH
      (ay_seed_digest_match_trace seed traceDigest matched)

theorem ay_seed_guidance_preserved_with_sat
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (model conflict frame : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest ->
    model ->
    frame ->
    AySeedGuidedResult
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult (AySeedOutcome model conflict) frame) :=
  fun guidance modelH frameH =>
    ay_seed_conj_intro
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult (AySeedOutcome model conflict) frame)
      guidance
      (ay_seed_conj_intro
        (AySeedOutcome model conflict)
        frame
        (ay_seed_disj_left model conflict modelH)
        frameH)

theorem ay_seed_guidance_preserved_with_unsat
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (model conflict frame : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest ->
    conflict ->
    frame ->
    AySeedGuidedResult
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult (AySeedOutcome model conflict) frame) :=
  fun guidance conflictH frameH =>
    ay_seed_conj_intro
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult (AySeedOutcome model conflict) frame)
      guidance
      (ay_seed_conj_intro
        (AySeedOutcome model conflict)
        frame
        (ay_seed_disj_right model conflict conflictH)
        frameH)

theorem ay_seed_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AySeedGuardMatch guard frame :=
  fun guardH frameH =>
    ay_seed_conj_intro guard frame guardH frameH

theorem ay_seed_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AySeedGuardMatch guard frame -> guard :=
  fun matched =>
    ay_seed_conj_left guard frame matched

theorem ay_seed_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AySeedGuardMatch guard frame -> frame :=
  fun matched =>
    ay_seed_conj_right guard frame matched

theorem ay_seed_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AySeedLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_seed_conj_intro guard
      (AySeedConj learnedClause checker)
      guardH
      (ay_seed_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_seed_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AySeedLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_seed_conj_left learnedClause checker
      (ay_seed_conj_right guard
        (AySeedConj learnedClause checker)
        entry)

theorem ay_seed_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AySeedLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_seed_conj_right learnedClause checker
      (ay_seed_conj_right guard
        (AySeedConj learnedClause checker)
        entry)

theorem ay_seed_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedGuardMatch guard frame ->
    AySeedLearnedEntry guard learnedClause checker ->
    AySeedAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_seed_conj_intro (AySeedGuardMatch guard frame)
      (AySeedLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_seed_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker ->
    AySeedGuardMatch guard frame :=
  fun reuse =>
    ay_seed_conj_left (AySeedGuardMatch guard frame)
      (AySeedLearnedEntry guard learnedClause checker)
      reuse

theorem ay_seed_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker ->
    AySeedLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_seed_conj_right (AySeedGuardMatch guard frame)
      (AySeedLearnedEntry guard learnedClause checker)
      reuse

theorem ay_seed_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_seed_guard_match_guard guard frame
      (ay_seed_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_seed_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_seed_guard_match_frame guard frame
      (ay_seed_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_seed_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_seed_learned_entry_clause guard learnedClause checker
      (ay_seed_reuse_entry frame guard learnedClause checker reuse)

theorem ay_seed_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AySeedAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_seed_learned_entry_checker guard learnedClause checker
      (ay_seed_reuse_entry frame guard learnedClause checker reuse)

theorem ay_seed_guides_sat_without_changing_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (model conflict : Prop) :
    AySeedEquisat original preprocessed ->
    assumption ->
    AySeedGuidance seed rngState tieBreak phase traceDigest ->
    (preprocessed -> model) ->
    AySeedState original base ->
    AySeedGuidedResult
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult
        (AySeedOutcome model conflict)
        (AySeedScope base assumption)) :=
  fun preprocess assumptionH guidance sat state =>
    ay_seed_guidance_preserved_with_sat
      seed rngState tieBreak phase traceDigest model conflict
      (AySeedScope base assumption)
      guidance
      (sat
        (ay_seed_conj_left preprocessed
          (AySeedScope base assumption)
          (ay_seed_preprocess_forward original preprocessed
            (AySeedScope base assumption)
            preprocess
            (ay_seed_state_push original base assumption
              state assumptionH))))
      (ay_seed_scope_push base assumption
        (ay_seed_conj_right original base state)
        assumptionH)

theorem ay_seed_guides_unsat_without_changing_soundness
    (base : Prop) (assumption : Prop)
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (model conflict : Prop) :
    assumption ->
    AySeedGuidance seed rngState tieBreak phase traceDigest ->
    conflict ->
    base ->
    AySeedGuidedResult
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult
        (AySeedOutcome model conflict)
        (AySeedScope base assumption)) :=
  fun assumptionH guidance conflictH baseH =>
    ay_seed_guidance_preserved_with_unsat
      seed rngState tieBreak phase traceDigest model conflict
      (AySeedScope base assumption)
      guidance
      conflictH
      (ay_seed_scope_push base assumption baseH assumptionH)

theorem ay_seed_learned_reuse_public_unsat
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AySeedAcceptedReuse
      (AySeedScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AySeedPublicResult
      (AySeedOutcome model conflict)
      (AySeedScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_seed_conj_intro
      (AySeedOutcome model conflict)
      (AySeedScope base assumption)
      (ay_seed_disj_right model conflict
        (learnedToConflict
          (ay_seed_reuse_learned_clause
            (AySeedScope base assumption)
            guard learnedClause checker reuse)))
      (ay_seed_reuse_current_frame
        (AySeedScope base assumption)
        guard learnedClause checker reuse)

theorem ay_seed_learned_reuse_with_guidance_sound
    (base : Prop) (assumption : Prop)
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AySeedGuidance seed rngState tieBreak phase traceDigest ->
    AySeedAcceptedReuse
      (AySeedScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AySeedGuidedResult
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult
        (AySeedOutcome model conflict)
        (AySeedScope base assumption)) :=
  fun guidance reuse learnedToConflict =>
    ay_seed_conj_intro
      (AySeedGuidance seed rngState tieBreak phase traceDigest)
      (AySeedPublicResult
        (AySeedOutcome model conflict)
        (AySeedScope base assumption))
      guidance
      (ay_seed_learned_reuse_public_unsat
        base assumption guard learnedClause checker model conflict
        reuse learnedToConflict)

theorem ay_seed_matching_digest_replay_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (seed : Prop) (rngState : Prop) (tieBreak : Prop)
    (phase : Prop) (traceDigest : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AySeedEquisat original preprocessed ->
    assumption ->
    AySeedDigestMatch seed traceDigest ->
    rngState ->
    tieBreak ->
    phase ->
    AySeedAcceptedReuse
      (AySeedScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AySeedState original base ->
    AySeedConj
      (AySeedGuidedResult
        (AySeedGuidance seed rngState tieBreak phase traceDigest)
        (AySeedPublicResult
          (AySeedOutcome model conflict)
          (AySeedScope base assumption)))
      (AySeedGuidedResult
        (AySeedGuidance seed rngState tieBreak phase traceDigest)
        (AySeedPublicResult
          (AySeedOutcome model conflict)
          (AySeedScope base assumption))) :=
  fun preprocess assumptionH matched rngH tieH phaseH reuse
      sat learnedToConflict state =>
    ay_seed_conj_intro
      (AySeedGuidedResult
        (AySeedGuidance seed rngState tieBreak phase traceDigest)
        (AySeedPublicResult
          (AySeedOutcome model conflict)
          (AySeedScope base assumption)))
      (AySeedGuidedResult
        (AySeedGuidance seed rngState tieBreak phase traceDigest)
        (AySeedPublicResult
          (AySeedOutcome model conflict)
          (AySeedScope base assumption)))
      (ay_seed_guides_sat_without_changing_soundness
        original preprocessed base assumption seed rngState tieBreak phase
        traceDigest model conflict preprocess assumptionH
        (ay_seed_matching_digest_replays_guidance
          seed rngState tieBreak phase traceDigest matched rngH tieH phaseH)
        sat state)
      (ay_seed_learned_reuse_with_guidance_sound
        base assumption seed rngState tieBreak phase traceDigest
        guard learnedClause checker model conflict
        (ay_seed_matching_digest_replays_guidance
          seed rngState tieBreak phase traceDigest matched rngH tieH phaseH)
        reuse learnedToConflict)
