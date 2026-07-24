-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked skeleton for sound learned-clause/cache reuse across incremental
-- SAT assumption frames. Cache guards, current frames, replay segments, and
-- public outcomes are abstract propositions. The theorem package records that
-- reuse is sound only after the cached guard matches the current frame, and
-- that accepted reuse preserves SAT/UNSAT public soundness for that frame.

def AyCacheConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyCacheDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCacheEquisat (before : Prop) (after : Prop) :=
  AyCacheConj (before -> after) (after -> before)

def AyCacheScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyCacheState (formula : Prop) (frame : Prop) :=
  AyCacheConj formula frame

def AyCacheGuardMatch (guard : Prop) (frame : Prop) :=
  AyCacheConj guard frame

def AyCacheReplaySegment
    (start : Prop) (finish : Prop) (learnedClause : Prop) :=
  AyCacheConj (start -> finish) (finish -> learnedClause)

def AyCacheEntry
    (guard : Prop) (learnedClause : Prop) (segment : Prop) :=
  AyCacheConj guard (AyCacheConj learnedClause segment)

def AyCacheAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (segment : Prop) :=
  AyCacheConj (AyCacheGuardMatch guard frame)
    (AyCacheEntry guard learnedClause segment)

def AyCacheOutcome (model : Prop) (conflict : Prop) :=
  AyCacheDisj model conflict

def AyCachePublicResult (outcome : Prop) (frame : Prop) :=
  AyCacheConj outcome frame

theorem ay_cache_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyCacheConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_cache_conj_left
    (left : Prop) (right : Prop) :
    AyCacheConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_cache_conj_right
    (left : Prop) (right : Prop) :
    AyCacheConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_cache_disj_left
    (left : Prop) (right : Prop) :
    left -> AyCacheDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_cache_disj_right
    (left : Prop) (right : Prop) :
    right -> AyCacheDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_cache_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyCacheEquisat before after :=
  fun forward backward =>
    ay_cache_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_cache_equisat_forward
    (before : Prop) (after : Prop) :
    AyCacheEquisat before after -> before -> after :=
  fun equisat =>
    ay_cache_conj_left (before -> after) (after -> before) equisat

theorem ay_cache_equisat_backward
    (before : Prop) (after : Prop) :
    AyCacheEquisat before after -> after -> before :=
  fun equisat =>
    ay_cache_conj_right (before -> after) (after -> before) equisat

theorem ay_cache_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyCacheScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_cache_scope_base
    (base : Prop) (assumption : Prop) :
    AyCacheScope base assumption -> base :=
  fun scope =>
    scope base (fun baseH _assumptionH => baseH)

theorem ay_cache_scope_assumption
    (base : Prop) (assumption : Prop) :
    AyCacheScope base assumption -> assumption :=
  fun scope =>
    scope assumption (fun _baseH assumptionH => assumptionH)

theorem ay_cache_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyCacheState formula base ->
    assumption ->
    AyCacheState formula (AyCacheScope base assumption) :=
  fun state assumptionH =>
    ay_cache_conj_intro formula (AyCacheScope base assumption)
      (ay_cache_conj_left formula base state)
      (ay_cache_scope_push base assumption
        (ay_cache_conj_right formula base state)
        assumptionH)

theorem ay_cache_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyCacheEquisat original preprocessed ->
    AyCacheState original frame ->
    AyCacheState preprocessed frame :=
  fun preprocess state =>
    ay_cache_conj_intro preprocessed frame
      (ay_cache_equisat_forward original preprocessed preprocess
        (ay_cache_conj_left original frame state))
      (ay_cache_conj_right original frame state)

theorem ay_cache_preprocess_backward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyCacheEquisat original preprocessed ->
    AyCacheState preprocessed frame ->
    AyCacheState original frame :=
  fun preprocess state =>
    ay_cache_conj_intro original frame
      (ay_cache_equisat_backward original preprocessed preprocess
        (ay_cache_conj_left preprocessed frame state))
      (ay_cache_conj_right preprocessed frame state)

theorem ay_cache_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyCacheGuardMatch guard frame :=
  fun guardH frameH =>
    ay_cache_conj_intro guard frame guardH frameH

theorem ay_cache_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyCacheGuardMatch guard frame -> guard :=
  fun matched =>
    ay_cache_conj_left guard frame matched

theorem ay_cache_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyCacheGuardMatch guard frame -> frame :=
  fun matched =>
    ay_cache_conj_right guard frame matched

theorem ay_cache_segment_intro
    (start : Prop) (finish : Prop) (learnedClause : Prop) :
    (start -> finish) ->
    (finish -> learnedClause) ->
    AyCacheReplaySegment start finish learnedClause :=
  fun replay learned =>
    ay_cache_conj_intro (start -> finish) (finish -> learnedClause)
      replay learned

theorem ay_cache_segment_lookup_step
    (start : Prop) (finish : Prop) (learnedClause : Prop) :
    AyCacheReplaySegment start finish learnedClause ->
    start ->
    finish :=
  fun segment =>
    ay_cache_conj_left (start -> finish) (finish -> learnedClause)
      segment

theorem ay_cache_segment_lookup_learned
    (start : Prop) (finish : Prop) (learnedClause : Prop) :
    AyCacheReplaySegment start finish learnedClause ->
    finish ->
    learnedClause :=
  fun segment =>
    ay_cache_conj_right (start -> finish) (finish -> learnedClause)
      segment

theorem ay_cache_entry_intro
    (guard : Prop) (learnedClause : Prop) (segment : Prop) :
    guard ->
    learnedClause ->
    segment ->
    AyCacheEntry guard learnedClause segment :=
  fun guardH learnedH segmentH =>
    ay_cache_conj_intro guard (AyCacheConj learnedClause segment)
      guardH
      (ay_cache_conj_intro learnedClause segment learnedH segmentH)

theorem ay_cache_entry_guard
    (guard : Prop) (learnedClause : Prop) (segment : Prop) :
    AyCacheEntry guard learnedClause segment -> guard :=
  fun entry =>
    ay_cache_conj_left guard (AyCacheConj learnedClause segment)
      entry

theorem ay_cache_entry_learned
    (guard : Prop) (learnedClause : Prop) (segment : Prop) :
    AyCacheEntry guard learnedClause segment -> learnedClause :=
  fun entry =>
    ay_cache_conj_left learnedClause segment
      (ay_cache_conj_right guard (AyCacheConj learnedClause segment)
        entry)

theorem ay_cache_entry_segment
    (guard : Prop) (learnedClause : Prop) (segment : Prop) :
    AyCacheEntry guard learnedClause segment -> segment :=
  fun entry =>
    ay_cache_conj_right learnedClause segment
      (ay_cache_conj_right guard (AyCacheConj learnedClause segment)
        entry)

theorem ay_cache_accept_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheGuardMatch guard frame ->
    AyCacheEntry guard learnedClause segment ->
    AyCacheAcceptedReuse frame guard learnedClause segment :=
  fun matched entry =>
    ay_cache_conj_intro (AyCacheGuardMatch guard frame)
      (AyCacheEntry guard learnedClause segment)
      matched entry

theorem ay_cache_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    AyCacheGuardMatch guard frame :=
  fun reuse =>
    ay_cache_conj_left (AyCacheGuardMatch guard frame)
      (AyCacheEntry guard learnedClause segment)
      reuse

theorem ay_cache_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    AyCacheEntry guard learnedClause segment :=
  fun reuse =>
    ay_cache_conj_right (AyCacheGuardMatch guard frame)
      (AyCacheEntry guard learnedClause segment)
      reuse

theorem ay_cache_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    frame :=
  fun reuse =>
    ay_cache_guard_match_frame guard frame
      (ay_cache_reuse_guard_match frame guard learnedClause segment reuse)

theorem ay_cache_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    guard :=
  fun reuse =>
    ay_cache_guard_match_guard guard frame
      (ay_cache_reuse_guard_match frame guard learnedClause segment reuse)

theorem ay_cache_reuse_segment
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    segment :=
  fun reuse =>
    ay_cache_entry_segment guard learnedClause segment
      (ay_cache_reuse_entry frame guard learnedClause segment reuse)

theorem ay_cache_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (segment : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause segment ->
    learnedClause :=
  fun reuse =>
    ay_cache_entry_learned guard learnedClause segment
      (ay_cache_reuse_entry frame guard learnedClause segment reuse)

theorem ay_cache_reconstruct_learned_from_reuse
    (frame : Prop) (guard : Prop)
    (start : Prop) (finish : Prop) (learnedClause : Prop) :
    AyCacheAcceptedReuse frame guard learnedClause
      (AyCacheReplaySegment start finish learnedClause) ->
    start ->
    learnedClause :=
  fun reuse startH =>
    ay_cache_segment_lookup_learned start finish learnedClause
      (ay_cache_reuse_segment frame guard learnedClause
        (AyCacheReplaySegment start finish learnedClause)
        reuse)
      (ay_cache_segment_lookup_step start finish learnedClause
        (ay_cache_reuse_segment frame guard learnedClause
          (AyCacheReplaySegment start finish learnedClause)
          reuse)
        startH)

theorem ay_cache_reuse_public_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (finish : Prop) (model conflict : Prop) :
    AyCacheEquisat original preprocessed ->
    assumption ->
    AyCacheAcceptedReuse
      (AyCacheScope base assumption)
      guard
      learnedClause
      (AyCacheReplaySegment
        (AyCacheState preprocessed (AyCacheScope base assumption))
        finish
        learnedClause) ->
    (preprocessed -> model) ->
    AyCacheState original base ->
    AyCachePublicResult
      (AyCacheOutcome model conflict)
      (AyCacheScope base assumption) :=
  fun preprocess assumptionH reuse sat state =>
    ay_cache_conj_intro
      (AyCacheOutcome model conflict)
      (AyCacheScope base assumption)
      (ay_cache_disj_left model conflict
        (sat
          (ay_cache_conj_left preprocessed (AyCacheScope base assumption)
            (ay_cache_preprocess_forward original preprocessed
              (AyCacheScope base assumption)
              preprocess
              (ay_cache_state_push original base assumption
                state assumptionH)))))
      (ay_cache_reuse_current_frame
        (AyCacheScope base assumption)
        guard
        learnedClause
        (AyCacheReplaySegment
          (AyCacheState preprocessed (AyCacheScope base assumption))
          finish
          learnedClause)
        reuse)

theorem ay_cache_reuse_public_unsat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (finish : Prop) (model conflict : Prop) :
    AyCacheEquisat original preprocessed ->
    assumption ->
    AyCacheAcceptedReuse
      (AyCacheScope base assumption)
      guard
      learnedClause
      (AyCacheReplaySegment
        (AyCacheState preprocessed (AyCacheScope base assumption))
        finish
        learnedClause) ->
    (learnedClause -> conflict) ->
    AyCacheState original base ->
    AyCachePublicResult
      (AyCacheOutcome model conflict)
      (AyCacheScope base assumption) :=
  fun preprocess assumptionH reuse learnedToConflict state =>
    ay_cache_conj_intro
      (AyCacheOutcome model conflict)
      (AyCacheScope base assumption)
      (ay_cache_disj_right model conflict
        (learnedToConflict
          (ay_cache_reconstruct_learned_from_reuse
            (AyCacheScope base assumption)
            guard
            (AyCacheState preprocessed (AyCacheScope base assumption))
            finish
            learnedClause
            reuse
            (ay_cache_preprocess_forward original preprocessed
              (AyCacheScope base assumption)
              preprocess
              (ay_cache_state_push original base assumption
                state assumptionH)))))
      (ay_cache_reuse_current_frame
        (AyCacheScope base assumption)
        guard
        learnedClause
        (AyCacheReplaySegment
          (AyCacheState preprocessed (AyCacheScope base assumption))
          finish
          learnedClause)
        reuse)

theorem ay_cache_reuse_public_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (finish : Prop) (model conflict : Prop) :
    AyCacheEquisat original preprocessed ->
    assumption ->
    AyCacheAcceptedReuse
      (AyCacheScope base assumption)
      guard
      learnedClause
      (AyCacheReplaySegment
        (AyCacheState preprocessed (AyCacheScope base assumption))
        finish
        learnedClause) ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyCacheState original base ->
    AyCacheConj
      (AyCachePublicResult
        (AyCacheOutcome model conflict)
        (AyCacheScope base assumption))
      (AyCachePublicResult
        (AyCacheOutcome model conflict)
        (AyCacheScope base assumption)) :=
  fun preprocess assumptionH reuse sat learnedToConflict state =>
    ay_cache_conj_intro
      (AyCachePublicResult
        (AyCacheOutcome model conflict)
        (AyCacheScope base assumption))
      (AyCachePublicResult
        (AyCacheOutcome model conflict)
        (AyCacheScope base assumption))
      (ay_cache_reuse_public_sat
        original preprocessed base assumption guard learnedClause
        finish model conflict
        preprocess assumptionH reuse sat state)
      (ay_cache_reuse_public_unsat
        original preprocessed base assumption guard learnedClause
        finish model conflict
        preprocess assumptionH reuse learnedToConflict state)
