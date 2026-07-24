-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Indexed incremental artifact skeleton for SAT-COMP certificates. Assumption
-- frames, solver states, compressed replay segments, and final outcomes are
-- abstract propositions; the checked content is the wiring that lets frame
-- certificates be looked up independently and reassembled into the compressed
-- SAT/UNSAT roundtrip theorem.

def AyIdxConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyIdxDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyIdxEquisat (before : Prop) (after : Prop) :=
  AyIdxConj (before -> after) (after -> before)

def AyIdxScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyIdxState (formula : Prop) (assumptions : Prop) :=
  AyIdxConj formula assumptions

def AyIdxCompressed (state : Prop) (finalClause : Prop) :=
  AyIdxConj state finalClause

def AyIdxCompressedSegment
    (start : Prop) (finish : Prop) (finalClause : Prop) :=
  AyIdxConj (start -> finish) (finish -> finalClause)

def AyIdxSegmentEntry (frame : Prop) (segment : Prop) :=
  AyIdxConj frame segment

def AyIdxArtifactIndex (frame : Prop) (segment : Prop) (outcome : Prop) :=
  AyIdxConj (AyIdxSegmentEntry frame segment) outcome

def AyIdxOutcome (model : Prop) (conflict : Prop) :=
  AyIdxDisj model conflict

theorem ay_idx_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyIdxConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_idx_conj_left
    (left : Prop) (right : Prop) :
    AyIdxConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_idx_conj_right
    (left : Prop) (right : Prop) :
    AyIdxConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_idx_disj_left
    (left : Prop) (right : Prop) :
    left -> AyIdxDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_idx_disj_right
    (left : Prop) (right : Prop) :
    right -> AyIdxDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_idx_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyIdxEquisat before after :=
  fun forward backward =>
    ay_idx_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_idx_equisat_forward
    (before : Prop) (after : Prop) :
    AyIdxEquisat before after -> before -> after :=
  fun equisat =>
    ay_idx_conj_left (before -> after) (after -> before) equisat

theorem ay_idx_equisat_backward
    (before : Prop) (after : Prop) :
    AyIdxEquisat before after -> after -> before :=
  fun equisat =>
    ay_idx_conj_right (before -> after) (after -> before) equisat

theorem ay_idx_scope_push
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyIdxScope active pushed :=
  fun activeH pushedH result build =>
    build activeH pushedH

theorem ay_idx_state_push
    (formula : Prop) (active : Prop) (pushed : Prop) :
    AyIdxState formula active ->
    pushed ->
    AyIdxState formula (AyIdxScope active pushed) :=
  fun state pushedH =>
    ay_idx_conj_intro formula (AyIdxScope active pushed)
      (ay_idx_conj_left formula active state)
      (ay_idx_scope_push active pushed
        (ay_idx_conj_right formula active state)
        pushedH)

theorem ay_idx_preprocess_forward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyIdxEquisat original preprocessed ->
    AyIdxState original assumptions ->
    AyIdxState preprocessed assumptions :=
  fun preprocess state =>
    ay_idx_conj_intro preprocessed assumptions
      (ay_idx_equisat_forward original preprocessed preprocess
        (ay_idx_conj_left original assumptions state))
      (ay_idx_conj_right original assumptions state)

theorem ay_idx_preprocess_backward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyIdxEquisat original preprocessed ->
    AyIdxState preprocessed assumptions ->
    AyIdxState original assumptions :=
  fun preprocess state =>
    ay_idx_conj_intro original assumptions
      (ay_idx_equisat_backward original preprocessed preprocess
        (ay_idx_conj_left preprocessed assumptions state))
      (ay_idx_conj_right preprocessed assumptions state)

theorem ay_idx_segment_intro
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    (start -> finish) ->
    (finish -> finalClause) ->
    AyIdxCompressedSegment start finish finalClause :=
  fun replay final =>
    ay_idx_conj_intro (start -> finish) (finish -> finalClause)
      replay final

theorem ay_idx_segment_lookup_step
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    AyIdxCompressedSegment start finish finalClause ->
    start ->
    finish :=
  fun segment =>
    ay_idx_conj_left (start -> finish) (finish -> finalClause)
      segment

theorem ay_idx_segment_lookup_final
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    AyIdxCompressedSegment start finish finalClause ->
    finish ->
    finalClause :=
  fun segment =>
    ay_idx_conj_right (start -> finish) (finish -> finalClause)
      segment

theorem ay_idx_segment_reconstruct_compressed
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    AyIdxCompressedSegment start finish finalClause ->
    start ->
    AyIdxCompressed finish finalClause :=
  fun segment startH =>
    ay_idx_conj_intro finish finalClause
      (ay_idx_segment_lookup_step start finish finalClause segment startH)
      (ay_idx_segment_lookup_final start finish finalClause segment
        (ay_idx_segment_lookup_step start finish finalClause segment startH))

theorem ay_idx_compressed_state
    (state : Prop) (finalClause : Prop) :
    AyIdxCompressed state finalClause -> state :=
  fun compressed =>
    ay_idx_conj_left state finalClause compressed

theorem ay_idx_compressed_final
    (state : Prop) (finalClause : Prop) :
    AyIdxCompressed state finalClause -> finalClause :=
  fun compressed =>
    ay_idx_conj_right state finalClause compressed

theorem ay_idx_entry_intro
    (frame : Prop) (segment : Prop) :
    frame -> segment -> AyIdxSegmentEntry frame segment :=
  fun frameH segmentH =>
    ay_idx_conj_intro frame segment frameH segmentH

theorem ay_idx_entry_frame
    (frame : Prop) (segment : Prop) :
    AyIdxSegmentEntry frame segment -> frame :=
  fun entry =>
    ay_idx_conj_left frame segment entry

theorem ay_idx_entry_segment
    (frame : Prop) (segment : Prop) :
    AyIdxSegmentEntry frame segment -> segment :=
  fun entry =>
    ay_idx_conj_right frame segment entry

theorem ay_idx_index_intro
    (frame : Prop) (segment : Prop) (outcome : Prop) :
    AyIdxSegmentEntry frame segment ->
    outcome ->
    AyIdxArtifactIndex frame segment outcome :=
  fun entry outcomeH =>
    ay_idx_conj_intro (AyIdxSegmentEntry frame segment) outcome
      entry outcomeH

theorem ay_idx_index_entry
    (frame : Prop) (segment : Prop) (outcome : Prop) :
    AyIdxArtifactIndex frame segment outcome ->
    AyIdxSegmentEntry frame segment :=
  fun index =>
    ay_idx_conj_left (AyIdxSegmentEntry frame segment) outcome index

theorem ay_idx_index_outcome
    (frame : Prop) (segment : Prop) (outcome : Prop) :
    AyIdxArtifactIndex frame segment outcome ->
    outcome :=
  fun index =>
    ay_idx_conj_right (AyIdxSegmentEntry frame segment) outcome index

theorem ay_idx_lookup_frame_from_index
    (frame : Prop) (segment : Prop) (outcome : Prop) :
    AyIdxArtifactIndex frame segment outcome ->
    frame :=
  fun index =>
    ay_idx_entry_frame frame segment
      (ay_idx_index_entry frame segment outcome index)

theorem ay_idx_lookup_segment_from_index
    (frame : Prop) (segment : Prop) (outcome : Prop) :
    AyIdxArtifactIndex frame segment outcome ->
    segment :=
  fun index =>
    ay_idx_entry_segment frame segment
      (ay_idx_index_entry frame segment outcome index)

theorem ay_idx_lookup_frame_preserves_scope
    (active : Prop) (pushed : Prop)
    (segment : Prop) (outcome : Prop) :
    AyIdxArtifactIndex (AyIdxScope active pushed) segment outcome ->
    AyIdxScope active pushed :=
  fun index =>
    ay_idx_lookup_frame_from_index
      (AyIdxScope active pushed) segment outcome index

theorem ay_idx_reconstruct_from_index
    (frame : Prop) (start : Prop) (finish : Prop)
    (finalClause : Prop) (outcome : Prop) :
    AyIdxArtifactIndex frame
      (AyIdxCompressedSegment start finish finalClause)
      outcome ->
    start ->
    AyIdxCompressed finish finalClause :=
  fun index startH =>
    ay_idx_segment_reconstruct_compressed start finish finalClause
      (ay_idx_lookup_segment_from_index frame
        (AyIdxCompressedSegment start finish finalClause)
        outcome
        index)
      startH

theorem ay_idx_sat_roundtrip_from_frame
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyIdxState original active ->
    model :=
  fun preprocess pushedH sat state =>
    sat
      (ay_idx_conj_left preprocessed (AyIdxScope active pushed)
        (ay_idx_preprocess_forward original preprocessed
          (AyIdxScope active pushed)
          preprocess
          (ay_idx_state_push original active pushed state pushedH)))

theorem ay_idx_unsat_roundtrip_from_index
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (outcome : Prop) (conflict : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    AyIdxArtifactIndex
      (AyIdxScope active pushed)
      (AyIdxCompressedSegment
        (AyIdxState preprocessed (AyIdxScope active pushed))
        finish
        finalClause)
      outcome ->
    (finalClause -> conflict) ->
    AyIdxState original active ->
    conflict :=
  fun preprocess pushedH index clauseToConflict state =>
    clauseToConflict
      (ay_idx_compressed_final finish finalClause
        (ay_idx_reconstruct_from_index
          (AyIdxScope active pushed)
          (AyIdxState preprocessed (AyIdxScope active pushed))
          finish
          finalClause
          outcome
          index
          (ay_idx_preprocess_forward original preprocessed
            (AyIdxScope active pushed)
            preprocess
            (ay_idx_state_push original active pushed state pushedH))))

theorem ay_idx_sat_outcome_from_frame
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop) (model conflict : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyIdxState original active ->
    AyIdxOutcome model conflict :=
  fun preprocess pushedH sat state =>
    ay_idx_disj_left model conflict
      (ay_idx_sat_roundtrip_from_frame
        original preprocessed active pushed model
        preprocess pushedH sat state)

theorem ay_idx_unsat_outcome_from_index
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (outcome : Prop) (model conflict : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    AyIdxArtifactIndex
      (AyIdxScope active pushed)
      (AyIdxCompressedSegment
        (AyIdxState preprocessed (AyIdxScope active pushed))
        finish
        finalClause)
      outcome ->
    (finalClause -> conflict) ->
    AyIdxState original active ->
    AyIdxOutcome model conflict :=
  fun preprocess pushedH index clauseToConflict state =>
    ay_idx_disj_right model conflict
      (ay_idx_unsat_roundtrip_from_index
        original preprocessed active pushed finish finalClause
        outcome conflict preprocess pushedH index clauseToConflict state)

theorem ay_idx_independent_frame_reassembly
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (outcome : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    AyIdxArtifactIndex
      (AyIdxScope active pushed)
      (AyIdxCompressedSegment
        (AyIdxState preprocessed (AyIdxScope active pushed))
        finish
        finalClause)
      outcome ->
    AyIdxState original active ->
    AyIdxConj
      (AyIdxScope active pushed)
      (AyIdxCompressed finish finalClause) :=
  fun preprocess pushedH index state =>
    ay_idx_conj_intro
      (AyIdxScope active pushed)
      (AyIdxCompressed finish finalClause)
      (ay_idx_lookup_frame_preserves_scope active pushed
        (AyIdxCompressedSegment
          (AyIdxState preprocessed (AyIdxScope active pushed))
          finish
          finalClause)
        outcome
        index)
      (ay_idx_reconstruct_from_index
        (AyIdxScope active pushed)
        (AyIdxState preprocessed (AyIdxScope active pushed))
        finish
        finalClause
        outcome
        index
        (ay_idx_preprocess_forward original preprocessed
          (AyIdxScope active pushed)
          preprocess
          (ay_idx_state_push original active pushed state pushedH)))

theorem ay_idx_full_compressed_roundtrip_reassembled
    (original : Prop) (preprocessed : Prop)
    (active : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (model conflict : Prop) (outcome : Prop) :
    AyIdxEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyIdxArtifactIndex
      (AyIdxScope active pushed)
      (AyIdxCompressedSegment
        (AyIdxState preprocessed (AyIdxScope active pushed))
        finish
        finalClause)
      outcome ->
    (finalClause -> conflict) ->
    AyIdxState original active ->
    AyIdxConj
      (AyIdxOutcome model conflict)
      (AyIdxOutcome model conflict) :=
  fun preprocess pushedH sat index clauseToConflict state =>
    ay_idx_conj_intro
      (AyIdxOutcome model conflict)
      (AyIdxOutcome model conflict)
      (ay_idx_sat_outcome_from_frame
        original preprocessed active pushed model conflict
        preprocess pushedH sat state)
      (ay_idx_unsat_outcome_from_index
        original preprocessed active pushed finish finalClause
        outcome model conflict
        preprocess pushedH index clauseToConflict state)
