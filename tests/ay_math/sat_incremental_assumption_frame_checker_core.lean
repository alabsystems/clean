-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked assumption-frame certificate skeleton for incremental SAT solving.
-- Frames, preprocessing facts, compressed replay segments, and branch outcomes
-- are abstract propositions. The useful checked content is the plumbing that
-- accepts one current-frame certificate, reassembles SAT/UNSAT public results
-- for that frame, and carries unrelated frames through unchanged.

def AyFrameConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFrameDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFrameEquisat (before : Prop) (after : Prop) :=
  AyFrameConj (before -> after) (after -> before)

def AyFrameScope (parent : Prop) (pushed : Prop) :=
  forall result : Prop, (parent -> pushed -> result) -> result

def AyFrameState (formula : Prop) (assumptions : Prop) :=
  AyFrameConj formula assumptions

def AyFrameCompressedSegment
    (start : Prop) (finish : Prop) (finalClause : Prop) :=
  AyFrameConj (start -> finish) (finish -> finalClause)

def AyFrameAcceptedCertificate
    (frame : Prop) (preprocess : Prop) (segment : Prop) :=
  AyFrameConj frame (AyFrameConj preprocess segment)

def AyFrameStack (current : Prop) (other : Prop) :=
  AyFrameConj current other

def AyFrameOutcome (model : Prop) (conflict : Prop) :=
  AyFrameDisj model conflict

def AyFramePublicResult (currentOutcome : Prop) (otherFrame : Prop) :=
  AyFrameConj currentOutcome otherFrame

theorem ay_frame_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFrameConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_frame_conj_left
    (left : Prop) (right : Prop) :
    AyFrameConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_frame_conj_right
    (left : Prop) (right : Prop) :
    AyFrameConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_frame_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFrameDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_frame_disj_right
    (left : Prop) (right : Prop) :
    right -> AyFrameDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_frame_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFrameEquisat before after :=
  fun forward backward =>
    ay_frame_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_frame_equisat_forward
    (before : Prop) (after : Prop) :
    AyFrameEquisat before after -> before -> after :=
  fun equisat =>
    ay_frame_conj_left (before -> after) (after -> before) equisat

theorem ay_frame_equisat_backward
    (before : Prop) (after : Prop) :
    AyFrameEquisat before after -> after -> before :=
  fun equisat =>
    ay_frame_conj_right (before -> after) (after -> before) equisat

theorem ay_frame_scope_push
    (parent : Prop) (pushed : Prop) :
    parent -> pushed -> AyFrameScope parent pushed :=
  fun parentH pushedH result build =>
    build parentH pushedH

theorem ay_frame_scope_parent
    (parent : Prop) (pushed : Prop) :
    AyFrameScope parent pushed -> parent :=
  fun scope =>
    scope parent (fun parentH _pushedH => parentH)

theorem ay_frame_scope_pushed
    (parent : Prop) (pushed : Prop) :
    AyFrameScope parent pushed -> pushed :=
  fun scope =>
    scope pushed (fun _parentH pushedH => pushedH)

theorem ay_frame_state_push
    (formula : Prop) (parent : Prop) (pushed : Prop) :
    AyFrameState formula parent ->
    pushed ->
    AyFrameState formula (AyFrameScope parent pushed) :=
  fun state pushedH =>
    ay_frame_conj_intro formula (AyFrameScope parent pushed)
      (ay_frame_conj_left formula parent state)
      (ay_frame_scope_push parent pushed
        (ay_frame_conj_right formula parent state)
        pushedH)

theorem ay_frame_state_pop
    (formula : Prop) (parent : Prop) (pushed : Prop) :
    AyFrameState formula (AyFrameScope parent pushed) ->
    AyFrameState formula parent :=
  fun state =>
    ay_frame_conj_intro formula parent
      (ay_frame_conj_left formula (AyFrameScope parent pushed) state)
      (ay_frame_scope_parent parent pushed
        (ay_frame_conj_right formula (AyFrameScope parent pushed) state))

theorem ay_frame_preprocess_forward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyFrameEquisat original preprocessed ->
    AyFrameState original assumptions ->
    AyFrameState preprocessed assumptions :=
  fun preprocess state =>
    ay_frame_conj_intro preprocessed assumptions
      (ay_frame_equisat_forward original preprocessed preprocess
        (ay_frame_conj_left original assumptions state))
      (ay_frame_conj_right original assumptions state)

theorem ay_frame_preprocess_backward
    (original : Prop) (preprocessed : Prop) (assumptions : Prop) :
    AyFrameEquisat original preprocessed ->
    AyFrameState preprocessed assumptions ->
    AyFrameState original assumptions :=
  fun preprocess state =>
    ay_frame_conj_intro original assumptions
      (ay_frame_equisat_backward original preprocessed preprocess
        (ay_frame_conj_left preprocessed assumptions state))
      (ay_frame_conj_right preprocessed assumptions state)

theorem ay_frame_segment_intro
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    (start -> finish) ->
    (finish -> finalClause) ->
    AyFrameCompressedSegment start finish finalClause :=
  fun replay final =>
    ay_frame_conj_intro (start -> finish) (finish -> finalClause)
      replay final

theorem ay_frame_segment_lookup_step
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    AyFrameCompressedSegment start finish finalClause ->
    start ->
    finish :=
  fun segment =>
    ay_frame_conj_left (start -> finish) (finish -> finalClause)
      segment

theorem ay_frame_segment_lookup_final
    (start : Prop) (finish : Prop) (finalClause : Prop) :
    AyFrameCompressedSegment start finish finalClause ->
    finish ->
    finalClause :=
  fun segment =>
    ay_frame_conj_right (start -> finish) (finish -> finalClause)
      segment

theorem ay_frame_certificate_intro
    (frame : Prop) (preprocess : Prop) (segment : Prop) :
    frame ->
    preprocess ->
    segment ->
    AyFrameAcceptedCertificate frame preprocess segment :=
  fun frameH preprocessH segmentH =>
    ay_frame_conj_intro frame (AyFrameConj preprocess segment)
      frameH
      (ay_frame_conj_intro preprocess segment preprocessH segmentH)

theorem ay_frame_certificate_frame
    (frame : Prop) (preprocess : Prop) (segment : Prop) :
    AyFrameAcceptedCertificate frame preprocess segment ->
    frame :=
  fun certificate =>
    ay_frame_conj_left frame (AyFrameConj preprocess segment)
      certificate

theorem ay_frame_certificate_preprocess
    (frame : Prop) (preprocess : Prop) (segment : Prop) :
    AyFrameAcceptedCertificate frame preprocess segment ->
    preprocess :=
  fun certificate =>
    ay_frame_conj_left preprocess segment
      (ay_frame_conj_right frame (AyFrameConj preprocess segment)
        certificate)

theorem ay_frame_certificate_segment
    (frame : Prop) (preprocess : Prop) (segment : Prop) :
    AyFrameAcceptedCertificate frame preprocess segment ->
    segment :=
  fun certificate =>
    ay_frame_conj_right preprocess segment
      (ay_frame_conj_right frame (AyFrameConj preprocess segment)
        certificate)

theorem ay_frame_stack_intro
    (current : Prop) (other : Prop) :
    current -> other -> AyFrameStack current other :=
  fun currentH otherH =>
    ay_frame_conj_intro current other currentH otherH

theorem ay_frame_stack_current
    (current : Prop) (other : Prop) :
    AyFrameStack current other -> current :=
  fun stack =>
    ay_frame_conj_left current other stack

theorem ay_frame_stack_other
    (current : Prop) (other : Prop) :
    AyFrameStack current other -> other :=
  fun stack =>
    ay_frame_conj_right current other stack

theorem ay_frame_lookup_segment_from_certificate
    (currentFrame : Prop)
    (preprocess : Prop) (start : Prop) (finish : Prop)
    (finalClause : Prop) :
    AyFrameAcceptedCertificate currentFrame preprocess
      (AyFrameCompressedSegment start finish finalClause) ->
    AyFrameCompressedSegment start finish finalClause :=
  fun certificate =>
    ay_frame_certificate_segment currentFrame preprocess
      (AyFrameCompressedSegment start finish finalClause)
      certificate

theorem ay_frame_reconstruct_final_clause
    (currentFrame : Prop)
    (preprocess : Prop) (start : Prop) (finish : Prop)
    (finalClause : Prop) :
    AyFrameAcceptedCertificate currentFrame preprocess
      (AyFrameCompressedSegment start finish finalClause) ->
    start ->
    finalClause :=
  fun certificate startH =>
    ay_frame_segment_lookup_final start finish finalClause
      (ay_frame_lookup_segment_from_certificate currentFrame preprocess
        start finish finalClause certificate)
      (ay_frame_segment_lookup_step start finish finalClause
        (ay_frame_lookup_segment_from_certificate currentFrame preprocess
          start finish finalClause certificate)
        startH)

theorem ay_frame_sat_public_result
    (original : Prop) (preprocessed : Prop)
    (parent : Prop) (pushed : Prop)
    (model conflict otherFrame : Prop) :
    AyFrameEquisat original preprocessed ->
    pushed ->
    (preprocessed -> model) ->
    AyFrameState original parent ->
    otherFrame ->
    AyFramePublicResult (AyFrameOutcome model conflict) otherFrame :=
  fun preprocess pushedH sat state otherH =>
    ay_frame_conj_intro (AyFrameOutcome model conflict) otherFrame
      (ay_frame_disj_left model conflict
        (sat
          (ay_frame_conj_left preprocessed (AyFrameScope parent pushed)
            (ay_frame_preprocess_forward original preprocessed
              (AyFrameScope parent pushed)
              preprocess
              (ay_frame_state_push original parent pushed state pushedH)))))
      otherH

theorem ay_frame_unsat_public_result
    (original : Prop) (preprocessed : Prop)
    (parent : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (model conflict otherFrame : Prop) :
    AyFrameEquisat original preprocessed ->
    pushed ->
    AyFrameAcceptedCertificate
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause) ->
    (finalClause -> conflict) ->
    AyFrameState original parent ->
    otherFrame ->
    AyFramePublicResult (AyFrameOutcome model conflict) otherFrame :=
  fun preprocess pushedH certificate finalToConflict state otherH =>
    ay_frame_conj_intro (AyFrameOutcome model conflict) otherFrame
      (ay_frame_disj_right model conflict
        (finalToConflict
          (ay_frame_reconstruct_final_clause
            (AyFrameScope parent pushed)
            (AyFrameEquisat original preprocessed)
            (AyFrameState preprocessed (AyFrameScope parent pushed))
            finish
            finalClause
            certificate
            (ay_frame_preprocess_forward original preprocessed
              (AyFrameScope parent pushed)
              preprocess
              (ay_frame_state_push original parent pushed state pushedH)))))
      otherH

theorem ay_frame_certificate_matches_current_scope
    (original : Prop) (preprocessed : Prop)
    (parent : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop) :
    AyFrameAcceptedCertificate
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause) ->
    AyFrameScope parent pushed :=
  fun certificate =>
    ay_frame_certificate_frame
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause)
      certificate

theorem ay_frame_certificate_uses_accepted_preprocess
    (original : Prop) (preprocessed : Prop)
    (parent : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop) :
    AyFrameAcceptedCertificate
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause) ->
    AyFrameEquisat original preprocessed :=
  fun certificate =>
    ay_frame_certificate_preprocess
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause)
      certificate

theorem ay_frame_no_other_frame_contamination
    (currentFrame : Prop) (otherFrame : Prop)
    (publicOutcome : Prop) :
    AyFrameStack currentFrame otherFrame ->
    AyFramePublicResult publicOutcome otherFrame ->
    otherFrame :=
  fun stack _public =>
    ay_frame_stack_other currentFrame otherFrame stack

theorem ay_frame_reassemble_current_without_contamination
    (original : Prop) (preprocessed : Prop)
    (parent : Prop) (pushed : Prop)
    (finish : Prop) (finalClause : Prop)
    (model conflict otherFrame : Prop) :
    pushed ->
    (preprocessed -> model) ->
    (finalClause -> conflict) ->
    AyFrameAcceptedCertificate
      (AyFrameScope parent pushed)
      (AyFrameEquisat original preprocessed)
      (AyFrameCompressedSegment
        (AyFrameState preprocessed (AyFrameScope parent pushed))
        finish
        finalClause) ->
    AyFrameState original parent ->
    AyFrameStack (AyFrameScope parent pushed) otherFrame ->
    AyFrameConj
      (AyFramePublicResult (AyFrameOutcome model conflict) otherFrame)
      (AyFramePublicResult (AyFrameOutcome model conflict) otherFrame) :=
  fun pushedH sat finalToConflict certificate state stack =>
    ay_frame_conj_intro
      (AyFramePublicResult (AyFrameOutcome model conflict) otherFrame)
      (AyFramePublicResult (AyFrameOutcome model conflict) otherFrame)
      (ay_frame_sat_public_result
        original preprocessed parent pushed model conflict otherFrame
        (ay_frame_certificate_uses_accepted_preprocess
          original preprocessed parent pushed finish finalClause certificate)
        pushedH
        sat
        state
        (ay_frame_stack_other (AyFrameScope parent pushed) otherFrame stack))
      (ay_frame_unsat_public_result
        original preprocessed parent pushed finish finalClause
        model conflict otherFrame
        (ay_frame_certificate_uses_accepted_preprocess
          original preprocessed parent pushed finish finalClause certificate)
        pushedH
        certificate
        finalToConflict
        state
        (ay_frame_stack_other (AyFrameScope parent pushed) otherFrame stack))
