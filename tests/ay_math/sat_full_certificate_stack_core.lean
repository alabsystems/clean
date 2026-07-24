-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for the full SAT-COMP certificate stack:
-- preprocessing certificates, streaming replay, incremental assumptions,
-- watched propagation, and final SAT/UNSAT outcome soundness.

def AyFCSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFCSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFCSEquisat (before : Prop) (after : Prop) :=
  AyFCSConj (before -> after) (after -> before)

def AyFCSVisibleMap (internal : Prop) (visible : Prop) :=
  AyFCSConj (internal -> visible) (visible -> internal)

def AyFCSPreprocessCertificate
    (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyFCSConj
    (AyFCSEquisat original preprocessed)
    (AyFCSVisibleMap preprocessed visible)

def AyFCSScope (active : Prop) (pushed : Prop) :=
  AyFCSConj active pushed

def AyFCSWatchedPropagation
    (queue : Prop) (units : Prop) (conflict : Prop) :=
  AyFCSConj (queue -> units) (units -> conflict)

def AyFCSState
    (formula : Prop) (assumptions : Prop) (propagation : Prop) :=
  AyFCSConj formula (AyFCSConj assumptions propagation)

def AyFCSChunkReplay
    (before_state : Prop) (chunk : Prop) (after_state : Prop) :=
  before_state -> chunk -> after_state

def AyFCSChunkPair (first_chunk : Prop) (second_chunk : Prop) :=
  AyFCSConj first_chunk second_chunk

def AyFCSProofReplay (formula : Prop) (final_clause : Prop) :=
  final_clause -> formula -> False

def AyFCSFinalOutcome (model : Prop) (unsat : Prop) :=
  AyFCSDisj model unsat

def AyFCSSolverOutcome (visible_model : Prop) (final_clause : Prop) :=
  AyFCSDisj visible_model final_clause

theorem ay_fcs_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFCSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_fcs_conj_left
    (left : Prop) (right : Prop) :
    AyFCSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_fcs_conj_right
    (left : Prop) (right : Prop) :
    AyFCSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_fcs_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFCSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_fcs_disj_right
    (left : Prop) (right : Prop) :
    right -> AyFCSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_fcs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFCSEquisat before after := by
  intro forward
  intro backward
  exact ay_fcs_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_fcs_equisat_forward
    (before : Prop) (after : Prop) :
    AyFCSEquisat before after -> before -> after := by
  intro certificate
  exact ay_fcs_conj_left (before -> after) (after -> before) certificate

theorem ay_fcs_equisat_backward
    (before : Prop) (after : Prop) :
    AyFCSEquisat before after -> after -> before := by
  intro certificate
  exact ay_fcs_conj_right (before -> after) (after -> before) certificate

theorem ay_fcs_visible_project
    (internal : Prop) (visible : Prop) :
    AyFCSVisibleMap internal visible -> internal -> visible := by
  intro visible_map
  exact ay_fcs_conj_left (internal -> visible) (visible -> internal)
    visible_map

theorem ay_fcs_visible_reconstruct
    (internal : Prop) (visible : Prop) :
    AyFCSVisibleMap internal visible -> visible -> internal := by
  intro visible_map
  exact ay_fcs_conj_right (internal -> visible) (visible -> internal)
    visible_map

theorem ay_fcs_preprocess_equisat
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSEquisat original preprocessed := by
  intro certificate
  exact ay_fcs_conj_left
    (AyFCSEquisat original preprocessed)
    (AyFCSVisibleMap preprocessed visible)
    certificate

theorem ay_fcs_preprocess_visible_map
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSVisibleMap preprocessed visible := by
  intro certificate
  exact ay_fcs_conj_right
    (AyFCSEquisat original preprocessed)
    (AyFCSVisibleMap preprocessed visible)
    certificate

theorem ay_fcs_reconstruct_original_model
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    visible ->
    original := by
  intro certificate
  intro hvisible
  exact ay_fcs_equisat_backward original preprocessed
    (ay_fcs_preprocess_equisat original preprocessed visible certificate)
    (ay_fcs_visible_reconstruct preprocessed visible
      (ay_fcs_preprocess_visible_map original preprocessed visible certificate)
      hvisible)

theorem ay_fcs_scope_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyFCSScope active pushed := by
  intro hactive
  intro hpushed
  exact ay_fcs_conj_intro active pushed hactive hpushed

theorem ay_fcs_scope_pop
    (active : Prop) (pushed : Prop) :
    AyFCSScope active pushed -> active := by
  intro hscope
  exact ay_fcs_conj_left active pushed hscope

theorem ay_fcs_state_intro
    (formula : Prop) (assumptions : Prop) (propagation : Prop) :
    formula -> assumptions -> propagation ->
    AyFCSState formula assumptions propagation := by
  intro hformula
  intro hassumptions
  intro hpropagation
  exact ay_fcs_conj_intro formula
    (AyFCSConj assumptions propagation)
    hformula
    (ay_fcs_conj_intro assumptions propagation
      hassumptions hpropagation)

theorem ay_fcs_state_formula
    (formula : Prop) (assumptions : Prop) (propagation : Prop) :
    AyFCSState formula assumptions propagation -> formula := by
  intro state
  exact ay_fcs_conj_left formula
    (AyFCSConj assumptions propagation)
    state

theorem ay_fcs_state_assumptions
    (formula : Prop) (assumptions : Prop) (propagation : Prop) :
    AyFCSState formula assumptions propagation -> assumptions := by
  intro state
  exact ay_fcs_conj_left assumptions propagation
    (ay_fcs_conj_right formula
      (AyFCSConj assumptions propagation)
      state)

theorem ay_fcs_state_propagation
    (formula : Prop) (assumptions : Prop) (propagation : Prop) :
    AyFCSState formula assumptions propagation -> propagation := by
  intro state
  exact ay_fcs_conj_right assumptions propagation
    (ay_fcs_conj_right formula
      (AyFCSConj assumptions propagation)
      state)

theorem ay_fcs_watched_units_sound
    (queue : Prop) (units : Prop) (conflict : Prop) :
    AyFCSWatchedPropagation queue units conflict ->
    queue ->
    units := by
  intro watched
  intro hqueue
  exact ay_fcs_conj_left (queue -> units) (units -> conflict)
    watched hqueue

theorem ay_fcs_watched_conflict_sound
    (queue : Prop) (units : Prop) (conflict : Prop) :
    AyFCSWatchedPropagation queue units conflict ->
    queue ->
    conflict := by
  intro watched
  intro hqueue
  exact ay_fcs_conj_right (queue -> units) (units -> conflict)
    watched
    (ay_fcs_watched_units_sound queue units conflict watched hqueue)

theorem ay_fcs_chunk_pair_intro
    (first_chunk : Prop) (second_chunk : Prop) :
    first_chunk -> second_chunk ->
    AyFCSChunkPair first_chunk second_chunk := by
  intro hfirst
  intro hsecond
  exact ay_fcs_conj_intro first_chunk second_chunk hfirst hsecond

theorem ay_fcs_chunk_pair_first
    (first_chunk : Prop) (second_chunk : Prop) :
    AyFCSChunkPair first_chunk second_chunk -> first_chunk := by
  intro chunks
  exact ay_fcs_conj_left first_chunk second_chunk chunks

theorem ay_fcs_chunk_pair_second
    (first_chunk : Prop) (second_chunk : Prop) :
    AyFCSChunkPair first_chunk second_chunk -> second_chunk := by
  intro chunks
  exact ay_fcs_conj_right first_chunk second_chunk chunks

theorem ay_fcs_chunk_handoff
    (state0 : Prop) (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) :
    AyFCSChunkReplay state0 chunk0 state1 ->
    AyFCSChunkReplay state1 chunk1 state2 ->
    state0 ->
    AyFCSChunkPair chunk0 chunk1 ->
    state2 := by
  intro first_replay
  intro second_replay
  intro hstate0
  intro chunks
  exact second_replay
    (first_replay hstate0
      (ay_fcs_chunk_pair_first chunk0 chunk1 chunks))
    (ay_fcs_chunk_pair_second chunk0 chunk1 chunks)

theorem ay_fcs_chunk_handoff_under_scope
    (formula : Prop) (active : Prop) (pushed : Prop)
    (prop0 : Prop) (prop1 : Prop) (prop2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) :
    AyFCSChunkReplay
      (AyFCSState formula (AyFCSScope active pushed) prop0)
      chunk0
      (AyFCSState formula (AyFCSScope active pushed) prop1) ->
    AyFCSChunkReplay
      (AyFCSState formula (AyFCSScope active pushed) prop1)
      chunk1
      (AyFCSState formula (AyFCSScope active pushed) prop2) ->
    AyFCSState formula (AyFCSScope active pushed) prop0 ->
    AyFCSChunkPair chunk0 chunk1 ->
    AyFCSState formula (AyFCSScope active pushed) prop2 := by
  intro first_replay
  intro second_replay
  exact ay_fcs_chunk_handoff
    (AyFCSState formula (AyFCSScope active pushed) prop0)
    (AyFCSState formula (AyFCSScope active pushed) prop1)
    (AyFCSState formula (AyFCSScope active pushed) prop2)
    chunk0
    chunk1
    first_replay
    second_replay

theorem ay_fcs_unsat_from_final_clause
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (final_clause : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSProofReplay preprocessed final_clause ->
    final_clause ->
    Not original := by
  intro preprocess
  intro replay
  intro hfinal
  intro horiginal
  exact replay hfinal
    (ay_fcs_equisat_forward original preprocessed
      (ay_fcs_preprocess_equisat original preprocessed visible preprocess)
      horiginal)

theorem ay_fcs_streamed_unsat_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (state0 : Prop) (state1 : Prop) (state2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (final_clause : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSChunkReplay state0 chunk0 state1 ->
    AyFCSChunkReplay state1 chunk1 state2 ->
    (state2 -> final_clause) ->
    AyFCSProofReplay preprocessed final_clause ->
    state0 ->
    AyFCSChunkPair chunk0 chunk1 ->
    Not original := by
  intro preprocess
  intro first_replay
  intro second_replay
  intro final_replay
  intro proof_replay
  intro hstate0
  intro chunks
  exact ay_fcs_unsat_from_final_clause original preprocessed visible
    final_clause
    preprocess
    proof_replay
    (final_replay
      (ay_fcs_chunk_handoff state0 state1 state2 chunk0 chunk1
        first_replay second_replay hstate0 chunks))

theorem ay_fcs_sat_outcome_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    visible ->
    AyFCSFinalOutcome original (Not original) := by
  intro preprocess
  intro hvisible
  exact ay_fcs_disj_left original (Not original)
    (ay_fcs_reconstruct_original_model original preprocessed visible
      preprocess hvisible)

theorem ay_fcs_unsat_outcome_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (final_clause : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSProofReplay preprocessed final_clause ->
    final_clause ->
    AyFCSFinalOutcome original (Not original) := by
  intro preprocess
  intro replay
  intro hfinal
  exact ay_fcs_disj_right original (Not original)
    (ay_fcs_unsat_from_final_clause original preprocessed visible
      final_clause preprocess replay hfinal)

theorem ay_fcs_solver_outcome_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (final_clause : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSProofReplay preprocessed final_clause ->
    AyFCSSolverOutcome visible final_clause ->
    AyFCSFinalOutcome original (Not original) := by
  intro preprocess
  intro replay
  intro outcome
  exact outcome (AyFCSFinalOutcome original (Not original))
    (ay_fcs_sat_outcome_sound original preprocessed visible preprocess)
    (ay_fcs_unsat_outcome_sound original preprocessed visible
      final_clause preprocess replay)

theorem ay_fcs_full_stack_unsat_sound
    (original : Prop) (preprocessed : Prop) (visible : Prop)
    (active : Prop) (pushed : Prop)
    (queue : Prop) (units : Prop) (conflict : Prop)
    (prop0 : Prop) (prop1 : Prop) (prop2 : Prop)
    (chunk0 : Prop) (chunk1 : Prop) (final_clause : Prop) :
    AyFCSPreprocessCertificate original preprocessed visible ->
    AyFCSWatchedPropagation queue units conflict ->
    AyFCSChunkReplay
      (AyFCSState preprocessed (AyFCSScope active pushed) prop0)
      chunk0
      (AyFCSState preprocessed (AyFCSScope active pushed) prop1) ->
    AyFCSChunkReplay
      (AyFCSState preprocessed (AyFCSScope active pushed) prop1)
      chunk1
      (AyFCSState preprocessed (AyFCSScope active pushed) prop2) ->
    (AyFCSState preprocessed (AyFCSScope active pushed) prop2 ->
      final_clause) ->
    AyFCSProofReplay preprocessed final_clause ->
    (conflict -> prop0) ->
    original ->
    active ->
    pushed ->
    queue ->
    AyFCSChunkPair chunk0 chunk1 ->
    AyFCSFinalOutcome original (Not original) := by
  intro preprocess
  intro watched
  intro first_replay
  intro second_replay
  intro final_replay
  intro proof_replay
  intro conflict_to_prop0
  intro horiginal
  intro hactive
  intro hpushed
  intro hqueue
  intro chunks
  have hstate0 :
      AyFCSState preprocessed (AyFCSScope active pushed) prop0 :=
    ay_fcs_state_intro preprocessed (AyFCSScope active pushed) prop0
      (ay_fcs_equisat_forward original preprocessed
        (ay_fcs_preprocess_equisat original preprocessed visible preprocess)
        horiginal)
      (ay_fcs_scope_intro active pushed hactive hpushed)
      (conflict_to_prop0
        (ay_fcs_watched_conflict_sound queue units conflict watched hqueue))
  exact ay_fcs_disj_right original (Not original)
    (ay_fcs_streamed_unsat_sound
      original preprocessed visible
      (AyFCSState preprocessed (AyFCSScope active pushed) prop0)
      (AyFCSState preprocessed (AyFCSScope active pushed) prop1)
      (AyFCSState preprocessed (AyFCSScope active pushed) prop2)
      chunk0 chunk1 final_clause
      preprocess first_replay second_replay final_replay proof_replay
      hstate0 chunks)
