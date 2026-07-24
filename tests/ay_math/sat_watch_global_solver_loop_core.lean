-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction for a SAT solver loop integrating watched propagation,
-- restarts, streaming proof replay, and final SAT/UNSAT outcomes. The
-- propositions stand for solver states, visible models, and replayed final
-- clauses; all maps are explicit Church-encoded certificates.

def AyWGSLConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyWGSLDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyWGSLEquisat (before : Prop) (after : Prop) :=
  AyWGSLConj (before -> after) (after -> before)

def AyWGSLClause (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWGSLDisj watchA (AyWGSLDisj watchB residual)

def AyWGSLPropagationState (queue : Prop) (units : Prop) :=
  AyWGSLConj queue units

def AyWGSLWatchCertificate
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) :=
  AyWGSLConj (AyWGSLClause watchA watchB residual)
    (AyWGSLPropagationState queue units)

def AyWGSLRestartReset (beforeState : Prop) (afterState : Prop) :=
  AyWGSLEquisat beforeState afterState

def AyWGSLReplayChunk (state : Prop) (logged : Prop) :=
  AyWGSLConj state logged

def AyWGSLStreamHandoff (fromState : Prop) (toState : Prop) :=
  fromState -> toState

def AyWGSLFinalReplay (state : Prop) (finalClause : Prop) :=
  state -> finalClause

def AyWGSLSatOutcome (visibleModel : Prop) (originalModel : Prop) :=
  AyWGSLConj visibleModel (visibleModel -> originalModel)

def AyWGSLUnsatOutcome (finalClause : Prop) (originalUnsat : Prop) :=
  AyWGSLConj finalClause (finalClause -> originalUnsat)

def AyWGSLFinalOutcome (satWitness : Prop) (unsatWitness : Prop) :=
  AyWGSLDisj satWitness unsatWitness

theorem ay_wgsl_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyWGSLConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_wgsl_conj_left
    (p : Prop) (q : Prop) :
    AyWGSLConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_wgsl_disj_left
    (p : Prop) (q : Prop) :
    p -> AyWGSLDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_wgsl_disj_right
    (p : Prop) (q : Prop) :
    q -> AyWGSLDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_wgsl_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyWGSLEquisat before after := by
  intro forward
  intro backward
  exact ay_wgsl_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_wgsl_equisat_forward
    (before : Prop) (after : Prop) :
    AyWGSLEquisat before after ->
    before ->
    after := by
  intro certificate
  exact certificate (before -> after)
    (fun forward _backward => forward)

theorem ay_wgsl_equisat_backward
    (before : Prop) (after : Prop) :
    AyWGSLEquisat before after ->
    after ->
    before := by
  intro certificate
  exact certificate (after -> before)
    (fun _forward backward => backward)

theorem ay_wgsl_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyWGSLEquisat before middle ->
    AyWGSLEquisat middle after ->
    AyWGSLEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_wgsl_watch_certificate_state
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) :
    AyWGSLWatchCertificate watchA watchB residual queue units ->
    AyWGSLPropagationState queue units := by
  intro certificate
  exact certificate (AyWGSLPropagationState queue units)
    (fun _clause state => state)

theorem ay_wgsl_restart_transport_watch
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeState : Prop) (afterState : Prop)
    (queue : Prop) (units : Prop) :
    AyWGSLRestartReset beforeState afterState ->
    (AyWGSLPropagationState queue units -> beforeState) ->
    (afterState -> AyWGSLPropagationState queue units) ->
    AyWGSLWatchCertificate watchA watchB residual queue units ->
    afterState := by
  intro reset
  intro state_to_before
  intro _after_to_state
  intro certificate
  exact ay_wgsl_equisat_forward beforeState afterState reset
    (state_to_before
      (ay_wgsl_watch_certificate_state
        watchA watchB residual queue units certificate))

theorem ay_wgsl_stream_chunk_state
    (state : Prop) (logged : Prop) :
    AyWGSLReplayChunk state logged -> state := by
  intro chunk
  exact ay_wgsl_conj_left state logged chunk

theorem ay_wgsl_stream_chunk_logged
    (state : Prop) (logged : Prop) :
    AyWGSLReplayChunk state logged -> logged := by
  intro chunk
  exact chunk logged (fun _state logged_fact => logged_fact)

theorem ay_wgsl_stream_handoff_preserves_chunk
    (fromState : Prop) (toState : Prop) (logged : Prop) :
    AyWGSLStreamHandoff fromState toState ->
    AyWGSLReplayChunk fromState logged ->
    AyWGSLReplayChunk toState logged := by
  intro handoff
  intro chunk
  exact ay_wgsl_conj_intro toState logged
    (handoff (ay_wgsl_stream_chunk_state fromState logged chunk))
    (ay_wgsl_stream_chunk_logged fromState logged chunk)

theorem ay_wgsl_restart_stream_handoff
    (beforeState : Prop) (afterRestart : Prop) (afterStream : Prop)
    (logged : Prop) :
    AyWGSLRestartReset beforeState afterRestart ->
    AyWGSLStreamHandoff afterRestart afterStream ->
    AyWGSLReplayChunk beforeState logged ->
    AyWGSLReplayChunk afterStream logged := by
  intro reset
  intro handoff
  intro chunk
  exact ay_wgsl_stream_handoff_preserves_chunk afterRestart afterStream logged
    handoff
    (ay_wgsl_stream_handoff_preserves_chunk beforeState afterRestart logged
      (ay_wgsl_equisat_forward beforeState afterRestart reset)
      chunk)

theorem ay_wgsl_final_clause_after_stream
    (state : Prop) (logged : Prop) (finalClause : Prop) :
    AyWGSLFinalReplay state finalClause ->
    AyWGSLReplayChunk state logged ->
    finalClause := by
  intro replay
  intro chunk
  exact replay (ay_wgsl_stream_chunk_state state logged chunk)

theorem ay_wgsl_sat_outcome_intro
    (visibleModel : Prop) (originalModel : Prop) :
    visibleModel ->
    (visibleModel -> originalModel) ->
    AyWGSLSatOutcome visibleModel originalModel := by
  intro hvisible
  intro reconstruct
  exact ay_wgsl_conj_intro visibleModel (visibleModel -> originalModel)
    hvisible
    reconstruct

theorem ay_wgsl_sat_model_reconstruction
    (visibleModel : Prop) (originalModel : Prop) :
    AyWGSLSatOutcome visibleModel originalModel ->
    originalModel := by
  intro outcome
  exact outcome originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_wgsl_sat_model_after_loop
    (state : Prop) (visibleModel : Prop) (originalModel : Prop) :
    (state -> visibleModel) ->
    (visibleModel -> originalModel) ->
    state ->
    originalModel := by
  intro extract_visible
  intro reconstruct
  intro hstate
  exact reconstruct (extract_visible hstate)

theorem ay_wgsl_unsat_outcome_intro
    (finalClause : Prop) (originalUnsat : Prop) :
    finalClause ->
    (finalClause -> originalUnsat) ->
    AyWGSLUnsatOutcome finalClause originalUnsat := by
  intro hfinal
  intro sound
  exact ay_wgsl_conj_intro finalClause (finalClause -> originalUnsat)
    hfinal
    sound

theorem ay_wgsl_unsat_final_clause_sound
    (finalClause : Prop) (originalUnsat : Prop) :
    AyWGSLUnsatOutcome finalClause originalUnsat ->
    originalUnsat := by
  intro outcome
  exact outcome originalUnsat
    (fun hfinal sound => sound hfinal)

theorem ay_wgsl_unsat_after_stream
    (state : Prop) (logged : Prop)
    (finalClause : Prop) (originalUnsat : Prop) :
    AyWGSLFinalReplay state finalClause ->
    (finalClause -> originalUnsat) ->
    AyWGSLReplayChunk state logged ->
    originalUnsat := by
  intro replay
  intro sound
  intro chunk
  exact sound
    (ay_wgsl_final_clause_after_stream state logged finalClause replay chunk)

theorem ay_wgsl_final_outcome_sat
    (satWitness : Prop) (unsatWitness : Prop) :
    satWitness ->
    AyWGSLFinalOutcome satWitness unsatWitness := by
  intro hs
  exact ay_wgsl_disj_left satWitness unsatWitness hs

theorem ay_wgsl_final_outcome_unsat
    (satWitness : Prop) (unsatWitness : Prop) :
    unsatWitness ->
    AyWGSLFinalOutcome satWitness unsatWitness := by
  intro hu
  exact ay_wgsl_disj_right satWitness unsatWitness hu

theorem ay_wgsl_global_sat_branch_sound
    (state : Prop) (visibleModel : Prop) (originalModel : Prop)
    (unsatWitness : Prop) :
    (state -> visibleModel) ->
    (visibleModel -> originalModel) ->
    state ->
    AyWGSLFinalOutcome originalModel unsatWitness := by
  intro extract_visible
  intro reconstruct
  intro hstate
  exact ay_wgsl_final_outcome_sat originalModel unsatWitness
    (ay_wgsl_sat_model_after_loop
      state visibleModel originalModel extract_visible reconstruct hstate)

theorem ay_wgsl_global_unsat_branch_sound
    (state : Prop) (logged : Prop)
    (finalClause : Prop) (originalUnsat : Prop)
    (satWitness : Prop) :
    AyWGSLFinalReplay state finalClause ->
    (finalClause -> originalUnsat) ->
    AyWGSLReplayChunk state logged ->
    AyWGSLFinalOutcome satWitness originalUnsat := by
  intro replay
  intro sound
  intro chunk
  exact ay_wgsl_final_outcome_unsat satWitness originalUnsat
    (ay_wgsl_unsat_after_stream
      state logged finalClause originalUnsat replay sound chunk)

theorem ay_wgsl_global_loop_equisat
    (initialState : Prop) (restartState : Prop) (streamState : Prop) :
    AyWGSLRestartReset initialState restartState ->
    AyWGSLStreamHandoff restartState streamState ->
    (streamState -> restartState) ->
    AyWGSLEquisat initialState streamState := by
  intro reset
  intro handoff
  intro reconstruct_stream
  exact ay_wgsl_equisat_compose initialState restartState streamState
    reset
    (ay_wgsl_equisat_intro restartState streamState
      handoff
      reconstruct_stream)
