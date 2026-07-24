-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction composing watched-literal BCP certificates with streaming
-- proof replay. Watched propagation units/conflicts are logged into replay
-- chunks, chunk handoff preserves propagation state, and final-clause soundness
-- is transported through the streamed replay state.

def AyWSCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyWSCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyWSCEquisat (before : Prop) (after : Prop) :=
  AyWSCConj (before -> after) (after -> before)

def AyWSCClause (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWSCDisj watchA (AyWSCDisj watchB residual)

def AyWSCUnitCertificate (watchA : Prop) (watchB : Prop) (unit : Prop) :=
  AyWSCConj (Not watchA) (AyWSCConj (Not watchB) unit)

def AyWSCConflictCertificate (watchA : Prop) (watchB : Prop) :=
  AyWSCConj (Not watchA) (Not watchB)

def AyWSCPropagationState (queue : Prop) (units : Prop) :=
  AyWSCConj queue units

def AyWSCReplayChunk (state : Prop) (logged : Prop) :=
  AyWSCConj state logged

def AyWSCChunkHandoff (fromState : Prop) (toState : Prop) :=
  fromState -> toState

def AyWSCFinalReplay (state : Prop) (finalClause : Prop) :=
  state -> finalClause

def AyWSCFinalTrace (state : Prop) (finalClause : Prop) :=
  AyWSCConj state finalClause

def AyWSCAbstractPropagationCertificate
    (queue : Prop) (units : Prop) (logged : Prop) :=
  AyWSCConj (AyWSCPropagationState queue units) logged

theorem ay_wsc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyWSCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_wsc_conj_left
    (p : Prop) (q : Prop) :
    AyWSCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_wsc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyWSCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_wsc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyWSCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_wsc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyWSCEquisat before after := by
  intro forward
  intro backward
  exact ay_wsc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_wsc_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyWSCEquisat before middle ->
    AyWSCEquisat middle after ->
    AyWSCEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_wsc_unit_discovery_sound
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWSCClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    unit := by
  intro clause
  intro notA
  intro notB
  exact clause unit
    (fun hwatchA => False.elim (notA hwatchA))
    (fun tail =>
      tail unit
        (fun hwatchB => False.elim (notB hwatchB))
        (fun hunit => hunit))

theorem ay_wsc_conflict_discovery_sound
    (watchA : Prop) (watchB : Prop) :
    AyWSCClause watchA watchB False ->
    AyWSCConflictCertificate watchA watchB ->
    False := by
  intro clause
  intro conflict_cert
  exact conflict_cert False
    (fun notA notB =>
      clause False
        (fun hwatchA => notA hwatchA)
        (fun tail =>
          tail False
            (fun hwatchB => notB hwatchB)
            (fun impossible => impossible)))

theorem ay_wsc_unit_certificate_intro
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    Not watchA ->
    Not watchB ->
    unit ->
    AyWSCUnitCertificate watchA watchB unit := by
  intro notA
  intro notB
  intro hunit
  exact ay_wsc_conj_intro
    (Not watchA)
    (AyWSCConj (Not watchB) unit)
    notA
    (ay_wsc_conj_intro (Not watchB) unit notB hunit)

theorem ay_wsc_log_watched_unit_chunk
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (queue : Prop) (units : Prop) :
    AyWSCClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    AyWSCPropagationState queue units ->
    AyWSCReplayChunk
      (AyWSCPropagationState queue units)
      unit := by
  intro clause
  intro notA
  intro notB
  intro state
  exact ay_wsc_conj_intro
    (AyWSCPropagationState queue units)
    unit
    state
    (ay_wsc_unit_discovery_sound watchA watchB unit clause notA notB)

theorem ay_wsc_log_watched_conflict_chunk
    (watchA : Prop) (watchB : Prop)
    (queue : Prop) (units : Prop) :
    AyWSCClause watchA watchB False ->
    AyWSCConflictCertificate watchA watchB ->
    AyWSCPropagationState queue units ->
    AyWSCReplayChunk
      (AyWSCPropagationState queue units)
      False := by
  intro clause
  intro conflict_cert
  intro state
  exact ay_wsc_conj_intro
    (AyWSCPropagationState queue units)
    False
    state
    (ay_wsc_conflict_discovery_sound watchA watchB clause conflict_cert)

theorem ay_wsc_chunk_state
    (state : Prop) (logged : Prop) :
    AyWSCReplayChunk state logged -> state := by
  intro chunk
  exact ay_wsc_conj_left state logged chunk

theorem ay_wsc_chunk_logged
    (state : Prop) (logged : Prop) :
    AyWSCReplayChunk state logged -> logged := by
  intro chunk
  exact chunk logged (fun _state hlogged => hlogged)

theorem ay_wsc_chunk_handoff_preserves_state
    (fromState : Prop) (toState : Prop) (logged : Prop) :
    AyWSCChunkHandoff fromState toState ->
    AyWSCReplayChunk fromState logged ->
    AyWSCReplayChunk toState logged := by
  intro handoff
  intro chunk
  exact ay_wsc_conj_intro
    toState
    logged
    (handoff (ay_wsc_chunk_state fromState logged chunk))
    (ay_wsc_chunk_logged fromState logged chunk)

theorem ay_wsc_two_chunk_handoff
    (state0 : Prop) (state1 : Prop) (state2 : Prop)
    (logged1 : Prop) (logged2 : Prop) :
    AyWSCChunkHandoff state0 state1 ->
    AyWSCChunkHandoff state1 state2 ->
    AyWSCReplayChunk state0 logged1 ->
    AyWSCReplayChunk state1 logged2 ->
    AyWSCReplayChunk state2 logged2 := by
  intro first_handoff
  intro second_handoff
  intro _first_chunk
  intro second_chunk
  exact ay_wsc_chunk_handoff_preserves_state
    state1 state2 logged2 second_handoff second_chunk

theorem ay_wsc_unit_chunk_to_abstract_certificate
    (queue : Prop) (units : Prop) (unit : Prop) :
    AyWSCReplayChunk
      (AyWSCPropagationState queue units)
      unit ->
    AyWSCAbstractPropagationCertificate queue units unit := by
  intro chunk
  exact chunk
    (AyWSCAbstractPropagationCertificate queue units unit)
    (fun state hunit =>
      ay_wsc_conj_intro
        (AyWSCPropagationState queue units)
        unit
        state
        hunit)

theorem ay_wsc_abstract_certificate_to_unit_chunk
    (queue : Prop) (units : Prop) (unit : Prop) :
    AyWSCAbstractPropagationCertificate queue units unit ->
    AyWSCReplayChunk
      (AyWSCPropagationState queue units)
      unit := by
  intro cert
  exact cert
    (AyWSCReplayChunk (AyWSCPropagationState queue units) unit)
    (fun state hunit =>
      ay_wsc_conj_intro
        (AyWSCPropagationState queue units)
        unit
        state
        hunit)

theorem ay_wsc_abstract_propagation_certificate_equisat
    (queue : Prop) (units : Prop) (unit : Prop) :
    AyWSCEquisat
      (AyWSCReplayChunk (AyWSCPropagationState queue units) unit)
      (AyWSCAbstractPropagationCertificate queue units unit) := by
  exact ay_wsc_equisat_intro
    (AyWSCReplayChunk (AyWSCPropagationState queue units) unit)
    (AyWSCAbstractPropagationCertificate queue units unit)
    (ay_wsc_unit_chunk_to_abstract_certificate queue units unit)
    (ay_wsc_abstract_certificate_to_unit_chunk queue units unit)

theorem ay_wsc_final_clause_preserved
    (state : Prop) (finalClause : Prop) :
    AyWSCFinalReplay state finalClause ->
    state ->
    AyWSCFinalTrace state finalClause := by
  intro final_replay
  intro hstate
  exact ay_wsc_conj_intro
    state
    finalClause
    hstate
    (final_replay hstate)

theorem ay_wsc_final_clause_sound
    (state : Prop) (finalClause : Prop) :
    AyWSCFinalReplay state finalClause ->
    state ->
    finalClause := by
  intro final_replay
  intro hstate
  exact final_replay hstate

theorem ay_wsc_final_clause_after_unit_chunk
    (queue : Prop) (units : Prop) (unit : Prop)
    (finalClause : Prop) :
    AyWSCFinalReplay
      (AyWSCPropagationState queue units)
      finalClause ->
    AyWSCReplayChunk
      (AyWSCPropagationState queue units)
      unit ->
    finalClause := by
  intro final_replay
  intro chunk
  exact final_replay
    (ay_wsc_chunk_state (AyWSCPropagationState queue units) unit chunk)

theorem ay_wsc_final_clause_after_handoff
    (state0 : Prop) (state1 : Prop) (logged : Prop)
    (finalClause : Prop) :
    AyWSCChunkHandoff state0 state1 ->
    AyWSCFinalReplay state1 finalClause ->
    AyWSCReplayChunk state0 logged ->
    finalClause := by
  intro handoff
  intro final_replay
  intro chunk
  exact final_replay
    (handoff (ay_wsc_chunk_state state0 logged chunk))

theorem ay_wsc_streamed_replay_equisat
    (state : Prop) (logged : Prop) :
    (state -> logged) ->
    AyWSCEquisat state (AyWSCReplayChunk state logged) := by
  intro produce_log
  exact ay_wsc_equisat_intro
    state
    (AyWSCReplayChunk state logged)
    (fun hstate =>
      ay_wsc_conj_intro state logged hstate (produce_log hstate))
    (ay_wsc_chunk_state state logged)
