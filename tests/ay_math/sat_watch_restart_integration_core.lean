-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction integrating watched-literal BCP, propagation queues, and
-- restart/trail reset soundness. Restart boundaries reset the trail but keep
-- watched clauses, queue invariants, learned unit facts, and conflict facts
-- transportable through the abstract certificate.

def AyWRIConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyWRIDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyWRIEquisat (before : Prop) (after : Prop) :=
  AyWRIConj (before -> after) (after -> before)

def AyWRIClause (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWRIDisj watchA (AyWRIDisj watchB residual)

def AyWRIQueueInvariant (queue : Prop) (units : Prop) :=
  queue -> units

def AyWRIWatchQueueCertificate
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) :=
  AyWRIConj (AyWRIClause watchA watchB residual)
    (AyWRIQueueInvariant queue units)

def AyWRILearnedCertificate (queue : Prop) (units : Prop) (learned : Prop) :=
  AyWRIConj (AyWRIQueueInvariant queue units) (units -> learned)

def AyWRIConflictCertificate (queue : Prop) (units : Prop) (conflict : Prop) :=
  AyWRIConj (AyWRIQueueInvariant queue units) (units -> conflict)

def AyWRIRestartReset (beforeQueue : Prop) (afterQueue : Prop) :=
  AyWRIEquisat beforeQueue afterQueue

def AyWRIRestartState
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) (learned : Prop) :=
  AyWRIConj
    (AyWRIWatchQueueCertificate watchA watchB residual queue units)
    learned

def AyWRIConflictTrace (queue : Prop) (units : Prop) (conflict : Prop) :=
  AyWRIConj (AyWRIConj queue units) conflict

def AyWRIModelReconstruction (visible : Prop) (original : Prop) :=
  visible -> original

theorem ay_wri_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyWRIConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_wri_conj_left
    (p : Prop) (q : Prop) :
    AyWRIConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_wri_disj_left
    (p : Prop) (q : Prop) :
    p -> AyWRIDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_wri_disj_right
    (p : Prop) (q : Prop) :
    q -> AyWRIDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_wri_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyWRIEquisat before after := by
  intro forward
  intro backward
  exact ay_wri_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_wri_equisat_forward
    (before : Prop) (after : Prop) :
    AyWRIEquisat before after ->
    before ->
    after := by
  intro certificate
  exact certificate (before -> after)
    (fun forward _backward => forward)

theorem ay_wri_equisat_backward
    (before : Prop) (after : Prop) :
    AyWRIEquisat before after ->
    after ->
    before := by
  intro certificate
  exact certificate (after -> before)
    (fun _forward backward => backward)

theorem ay_wri_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyWRIEquisat before middle ->
    AyWRIEquisat middle after ->
    AyWRIEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_wri_watch_queue_restart_forward
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop) (units : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units ->
    AyWRIWatchQueueCertificate watchA watchB residual afterQueue units := by
  intro reset
  intro certificate
  exact certificate
    (AyWRIWatchQueueCertificate watchA watchB residual afterQueue units)
    (fun clause invariant =>
      ay_wri_conj_intro
        (AyWRIClause watchA watchB residual)
        (AyWRIQueueInvariant afterQueue units)
        clause
        (fun after_queue =>
          invariant
            (ay_wri_equisat_backward beforeQueue afterQueue reset after_queue)))

theorem ay_wri_watch_queue_restart_backward
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop) (units : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIWatchQueueCertificate watchA watchB residual afterQueue units ->
    AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units := by
  intro reset
  intro certificate
  exact certificate
    (AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units)
    (fun clause invariant =>
      ay_wri_conj_intro
        (AyWRIClause watchA watchB residual)
        (AyWRIQueueInvariant beforeQueue units)
        clause
        (fun before_queue =>
          invariant
            (ay_wri_equisat_forward beforeQueue afterQueue reset before_queue)))

theorem ay_wri_watch_queue_certificate_survives_restart
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop) (units : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIEquisat
      (AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units)
      (AyWRIWatchQueueCertificate watchA watchB residual afterQueue units) := by
  intro reset
  exact ay_wri_equisat_intro
    (AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units)
    (AyWRIWatchQueueCertificate watchA watchB residual afterQueue units)
    (ay_wri_watch_queue_restart_forward
      watchA watchB residual beforeQueue afterQueue units reset)
    (ay_wri_watch_queue_restart_backward
      watchA watchB residual beforeQueue afterQueue units reset)

theorem ay_wri_learned_transport_forward
    (beforeQueue : Prop) (afterQueue : Prop)
    (units : Prop) (learned : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRILearnedCertificate beforeQueue units learned ->
    AyWRILearnedCertificate afterQueue units learned := by
  intro reset
  intro learned_cert
  exact learned_cert
    (AyWRILearnedCertificate afterQueue units learned)
    (fun invariant learn =>
      ay_wri_conj_intro
        (AyWRIQueueInvariant afterQueue units)
        (units -> learned)
        (fun after_queue =>
          invariant
            (ay_wri_equisat_backward beforeQueue afterQueue reset after_queue))
        learn)

theorem ay_wri_conflict_transport_forward
    (beforeQueue : Prop) (afterQueue : Prop)
    (units : Prop) (conflict : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIConflictCertificate beforeQueue units conflict ->
    AyWRIConflictCertificate afterQueue units conflict := by
  intro reset
  intro conflict_cert
  exact conflict_cert
    (AyWRIConflictCertificate afterQueue units conflict)
    (fun invariant conflict_from_units =>
      ay_wri_conj_intro
        (AyWRIQueueInvariant afterQueue units)
        (units -> conflict)
        (fun after_queue =>
          invariant
            (ay_wri_equisat_backward beforeQueue afterQueue reset after_queue))
        conflict_from_units)

theorem ay_wri_learned_unit_after_restart
    (queue : Prop) (units : Prop) (learned : Prop) :
    AyWRILearnedCertificate queue units learned ->
    queue ->
    learned := by
  intro learned_cert
  intro hqueue
  exact learned_cert learned
    (fun invariant learn => learn (invariant hqueue))

theorem ay_wri_conflict_trace_after_restart
    (queue : Prop) (units : Prop) (conflict : Prop) :
    AyWRIConflictCertificate queue units conflict ->
    queue ->
    AyWRIConflictTrace queue units conflict := by
  intro conflict_cert
  intro hqueue
  exact conflict_cert
    (AyWRIConflictTrace queue units conflict)
    (fun invariant conflict_from_units =>
      ay_wri_conj_intro
        (AyWRIConj queue units)
        conflict
        (ay_wri_conj_intro queue units hqueue (invariant hqueue))
        (conflict_from_units (invariant hqueue)))

theorem ay_wri_restart_state_forward
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop)
    (units : Prop) (learned : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIRestartState watchA watchB residual beforeQueue units learned ->
    AyWRIRestartState watchA watchB residual afterQueue units learned := by
  intro reset
  intro state
  exact state
    (AyWRIRestartState watchA watchB residual afterQueue units learned)
    (fun certificate hlearned =>
      ay_wri_conj_intro
        (AyWRIWatchQueueCertificate watchA watchB residual afterQueue units)
        learned
        (ay_wri_watch_queue_restart_forward
          watchA watchB residual beforeQueue afterQueue units reset certificate)
        hlearned)

theorem ay_wri_restart_state_backward
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop)
    (units : Prop) (learned : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIRestartState watchA watchB residual afterQueue units learned ->
    AyWRIRestartState watchA watchB residual beforeQueue units learned := by
  intro reset
  intro state
  exact state
    (AyWRIRestartState watchA watchB residual beforeQueue units learned)
    (fun certificate hlearned =>
      ay_wri_conj_intro
        (AyWRIWatchQueueCertificate watchA watchB residual beforeQueue units)
        learned
        (ay_wri_watch_queue_restart_backward
          watchA watchB residual beforeQueue afterQueue units reset certificate)
        hlearned)

theorem ay_wri_restart_state_equisat
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (beforeQueue : Prop) (afterQueue : Prop)
    (units : Prop) (learned : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    AyWRIEquisat
      (AyWRIRestartState watchA watchB residual beforeQueue units learned)
      (AyWRIRestartState watchA watchB residual afterQueue units learned) := by
  intro reset
  exact ay_wri_equisat_intro
    (AyWRIRestartState watchA watchB residual beforeQueue units learned)
    (AyWRIRestartState watchA watchB residual afterQueue units learned)
    (ay_wri_restart_state_forward
      watchA watchB residual beforeQueue afterQueue units learned reset)
    (ay_wri_restart_state_backward
      watchA watchB residual beforeQueue afterQueue units learned reset)

theorem ay_wri_final_model_reconstruction
    (original : Prop) (visible : Prop)
    (beforeQueue : Prop) (afterQueue : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    (beforeQueue -> original) ->
    (visible -> afterQueue) ->
    AyWRIModelReconstruction visible original := by
  intro reset
  intro reconstruct_before
  intro visible_to_after
  intro hvisible
  exact reconstruct_before
    (ay_wri_equisat_backward beforeQueue afterQueue reset
      (visible_to_after hvisible))

theorem ay_wri_final_equisat_with_reconstruction
    (original : Prop) (visible : Prop)
    (beforeQueue : Prop) (afterQueue : Prop) :
    AyWRIRestartReset beforeQueue afterQueue ->
    (original -> beforeQueue) ->
    (beforeQueue -> original) ->
    (afterQueue -> visible) ->
    (visible -> afterQueue) ->
    AyWRIEquisat original visible := by
  intro reset
  intro original_to_before
  intro before_to_original
  intro after_to_visible
  intro visible_to_after
  exact ay_wri_equisat_intro
    original
    visible
    (fun horiginal =>
      after_to_visible
        (ay_wri_equisat_forward beforeQueue afterQueue reset
          (original_to_before horiginal)))
    (ay_wri_final_model_reconstruction
      original visible beforeQueue afterQueue
      reset before_to_original visible_to_after)
