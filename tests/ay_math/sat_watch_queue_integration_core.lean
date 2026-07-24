-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction integrating watched-literal BCP with propagation queue
-- invariants. Watched clauses, queue states, propagated units, and conflicts
-- are abstract propositions; the theorems connect watched BCP steps to the
-- abstract propagation certificate carried by the queue.

def AyWQIConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyWQIDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyWQIEquisat (before : Prop) (after : Prop) :=
  AyWQIConj (before -> after) (after -> before)

def AyWQIClause (watchA : Prop) (watchB : Prop) (residual : Prop) :=
  AyWQIDisj watchA (AyWQIDisj watchB residual)

def AyWQIQueueInvariant (queue : Prop) (units : Prop) :=
  queue -> units

def AyWQIQueueCertificate
    (watchA : Prop) (watchB : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) :=
  AyWQIConj (AyWQIClause watchA watchB residual)
    (AyWQIQueueInvariant queue units)

def AyWQIWatchMoveCertificate (oldWatch : Prop) (newWatch : Prop) :=
  AyWQIConj (oldWatch -> newWatch) (newWatch -> oldWatch)

def AyWQIEnqueueStep (oldQueue : Prop) (newQueue : Prop) (unit : Prop) :=
  oldQueue -> AyWQIConj newQueue unit

def AyWQIConflictCertificate (watchA : Prop) (watchB : Prop) :=
  AyWQIConj (Not watchA) (Not watchB)

def AyWQIConflictTrace (queue : Prop) (units : Prop) (conflict : Prop) :=
  AyWQIConj (AyWQIConj queue units) conflict

def AyWQIAbstractPropagationCertificate
    (queue : Prop) (units : Prop) (unit : Prop) :=
  AyWQIConj (AyWQIQueueInvariant queue units) unit

def AyWQIWatchedPropagationCertificate
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (queue : Prop) (units : Prop) :=
  AyWQIConj
    (AyWQIClause watchA watchB unit)
    (AyWQIConj
      (AyWQIConflictCertificate watchA watchB)
      (AyWQIQueueInvariant queue units))

theorem ay_wqi_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyWQIConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_wqi_conj_left
    (p : Prop) (q : Prop) :
    AyWQIConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_wqi_disj_left
    (p : Prop) (q : Prop) :
    p -> AyWQIDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_wqi_disj_right
    (p : Prop) (q : Prop) :
    q -> AyWQIDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_wqi_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyWQIEquisat before after := by
  intro forward
  intro backward
  exact ay_wqi_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_wqi_move_clause_forward
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWQIWatchMoveCertificate oldWatch newWatch ->
    AyWQIClause oldWatch otherWatch residual ->
    AyWQIClause newWatch otherWatch residual := by
  intro move_cert
  intro clause
  exact clause (AyWQIClause newWatch otherWatch residual)
    (fun hold =>
      ay_wqi_disj_left newWatch (AyWQIDisj otherWatch residual)
        (ay_wqi_conj_left (oldWatch -> newWatch)
          (newWatch -> oldWatch) move_cert hold))
    (fun tail =>
      ay_wqi_disj_right newWatch (AyWQIDisj otherWatch residual) tail)

theorem ay_wqi_move_clause_backward
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWQIWatchMoveCertificate oldWatch newWatch ->
    AyWQIClause newWatch otherWatch residual ->
    AyWQIClause oldWatch otherWatch residual := by
  intro move_cert
  intro clause
  exact clause (AyWQIClause oldWatch otherWatch residual)
    (fun hnew =>
      ay_wqi_disj_left oldWatch (AyWQIDisj otherWatch residual)
        (move_cert oldWatch
          (fun (_old_to_new : oldWatch -> newWatch)
               (new_to_old : newWatch -> oldWatch) =>
            new_to_old hnew)))
    (fun tail =>
      ay_wqi_disj_right oldWatch (AyWQIDisj otherWatch residual) tail)

theorem ay_wqi_watch_movement_clause_equisat
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop) :
    AyWQIWatchMoveCertificate oldWatch newWatch ->
    AyWQIEquisat
      (AyWQIClause oldWatch otherWatch residual)
      (AyWQIClause newWatch otherWatch residual) := by
  intro move_cert
  exact ay_wqi_equisat_intro
    (AyWQIClause oldWatch otherWatch residual)
    (AyWQIClause newWatch otherWatch residual)
    (ay_wqi_move_clause_forward
      oldWatch newWatch otherWatch residual move_cert)
    (ay_wqi_move_clause_backward
      oldWatch newWatch otherWatch residual move_cert)

theorem ay_wqi_watch_movement_preserves_queue_certificate
    (oldWatch : Prop) (newWatch : Prop)
    (otherWatch : Prop) (residual : Prop)
    (queue : Prop) (units : Prop) :
    AyWQIWatchMoveCertificate oldWatch newWatch ->
    AyWQIQueueCertificate oldWatch otherWatch residual queue units ->
    AyWQIQueueCertificate newWatch otherWatch residual queue units := by
  intro move_cert
  intro certificate
  exact certificate
    (AyWQIQueueCertificate newWatch otherWatch residual queue units)
    (fun clause invariant =>
      ay_wqi_conj_intro
        (AyWQIClause newWatch otherWatch residual)
        (AyWQIQueueInvariant queue units)
        (ay_wqi_move_clause_forward
          oldWatch newWatch otherWatch residual move_cert clause)
        invariant)

theorem ay_wqi_unit_discovery_sound
    (watchA : Prop) (watchB : Prop) (unit : Prop) :
    AyWQIClause watchA watchB unit ->
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

theorem ay_wqi_unit_discovery_enqueues_sound_unit
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (oldQueue : Prop) (newQueue : Prop) :
    AyWQIClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    (oldQueue -> newQueue) ->
    oldQueue ->
    AyWQIConj newQueue unit := by
  intro clause
  intro notA
  intro notB
  intro enqueue
  intro old_queue
  exact ay_wqi_conj_intro newQueue unit
    (enqueue old_queue)
    (ay_wqi_unit_discovery_sound watchA watchB unit clause notA notB)

theorem ay_wqi_enqueue_step_from_unit_discovery
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (oldQueue : Prop) (newQueue : Prop) :
    AyWQIClause watchA watchB unit ->
    Not watchA ->
    Not watchB ->
    (oldQueue -> newQueue) ->
    AyWQIEnqueueStep oldQueue newQueue unit := by
  intro clause
  intro notA
  intro notB
  intro enqueue
  intro old_queue
  exact ay_wqi_unit_discovery_enqueues_sound_unit
    watchA watchB unit oldQueue newQueue clause notA notB enqueue old_queue

theorem ay_wqi_conflict_discovery_sound
    (watchA : Prop) (watchB : Prop) :
    AyWQIClause watchA watchB False ->
    AyWQIConflictCertificate watchA watchB ->
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

theorem ay_wqi_conflict_discovery_closes_queue_trace
    (watchA : Prop) (watchB : Prop)
    (queue : Prop) (units : Prop) :
    AyWQIClause watchA watchB False ->
    AyWQIConflictCertificate watchA watchB ->
    AyWQIQueueInvariant queue units ->
    queue ->
    AyWQIConflictTrace queue units False := by
  intro clause
  intro conflict_cert
  intro invariant
  intro hqueue
  exact ay_wqi_conj_intro
    (AyWQIConj queue units)
    False
    (ay_wqi_conj_intro queue units hqueue (invariant hqueue))
    (ay_wqi_conflict_discovery_sound watchA watchB clause conflict_cert)

theorem ay_wqi_watched_to_abstract_certificate
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (queue : Prop) (units : Prop) :
    AyWQIWatchedPropagationCertificate watchA watchB unit queue units ->
    AyWQIAbstractPropagationCertificate queue units unit := by
  intro watched_cert
  exact watched_cert
    (AyWQIAbstractPropagationCertificate queue units unit)
    (fun clause tail =>
      tail (AyWQIAbstractPropagationCertificate queue units unit)
        (fun conflict_cert invariant =>
          ay_wqi_conj_intro
            (AyWQIQueueInvariant queue units)
            unit
            invariant
            (conflict_cert unit
              (fun notA notB =>
                ay_wqi_unit_discovery_sound
                  watchA watchB unit clause notA notB))))

theorem ay_wqi_abstract_to_watched_certificate
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (queue : Prop) (units : Prop) :
    AyWQIClause watchA watchB unit ->
    AyWQIConflictCertificate watchA watchB ->
    AyWQIAbstractPropagationCertificate queue units unit ->
    AyWQIWatchedPropagationCertificate watchA watchB unit queue units := by
  intro clause
  intro conflict_cert
  intro abstract_cert
  exact abstract_cert
    (AyWQIWatchedPropagationCertificate watchA watchB unit queue units)
    (fun invariant _hunit =>
      ay_wqi_conj_intro
        (AyWQIClause watchA watchB unit)
        (AyWQIConj
          (AyWQIConflictCertificate watchA watchB)
          (AyWQIQueueInvariant queue units))
        clause
        (ay_wqi_conj_intro
          (AyWQIConflictCertificate watchA watchB)
          (AyWQIQueueInvariant queue units)
          conflict_cert
          invariant))

theorem ay_wqi_abstract_propagation_certificate_equiv
    (watchA : Prop) (watchB : Prop) (unit : Prop)
    (queue : Prop) (units : Prop) :
    AyWQIClause watchA watchB unit ->
    AyWQIConflictCertificate watchA watchB ->
    AyWQIEquisat
      (AyWQIWatchedPropagationCertificate watchA watchB unit queue units)
      (AyWQIAbstractPropagationCertificate queue units unit) := by
  intro clause
  intro conflict_cert
  exact ay_wqi_equisat_intro
    (AyWQIWatchedPropagationCertificate watchA watchB unit queue units)
    (AyWQIAbstractPropagationCertificate queue units unit)
    (ay_wqi_watched_to_abstract_certificate
      watchA watchB unit queue units)
    (ay_wqi_abstract_to_watched_certificate
      watchA watchB unit queue units clause conflict_cert)
