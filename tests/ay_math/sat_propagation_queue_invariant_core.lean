-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for Boolean propagation queue invariants.
-- Queue states, unit consequences, conflicts, learned units, and preprocessing
-- maps are abstract propositions standing for checker-visible facts.

def AyPQIConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyPQIDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPQIEquisat (before : Prop) (after : Prop) :=
  AyPQIConj (before -> after) (after -> before)

def AyPQIQueueInvariant (queue : Prop) (units : Prop) :=
  queue -> units

def AyPQIEnqueuePreserves (old_queue : Prop) (new_queue : Prop) :=
  old_queue -> new_queue

def AyPQIDequeuePreserves (old_queue : Prop) (new_queue : Prop) :=
  old_queue -> new_queue

def AyPQIConflictCheck (units : Prop) (conflict : Prop) :=
  units -> conflict

def AyPQILearnedUnitAdd (units : Prop) (learned_unit : Prop) :=
  units -> learned_unit

def AyPQIQueueWithLearned (queue : Prop) (learned_unit : Prop) :=
  AyPQIConj queue learned_unit

def AyPQIPropagationTrace (queue : Prop) (units : Prop) (conflict : Prop) :=
  AyPQIConj (AyPQIConj queue units) conflict

theorem ay_pqi_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyPQIConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pqi_conj_left
    (left : Prop) (right : Prop) :
    AyPQIConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pqi_conj_right
    (left : Prop) (right : Prop) :
    AyPQIConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pqi_disj_left
    (left : Prop) (right : Prop) :
    left -> AyPQIDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_pqi_disj_right
    (left : Prop) (right : Prop) :
    right -> AyPQIDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_pqi_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyPQIEquisat before after := by
  intro forward
  intro backward
  exact ay_pqi_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_pqi_equisat_forward
    (before : Prop) (after : Prop) :
    AyPQIEquisat before after -> before -> after := by
  intro certificate
  exact ay_pqi_conj_left (before -> after) (after -> before) certificate

theorem ay_pqi_equisat_backward
    (before : Prop) (after : Prop) :
    AyPQIEquisat before after -> after -> before := by
  intro certificate
  exact ay_pqi_conj_right (before -> after) (after -> before) certificate

theorem ay_pqi_enqueue_preserves_unit_consequence
    (old_queue : Prop) (new_queue : Prop) (units : Prop) :
    AyPQIEnqueuePreserves old_queue new_queue ->
    AyPQIQueueInvariant new_queue units ->
    old_queue ->
    units := by
  intro enqueue
  intro invariant
  intro old_sat
  exact invariant (enqueue old_sat)

theorem ay_pqi_dequeue_preserves_unit_consequence
    (old_queue : Prop) (new_queue : Prop) (units : Prop) :
    AyPQIDequeuePreserves old_queue new_queue ->
    AyPQIQueueInvariant new_queue units ->
    old_queue ->
    units := by
  intro dequeue
  intro invariant
  intro old_sat
  exact invariant (dequeue old_sat)

theorem ay_pqi_enqueue_dequeue_preserve_units
    (start_queue : Prop) (enqueued_queue : Prop)
    (dequeued_queue : Prop) (units : Prop) :
    AyPQIEnqueuePreserves start_queue enqueued_queue ->
    AyPQIDequeuePreserves enqueued_queue dequeued_queue ->
    AyPQIQueueInvariant dequeued_queue units ->
    start_queue ->
    units := by
  intro enqueue
  intro dequeue
  intro invariant
  intro start_sat
  exact invariant (dequeue (enqueue start_sat))

theorem ay_pqi_conflict_detection_sound
    (queue : Prop) (units : Prop) (conflict : Prop) :
    AyPQIQueueInvariant queue units ->
    AyPQIConflictCheck units conflict ->
    queue ->
    conflict := by
  intro invariant
  intro conflict_check
  intro queue_sat
  exact conflict_check (invariant queue_sat)

theorem ay_pqi_conflict_trace_sound
    (queue : Prop) (units : Prop) (conflict : Prop) :
    AyPQIQueueInvariant queue units ->
    AyPQIConflictCheck units conflict ->
    queue ->
    AyPQIPropagationTrace queue units conflict := by
  intro invariant
  intro conflict_check
  intro queue_sat
  exact ay_pqi_conj_intro
    (AyPQIConj queue units)
    conflict
    (ay_pqi_conj_intro queue units queue_sat (invariant queue_sat))
    (conflict_check (invariant queue_sat))

theorem ay_pqi_learned_unit_add_sound
    (queue : Prop) (units : Prop) (learned_unit : Prop) :
    AyPQIQueueInvariant queue units ->
    AyPQILearnedUnitAdd units learned_unit ->
    queue ->
    AyPQIQueueWithLearned queue learned_unit := by
  intro invariant
  intro learn
  intro queue_sat
  exact ay_pqi_conj_intro queue learned_unit
    queue_sat
    (learn (invariant queue_sat))

theorem ay_pqi_learned_unit_is_consequence
    (queue : Prop) (units : Prop) (learned_unit : Prop) :
    AyPQIQueueInvariant queue units ->
    AyPQILearnedUnitAdd units learned_unit ->
    queue ->
    learned_unit := by
  intro invariant
  intro learn
  intro queue_sat
  exact ay_pqi_conj_right queue learned_unit
    (ay_pqi_learned_unit_add_sound queue units learned_unit
      invariant learn queue_sat)

theorem ay_pqi_learned_queue_projection
    (queue : Prop) (learned_unit : Prop) :
    AyPQIQueueWithLearned queue learned_unit -> queue := by
  intro with_learned
  exact ay_pqi_conj_left queue learned_unit with_learned

theorem ay_pqi_learned_add_equisat
    (queue : Prop) (units : Prop) (learned_unit : Prop) :
    AyPQIQueueInvariant queue units ->
    AyPQILearnedUnitAdd units learned_unit ->
    AyPQIEquisat queue (AyPQIQueueWithLearned queue learned_unit) := by
  intro invariant
  intro learn
  exact ay_pqi_equisat_intro
    queue
    (AyPQIQueueWithLearned queue learned_unit)
    (ay_pqi_learned_unit_add_sound queue units learned_unit invariant learn)
    (ay_pqi_learned_queue_projection queue learned_unit)

theorem ay_pqi_transport_invariant_forward
    (before_queue : Prop) (after_queue : Prop) (units : Prop) :
    AyPQIEquisat before_queue after_queue ->
    AyPQIQueueInvariant after_queue units ->
    AyPQIQueueInvariant before_queue units := by
  intro certificate
  intro invariant
  intro before_sat
  exact invariant
    (ay_pqi_equisat_forward before_queue after_queue certificate before_sat)

theorem ay_pqi_transport_invariant_backward
    (before_queue : Prop) (after_queue : Prop) (units : Prop) :
    AyPQIEquisat before_queue after_queue ->
    AyPQIQueueInvariant before_queue units ->
    AyPQIQueueInvariant after_queue units := by
  intro certificate
  intro invariant
  intro after_sat
  exact invariant
    (ay_pqi_equisat_backward before_queue after_queue certificate after_sat)

theorem ay_pqi_transport_conflict_through_preprocess
    (before_queue : Prop) (after_queue : Prop)
    (units : Prop) (conflict : Prop) :
    AyPQIEquisat before_queue after_queue ->
    AyPQIQueueInvariant after_queue units ->
    AyPQIConflictCheck units conflict ->
    before_queue ->
    conflict := by
  intro certificate
  intro invariant
  intro conflict_check
  intro before_sat
  exact ay_pqi_conflict_detection_sound after_queue units conflict
    invariant
    conflict_check
    (ay_pqi_equisat_forward before_queue after_queue certificate before_sat)

theorem ay_pqi_transport_learned_unit_through_preprocess
    (before_queue : Prop) (after_queue : Prop)
    (units : Prop) (learned_unit : Prop) :
    AyPQIEquisat before_queue after_queue ->
    AyPQIQueueInvariant after_queue units ->
    AyPQILearnedUnitAdd units learned_unit ->
    before_queue ->
    learned_unit := by
  intro certificate
  intro invariant
  intro learn
  intro before_sat
  exact ay_pqi_learned_unit_is_consequence after_queue units learned_unit
    invariant
    learn
    (ay_pqi_equisat_forward before_queue after_queue certificate before_sat)

theorem ay_pqi_queue_pipeline_sound
    (before_queue : Prop) (after_queue : Prop)
    (enqueued_queue : Prop) (dequeued_queue : Prop)
    (units : Prop) (learned_unit : Prop) (conflict : Prop) :
    AyPQIEquisat before_queue after_queue ->
    AyPQIEnqueuePreserves after_queue enqueued_queue ->
    AyPQIDequeuePreserves enqueued_queue dequeued_queue ->
    AyPQIQueueInvariant dequeued_queue units ->
    AyPQILearnedUnitAdd units learned_unit ->
    AyPQIConflictCheck learned_unit conflict ->
    before_queue ->
    AyPQIConj learned_unit conflict := by
  intro certificate
  intro enqueue
  intro dequeue
  intro invariant
  intro learn
  intro conflict_check
  intro before_sat
  have units_sat : units :=
    ay_pqi_enqueue_dequeue_preserve_units
      after_queue enqueued_queue dequeued_queue units
      enqueue dequeue invariant
      (ay_pqi_equisat_forward before_queue after_queue certificate before_sat)
  have learned_sat : learned_unit := learn units_sat
  exact ay_pqi_conj_intro learned_unit conflict
    learned_sat
    (conflict_check learned_sat)
