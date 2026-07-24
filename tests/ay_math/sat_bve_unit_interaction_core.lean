-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for the interaction between binary variable
-- elimination and unit propagation at a propositional abstraction level.

def AyBveUnitConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBveUnitDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBveUnitProjection (before : Prop) (after : Prop) :=
  before -> after

def AyBveUnitReconstruction (before : Prop) (after : Prop) :=
  after -> before

def AyBveUnitPivotParents (left : Prop) (right : Prop) (pivot : Prop) :=
  AyBveUnitConj
    (AyBveUnitDisj left pivot)
    (AyBveUnitDisj right (Not pivot))

def AyBveUnitPivotResolvent (left : Prop) (right : Prop) :=
  AyBveUnitDisj left right

def AyBveUnitPivotReconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyBveUnitConj (left -> Not pivot) (right -> pivot)

def AyBveUnitBeforePropagation (unit : Prop) (residual : Prop) :=
  AyBveUnitConj unit (AyBveUnitDisj (Not unit) residual)

def AyBveUnitAfterPropagation (unit : Prop) (residual : Prop) :=
  AyBveUnitConj unit residual

def AyBveUnitPipelineBefore
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :=
  AyBveUnitConj
    (AyBveUnitPivotParents left right pivot)
    (AyBveUnitBeforePropagation unit residual)

def AyBveUnitPipelineMiddle
    (left : Prop) (right : Prop)
    (unit : Prop) (residual : Prop) :=
  AyBveUnitConj
    (AyBveUnitPivotResolvent left right)
    (AyBveUnitBeforePropagation unit residual)

def AyBveUnitPipelineAfter
    (left : Prop) (right : Prop)
    (unit : Prop) (residual : Prop) :=
  AyBveUnitConj
    (AyBveUnitPivotResolvent left right)
    (AyBveUnitAfterPropagation unit residual)

def AyBveUnitEquisat (before : Prop) (after : Prop) :=
  AyBveUnitConj
    (AyBveUnitProjection before after)
    (AyBveUnitReconstruction before after)

theorem ay_bve_unit_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBveUnitConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_bve_unit_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBveUnitDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_bve_unit_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBveUnitDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_bve_unit_projection_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyBveUnitProjection before middle ->
    AyBveUnitProjection middle after ->
    AyBveUnitProjection before after :=
  fun first second hbefore => second (first hbefore)

theorem ay_bve_unit_reconstruction_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyBveUnitReconstruction before middle ->
    AyBveUnitReconstruction middle after ->
    AyBveUnitReconstruction before after :=
  fun first second hafter => first (second hafter)

theorem ay_bve_unit_bve_projection
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyBveUnitProjection
      (AyBveUnitPivotParents left right pivot)
      (AyBveUnitPivotResolvent left right) := by
  intro parents
  intro result
  intro left_case
  intro right_case
  exact parents result
    (fun positive_parent negative_parent =>
      positive_parent result left_case
        (fun pivot_sat =>
          negative_parent result right_case
            (fun pivot_unsat => False.elim (pivot_unsat pivot_sat))))

theorem ay_bve_unit_bve_reconstruct_from_left
    (left : Prop) (right : Prop) (pivot : Prop) :
    (left -> Not pivot) ->
    left ->
    AyBveUnitPivotParents left right pivot := by
  intro reconstruct_not_pivot
  intro hleft
  exact ay_bve_unit_conj_intro
    (AyBveUnitDisj left pivot)
    (AyBveUnitDisj right (Not pivot))
    (ay_bve_unit_disj_left left pivot hleft)
    (ay_bve_unit_disj_right right (Not pivot)
      (reconstruct_not_pivot hleft))

theorem ay_bve_unit_bve_reconstruct_from_right
    (left : Prop) (right : Prop) (pivot : Prop) :
    (right -> pivot) ->
    right ->
    AyBveUnitPivotParents left right pivot := by
  intro reconstruct_pivot
  intro hright
  exact ay_bve_unit_conj_intro
    (AyBveUnitDisj left pivot)
    (AyBveUnitDisj right (Not pivot))
    (ay_bve_unit_disj_right left pivot
      (reconstruct_pivot hright))
    (ay_bve_unit_disj_left right (Not pivot) hright)

theorem ay_bve_unit_bve_reconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyBveUnitPivotReconstruction left right pivot ->
    AyBveUnitReconstruction
      (AyBveUnitPivotParents left right pivot)
      (AyBveUnitPivotResolvent left right) := by
  intro reconstruct
  intro resolvent
  exact resolvent (AyBveUnitPivotParents left right pivot)
    (fun hleft =>
      reconstruct (AyBveUnitPivotParents left right pivot)
        (fun reconstruct_not_pivot _reconstruct_pivot =>
          ay_bve_unit_bve_reconstruct_from_left left right pivot
            reconstruct_not_pivot hleft))
    (fun hright =>
      reconstruct (AyBveUnitPivotParents left right pivot)
        (fun _reconstruct_not_pivot reconstruct_pivot =>
          ay_bve_unit_bve_reconstruct_from_right left right pivot
            reconstruct_pivot hright))

theorem ay_bve_unit_propagation_projection
    (unit : Prop) (residual : Prop) :
    AyBveUnitProjection
      (AyBveUnitBeforePropagation unit residual)
      (AyBveUnitAfterPropagation unit residual) := by
  intro before
  exact before (AyBveUnitAfterPropagation unit residual)
    (fun unit_sat clause =>
      ay_bve_unit_conj_intro unit residual
        unit_sat
        (clause residual
          (fun not_unit => False.elim (not_unit unit_sat))
          (fun residual_sat => residual_sat)))

theorem ay_bve_unit_propagation_reconstruction
    (unit : Prop) (residual : Prop) :
    AyBveUnitReconstruction
      (AyBveUnitBeforePropagation unit residual)
      (AyBveUnitAfterPropagation unit residual) := by
  intro after
  exact after (AyBveUnitBeforePropagation unit residual)
    (fun unit_sat residual_sat =>
      ay_bve_unit_conj_intro unit
        (AyBveUnitDisj (Not unit) residual)
        unit_sat
        (ay_bve_unit_disj_right (Not unit) residual residual_sat))

theorem ay_bve_unit_bve_pipeline_projection
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitProjection
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineMiddle left right unit residual) := by
  intro before
  exact before (AyBveUnitPipelineMiddle left right unit residual)
    (fun parents propagation_before =>
      ay_bve_unit_conj_intro
        (AyBveUnitPivotResolvent left right)
        (AyBveUnitBeforePropagation unit residual)
        (ay_bve_unit_bve_projection left right pivot parents)
        propagation_before)

theorem ay_bve_unit_bve_pipeline_reconstruction
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitPivotReconstruction left right pivot ->
    AyBveUnitReconstruction
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineMiddle left right unit residual) := by
  intro reconstruct
  intro middle
  exact middle (AyBveUnitPipelineBefore left right pivot unit residual)
    (fun resolvent propagation_before =>
      ay_bve_unit_conj_intro
        (AyBveUnitPivotParents left right pivot)
        (AyBveUnitBeforePropagation unit residual)
        (ay_bve_unit_bve_reconstruction left right pivot
          reconstruct resolvent)
        propagation_before)

theorem ay_bve_unit_unit_pipeline_projection
    (left : Prop) (right : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitProjection
      (AyBveUnitPipelineMiddle left right unit residual)
      (AyBveUnitPipelineAfter left right unit residual) := by
  intro middle
  exact middle (AyBveUnitPipelineAfter left right unit residual)
    (fun resolvent propagation_before =>
      ay_bve_unit_conj_intro
        (AyBveUnitPivotResolvent left right)
        (AyBveUnitAfterPropagation unit residual)
        resolvent
        (ay_bve_unit_propagation_projection unit residual
          propagation_before))

theorem ay_bve_unit_unit_pipeline_reconstruction
    (left : Prop) (right : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitReconstruction
      (AyBveUnitPipelineMiddle left right unit residual)
      (AyBveUnitPipelineAfter left right unit residual) := by
  intro after
  exact after (AyBveUnitPipelineMiddle left right unit residual)
    (fun resolvent propagation_after =>
      ay_bve_unit_conj_intro
        (AyBveUnitPivotResolvent left right)
        (AyBveUnitBeforePropagation unit residual)
        resolvent
        (ay_bve_unit_propagation_reconstruction unit residual
          propagation_after))

theorem ay_bve_unit_forward_map
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitProjection
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineAfter left right unit residual) := by
  exact ay_bve_unit_projection_compose
    (AyBveUnitPipelineBefore left right pivot unit residual)
    (AyBveUnitPipelineMiddle left right unit residual)
    (AyBveUnitPipelineAfter left right unit residual)
    (ay_bve_unit_bve_pipeline_projection
      left right pivot unit residual)
    (ay_bve_unit_unit_pipeline_projection
      left right unit residual)

theorem ay_bve_unit_backward_map
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitPivotReconstruction left right pivot ->
    AyBveUnitReconstruction
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineAfter left right unit residual) := by
  intro reconstruct
  exact ay_bve_unit_reconstruction_compose
    (AyBveUnitPipelineBefore left right pivot unit residual)
    (AyBveUnitPipelineMiddle left right unit residual)
    (AyBveUnitPipelineAfter left right unit residual)
    (ay_bve_unit_bve_pipeline_reconstruction
      left right pivot unit residual reconstruct)
    (ay_bve_unit_unit_pipeline_reconstruction
      left right unit residual)

theorem ay_bve_unit_interaction_equisat
    (left : Prop) (right : Prop) (pivot : Prop)
    (unit : Prop) (residual : Prop) :
    AyBveUnitPivotReconstruction left right pivot ->
    AyBveUnitEquisat
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineAfter left right unit residual) := by
  intro reconstruct
  exact ay_bve_unit_conj_intro
    (AyBveUnitProjection
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineAfter left right unit residual))
    (AyBveUnitReconstruction
      (AyBveUnitPipelineBefore left right pivot unit residual)
      (AyBveUnitPipelineAfter left right unit residual))
    (ay_bve_unit_forward_map left right pivot unit residual)
    (ay_bve_unit_backward_map left right pivot unit residual reconstruct)
