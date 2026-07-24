-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing interacting with
-- binary variable elimination. A failed-literal-derived unit simplifies a
-- pivot context before BVE projection; reconstruction composes back through
-- the simplified context.

def AyFailedBveConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedBveDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFailedBveEquisat (before : Prop) (after : Prop) :=
  AyFailedBveConj (before -> after) (after -> before)

def AyFailedBveProbe (rest : Prop) (literal : Prop) :=
  rest -> literal -> False

def AyFailedBvePivotParents (left : Prop) (right : Prop) (pivot : Prop) :=
  AyFailedBveConj
    (AyFailedBveDisj left pivot)
    (AyFailedBveDisj right (Not pivot))

def AyFailedBvePivotResolvent (left : Prop) (right : Prop) :=
  AyFailedBveDisj left right

def AyFailedBvePivotReconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyFailedBveConj (left -> Not pivot) (right -> pivot)

def AyFailedBveContextBefore
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyFailedBveConj rest
    (AyFailedBveConj
      (AyFailedBveDisj failedLiteral residual)
      (AyFailedBvePivotParents left right pivot))

def AyFailedBveContextSimplified
    (rest : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyFailedBveConj rest
    (AyFailedBveConj
      residual
      (AyFailedBvePivotParents left right pivot))

def AyFailedBveContextProjected
    (rest : Prop) (residual : Prop) (left : Prop) (right : Prop) :=
  AyFailedBveConj rest
    (AyFailedBveConj
      residual
      (AyFailedBvePivotResolvent left right))

theorem ay_failed_bve_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFailedBveConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_failed_bve_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFailedBveDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_failed_bve_disj_right
    (left : Prop) (right : Prop) :
    right -> AyFailedBveDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_failed_bve_failed_unit
    (rest : Prop) (literal : Prop) :
    AyFailedBveProbe rest literal ->
    rest ->
    Not literal :=
  fun failed restH literalH =>
    failed restH literalH

theorem ay_failed_bve_simplify_clause
    (rest : Prop) (failedLiteral : Prop) (residual : Prop) :
    AyFailedBveProbe rest failedLiteral ->
    rest ->
    AyFailedBveDisj failedLiteral residual ->
    residual :=
  fun failed restH clause =>
    clause residual
      (fun literalH =>
        False.elim (failed restH literalH))
      (fun residualH => residualH)

theorem ay_failed_bve_unsimplify_clause
    (failedLiteral : Prop) (residual : Prop) :
    residual ->
    AyFailedBveDisj failedLiteral residual :=
  fun residualH =>
    ay_failed_bve_disj_right failedLiteral residual residualH

theorem ay_failed_bve_projection
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBvePivotParents left right pivot ->
    AyFailedBvePivotResolvent left right := by
  intro parents
  intro result
  intro leftCase
  intro rightCase
  exact parents result
    (fun positiveParent negativeParent =>
      positiveParent result leftCase
        (fun pivotH =>
          negativeParent result rightCase
            (fun notPivotH => False.elim (notPivotH pivotH))))

theorem ay_failed_bve_reconstruct_from_left
    (left : Prop) (right : Prop) (pivot : Prop) :
    (left -> Not pivot) ->
    left ->
    AyFailedBvePivotParents left right pivot := by
  intro reconstructNotPivot
  intro leftH
  exact ay_failed_bve_conj_intro
    (AyFailedBveDisj left pivot)
    (AyFailedBveDisj right (Not pivot))
    (ay_failed_bve_disj_left left pivot leftH)
    (ay_failed_bve_disj_right right (Not pivot)
      (reconstructNotPivot leftH))

theorem ay_failed_bve_reconstruct_from_right
    (left : Prop) (right : Prop) (pivot : Prop) :
    (right -> pivot) ->
    right ->
    AyFailedBvePivotParents left right pivot := by
  intro reconstructPivot
  intro rightH
  exact ay_failed_bve_conj_intro
    (AyFailedBveDisj left pivot)
    (AyFailedBveDisj right (Not pivot))
    (ay_failed_bve_disj_right left pivot
      (reconstructPivot rightH))
    (ay_failed_bve_disj_left right (Not pivot) rightH)

theorem ay_failed_bve_reconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBvePivotReconstruction left right pivot ->
    AyFailedBvePivotResolvent left right ->
    AyFailedBvePivotParents left right pivot := by
  intro reconstruct
  intro resolvent
  exact resolvent (AyFailedBvePivotParents left right pivot)
    (fun leftH =>
      reconstruct (AyFailedBvePivotParents left right pivot)
        (fun reconstructNotPivot _reconstructPivot =>
          ay_failed_bve_reconstruct_from_left left right pivot
            reconstructNotPivot leftH))
    (fun rightH =>
      reconstruct (AyFailedBvePivotParents left right pivot)
        (fun _reconstructNotPivot reconstructPivot =>
          ay_failed_bve_reconstruct_from_right left right pivot
            reconstructPivot rightH))

theorem ay_failed_bve_simplified_forward
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveProbe rest failedLiteral ->
    AyFailedBveContextBefore
      rest failedLiteral residual left right pivot ->
    AyFailedBveContextSimplified rest residual left right pivot := by
  intro failed
  intro before
  exact before (AyFailedBveContextSimplified rest residual left right pivot)
    (fun restH tail =>
      tail (AyFailedBveContextSimplified rest residual left right pivot)
        (fun clause parents =>
          ay_failed_bve_conj_intro rest
            (AyFailedBveConj residual
              (AyFailedBvePivotParents left right pivot))
            restH
            (ay_failed_bve_conj_intro residual
              (AyFailedBvePivotParents left right pivot)
              (ay_failed_bve_simplify_clause
                rest failedLiteral residual failed restH clause)
              parents)))

theorem ay_failed_bve_simplified_backward
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveContextSimplified rest residual left right pivot ->
    AyFailedBveContextBefore
      rest failedLiteral residual left right pivot := by
  intro simplified
  exact simplified
    (AyFailedBveContextBefore rest failedLiteral residual left right pivot)
    (fun restH tail =>
      tail
        (AyFailedBveContextBefore
          rest failedLiteral residual left right pivot)
        (fun residualH parents =>
          ay_failed_bve_conj_intro rest
            (AyFailedBveConj
              (AyFailedBveDisj failedLiteral residual)
              (AyFailedBvePivotParents left right pivot))
            restH
            (ay_failed_bve_conj_intro
              (AyFailedBveDisj failedLiteral residual)
              (AyFailedBvePivotParents left right pivot)
              (ay_failed_bve_unsimplify_clause
                failedLiteral residual residualH)
              parents)))

theorem ay_failed_bve_simplified_equisat
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveProbe rest failedLiteral ->
    AyFailedBveEquisat
      (AyFailedBveContextBefore
        rest failedLiteral residual left right pivot)
      (AyFailedBveContextSimplified rest residual left right pivot) :=
  fun failed result keep =>
    keep
      (ay_failed_bve_simplified_forward
        rest failedLiteral residual left right pivot failed)
      (ay_failed_bve_simplified_backward
        rest failedLiteral residual left right pivot)

theorem ay_failed_bve_project_forward
    (rest : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveContextSimplified rest residual left right pivot ->
    AyFailedBveContextProjected rest residual left right := by
  intro simplified
  exact simplified
    (AyFailedBveContextProjected rest residual left right)
    (fun restH tail =>
      tail (AyFailedBveContextProjected rest residual left right)
        (fun residualH parents =>
          ay_failed_bve_conj_intro rest
            (AyFailedBveConj residual
              (AyFailedBvePivotResolvent left right))
            restH
            (ay_failed_bve_conj_intro residual
              (AyFailedBvePivotResolvent left right)
              residualH
              (ay_failed_bve_projection left right pivot parents))))

theorem ay_failed_bve_project_backward
    (rest : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBvePivotReconstruction left right pivot ->
    AyFailedBveContextProjected rest residual left right ->
    AyFailedBveContextSimplified rest residual left right pivot := by
  intro reconstruct
  intro projected
  exact projected
    (AyFailedBveContextSimplified rest residual left right pivot)
    (fun restH tail =>
      tail
        (AyFailedBveContextSimplified rest residual left right pivot)
        (fun residualH resolvent =>
          ay_failed_bve_conj_intro rest
            (AyFailedBveConj residual
              (AyFailedBvePivotParents left right pivot))
            restH
            (ay_failed_bve_conj_intro residual
              (AyFailedBvePivotParents left right pivot)
              residualH
              (ay_failed_bve_reconstruction
                left right pivot reconstruct resolvent))))

theorem ay_failed_bve_project_equisat
    (rest : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBvePivotReconstruction left right pivot ->
    AyFailedBveEquisat
      (AyFailedBveContextSimplified rest residual left right pivot)
      (AyFailedBveContextProjected rest residual left right) :=
  fun reconstruct result keep =>
    keep
      (ay_failed_bve_project_forward
        rest residual left right pivot)
      (ay_failed_bve_project_backward
        rest residual left right pivot reconstruct)

theorem ay_failed_bve_composed_forward
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveProbe rest failedLiteral ->
    AyFailedBveContextBefore
      rest failedLiteral residual left right pivot ->
    AyFailedBveContextProjected rest residual left right :=
  fun failed before =>
    ay_failed_bve_project_forward rest residual left right pivot
      (ay_failed_bve_simplified_forward
        rest failedLiteral residual left right pivot failed before)

theorem ay_failed_bve_composed_backward
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBvePivotReconstruction left right pivot ->
    AyFailedBveContextProjected rest residual left right ->
    AyFailedBveContextBefore
      rest failedLiteral residual left right pivot :=
  fun reconstruct projected =>
    ay_failed_bve_simplified_backward
      rest failedLiteral residual left right pivot
      (ay_failed_bve_project_backward
        rest residual left right pivot reconstruct projected)

theorem ay_failed_bve_composed_equisat
    (rest : Prop) (failedLiteral : Prop) (residual : Prop)
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyFailedBveProbe rest failedLiteral ->
    AyFailedBvePivotReconstruction left right pivot ->
    AyFailedBveEquisat
      (AyFailedBveContextBefore
        rest failedLiteral residual left right pivot)
      (AyFailedBveContextProjected rest residual left right) :=
  fun failed reconstruct result keep =>
    keep
      (ay_failed_bve_composed_forward
        rest failedLiteral residual left right pivot failed)
      (ay_failed_bve_composed_backward
        rest failedLiteral residual left right pivot reconstruct)
