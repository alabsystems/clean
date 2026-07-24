-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for chaining binary variable elimination
-- projection and reconstruction witnesses.

def AyBveChainConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyBveChainDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyBveProjection (before : Prop) (after : Prop) :=
  before -> after

def AyBveReconstruction (before : Prop) (after : Prop) :=
  after -> before

def AyBveElimination (before : Prop) (after : Prop) :=
  AyBveChainConj
    (AyBveProjection before after)
    (AyBveReconstruction before after)

def AyBvePivotParents (left : Prop) (right : Prop) (pivot : Prop) :=
  AyBveChainConj
    (AyBveChainDisj left pivot)
    (AyBveChainDisj right (Not pivot))

def AyBvePivotResolvent (left : Prop) (right : Prop) :=
  AyBveChainDisj left right

def AyBvePivotReconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :=
  AyBveChainConj (left -> Not pivot) (right -> pivot)

def AyBveTwoPivotBefore
    (left1 : Prop) (right1 : Prop) (pivot1 : Prop)
    (left2 : Prop) (right2 : Prop) (pivot2 : Prop) :=
  AyBveChainConj
    (AyBvePivotParents left1 right1 pivot1)
    (AyBvePivotParents left2 right2 pivot2)

def AyBveTwoPivotMiddle
    (left1 : Prop) (right1 : Prop)
    (left2 : Prop) (right2 : Prop) (pivot2 : Prop) :=
  AyBveChainConj
    (AyBvePivotResolvent left1 right1)
    (AyBvePivotParents left2 right2 pivot2)

def AyBveTwoPivotAfter
    (left1 : Prop) (right1 : Prop)
    (left2 : Prop) (right2 : Prop) :=
  AyBveChainConj
    (AyBvePivotResolvent left1 right1)
    (AyBvePivotResolvent left2 right2)

theorem ay_bve_chain_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyBveChainConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_bve_chain_disj_left_intro
    (p : Prop) (q : Prop) :
    p -> AyBveChainDisj p q := by
  intro hp
  intro result
  intro left_case
  intro _right_case
  exact left_case hp

theorem ay_bve_chain_disj_right_intro
    (p : Prop) (q : Prop) :
    q -> AyBveChainDisj p q := by
  intro hq
  intro result
  intro _left_case
  intro right_case
  exact right_case hq

theorem ay_bve_chain_projection_compose
    (original : Prop) (middle : Prop) (final : Prop) :
    AyBveProjection original middle ->
    AyBveProjection middle final ->
    AyBveProjection original final := by
  intro first_project
  intro second_project
  intro horiginal
  exact second_project (first_project horiginal)

theorem ay_bve_chain_reconstruction_compose
    (original : Prop) (middle : Prop) (final : Prop) :
    AyBveReconstruction original middle ->
    AyBveReconstruction middle final ->
    AyBveReconstruction original final := by
  intro first_reconstruct
  intro second_reconstruct
  intro hfinal
  exact first_reconstruct (second_reconstruct hfinal)

theorem ay_bve_chain_eliminations_compose
    (original : Prop) (middle : Prop) (final : Prop) :
    AyBveElimination original middle ->
    AyBveElimination middle final ->
    AyBveElimination original final := by
  intro first_elim
  intro second_elim
  exact first_elim (AyBveElimination original final)
    (fun first_project first_reconstruct =>
      second_elim (AyBveElimination original final)
        (fun second_project second_reconstruct =>
          ay_bve_chain_conj_intro
            (AyBveProjection original final)
            (AyBveReconstruction original final)
            (ay_bve_chain_projection_compose
              original middle final first_project second_project)
            (ay_bve_chain_reconstruction_compose
              original middle final first_reconstruct second_reconstruct)))

theorem ay_bve_chain_pivot_projection
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyBveProjection
      (AyBvePivotParents left right pivot)
      (AyBvePivotResolvent left right) := by
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

theorem ay_bve_chain_pivot_reconstruct_from_left
    (left : Prop) (right : Prop) (pivot : Prop) :
    (left -> Not pivot) ->
    left ->
    AyBvePivotParents left right pivot := by
  intro reconstruct_not_pivot
  intro hleft
  exact ay_bve_chain_conj_intro
    (AyBveChainDisj left pivot)
    (AyBveChainDisj right (Not pivot))
    (ay_bve_chain_disj_left_intro left pivot hleft)
    (ay_bve_chain_disj_right_intro right (Not pivot)
      (reconstruct_not_pivot hleft))

theorem ay_bve_chain_pivot_reconstruct_from_right
    (left : Prop) (right : Prop) (pivot : Prop) :
    (right -> pivot) ->
    right ->
    AyBvePivotParents left right pivot := by
  intro reconstruct_pivot
  intro hright
  exact ay_bve_chain_conj_intro
    (AyBveChainDisj left pivot)
    (AyBveChainDisj right (Not pivot))
    (ay_bve_chain_disj_right_intro left pivot
      (reconstruct_pivot hright))
    (ay_bve_chain_disj_left_intro right (Not pivot) hright)

theorem ay_bve_chain_pivot_reconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyBvePivotReconstruction left right pivot ->
    AyBveReconstruction
      (AyBvePivotParents left right pivot)
      (AyBvePivotResolvent left right) := by
  intro reconstruct
  intro resolvent
  exact resolvent (AyBvePivotParents left right pivot)
    (fun hleft =>
      reconstruct (AyBvePivotParents left right pivot)
        (fun reconstruct_not_pivot _reconstruct_pivot =>
          ay_bve_chain_pivot_reconstruct_from_left left right pivot
            reconstruct_not_pivot hleft))
    (fun hright =>
      reconstruct (AyBvePivotParents left right pivot)
        (fun _reconstruct_not_pivot reconstruct_pivot =>
          ay_bve_chain_pivot_reconstruct_from_right left right pivot
            reconstruct_pivot hright))

theorem ay_bve_chain_pivot_elimination
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyBvePivotReconstruction left right pivot ->
    AyBveElimination
      (AyBvePivotParents left right pivot)
      (AyBvePivotResolvent left right) := by
  intro reconstruct
  exact ay_bve_chain_conj_intro
    (AyBveProjection
      (AyBvePivotParents left right pivot)
      (AyBvePivotResolvent left right))
    (AyBveReconstruction
      (AyBvePivotParents left right pivot)
      (AyBvePivotResolvent left right))
    (ay_bve_chain_pivot_projection left right pivot)
    (ay_bve_chain_pivot_reconstruction left right pivot reconstruct)

theorem ay_bve_chain_two_pivot_projection
    (left1 : Prop) (right1 : Prop) (pivot1 : Prop)
    (left2 : Prop) (right2 : Prop) (pivot2 : Prop) :
    AyBveProjection
      (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
      (AyBveTwoPivotAfter left1 right1 left2 right2) := by
  intro before
  exact before (AyBveTwoPivotAfter left1 right1 left2 right2)
    (fun first_parents second_parents =>
      ay_bve_chain_conj_intro
        (AyBvePivotResolvent left1 right1)
        (AyBvePivotResolvent left2 right2)
        (ay_bve_chain_pivot_projection left1 right1 pivot1
          first_parents)
        (ay_bve_chain_pivot_projection left2 right2 pivot2
          second_parents))

theorem ay_bve_chain_two_pivot_reconstruction
    (left1 : Prop) (right1 : Prop) (pivot1 : Prop)
    (left2 : Prop) (right2 : Prop) (pivot2 : Prop) :
    AyBvePivotReconstruction left1 right1 pivot1 ->
    AyBvePivotReconstruction left2 right2 pivot2 ->
    AyBveReconstruction
      (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
      (AyBveTwoPivotAfter left1 right1 left2 right2) := by
  intro reconstruct_first
  intro reconstruct_second
  intro after
  exact after (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
    (fun first_resolvent second_resolvent =>
      ay_bve_chain_conj_intro
        (AyBvePivotParents left1 right1 pivot1)
        (AyBvePivotParents left2 right2 pivot2)
        (ay_bve_chain_pivot_reconstruction left1 right1 pivot1
          reconstruct_first first_resolvent)
        (ay_bve_chain_pivot_reconstruction left2 right2 pivot2
          reconstruct_second second_resolvent))

theorem ay_bve_chain_two_pivot_elimination
    (left1 : Prop) (right1 : Prop) (pivot1 : Prop)
    (left2 : Prop) (right2 : Prop) (pivot2 : Prop) :
    AyBvePivotReconstruction left1 right1 pivot1 ->
    AyBvePivotReconstruction left2 right2 pivot2 ->
    AyBveElimination
      (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
      (AyBveTwoPivotAfter left1 right1 left2 right2) := by
  intro reconstruct_first
  intro reconstruct_second
  exact ay_bve_chain_conj_intro
    (AyBveProjection
      (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
      (AyBveTwoPivotAfter left1 right1 left2 right2))
    (AyBveReconstruction
      (AyBveTwoPivotBefore left1 right1 pivot1 left2 right2 pivot2)
      (AyBveTwoPivotAfter left1 right1 left2 right2))
    (ay_bve_chain_two_pivot_projection
      left1 right1 pivot1 left2 right2 pivot2)
    (ay_bve_chain_two_pivot_reconstruction
      left1 right1 pivot1 left2 right2 pivot2
      reconstruct_first reconstruct_second)
