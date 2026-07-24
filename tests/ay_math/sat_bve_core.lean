-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for binary variable elimination at the
-- propositional abstraction level.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def PivotParents (left : Prop) (right : Prop) (pivot : Prop) :=
  AyConj (AyDisj left pivot) (AyDisj right (Not pivot))

def PivotResolvent (left : Prop) (right : Prop) :=
  AyDisj left right

def PivotReconstruction (left : Prop) (right : Prop) (pivot : Prop) :=
  AyConj (left -> Not pivot) (right -> pivot)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_disj_left_intro
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_case
  intro _right_case
  exact left_case hp

theorem ay_disj_right_intro
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_case
  intro right_case
  exact right_case hq

theorem ay_bve_resolvent_projection_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    PivotParents left right pivot ->
    PivotResolvent left right := by
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

theorem ay_bve_reconstruct_from_left
    (left : Prop) (right : Prop) (pivot : Prop) :
    (left -> Not pivot) ->
    left ->
    PivotParents left right pivot := by
  intro reconstruct_not_pivot
  intro hleft
  exact ay_conj_intro
    (AyDisj left pivot)
    (AyDisj right (Not pivot))
    (ay_disj_left_intro left pivot hleft)
    (ay_disj_right_intro right (Not pivot)
      (reconstruct_not_pivot hleft))

theorem ay_bve_reconstruct_from_right
    (left : Prop) (right : Prop) (pivot : Prop) :
    (right -> pivot) ->
    right ->
    PivotParents left right pivot := by
  intro reconstruct_pivot
  intro hright
  exact ay_conj_intro
    (AyDisj left pivot)
    (AyDisj right (Not pivot))
    (ay_disj_right_intro left pivot
      (reconstruct_pivot hright))
    (ay_disj_left_intro right (Not pivot) hright)

theorem ay_bve_resolvent_reconstruction_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    PivotReconstruction left right pivot ->
    PivotResolvent left right ->
    PivotParents left right pivot := by
  intro reconstruct
  intro resolvent
  exact resolvent (PivotParents left right pivot)
    (fun hleft =>
      reconstruct (PivotParents left right pivot)
        (fun reconstruct_not_pivot _reconstruct_pivot =>
          ay_bve_reconstruct_from_left left right pivot
            reconstruct_not_pivot
            hleft))
    (fun hright =>
      reconstruct (PivotParents left right pivot)
        (fun _reconstruct_not_pivot reconstruct_pivot =>
          ay_bve_reconstruct_from_right left right pivot
            reconstruct_pivot
            hright))

theorem ay_bve_resolvent_replacement_equisat_with_reconstruction
    (left : Prop) (right : Prop) (pivot : Prop) :
    PivotReconstruction left right pivot ->
    AyConj
      (PivotParents left right pivot -> PivotResolvent left right)
      (PivotResolvent left right -> PivotParents left right pivot) := by
  intro reconstruct
  exact ay_conj_intro
    (PivotParents left right pivot -> PivotResolvent left right)
    (PivotResolvent left right -> PivotParents left right pivot)
    (ay_bve_resolvent_projection_sound left right pivot)
    (ay_bve_resolvent_reconstruction_sound left right pivot reconstruct)
