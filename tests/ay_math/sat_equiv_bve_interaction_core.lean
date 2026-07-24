-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for SCC/equivalence substitution interacting with
-- binary variable elimination reconstruction. The package is self-contained
-- and uses Church encodings, matching the SAT-COMP-facing theorem style.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquiv (p : Prop) (q : Prop) :=
  AyConj (p -> q) (q -> p)

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

theorem ay_equiv_forward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> p -> q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_equiv_backward
    (p : Prop) (q : Prop) :
    AyEquiv p q -> q -> p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

theorem ay_disj_map_left_forward
    (p : Prop) (q : Prop) (tail : Prop) :
    (p -> q) ->
    AyDisj p tail ->
    AyDisj q tail := by
  intro p_to_q
  intro disj
  intro result
  intro q_case
  intro tail_case
  exact disj result
    (fun hp => q_case (p_to_q hp))
    tail_case

theorem ay_disj_map_left_backward
    (p : Prop) (q : Prop) (tail : Prop) :
    (q -> p) ->
    AyDisj q tail ->
    AyDisj p tail := by
  intro q_to_p
  intro disj
  intro result
  intro p_case
  intro tail_case
  exact disj result
    (fun hq => p_case (q_to_p hq))
    tail_case

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

theorem ay_equiv_subst_pivot_parents_forward
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotParents left right pivot ->
    PivotParents leftSubst right pivot := by
  intro left_equiv_subst
  intro parents
  intro result
  intro build
  exact parents result
    (fun positiveParent negativeParent =>
      build
        (ay_disj_map_left_forward left leftSubst pivot
          (ay_equiv_forward left leftSubst left_equiv_subst)
          positiveParent)
        negativeParent)

theorem ay_equiv_subst_pivot_parents_backward
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotParents leftSubst right pivot ->
    PivotParents left right pivot := by
  intro left_equiv_subst
  intro parents
  intro result
  intro build
  exact parents result
    (fun positiveParent negativeParent =>
      build
        (ay_disj_map_left_backward left leftSubst pivot
          (ay_equiv_backward left leftSubst left_equiv_subst)
          positiveParent)
        negativeParent)

theorem ay_equiv_subst_resolvent_forward
    (left : Prop) (leftSubst : Prop) (right : Prop) :
    AyEquiv left leftSubst ->
    PivotResolvent left right ->
    PivotResolvent leftSubst right := by
  intro left_equiv_subst
  exact ay_disj_map_left_forward left leftSubst right
    (ay_equiv_forward left leftSubst left_equiv_subst)

theorem ay_equiv_subst_resolvent_backward
    (left : Prop) (leftSubst : Prop) (right : Prop) :
    AyEquiv left leftSubst ->
    PivotResolvent leftSubst right ->
    PivotResolvent left right := by
  intro left_equiv_subst
  exact ay_disj_map_left_backward left leftSubst right
    (ay_equiv_backward left leftSubst left_equiv_subst)

theorem ay_equiv_subst_reconstruction_forward
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotReconstruction left right pivot ->
    PivotReconstruction leftSubst right pivot := by
  intro left_equiv_subst
  intro reconstruct
  exact ay_conj_intro
    (leftSubst -> Not pivot)
    (right -> pivot)
    (fun hleftSubst =>
      reconstruct (Not pivot)
        (fun left_to_not_pivot _right_to_pivot =>
          left_to_not_pivot
            (ay_equiv_backward left leftSubst
              left_equiv_subst hleftSubst)))
    (reconstruct (right -> pivot)
      (fun _left_to_not_pivot right_to_pivot => right_to_pivot))

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

theorem ay_equiv_before_bve_projection_sound
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotParents left right pivot ->
    PivotResolvent leftSubst right := by
  intro left_equiv_subst
  intro parents
  exact ay_equiv_subst_resolvent_forward left leftSubst right
    left_equiv_subst
    (ay_bve_resolvent_projection_sound left right pivot parents)

theorem ay_equiv_before_bve_reconstruction_sound
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotReconstruction left right pivot ->
    PivotResolvent leftSubst right ->
    PivotParents left right pivot := by
  intro left_equiv_subst
  intro reconstruct
  intro substitutedResolvent
  exact ay_bve_resolvent_reconstruction_sound left right pivot
    reconstruct
    (ay_equiv_subst_resolvent_backward left leftSubst right
      left_equiv_subst substitutedResolvent)

theorem ay_equiv_before_bve_substituted_skeleton
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotReconstruction left right pivot ->
    AyConj
      (PivotParents left right pivot -> PivotResolvent leftSubst right)
      (PivotResolvent leftSubst right -> PivotParents left right pivot) := by
  intro left_equiv_subst
  intro reconstruct
  exact ay_conj_intro
    (PivotParents left right pivot -> PivotResolvent leftSubst right)
    (PivotResolvent leftSubst right -> PivotParents left right pivot)
    (ay_equiv_before_bve_projection_sound
      left leftSubst right pivot left_equiv_subst)
    (ay_equiv_before_bve_reconstruction_sound
      left leftSubst right pivot left_equiv_subst reconstruct)

theorem ay_equiv_before_bve_substituted_bve_skeleton
    (left : Prop) (leftSubst : Prop) (right : Prop) (pivot : Prop) :
    AyEquiv left leftSubst ->
    PivotReconstruction left right pivot ->
    AyConj
      (PivotParents leftSubst right pivot -> PivotResolvent leftSubst right)
      (PivotResolvent leftSubst right -> PivotParents leftSubst right pivot) := by
  intro left_equiv_subst
  intro reconstruct
  exact ay_conj_intro
    (PivotParents leftSubst right pivot -> PivotResolvent leftSubst right)
    (PivotResolvent leftSubst right -> PivotParents leftSubst right pivot)
    (ay_bve_resolvent_projection_sound leftSubst right pivot)
    (ay_bve_resolvent_reconstruction_sound leftSubst right pivot
      (ay_equiv_subst_reconstruction_forward
        left leftSubst right pivot left_equiv_subst reconstruct))
