-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for SAT-COMP-facing ay transformations.
-- These use Church encodings where clean's current checker is strongest.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

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

theorem ay_conj_assoc_forward
    (p : Prop) (q : Prop) (r : Prop) :
    AyConj p (AyConj q r) ->
    AyConj (AyConj p q) r := by
  intro grouped
  intro result
  intro build
  exact grouped result
    (fun hp tail =>
      tail result
        (fun hq hr =>
          build (ay_conj_intro p q hp hq) hr))

theorem ay_conj_assoc_backward
    (p : Prop) (q : Prop) (r : Prop) :
    AyConj (AyConj p q) r ->
    AyConj p (AyConj q r) := by
  intro grouped
  intro result
  intro build
  exact grouped result
    (fun head hr =>
      head result
        (fun hp hq =>
          build hp (ay_conj_intro q r hq hr)))

theorem ay_equisat_refl
    (p : Prop) :
    AyEquisat p p := by
  exact ay_conj_intro
    (p -> p)
    (p -> p)
    (fun hp => hp)
    (fun hp => hp)

theorem ay_equisat_symm
    (p : Prop) (q : Prop) :
    AyEquisat p q ->
    AyEquisat q p := by
  intro eqpq
  exact ay_conj_intro
    (q -> p)
    (p -> q)
    (eqpq (q -> p) (fun _forward backward => backward))
    (eqpq (p -> q) (fun forward _backward => forward))

theorem ay_equisat_forward
    (p : Prop) (q : Prop) :
    AyEquisat p q -> p -> q := by
  intro eqpq
  exact eqpq (p -> q) (fun forward _backward => forward)

theorem ay_equisat_backward
    (p : Prop) (q : Prop) :
    AyEquisat p q -> q -> p := by
  intro eqpq
  exact eqpq (q -> p) (fun _forward backward => backward)

theorem ay_equisat_trans
    (p : Prop) (q : Prop) (r : Prop) :
    AyEquisat p q ->
    AyEquisat q r ->
    AyEquisat p r := by
  intro eqpq
  intro eqqr
  exact ay_conj_intro
    (p -> r)
    (r -> p)
    (fun hp =>
      ay_equisat_forward q r eqqr
        (ay_equisat_forward p q eqpq hp))
    (fun hr =>
      ay_equisat_backward p q eqpq
        (ay_equisat_backward q r eqqr hr))

theorem ay_sat_resolution_sound
    (left : Prop) (right : Prop) (pivot : Prop) :
    AyDisj left pivot ->
    AyDisj right (Not pivot) ->
    AyDisj left right := by
  intro left_or_pivot
  intro right_or_not_pivot
  intro result
  intro left_to_result
  intro right_to_result
  exact left_or_pivot result left_to_result
    (fun pivot_sat =>
      right_or_not_pivot result right_to_result
        (fun pivot_unsat => False.elim (pivot_unsat pivot_sat)))

theorem ay_disj_comm
    (p : Prop) (q : Prop) :
    AyDisj p q -> AyDisj q p := by
  intro disj
  intro result
  intro q_to_result
  intro p_to_result
  exact disj result p_to_result q_to_result

theorem ay_self_subsuming_resolution_kernel
    (rest : Prop) (pivot : Prop) :
    AyDisj rest pivot ->
    AyDisj (Not pivot) rest ->
    AyDisj rest rest := by
  intro positive_parent
  intro negative_parent
  exact ay_sat_resolution_sound rest rest pivot
    positive_parent
    (ay_disj_comm (Not pivot) rest negative_parent)

def AyDuplicateCnf (sub : Prop) (left : Prop) (right : Prop) :=
  AyConj sub (AyConj left (AyConj sub right))

def AyFactoredCnf (sub : Prop) (left : Prop) (right : Prop) :=
  AyConj sub (AyConj left right)

theorem ay_duplicate_subconstraint_factor_forward
    (sub : Prop) (left : Prop) (right : Prop) :
    AyDuplicateCnf sub left right ->
    AyFactoredCnf sub left right := by
  intro original
  intro result
  intro build
  exact original result
    (fun hsub tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hsubAgain hright =>
              build hsub (ay_conj_intro left right hleft hright))))

theorem ay_duplicate_subconstraint_factor_backward
    (sub : Prop) (left : Prop) (right : Prop) :
    AyFactoredCnf sub left right ->
    AyDuplicateCnf sub left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hsub tail =>
      tail result
        (fun hleft hright =>
          build hsub
            (ay_conj_intro left (AyConj sub right) hleft
              (ay_conj_intro sub right hsub hright))))

theorem ay_duplicate_subconstraint_factor_equisat
    (sub : Prop) (left : Prop) (right : Prop) :
    AyEquisat
      (AyDuplicateCnf sub left right)
      (AyFactoredCnf sub left right) := by
  exact ay_conj_intro
    (AyDuplicateCnf sub left right -> AyFactoredCnf sub left right)
    (AyFactoredCnf sub left right -> AyDuplicateCnf sub left right)
    (ay_duplicate_subconstraint_factor_forward sub left right)
    (ay_duplicate_subconstraint_factor_backward sub left right)

def AySubsumedCnf (strong : Prop) (weak : Prop) (rest : Prop) :=
  AyConj strong (AyConj weak rest)

def AySubsumedDeletedCnf (strong : Prop) (rest : Prop) :=
  AyConj strong rest

theorem ay_subsumption_delete_forward
    (strong : Prop) (weak : Prop) (rest : Prop) :
    AySubsumedCnf strong weak rest ->
    AySubsumedDeletedCnf strong rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun hstrong tail =>
      tail result
        (fun _hweak hrest =>
          build hstrong hrest))

theorem ay_subsumption_delete_backward
    (strong : Prop) (weak : Prop) (rest : Prop) :
    (strong -> weak) ->
    AySubsumedDeletedCnf strong rest ->
    AySubsumedCnf strong weak rest := by
  intro entails
  intro deleted
  intro result
  intro build
  exact deleted result
    (fun hstrong hrest =>
      build hstrong
        (ay_conj_intro weak rest (entails hstrong) hrest))

theorem ay_subsumption_delete_equisat
    (strong : Prop) (weak : Prop) (rest : Prop) :
    (strong -> weak) ->
    AyEquisat
      (AySubsumedCnf strong weak rest)
      (AySubsumedDeletedCnf strong rest) := by
  intro entails
  exact ay_conj_intro
    (AySubsumedCnf strong weak rest -> AySubsumedDeletedCnf strong rest)
    (AySubsumedDeletedCnf strong rest -> AySubsumedCnf strong weak rest)
    (ay_subsumption_delete_forward strong weak rest)
    (ay_subsumption_delete_backward strong weak rest entails)

theorem ay_aux_extension_complete
    (base : Prop) (aux : Prop) :
    aux -> base -> AyConj aux base := by
  intro haux
  intro hbase
  exact ay_conj_intro aux base haux hbase
